from __future__ import annotations

import asyncio
import contextlib
import secrets
import string
import typing
import urllib.parse
from collections import namedtuple
from typing import Awaitable, List, Optional, cast

import aiohttp
from aiohttp import ServerDisconnectedError
from async_lru import alru_cache
from discord.backoff import ExponentialBackoff
from discord.ext.commands import Bot

try:
    from redbot import json
except ImportError:
    import json

from . import __version__, ws_discord_log, ws_ll_log
from .enums import *
from .filters import (
    ChannelMix,
    Distortion,
    Equalizer,
    Karaoke,
    LowPass,
    Rotation,
    Timescale,
    Tremolo,
    Vibrato,
    Volume,
)
from .player_manager import PlayerManager
from .rest_api import Track

__all__ = ["Stats", "Node", "NodeStats", "get_node", "get_nodes_stats", "join_voice"]

_nodes: List[Node] = []

PlayerState = namedtuple("PlayerState", "position time connected")
MemoryInfo = namedtuple("MemoryInfo", "reservable used free allocated")
CPUInfo = namedtuple("CPUInfo", "cores systemLoad lavalinkLoad")


# Originally Added in: https://github.com/PythonistaGuild/Wavelink/pull/66
class _Key:
    def __init__(self, Len: int = 32):
        self.Len: int = Len
        self.persistent: str = ""
        self.__repr__()

    def __repr__(self):
        """Generate a new key, return it and make it persistent"""
        alphabet = string.ascii_letters + string.digits + "#$%&()*+,-./:;<=>?@[]^_~!"
        key = "".join(secrets.choice(alphabet) for i in range(self.Len))
        self.persistent = key
        return key

    def __str__(self):
        """Return the persistent key."""
        # Ensure output is not a non-string
        # Since input could be Any object.
        if not self.persistent:
            return self.__repr__()
        return str(self.persistent)


class Stats:
    def __init__(self, memory, players, active_players, cpu, uptime):
        self.memory = MemoryInfo(**memory)
        self.players = players
        self.active_players = active_players
        self.cpu_info = CPUInfo(**cpu)
        self.uptime = uptime


# Node stats related class below and how it is called is originally from:
# https://github.com/PythonistaGuild/Wavelink/blob/master/wavelink/stats.py#L41
# https://github.com/PythonistaGuild/Wavelink/blob/master/wavelink/websocket.py#L132
class NodeStats:
    def __init__(self, data: dict):
        self.uptime = data["uptime"]

        self.players = data["players"]
        self.playing_players = data["playingPlayers"]

        memory = data["memory"]
        self.memory_free = memory["free"]
        self.memory_used = memory["used"]
        self.memory_allocated = memory["allocated"]
        self.memory_reservable = memory["reservable"]

        cpu = data["cpu"]
        self.cpu_cores = cpu["cores"]
        self.system_load = cpu["systemLoad"]
        self.lavalink_load = cpu["lavalinkLoad"]

        frame_stats = data.get("frameStats", {})
        self.frames_sent = frame_stats.get("sent", -1)
        self.frames_nulled = frame_stats.get("nulled", -1)
        self.frames_deficit = frame_stats.get("deficit", -1)

    def __repr__(self):
        return (
            "<NoteStats: "
            f"uptime={self.uptime}, "
            f"players={self.players}, "
            f"playing_players={self.playing_players}, "
            f"memory_free={self.memory_free}, memory_used={self.memory_used}, "
            f"cpu_cores={self.cpu_cores}, system_load={self.system_load}, "
            f"lavalink_load={self.lavalink_load}>"
        )


class Node:

    _is_shutdown = False  # type: bool

    def __init__(
        self,
        _loop: asyncio.BaseEventLoop,
        event_handler: typing.Callable,
        voice_ws_func: typing.Callable,
        password: str,
        user_id: int,
        num_shards: int,
        resume_key: Optional[str] = None,
        resume_timeout: int = 60,
        bot: Bot = None,
        client_name: Optional[str] = None,
        name: Optional[str] = "Primary",
        rest_uri: Optional[str] = None,
        host: Optional[str] = None,
        port: Optional[int] = None,
    ):
        """
        Represents a Lavalink node.

        Parameters
        ----------
        _loop : asyncio.BaseEventLoop
            The event loop of the bot.
        event_handler
            Function to dispatch events to.
        voice_ws_func : typing.Callable
            Function that takes one argument, guild ID, and returns a websocket.
        host : str
            Lavalink player host.
        password : str
            Password for the Lavalink player.
        port : int
            Port of the Lavalink player event websocket.
        rest : int
            Port for the Lavalink REST API.
        user_id : int
            User ID of the bot.
        num_shards : int
            Number of shards to which the bot is currently connected.
        resume_key : Optional[str]
            A resume key used for resuming a session upon re-establishing a WebSocket connection to Lavalink.
        resume_timeout : int
            How long the node should wait for a connection while disconnected before clearing all players.
        bot: AutoShardedBot
            The Bot object thats connect to discord.
        client_name: str
            The name of the connecting client.
        """
        if not rest_uri:
            if not all([port, host]):
                raise RuntimeError(
                    "`rest_uri` must be provided if both `port` and `host` are not."
                )
        self.loop = _loop
        self.bot = bot
        self.event_handler = event_handler
        self.get_voice_ws = voice_ws_func
        self.host = host
        self.port = port
        self.password = password
        self._resume_key = resume_key
        self.rest_uri = rest_uri

        if not self.rest_uri:
            self.rest_uri = f"{self.host}:{self.port}"
        ws_url = urllib.parse.urlparse(self.rest_uri)
        self.ws_uri = f"ws://{ws_url.netloc}"

        self.name = name
        if self._resume_key is None:
            self._resume_key = self._gen_key()
            self._client_name = client_name or f"Red-Lavalink-{__version__}--{self.bot.user.id}"
        else:
            self._client_name = client_name or f"Red-Lavalink-{__version__}--{self._resume_key}"

        self._resume_timeout = resume_timeout
        self._resuming_configured = False
        self.num_shards = num_shards
        self.user_id = user_id

        self._ready_event = asyncio.Event()

        self._ws = None
        self._listener_task = None
        self.session = aiohttp.ClientSession(json_serialize=json.dumps)

        self._queue: List = []

        self.state = NodeState.CONNECTING
        self._state_handlers: List = []
        self._retries = 0

        self.player_manager = PlayerManager(self)

        self.stats = None

        if self not in _nodes:
            _nodes.append(self)

        self._closers = (
            aiohttp.WSMsgType.CLOSE,
            aiohttp.WSMsgType.CLOSING,
            aiohttp.WSMsgType.CLOSED,
        )
        self._metadata_uri = f"{self.rest_uri}/metadata"

    @alru_cache(maxsize=32, cache_exceptions=False)
    async def server_metadata(self):
        try:
            async with aiohttp.ClientSession(json_serialize=json.dumps) as session:
                async with session.get(f"{self._metadata_uri}", headers=self.headers) as resp:
                    if resp.status != 200:
                        return {}
                    return await resp.json(content_type=None, loads=json.loads)
        except ServerDisconnectedError:
            return {}

    def __repr__(self):
        return (
            "<Node: "
            f"name={self.name}, "
            f"state={self.state.name}, "
            f"host={self.host}, "
            f"port={self.port}, "
            f"rest_uri={self.rest_uri}, "
            f"password={'*' * len(self.password)}, resume_key={self._resume_key}, "
            f"shards={self.num_shards}, user={self.user_id}, stats={self.stats}>"
        )

    @property
    def headers(self) -> dict:
        return self._get_connect_headers()

    def _gen_key(self):
        if self._resume_key is None:
            return _Key()
        else:
            # if this is a class then it will generate a persistent key
            # We should not't check the instance since
            # we would still make 1 extra call to check, which is useless.
            self._resume_key.__repr__()
            return self._resume_key

    async def connect(self, timeout=None):
        """
        Connects to the Lavalink player event websocket.

        Parameters
        ----------
        timeout : int
            Time after which to timeout on attempting to connect to the Lavalink websocket,
            ``None`` is considered never, but the underlying code may stop trying past a
            certain point.

        Raises
        ------
        asyncio.TimeoutError
            If the websocket failed to connect after the given time.
        """
        self._is_shutdown = False

        ws_ll_log.info(
            "[NODE-%s] | Lavalink WS connecting to %s with headers %s",
            self.name,
            self.ws_uri,
            self._get_connect_headers(show_password=False),
        )

        for task in asyncio.as_completed([self._multi_try_connect(self.ws_uri)], timeout=timeout):
            with contextlib.suppress(Exception):
                if await cast(Awaitable[Optional[aiohttp.ClientWebSocketResponse]], task):
                    break
        else:
            raise asyncio.TimeoutError

        ws_ll_log.debug("[NODE-%s] | Creating listener.", self.name)
        if self._listener_task is not None:
            self._listener_task.cancel()
        self._listener_task = self.loop.create_task(self.listener())
        self.loop.create_task(self._configure_resume())
        if self._queue:
            for data in self._queue:
                await self.send(data)
            self._queue.clear()
        self._ready_event.set()
        self.update_state(NodeState.READY)
        ws_ll_log.info("[NODE-%s] | WS Connected - Listening.", self.name)

    async def _configure_resume(self):
        if self._resuming_configured:
            return
        if self._resume_key and self._resume_timeout and self._resume_timeout > 0:
            await self.send(
                dict(
                    op="configureResuming",
                    key=str(self._resume_key),
                    timeout=self._resume_timeout,
                )
            )
            self._resuming_configured = True
            ws_ll_log.debug("[NODE-%s] | Resuming has been configured.", self.name)

    async def wait_until_ready(self, timeout: Optional[float] = None):
        await asyncio.wait_for(self._ready_event.wait(), timeout=timeout)

    def _get_connect_headers(self, show_password: bool = True) -> dict:
        headers = {
            "Authorization": self.password if show_password else "*" * len(self.password),
            "User-Id": str(self.user_id),
            "Client-Name": str(self._client_name),
        }
        if self._resume_key:
            headers["Resume-Key"] = str(self._resume_key)
        return headers

    @property
    def lavalink_major_version(self):
        if not self.ready:
            raise RuntimeError(f"[NODE-{self.name}] | Node not ready!")
        return self._ws.response_headers.get("Lavalink-Major-Version")

    @property
    def ready(self) -> bool:
        """
        Whether the underlying node is ready for requests.
        """
        return self.state == NodeState.READY

    async def _multi_try_connect(self, uri):
        backoff = ExponentialBackoff()
        attempt = 1
        if self._ws is not None:
            await self._ws.close(code=4006, message=b"Reconnecting")

        while self._is_shutdown is False and (self._ws is None or self._ws.closed):
            self._retries += 1
            try:
                ws = await self.session.ws_connect(url=uri, headers=self.headers, heartbeat=60)
            except (OSError, aiohttp.ClientConnectionError):
                delay = backoff.delay()
                ws_ll_log.error(
                    "[NODE-%s] |Failed connect attempt %s, retrying in %s",
                    self.name,
                    attempt,
                    delay,
                )
                await asyncio.sleep(delay)
                attempt += 1
                if attempt > 5:
                    raise asyncio.TimeoutError
            except aiohttp.WSServerHandshakeError:
                ws_ll_log.error("[NODE-%s] | Failed connect WSServerHandshakeError", self.name)
                return None
            else:
                self.session_resumed = ws._response.headers.get("Session-Resumed", False)
                if self._ws is not None and self.session_resumed:
                    ws_ll_log.info(
                        "[NODE-%s] | Resumed Session with key: %s", self.name, self._resume_key
                    )
                self._ws = ws
                return self._ws

    async def listener(self):
        """
        Listener task for receiving ops from Lavalink.
        """
        while self._is_shutdown is False:
            msg = await self._ws.receive()
            if msg.type in self._closers:
                if self._resuming_configured:
                    if self.state != NodeState.RECONNECTING:
                        ws_ll_log.info("[NODE-%s] | Resuming: %s", self.name, msg.extra)
                        self.update_state(NodeState.RECONNECTING)
                        self.loop.create_task(self._reconnect())
                    return
                else:
                    ws_ll_log.info("[NODE-%s] | Listener closing: %s", self.name, msg.extra)
                    break
            elif msg.type == aiohttp.WSMsgType.TEXT:
                data = msg.json(loads=json.loads)
                try:
                    op = LavalinkIncomingOp(data.get("op"))
                except ValueError:
                    ws_ll_log.info("[NODE-%s] | Received unknown op: %s", self.name, data)
                else:
                    ws_ll_log.debug("[NODE-%s] | Received known op: %s", self.name, data)
                    self.loop.create_task(self._handle_op(op, data))
            elif msg.type == aiohttp.WSMsgType.ERROR:
                exc = self._ws.exception()
                ws_ll_log.info("[NODE-%s] | Exception in WebSocket!", self.name, exc_info=exc)
                break
            else:
                ws_ll_log.info(
                    "[NODE-%s] | WebSocket connection received unexpected message: %s:%s",
                    self.name,
                    msg.type,
                    msg.data,
                )
        if self.state != NodeState.RECONNECTING:
            ws_ll_log.warning(
                "[NODE-%s] | WS closed: %s | Node Shutdown: %s.",
                self.name,
                self._ws.closed,
                self._is_shutdown,
            )
            self.update_state(NodeState.RECONNECTING)
            self.loop.create_task(self._reconnect())

    async def _handle_op(self, op: LavalinkIncomingOp, data):
        if op == LavalinkIncomingOp.EVENT:
            try:
                event = LavalinkEvents(data.get("type"))
            except ValueError:
                ws_ll_log.info("[NODE-%s] | Unknown event type: %s", self.name, data)
            else:
                self.event_handler(op, event, data)
        elif op == LavalinkIncomingOp.PLAYER_UPDATE:
            state = data.get("state", {})
            state = PlayerState(
                position=state.get("position", 0),
                time=state.get("time", 0),
                connected=state.get("connected", False),
            )
            self.event_handler(op, state, data)
        elif op == LavalinkIncomingOp.STATS:
            stats = Stats(
                memory=data.get("memory"),
                players=data.get("players"),
                active_players=data.get("playingPlayers"),
                cpu=data.get("cpu"),
                uptime=data.get("uptime"),
            )
            self.stats = NodeStats(data)
            self.event_handler(op, stats, data)
        else:
            ws_ll_log.info("[NODE-%s] | Unknown op type: %r", self.name, data)

    async def _reconnect(self):
        self._ready_event.clear()

        if self._is_shutdown is True:
            ws_ll_log.info("[NODE-%s] | Node is shutting down.", self.name)
            return
        if self.state != NodeState.CONNECTING:
            self.update_state(NodeState.RECONNECTING)
        if self.state != NodeState.RECONNECTING:
            return
        backoff = ExponentialBackoff(base=1)
        attempt = 1
        while self.state == NodeState.RECONNECTING:
            attempt += 1
            try:
                await self.connect()
            except asyncio.TimeoutError:
                delay = backoff.delay()
                ws_ll_log.info("[NODE-%s] | Failed to reconnect.", self.name)
                ws_ll_log.info(
                    "[NODE-%s] | Node WS reconnect connect attempt %s, retrying in %s",
                    self.name,
                    attempt,
                    delay,
                )

            else:
                ws_ll_log.info("[NODE-%s] | Reconnect successful.", self.name)
                self.dispatch_reconnect()
                self._retries = 0

    def dispatch_reconnect(self):
        for guild_id in self.player_manager.guild_ids:
            self.event_handler(
                LavalinkIncomingOp.EVENT,
                LavalinkEvents.WEBSOCKET_CLOSED,
                {
                    "guildId": guild_id,
                    "code": 42069,
                    "reason": "Lavalink WS reconnected",
                    "byRemote": True,
                    "retries": self._retries,
                },
            )

    def update_state(self, next_state: NodeState):
        if next_state == self.state:
            return

        ws_ll_log.debug(
            "[NODE-%s] | Changing state: %s -> %s", self.name, self.state.name, next_state.name
        )
        old_state = self.state
        self.state = next_state
        if self.loop.is_closed():
            ws_ll_log.debug(
                "[NODE-%s] | Event loop closed, not notifying state handlers.", self.name
            )
            return
        for handler in self._state_handlers:
            self.loop.create_task(handler(next_state, old_state))

    def register_state_handler(self, func):
        if not asyncio.iscoroutinefunction(func):
            raise ValueError("Argument must be a coroutine object.")

        if func not in self._state_handlers:
            self._state_handlers.append(func)

    def unregister_state_handler(self, func):
        self._state_handlers.remove(func)

    async def join_voice_channel(self, guild_id, channel_id, deafen: bool = False):
        """
        Alternative way to join a voice channel if node is known.
        """
        voice_ws = self.get_voice_ws(guild_id)
        await voice_ws.voice_state(guild_id, channel_id, self_deaf=deafen)

    async def disconnect(self):
        """
        Shuts down and disconnects the websocket.
        """
        self._is_shutdown = True
        self._ready_event.clear()

        self.update_state(NodeState.DISCONNECTING)

        if self._resuming_configured:
            await self.send(dict(op="configureResuming", key=None))
        self._resuming_configured = False
        await self.player_manager.disconnect()

        if self._ws is not None and not self._ws.closed:
            await self._ws.close()

        if self._listener_task is not None and not self.loop.is_closed():
            self._listener_task.cancel()

        await self.session.close()

        self._state_handlers = []

        _nodes.remove(self)
        ws_ll_log.info("[NODE-%s] | Shutdown WS.", self.name)

    async def send(self, data):
        if self._ws is None or self._ws.closed:
            self._queue.append(data)
        else:
            ws_ll_log.debug("[NODE-%s] | Sending data: %s", self.name, data)
            await self._ws.send_json(data)

    async def send_lavalink_voice_update(self, guild_id, session_id, event):
        await self.send(
            {
                "op": LavalinkOutgoingOp.VOICE_UPDATE.value,
                "guildId": str(guild_id),
                "sessionId": session_id,
                "event": event,
            }
        )

    async def destroy_guild(self, guild_id: int):
        await self.send({"op": LavalinkOutgoingOp.DESTROY.value, "guildId": str(guild_id)})

    async def no_event_stop(self, guild_id: int):
        await self.send({"op": LavalinkOutgoingOp.STOP.value, "guildId": str(guild_id)})

    # Player commands
    async def stop(self, guild_id: int):
        await self.no_event_stop(guild_id=guild_id)
        self.event_handler(
            LavalinkIncomingOp.EVENT, LavalinkEvents.QUEUE_END, {"guildId": str(guild_id)}
        )

    async def no_stop_play(
        self,
        guild_id: int,
        track: Track,
        replace: bool = True,
        start: int = 0,
        pause: bool = False,
    ):
        await self.send(
            {
                "op": LavalinkOutgoingOp.PLAY.value,
                "guildId": str(guild_id),
                "track": track.track_identifier,
                "noReplace": not replace,
                "startTime": str(start),
                "pause": pause,
            }
        )

    async def play(
        self,
        guild_id: int,
        track: Track,
        replace: bool = True,
        start: int = 0,
        pause: bool = False,
    ):
        await self.send({"op": LavalinkOutgoingOp.STOP.value, "guildId": str(guild_id)})
        await self.no_stop_play(
            guild_id=guild_id, track=track, replace=replace, start=start, pause=pause
        )

    async def pause(self, guild_id, paused):
        await self.send(
            {"op": LavalinkOutgoingOp.PAUSE.value, "guildId": str(guild_id), "pause": paused}
        )

    async def filters(
        self,
        *,
        guild_id: int,
        volume: Volume = None,
        equalizer: Equalizer = None,
        karaoke: Karaoke = None,
        timescale: Timescale = None,
        tremolo: Tremolo = None,
        vibrato: Vibrato = None,
        rotation: Rotation = None,
        distortion: Distortion = None,
        low_pass: LowPass = None,
        channel_mix: ChannelMix = None,
    ):
        op = {
            "op": LavalinkOutgoingOp.FILTERS.value,
            "guildId": str(guild_id),
        }
        if volume and volume.changed:
            op["volume"] = volume.get()
        if equalizer and equalizer.changed:
            op["equalizer"] = equalizer.get()
        if karaoke and karaoke.changed:
            op["karaoke"] = karaoke.get()
        if timescale and timescale.changed:
            op["timescale"] = timescale.get()
        if tremolo and tremolo.changed:
            op["tremolo"] = tremolo.get()
        if vibrato and vibrato.changed:
            op["vibrato"] = vibrato.get()
        if rotation and rotation.changed:
            op["rotation"] = rotation.get()
        if distortion and distortion.changed:
            op["distortion"] = distortion.get()
        if low_pass and low_pass.changed:
            op["lowPass"] = low_pass.get()
        if channel_mix and channel_mix.changed:
            op["channelMix"] = channel_mix.get()

        await self.send(op)

    async def volume(self, guild_id: int, volume: Volume):
        await self.send(
            {
                "op": LavalinkOutgoingOp.FILTERS.value,
                "guildId": str(guild_id),
                "volume": volume.get(),
            }
        )

    async def equalizer(self, guild_id: int, equalizer: Equalizer):
        await self.send(
            {
                "op": LavalinkOutgoingOp.EQUALIZER.value,
                "guildId": str(guild_id),
                "equalizer": equalizer.get(),
            }
        )

    async def karaoke(self, guild_id: int, karaoke: Karaoke):
        await self.send(
            {
                "op": LavalinkOutgoingOp.KARAOKE.value,
                "guildId": str(guild_id),
                "karaoke": karaoke.get(),
            }
        )

    async def timescale(self, guild_id: int, timescale: Timescale):
        await self.send(
            {
                "op": LavalinkOutgoingOp.TIMESCALE.value,
                "guildId": str(guild_id),
                "timescale": timescale.get(),
            }
        )

    async def tremolo(self, guild_id: int, tremolo: Tremolo):
        await self.send(
            {
                "op": LavalinkOutgoingOp.TREMOLO.value,
                "guildId": str(guild_id),
                "tremolo": tremolo.get(),
            }
        )

    async def vibrato(self, guild_id: int, vibrato: Vibrato):
        await self.send(
            {
                "op": LavalinkOutgoingOp.VIBRATO.value,
                "guildId": str(guild_id),
                "vibrato": vibrato.get(),
            }
        )

    async def rotation(self, guild_id: int, rotation: Rotation):
        await self.send(
            {
                "op": LavalinkOutgoingOp.ROTATION.value,
                "guildId": str(guild_id),
                "rotation": rotation.get(),
            }
        )

    async def distortion(self, guild_id: int, distortion: Distortion):
        await self.send(
            {
                "op": LavalinkOutgoingOp.DISTORTION.value,
                "guildId": str(guild_id),
                "distortion": distortion.get(),
            }
        )

    async def low_pass(self, guild_id: int, low_pass: LowPass):
        await self.send(
            {
                "op": LavalinkOutgoingOp.LOWPASS.value,
                "guildId": str(guild_id),
                "lowPass": low_pass.get(),
            }
        )

    async def channel_mix(self, guild_id: int, channel_mix: ChannelMix):
        await self.send(
            {
                "op": LavalinkOutgoingOp.CHANNELMIX.value,
                "guildId": str(guild_id),
                "channelMix": channel_mix.get(),
            }
        )

    async def seek(self, guild_id: int, position: int):
        await self.send(
            {"op": LavalinkOutgoingOp.SEEK.value, "guildId": str(guild_id), "position": position}
        )


def get_node(guild_id: int, ignore_ready_status: bool = False) -> Node:
    """
    Gets a node based on a guild ID, useful for noding separation. If the
    guild ID does not already have a node association, the least used
    node is returned. Skips over nodes that are not yet ready.

    Parameters
    ----------
    guild_id : int
    ignore_ready_status : bool

    Returns
    -------
    Node
    """
    guild_count = 1e10
    least_used = None

    for node in _nodes:
        guild_ids = node.player_manager.guild_ids

        if ignore_ready_status is False and not node.ready:
            continue
        elif len(guild_ids) < guild_count:
            guild_count = len(guild_ids)
            least_used = node

        if guild_id in guild_ids:
            return node

    if least_used is None:
        raise IndexError("No nodes found.")

    return least_used


def get_nodes_stats():
    return [node.stats for node in _nodes]


async def join_voice(guild_id: int, channel_id: int, deafen: bool = False):
    """
    Joins a voice channel by ID's.

    Parameters
    ----------
    guild_id : int
    channel_id : int
    """
    node = get_node(guild_id)
    await node.join_voice_channel(guild_id, channel_id, deafen)


async def disconnect():
    for node in _nodes.copy():
        await node.disconnect()


async def on_socket_response(data):
    raw_event = data.get("t")
    try:
        event = DiscordVoiceSocketResponses(raw_event)
    except ValueError:
        return

    guild_id = data["d"]["guild_id"]

    try:
        node = get_node(guild_id, ignore_ready_status=True)
    except IndexError:
        ws_ll_log.debug(
            f"Received unhandled Discord WS voice response for guild: %s, %s", guild_id, data
        )
    else:
        ws_ll_log.debug(
            f"[NODE-%s] | Received Discord WS voice response for guild: %s, %s",
            node.name,
            guild_id,
            data,
        )
        await node.player_manager.on_socket_response(data)
