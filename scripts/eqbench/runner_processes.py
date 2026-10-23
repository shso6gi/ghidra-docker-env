"""Process ownership of one matrix-runner execution (eval plan v2 PR-A).

A runner claims a fresh owner token when it starts
(``validation_claim_process_ownership`` in ``validation_matrix_common.sh``) and
exports it as ``EQBENCH_PROCESS_OWNER_TOKEN`` before it starts anything, so
every process of that execution -- pair jobs, GNU time, supervisors, the
analysis child (the supervisor passes its environment on), classifiers,
receipt writers -- carries it, including a process whose parent has already
died and which has been re-parented away from the runner.

On a stop request the runner calls :func:`stop` before it removes its run
tmpdir.  The owned set is "every process carrying the token" together with
"every descendant of the runner", so a pair job that was forked but not yet
registered with the scheduler is owned exactly like a registered one, and an
orphan that left the process tree is still found by its token.  The set is
frozen with SIGSTOP until a rescan finds nothing new (a frozen process cannot
start another one), then killed with SIGKILL and waited for.  Nothing is given
time to finish: a stopped pair must not get as far as classifying or
publishing a result, so there is no grace period and no setting it depends on.

Processes are named by ``(pid, start time)`` so a PID reused between the scan
and the signal is never signalled.  The caller and its ancestors are never
part of the owned set.
"""

from __future__ import annotations

import argparse
import os
import signal
import sys
import time
from typing import Dict, Iterable, Mapping, Optional, Tuple

OWNER_TOKEN_ENV = "EQBENCH_PROCESS_OWNER_TOKEN"
#: How long :func:`stop` waits for killed processes to disappear.  A process
#: that survives SIGKILL this long is stuck in the kernel; the caller then must
#: not remove the state that process may still use.
KILL_WAIT_SECONDS = 60.0
_POLL_SECONDS = 0.02
_FREEZE_ROUNDS = 200

Identity = Tuple[int, int]  # (pid, start time in clock ticks)


def _stat(pid: int) -> Optional[Tuple[int, str, int]]:
    """``(ppid, state, start time)`` of ``pid``, or ``None`` when it is gone."""

    try:
        with open(f"/proc/{pid}/stat", "rb") as stream:
            raw = stream.read().decode("ascii", "replace")
    except OSError:
        return None
    try:
        fields = raw.rsplit(")", 1)[1].split()
        return int(fields[1]), fields[0], int(fields[19])
    except (IndexError, ValueError):
        return None


def _carries_token(pid: int, token: bytes) -> bool:
    try:
        with open(f"/proc/{pid}/environ", "rb") as stream:
            environ = stream.read()
    except OSError:
        return False
    return token in environ.split(b"\0")


def _all_pids() -> Iterable[int]:
    for name in os.listdir("/proc"):
        if name.isdigit():
            yield int(name)


def _ancestors(pid: int) -> set:
    chain = set()
    while pid > 1 and pid not in chain:
        chain.add(pid)
        stat = _stat(pid)
        if stat is None:
            break
        pid = stat[0]
    return chain


def owned_processes(token: str, root: int, *, exclude: Iterable[int] = ()) -> Dict[int, int]:
    """Every live process carrying ``token`` or descending from ``root``.

    Returns ``{pid: start time}``.  ``root`` itself, the calling process and
    its ancestors, and ``exclude`` are never included.
    """

    if not token:
        raise ValueError("owner token is empty")
    needle = f"{OWNER_TOKEN_ENV}={token}".encode()
    excluded = _ancestors(os.getpid()) | {root} | set(exclude)
    stats: Dict[int, Tuple[int, str, int]] = {}
    for pid in _all_pids():
        stat = _stat(pid)
        if stat is not None:
            stats[pid] = stat
    children: Dict[int, list] = {}
    for pid, (ppid, _state, _start) in stats.items():
        children.setdefault(ppid, []).append(pid)
    owned = set()
    queue = [root]
    while queue:
        for child in children.get(queue.pop(), ()):
            if child not in owned:
                owned.add(child)
                queue.append(child)
    owned.update(pid for pid in stats if _carries_token(pid, needle))
    return {
        pid: stats[pid][2] for pid in owned
        if pid not in excluded and stats[pid][1] != "Z"
    }


def _is(identity: Identity) -> bool:
    stat = _stat(identity[0])
    return stat is not None and stat[2] == identity[1]


def _alive(identity: Identity) -> bool:
    stat = _stat(identity[0])
    return stat is not None and stat[2] == identity[1] and stat[1] != "Z"


def _signal(identity: Identity, signum: int) -> None:
    if _is(identity):
        try:
            os.kill(identity[0], signum)
        except ProcessLookupError:
            pass


def stop(token: str, root: int, *, wait_seconds: float = KILL_WAIT_SECONDS) -> Mapping[int, int]:
    """Freeze, kill and wait for every owned process.  Returns the survivors."""

    frozen: Dict[int, int] = {}
    for _ in range(_FREEZE_ROUNDS):
        new = {
            pid: start for pid, start in owned_processes(token, root).items()
            if frozen.get(pid) != start
        }
        if not new:
            break
        for identity in new.items():
            _signal(identity, signal.SIGSTOP)
        frozen.update(new)
    for identity in frozen.items():
        _signal(identity, signal.SIGKILL)
    deadline = time.monotonic() + wait_seconds
    while True:
        survivors = {pid: start for pid, start in frozen.items() if _alive((pid, start))}
        # A process that appeared after the last freeze round (it cannot have:
        # only a running owned process could have started it) is still owned.
        late = {
            pid: start for pid, start in owned_processes(token, root).items()
            if frozen.get(pid) != start
        }
        for identity in late.items():
            _signal(identity, signal.SIGKILL)
        frozen.update(late)
        survivors.update(late)
        if not survivors or time.monotonic() >= deadline:
            return survivors
        time.sleep(_POLL_SECONDS)


def main(arguments: Optional[list] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    stop_parser = sub.add_parser("stop", help="freeze, kill and reap every owned process")
    stop_parser.add_argument("--token", required=True)
    stop_parser.add_argument("--root", required=True, type=int)
    list_parser = sub.add_parser("list", help="print the owned processes (pid start)")
    list_parser.add_argument("--token", required=True)
    list_parser.add_argument("--root", required=True, type=int)
    args = parser.parse_args(arguments)
    if args.command == "list":
        for pid, start in sorted(owned_processes(args.token, args.root).items()):
            print(pid, start)
        return 0
    survivors = stop(args.token, args.root)
    if survivors:
        print(
            "runner_processes: owned processes survived SIGKILL: "
            + " ".join(str(pid) for pid in sorted(survivors)),
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
