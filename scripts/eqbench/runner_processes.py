"""Process ownership of one matrix-runner execution (eval plan v2 PR-A).

A runner claims a fresh owner token when it starts
(``validation_claim_process_ownership`` in ``validation_matrix_common.sh``):
it **re-executes itself** with ``EQBENCH_PROCESS_OWNER_TOKEN`` in its initial
environment before it starts anything.  ``/proc/<pid>/environ`` shows a
process's initial environment area, which a fork copies and an exec rebuilds
from the exported variables, so after the re-exec every process of that
execution carries the token there -- bash subshells that never exec (pair
jobs, the progress loop) as well as exec'd ones (GNU time, supervisors, the
analysis child: the supervisor passes its environment on; classifiers,
receipt writers) -- including a process whose parent has already died and
which has been re-parented away from the runner.  (A bash ``export`` alone
would not do: it changes the environment of later execs, not the shell's own
``/proc/<pid>/environ``, so a fork-only orphan would carry no token.)

On a stop request the runner calls :func:`stop` before it removes its run
tmpdir.  The owned set is "every process carrying the token" together with
"every descendant of the runner", so a pair job that was forked but not yet
registered with the scheduler is owned exactly like a registered one, and an
orphan that left the process tree is still found by its token.  The set is
frozen with SIGSTOP until a rescan finds nothing new (a frozen process cannot
start another one), then killed with SIGKILL and waited for.  Nothing is given
time to finish: a stopped pair must not get as far as classifying or
publishing a result, so there is no grace period and no setting it depends on.

A process this module cannot read is never taken for "not ours": a process
of the same user, started after the runner, whose environment cannot be read
(it made itself non-dumpable, say) and that is not provably a descendant is
*unverifiable*.  It is not signalled (it may belong to someone else), and
:func:`stop` reports it, so the caller keeps its tmpdir and fails.

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
#: How long an unverifiable process has to stay unverifiable to count.
UNVERIFIABLE_SETTLE_SECONDS = 1.0
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


def _environ(pid: int) -> Optional[bytes]:
    """The initial environment of ``pid``, or ``None`` when it cannot be read."""

    try:
        with open(f"/proc/{pid}/environ", "rb") as stream:
            return stream.read()
    except OSError:
        return None


def _uid(pid: int) -> Optional[int]:
    try:
        return os.stat(f"/proc/{pid}").st_uid
    except OSError:
        return None


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

    return scan(token, root, exclude=exclude)[0]


def scan(
    token: str, root: int, *, exclude: Iterable[int] = (),
) -> Tuple[Dict[int, int], Dict[int, int]]:
    """``(owned, unverifiable)``, each ``{pid: start time}`` of live processes.

    *owned*: carries ``token`` in its environment or descends from ``root``.
    *unverifiable*: not owned, but of this user, started at or after ``root``,
    and its environment could not be read -- so it cannot be shown not to be
    owned.  The listing of ``/proc`` itself failing raises.
    """

    if not token:
        raise ValueError("owner token is empty")
    needle = f"{OWNER_TOKEN_ENV}={token}".encode()
    excluded = _ancestors(os.getpid()) | {root} | set(exclude)
    root_stat = _stat(root)
    if root_stat is None:
        raise ValueError(f"the runner process {root} is not alive")
    root_start = root_stat[2]
    uid = os.getuid()
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
    unverifiable = set()
    for pid, (ppid, state, start) in stats.items():
        # kernel threads (kthreadd and its children) have no environment and are never ours
        if pid in owned or pid in excluded or state == "Z" or pid == 2 or ppid == 2:
            continue
        environ = _environ(pid)
        if environ is not None and environ:
            if needle in environ.split(b"\0"):
                owned.add(pid)
        elif _uid(pid) == uid and start >= root_start and _stat(pid) is not None:
            unverifiable.add(pid)
    live = {pid for pid in owned if pid not in excluded and stats[pid][1] != "Z"}
    return (
        {pid: stats[pid][2] for pid in live},
        {pid: stats[pid][2] for pid in unverifiable if pid not in live},
    )


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


def stop(token: str, root: int, *, wait_seconds: float = KILL_WAIT_SECONDS) -> Mapping[int, str]:
    """Freeze, kill and wait for every owned process.

    Returns what keeps the stop from being confirmed, ``{pid: reason}``: an
    owned process still alive after SIGKILL and ``wait_seconds``, or an
    unverifiable process (never signalled).  An empty result means every
    process of the run is confirmed gone.
    """

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
        if not survivors:
            break
        if time.monotonic() >= deadline:
            return {pid: "owned process survived SIGKILL" for pid in survivors}
        time.sleep(_POLL_SECONDS)
    owned, unverifiable = scan(token, root)
    # A process in the middle of exiting can briefly show an empty environment;
    # only what stays owned or unverifiable while it is watched is a problem.
    settle = time.monotonic() + UNVERIFIABLE_SETTLE_SECONDS
    while (owned or unverifiable) and time.monotonic() < settle:
        time.sleep(_POLL_SECONDS)
        owned_again, unverifiable_again = scan(token, root)
        owned = {pid: start for pid, start in owned_again.items()}
        unverifiable = {
            pid: start for pid, start in unverifiable.items()
            if unverifiable_again.get(pid) == start
        }
    problems = {pid: "owned process still alive after the stop" for pid in owned}
    problems.update(
        (pid, "process of this user whose ownership could not be read")
        for pid in unverifiable
    )
    return problems


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
    try:
        problems = stop(args.token, args.root)
    except (OSError, ValueError) as exc:
        print(f"runner_processes: the stop could not be carried out: {exc}", file=sys.stderr)
        return 1
    if problems:
        for pid, reason in sorted(problems.items()):
            print(f"runner_processes: pid {pid}: {reason}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
