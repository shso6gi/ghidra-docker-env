"""Process ownership of one matrix-runner execution (eval plan v2 PR-A).

A runner claims a fresh owner token when it starts
(``validation_claim_process_ownership`` in ``validation_matrix_common.sh``,
which asks :func:`claim`): it **re-executes itself** with
``EQBENCH_PROCESS_OWNER_TOKEN`` in its initial environment before it starts
anything.  The re-exec is bound to the runner's ``(pid, start time)``
(``EQBENCH_PROCESS_OWNER_ROOT`` / ``..._ROOT_START``; an exec keeps both), so
it happens exactly once: the re-executed image must find the token in its own
``/proc/<pid>/environ``, and if that cannot be confirmed -- not present, or
not readable -- the claim fails instead of re-executing again.  Owner values
inherited from another runner never match, so a nested runner takes its own
token.  ``/proc/<pid>/environ`` shows a
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
start another one), then killed with SIGKILL.  The stop is then confirmed by
one rule applied to every rescan: only the **latest** scan counts, every owned
process it shows is killed (again), and the stop succeeds only when two
consecutive scans, each finished before the deadline, show neither an owned nor
an unverifiable process.  :func:`stop` returns a :class:`StopResult` whose
verdict -- not whether the latest scan was empty -- says whether it succeeded.  A
process that appears, disappears, is replaced by its child or becomes readable
while the stop is being confirmed is judged by that same rule.  The deadline
is checked before success after every scan, so a scan finished at or after it
never counts: when the deadline comes first -- or unverifiable processes have
been seen continuously for :data:`UNVERIFIABLE_SETTLE_SECONDS` -- the stop
fails, even if the latest scan showed nothing (its findings are reported as a
diagnostic only).  Nothing is given time to finish: a stopped pair must not get as far as classifying or
publishing a result, so there is no grace period and no setting it depends on.

A process this module cannot read is never taken for "not ours": a process
of the same user, started after the runner, whose environment cannot be read
(it made itself non-dumpable, say) and that is not provably a descendant is
*unverifiable*.  It is not signalled (it may belong to someone else), and
:func:`stop` reports it, so the caller keeps its tmpdir and fails.

A process that is already exiting (``PF_EXITING``: it runs no more user code
and can start nothing) and kernel threads (``PF_KTHREAD``) are told apart by
the flags in ``/proc/<pid>/stat``; an exiting process shows an empty
environment, so it is never taken for unverifiable.

Processes are named by ``(pid, start time)`` so a PID reused between the scan
and the signal is never signalled.  The caller and its ancestors are never
part of the owned set.
"""

from __future__ import annotations

import argparse
import os
import re
import secrets
import signal
import sys
import time
from enum import Enum
from typing import Dict, Iterable, Mapping, NamedTuple, Optional, Tuple

OWNER_TOKEN_ENV = "EQBENCH_PROCESS_OWNER_TOKEN"
OWNER_ROOT_ENV = "EQBENCH_PROCESS_OWNER_ROOT"
OWNER_ROOT_START_ENV = "EQBENCH_PROCESS_OWNER_ROOT_START"
#: ``claim`` exit code: re-execute with the printed ``<token> <start time>``.
CLAIM_REEXEC_EXIT = 3
#: How long :func:`stop` waits for killed processes to disappear.  A process
#: that survives SIGKILL this long is stuck in the kernel; the caller then must
#: not remove the state that process may still use.
KILL_WAIT_SECONDS = 60.0
#: How long unverifiable processes may be seen without a break before the stop
#: fails (a process in the middle of an exec briefly shows an empty environment).
UNVERIFIABLE_SETTLE_SECONDS = 1.0
#: Consecutive scans that must show nothing for the stop to be confirmed.
CLEAN_SCANS = 2
_PF_EXITING = 0x00000004
_PF_KTHREAD = 0x00200000
_TOKEN = re.compile(r"[0-9a-f]{32}")
_POLL_SECONDS = 0.02
_FREEZE_ROUNDS = 200

Identity = Tuple[int, int]  # (pid, start time in clock ticks)


def _stat(pid: int) -> Optional[Tuple[int, str, int, int]]:
    """``(ppid, state, start time, flags)`` of ``pid``, or ``None`` when it is gone."""

    try:
        with open(f"/proc/{pid}/stat", "rb") as stream:
            raw = stream.read().decode("ascii", "replace")
    except OSError:
        return None
    try:
        fields = raw.rsplit(")", 1)[1].split()
        return int(fields[1]), fields[0], int(fields[19]), int(fields[6])
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
    still running (not exiting), and its environment could not be read or was
    empty -- so it cannot be shown not to be owned.  The listing of ``/proc``
    itself failing raises.
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
    stats: Dict[int, Tuple[int, str, int, int]] = {}
    for pid in _all_pids():
        stat = _stat(pid)
        if stat is not None:
            stats[pid] = stat
    children: Dict[int, list] = {}
    for pid, (ppid, _state, _start, _flags) in stats.items():
        children.setdefault(ppid, []).append(pid)
    owned = set()
    queue = [root]
    while queue:
        for child in children.get(queue.pop(), ()):
            if child not in owned:
                owned.add(child)
                queue.append(child)
    unverifiable = set()
    for pid, (_ppid, state, start, flags) in stats.items():
        # kernel threads have no environment and are never ours; an exiting process
        # runs no more user code (its environment reads empty once its memory is gone)
        if pid in owned or pid in excluded or not _running(state, flags):
            continue
        environ = _environ(pid)
        if environ:
            if needle in environ.split(b"\0"):
                owned.add(pid)
        elif _uid(pid) == uid and start >= root_start and _still_running(pid, start):
            unverifiable.add(pid)
    live = {pid for pid in owned if pid not in excluded and stats[pid][1] != "Z"}
    return (
        {pid: stats[pid][2] for pid in live},
        {pid: stats[pid][2] for pid in unverifiable if pid not in live},
    )


def _running(state: str, flags: int) -> bool:
    return state != "Z" and not flags & (_PF_EXITING | _PF_KTHREAD)


def _still_running(pid: int, start: int) -> bool:
    """``pid`` is still the process that started at ``start`` and is not exiting.

    Read *after* its environment, so an environment that read empty because the
    process had begun to exit is never mistaken for an unreadable one.
    """

    stat = _stat(pid)
    return stat is not None and stat[2] == start and _running(stat[1], stat[3])


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


class StopVerdict(str, Enum):
    """How :func:`stop` ended.  Only ``CONFIRMED`` lets the caller remove state."""

    #: :data:`CLEAN_SCANS` consecutive scans, each finished before the deadline,
    #: showed neither an owned nor an unverifiable process.
    CONFIRMED = "CONFIRMED"
    #: The deadline came before the stop was confirmed (whatever the last scan showed).
    DEADLINE = "DEADLINE"
    #: Unverifiable processes were seen without a break for ``settle_seconds``.
    UNVERIFIABLE = "UNVERIFIABLE"


class StopResult(NamedTuple):
    verdict: StopVerdict
    #: What the latest scan showed, ``{pid: reason}``.  It is a diagnostic only:
    #: it can be empty when the verdict is not ``CONFIRMED`` (the deadline came
    #: before enough clean scans), and the verdict alone decides success.
    problems: Mapping[int, str]
    #: Consecutive clean scans finished before the deadline (diagnostic).
    clean_scans: int

    @property
    def confirmed(self) -> bool:
        return self.verdict is StopVerdict.CONFIRMED


def stop(
    token: str, root: int, *,
    wait_seconds: float = KILL_WAIT_SECONDS,
    settle_seconds: float = UNVERIFIABLE_SETTLE_SECONDS,
) -> StopResult:
    """Freeze and kill every owned process, then confirm none is left.

    The stop is confirmed only when :data:`CLEAN_SCANS` consecutive scans,
    **each finished before the deadline** (``wait_seconds`` from the call),
    showed neither an owned nor an unverifiable process.  The deadline is
    checked first after every scan: a scan finished at or after it never counts,
    so a stop that could not be confirmed in time is ``DEADLINE`` even if that
    scan was clean.  Unverifiable processes seen without a break for
    ``settle_seconds`` end the stop as ``UNVERIFIABLE``.  Failing to observe
    the process table raises (``OSError`` / ``ValueError``); the caller treats
    that as a failed stop too.
    """

    deadline = time.monotonic() + wait_seconds
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
    killed = dict(frozen)
    for identity in killed.items():
        _signal(identity, signal.SIGKILL)
    clean = 0
    unverifiable_since: Optional[float] = None
    while True:
        # Only the latest scan counts: whatever it shows -- a survivor, a process
        # that appeared or became readable, a child left by an exited parent --
        # keeps the stop unconfirmed.  Owned processes are killed (again).
        owned, unverifiable = scan(token, root)
        for identity in owned.items():
            _signal(identity, signal.SIGKILL)
        killed.update(owned)
        survivors = {pid: start for pid, start in killed.items() if _alive((pid, start))}
        survivors.update(owned)
        problems = {pid: "owned process still alive after the stop" for pid in survivors}
        problems.update(
            (pid, "process of this user whose ownership could not be read")
            for pid in unverifiable
        )
        now = time.monotonic()
        # The deadline comes first: a scan finished at or after it does not count.
        if now >= deadline:
            return StopResult(StopVerdict.DEADLINE, problems, clean)
        if problems:
            clean = 0
        else:
            clean += 1
            if clean >= CLEAN_SCANS:
                return StopResult(StopVerdict.CONFIRMED, {}, clean)
        if not unverifiable:
            unverifiable_since = None
        elif unverifiable_since is None:
            unverifiable_since = now
        elif now - unverifiable_since >= settle_seconds:
            return StopResult(StopVerdict.UNVERIFIABLE, problems, clean)
        time.sleep(_POLL_SECONDS)


class OwnershipError(Exception):
    """The re-executed runner cannot confirm the owner token it was given."""


def claim(pid: int, environment: Mapping[str, str]) -> Optional[Tuple[str, int]]:
    """Decide the ownership claim of the runner ``pid``.

    ``environment`` is the runner's current environment.  Returns ``None`` when
    ``pid`` is the re-executed runner and its initial environment
    (``/proc/<pid>/environ``) carries its token; otherwise a fresh
    ``(token, start time)`` to re-execute with.  Raises :class:`OwnershipError`
    when ``pid`` is the re-executed runner but the token is missing or cannot
    be read -- re-executing again could never fix that.
    """

    stat = _stat(pid)
    if stat is None:
        raise OwnershipError(f"the runner process {pid} is not alive")
    start = stat[2]
    if (environment.get(OWNER_ROOT_ENV), environment.get(OWNER_ROOT_START_ENV)) != (
        str(pid), str(start),
    ):
        return secrets.token_hex(16), start
    token = environment.get(OWNER_TOKEN_ENV, "")
    if not _TOKEN.fullmatch(token):
        raise OwnershipError("the re-executed runner has no valid owner token")
    try:
        with open(f"/proc/{pid}/environ", "rb") as stream:
            entries = stream.read().split(b"\0")
    except OSError as exc:
        raise OwnershipError(f"the runner's environment cannot be read: {exc}") from exc
    if f"{OWNER_TOKEN_ENV}={token}".encode() not in entries:
        raise OwnershipError("the owner token is not in the runner's initial environment")
    return None


def main(arguments: Optional[list] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    stop_parser = sub.add_parser("stop", help="freeze, kill and reap every owned process")
    stop_parser.add_argument("--token", required=True)
    stop_parser.add_argument("--root", required=True, type=int)
    list_parser = sub.add_parser("list", help="print the owned processes (pid start)")
    list_parser.add_argument("--token", required=True)
    list_parser.add_argument("--root", required=True, type=int)
    claim_parser = sub.add_parser(
        "claim",
        help=f"exit 0 when PID holds its claim; exit {CLAIM_REEXEC_EXIT} printing "
        "'<token> <start time>' to re-execute with; exit 1 when it cannot be confirmed",
    )
    claim_parser.add_argument("--pid", required=True, type=int)
    args = parser.parse_args(arguments)
    if args.command == "claim":
        try:
            reexec = claim(args.pid, os.environ)
        except OwnershipError as exc:
            print(f"runner_processes: the ownership claim failed: {exc}", file=sys.stderr)
            return 1
        if reexec is None:
            return 0
        print(*reexec)
        return CLAIM_REEXEC_EXIT
    if args.command == "list":
        for pid, start in sorted(owned_processes(args.token, args.root).items()):
            print(pid, start)
        return 0
    try:
        result = stop(args.token, args.root)
    except (OSError, ValueError) as exc:
        print(f"runner_processes: the stop could not be carried out: {exc}", file=sys.stderr)
        return 1
    if result.confirmed:
        return 0
    print(
        f"runner_processes: the stop was not confirmed ({result.verdict.value}; "
        f"{result.clean_scans} of {CLEAN_SCANS} consecutive clean scans before the deadline)",
        file=sys.stderr,
    )
    for pid, reason in sorted(result.problems.items()):
        print(f"runner_processes: pid {pid}: {reason}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
