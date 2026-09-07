"""Tests for scripts/eqbench/pair_scheduler.sh (Issue #26).

The EqBench/NeqBench runners schedule pair jobs across functions through this
bash library.  The tests drive the library through real ``bash`` processes and
check the scheduling contract the runners rely on:

* up to PARALLEL_JOBS jobs stay in flight across function groups,
* the per-group completion hook fires exactly once per group, only after every
  job started for the group has been reaped (and immediately on close when the
  group started no job at all),
* non-zero job exits are counted into the caller's failure counter,
* finalisation closes groups the caller left open.
"""
from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[4]
SCHEDULER = REPO_ROOT / "scripts" / "eqbench" / "pair_scheduler.sh"
BASH = shutil.which("bash")

pytestmark = pytest.mark.skipif(BASH is None, reason="bash is required")

WAIT_PID_MODES = ["wait-p", "scan"]


def _bash_supports_wait_p() -> bool:
    out = subprocess.run(
        [BASH, "-c", 'echo "${BASH_VERSINFO[0]}.${BASH_VERSINFO[1]}"'],
        check=True, capture_output=True, text=True,
    ).stdout.strip()
    major, minor = (int(part) for part in out.split("."))
    return (major, minor) >= (5, 1)


def _run_harness(tmp_path: Path, script: str, mode: str) -> subprocess.CompletedProcess:
    if mode == "wait-p" and not _bash_supports_wait_p():
        pytest.skip("wait -n -p requires bash >= 5.1")
    harness = tmp_path / "harness.sh"
    harness.write_text(
        "set -euo pipefail\n"
        f"source {SCHEDULER}\n"
        f"WORK={tmp_path}\n"
        + script
    )
    env = dict(os.environ, PAIR_SCHEDULER_WAIT_PID_MODE=mode)
    return subprocess.run(
        [BASH, str(harness)], capture_output=True, text=True, env=env,
        cwd=str(tmp_path), timeout=120,
    )


# A job that records itself as running, sleeps, records completion and exits
# with the requested status.  The hook records, at completion time, how many
# of the group's jobs have finished (must equal the number started) and how
# many jobs of *any* group are still running (evidence that other groups keep
# running while this one completes).
COMMON = r"""
job() {
    local group="$1" index="$2" sleep_for="$3" exit_status="${4:-0}"
    touch "$WORK/running.$group.$index"
    sleep "$sleep_for"
    touch "$WORK/done.$group.$index"
    rm -f "$WORK/running.$group.$index"
    exit "$exit_status"
}
on_group_complete() {
    local key="$1" context="$2"
    local started done running
    started="$(ls "$WORK" | grep -c "^done\.$key\.\|^running\.$key\." || true)"
    done="$(ls "$WORK" | grep -c "^done\.$key\." || true)"
    running="$(ls "$WORK" | grep -c '^running\.' || true)"
    printf 'complete key=%s context=%s done=%s started=%s others_running=%s\n' \
        "$key" "$context" "$done" "$started" "$running" >> "$WORK/events.log"
}
FAILURES=0
"""


def _events(tmp_path: Path) -> list[str]:
    path = tmp_path / "events.log"
    return path.read_text().splitlines() if path.exists() else []


@pytest.mark.parametrize("mode", WAIT_PID_MODES)
def test_jobs_run_across_groups_and_hooks_fire_after_group_drains(tmp_path, mode):
    script = COMMON + r"""
pair_scheduler_init 6 on_group_complete FAILURES
# f1's jobs are short and the later groups' jobs long, so that when f1
# completes the already-scheduled f2 jobs are still running regardless of
# host load.
for group in f1 f2 f3; do
    pair_scheduler_open_group "$group" "ctx-$group"
    sleep_for=1.5
    [[ "$group" == f1 ]] && sleep_for=0.3
    for index in 1 2 3 4; do
        pair_scheduler_wait_for_slot
        job "$group" "$index" "$sleep_for" &
        pair_scheduler_start_job "$group" "$!"
    done
    pair_scheduler_close_group "$group"
done
pair_scheduler_finalize
printf 'peak=%s active=%s failures=%s completed=%s\n' \
    "$PAIR_SCHEDULER_PEAK_ACTIVE_JOBS" "$PAIR_SCHEDULER_ACTIVE_JOBS" \
    "$FAILURES" "$PAIR_SCHEDULER_COMPLETED_GROUPS"
"""
    proc = _run_harness(tmp_path, script, mode)
    assert proc.returncode == 0, proc.stderr
    summary = proc.stdout.strip().splitlines()[-1]
    # Six jobs in flight although each group only has four: the scheduler
    # crosses function boundaries instead of draining per group.
    assert summary == "peak=6 active=0 failures=0 completed=3"

    events = _events(tmp_path)
    assert [line.split()[1] for line in events] == ["key=f1", "key=f2", "key=f3"]
    for line in events:
        fields = dict(part.split("=", 1) for part in line.split()[1:])
        assert fields["done"] == "4" and fields["started"] == "4"
        assert fields["context"] == f"ctx-{fields['key']}"
    # While f1 completes, jobs of f2 (already scheduled) are still running.
    first = dict(part.split("=", 1) for part in events[0].split()[1:])
    assert int(first["others_running"]) > 0
    assert not list(tmp_path.glob("running.*"))


@pytest.mark.parametrize("mode", WAIT_PID_MODES)
def test_group_without_jobs_completes_on_close(tmp_path, mode):
    script = COMMON + r"""
pair_scheduler_init 2 on_group_complete FAILURES
pair_scheduler_open_group skipped "all-pairs-skipped"
pair_scheduler_close_group skipped
printf 'events_after_close=%s\n' "$(wc -l < "$WORK/events.log")"
pair_scheduler_open_group later "x"
pair_scheduler_wait_for_slot
job later 1 0.1 &
pair_scheduler_start_job later "$!"
pair_scheduler_close_group later
printf 'events_before_drain=%s\n' "$(wc -l < "$WORK/events.log")"
pair_scheduler_finalize
printf 'events_after_drain=%s\n' "$(wc -l < "$WORK/events.log")"
"""
    proc = _run_harness(tmp_path, script, mode)
    assert proc.returncode == 0, proc.stderr
    lines = proc.stdout.strip().splitlines()
    assert lines == [
        "events_after_close=1",
        "events_before_drain=1",
        "events_after_drain=2",
    ]
    assert _events(tmp_path)[0].startswith("complete key=skipped context=all-pairs-skipped done=0 started=0")


@pytest.mark.parametrize("mode", WAIT_PID_MODES)
def test_failed_jobs_are_counted_into_named_counter(tmp_path, mode):
    script = COMMON + r"""
pair_scheduler_init 3 on_group_complete FAILURES
pair_scheduler_open_group g "ctx"
statuses=(0 3 0 1 2)
for index in "${!statuses[@]}"; do
    pair_scheduler_wait_for_slot
    job g "$index" 0.2 "${statuses[$index]}" &
    pair_scheduler_start_job g "$!"
done
pair_scheduler_close_group g
pair_scheduler_finalize
printf 'failures=%s completed=%s\n' "$FAILURES" "$PAIR_SCHEDULER_COMPLETED_GROUPS"
"""
    proc = _run_harness(tmp_path, script, mode)
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout.strip().splitlines()[-1] == "failures=3 completed=1"
    assert len(_events(tmp_path)) == 1


@pytest.mark.parametrize("mode", WAIT_PID_MODES)
def test_finalize_closes_groups_left_open(tmp_path, mode):
    # Mirrors the runners' early "stop scheduling" exit: the group of the
    # function being scheduled is never closed explicitly, yet its summary
    # hook must still fire after the in-flight jobs drain.
    script = COMMON + r"""
pair_scheduler_init 4 on_group_complete FAILURES
pair_scheduler_open_group aborted "ctx"
for index in 1 2; do
    pair_scheduler_wait_for_slot
    job aborted "$index" 0.2 &
    pair_scheduler_start_job aborted "$!"
done
pair_scheduler_finalize
printf 'completed=%s active=%s\n' "$PAIR_SCHEDULER_COMPLETED_GROUPS" "$PAIR_SCHEDULER_ACTIVE_JOBS"
"""
    proc = _run_harness(tmp_path, script, mode)
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout.strip().splitlines()[-1] == "completed=1 active=0"
    assert _events(tmp_path) == ["complete key=aborted context=ctx done=2 started=2 others_running=0"]


@pytest.mark.parametrize("mode", WAIT_PID_MODES)
def test_untracked_children_do_not_disturb_accounting(tmp_path, mode):
    # Background processes the scheduler does not know about finish (with a
    # non-zero status) while pair jobs are in flight.  They must neither be
    # attributed to a group nor counted as pair failures: only tracked B
    # (exit 3) may increment the counter, so the expected failure count is 1.
    script = COMMON + r"""
pair_scheduler_init 2 on_group_complete FAILURES
(sleep 0.05; exit 7) &
pair_scheduler_open_group g "ctx"
pair_scheduler_wait_for_slot
job g A 0.4 0 &
pair_scheduler_start_job g "$!"
pair_scheduler_wait_for_slot
job g B 0.4 3 &
pair_scheduler_start_job g "$!"
(sleep 0.01; exit 7) &
pair_scheduler_wait_for_slot
job g C 0.1 0 &
pair_scheduler_start_job g "$!"
pair_scheduler_close_group g
pair_scheduler_finalize
printf 'failures=%s completed=%s active=%s\n' "$FAILURES" "$PAIR_SCHEDULER_COMPLETED_GROUPS" "$PAIR_SCHEDULER_ACTIVE_JOBS"
"""
    proc = _run_harness(tmp_path, script, mode)
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout.strip().splitlines()[-1] == "failures=1 completed=1 active=0"
    assert _events(tmp_path) == ["complete key=g context=ctx done=3 started=3 others_running=0"]


@pytest.mark.parametrize("mode", WAIT_PID_MODES)
def test_untracked_failure_before_first_slot_wait_is_not_counted(tmp_path, mode):
    # The untracked child has already exited (exit 7) by the time the
    # scheduler waits for a slot; the tracked job A exits 0.  A scheduler that
    # reaped "any" child and attributed the status to a tracked PID would
    # report failures=1 here.
    script = COMMON + r"""
pair_scheduler_init 1 on_group_complete FAILURES
(exit 7) &
sleep 0.2
pair_scheduler_open_group g "ctx"
pair_scheduler_wait_for_slot
job g A 0.3 0 &
pair_scheduler_start_job g "$!"
pair_scheduler_wait_for_slot
job g B 0.1 0 &
pair_scheduler_start_job g "$!"
pair_scheduler_close_group g
pair_scheduler_finalize
printf 'failures=%s completed=%s active=%s\n' "$FAILURES" "$PAIR_SCHEDULER_COMPLETED_GROUPS" "$PAIR_SCHEDULER_ACTIVE_JOBS"
"""
    proc = _run_harness(tmp_path, script, mode)
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout.strip().splitlines()[-1] == "failures=0 completed=1 active=0"


@pytest.mark.parametrize("mode", WAIT_PID_MODES)
def test_tracked_job_without_a_child_is_accounted_not_fatal(tmp_path, mode):
    # Issue #118: a tracked PID with no corresponding child (the child was
    # already reaped elsewhere, or the bookkeeping drifted).  `wait -n -p pid`
    # then *unsets* pid, and the runners run with `set -u`, so an unguarded
    # read of "$pid" aborted the whole matrix run before the orphan-accounting
    # path could run.  The scheduler must instead count the orphan as a
    # failure, complete its group and return normally.
    script = COMMON + r"""
pair_scheduler_init 2 on_group_complete FAILURES
pair_scheduler_open_group g "ctx"
# A PID that is not a child of this shell: no `wait` can ever reap it.
pair_scheduler_start_job g 999999
pair_scheduler_close_group g
pair_scheduler_finalize
printf 'failures=%s completed=%s active=%s\n' "$FAILURES" "$PAIR_SCHEDULER_COMPLETED_GROUPS" "$PAIR_SCHEDULER_ACTIVE_JOBS"
"""
    proc = _run_harness(tmp_path, script, mode)
    assert proc.returncode == 0, proc.stderr
    assert "unbound variable" not in proc.stderr
    assert proc.stdout.strip().splitlines()[-1] == "failures=1 completed=1 active=0"


@pytest.mark.parametrize("mode", WAIT_PID_MODES)
def test_orphaned_tracked_job_does_not_strand_later_groups(tmp_path, mode):
    # The same drift while a real job of another group is in flight: the
    # scheduler must still reap the real job, complete both groups and leave
    # nothing in flight.
    script = COMMON + r"""
pair_scheduler_init 2 on_group_complete FAILURES
pair_scheduler_open_group g1 "ctx1"
pair_scheduler_start_job g1 999999
pair_scheduler_close_group g1
pair_scheduler_open_group g2 "ctx2"
pair_scheduler_wait_for_slot
job g2 A 0.2 0 &
pair_scheduler_start_job g2 "$!"
pair_scheduler_close_group g2
pair_scheduler_finalize
printf 'failures=%s completed=%s active=%s\n' "$FAILURES" "$PAIR_SCHEDULER_COMPLETED_GROUPS" "$PAIR_SCHEDULER_ACTIVE_JOBS"
"""
    proc = _run_harness(tmp_path, script, mode)
    assert proc.returncode == 0, proc.stderr
    assert "unbound variable" not in proc.stderr
    assert proc.stdout.strip().splitlines()[-1] == "failures=1 completed=2 active=0"
    assert sorted(line.split()[1] for line in _events(tmp_path)) == ["key=g1", "key=g2"]
    assert not list(tmp_path.glob("running.*"))


def test_init_rejects_bad_arguments(tmp_path):
    script = COMMON + r"""
set +e
pair_scheduler_init 0 on_group_complete FAILURES; echo "max0=$?"
pair_scheduler_init 4 no_such_hook FAILURES; echo "hook=$?"
pair_scheduler_init 4 on_group_complete 'bad name'; echo "counter=$?"
PAIR_SCHEDULER_WAIT_PID_MODE=bogus pair_scheduler_init 4 on_group_complete FAILURES; echo "mode=$?"
pair_scheduler_init 4 on_group_complete FAILURES; echo "ok=$?"
pair_scheduler_start_job unopened 12345; echo "unopened=$?"
pair_scheduler_open_group g ctx; pair_scheduler_open_group g ctx; echo "dup=$?"
"""
    proc = _run_harness(tmp_path, script, "scan")
    assert proc.stdout.strip().splitlines() == [
        "max0=1", "hook=1", "counter=1", "mode=1", "ok=0", "unopened=1", "dup=1",
    ]


def test_runners_source_the_scheduler_and_no_longer_drain_per_function():
    for runner in ("eqbench_run_all_32jobs.sh", "neqbench_run_all_32jobs.sh"):
        text = (REPO_ROOT / runner).read_text()
        assert 'scripts/eqbench/pair_scheduler.sh' in text, runner
        assert "pair_scheduler_open_group" in text and "pair_scheduler_close_group" in text, runner
        assert "pair_scheduler_finalize" in text, runner
        # The old per-function drain must be gone: the only `wait -n` lives in
        # the scheduler library.
        assert "wait -n" not in text.replace("wait -n\" >&2", ""), runner
        assert "wait_for_all_jobs" not in text and "wait_all" not in text, runner
