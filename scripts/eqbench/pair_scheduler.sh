#!/usr/bin/env bash
# Cross-function pair scheduler shared by eqbench_run_all_32jobs.sh and
# neqbench_run_all_32jobs.sh.
#
# The runners used to launch one function's pairs and then wait for all of
# them before moving on, so the effective parallelism was capped at the pair
# count of a single function (8 in the representative Eq scope) regardless of
# PARALLEL_JOBS.  This library keeps up to PARALLEL_JOBS pair jobs in flight
# across functions and still produces the per-function artefacts (the
# results_summary.txt of a function) exactly once, when that function's last
# pair has been reaped.
#
# Model
#   * A "group" is one function directory.  The runner opens the group before
#     scheduling its pairs, starts each pair job against it, and closes the
#     group once no more pairs of that function will be scheduled.
#   * The completion hook (a shell function name given to
#     pair_scheduler_init) fires exactly once per group, after the group is
#     closed AND every job started for it has been reaped.  A group closed with
#     zero started jobs (all pairs skipped) completes immediately on close,
#     matching the old per-function flow where the summary was rewritten even
#     when nothing ran.
#   * Job exit statuses are counted into the caller's failure counter (a
#     variable name given to pair_scheduler_init), exactly like the previous
#     `wait -n` bookkeeping did.
#
# Which job finished is taken from `wait -n -p` on bash >= 5.1.  On older bash
# the scheduler never uses `wait -n`: it polls the tracked PIDs through
# /proc/<pid>/stat (state Z or gone) and reaps the finished one with
# `wait "$pid"`, so the exit status is always the status of that PID and a
# background child the scheduler does not track can neither be mistaken for
# a pair job nor contribute its status.  PAIR_SCHEDULER_WAIT_PID_MODE=auto|
# wait-p|scan overrides the detection (used by the unit test to exercise
# both paths); PAIR_SCHEDULER_POLL_INTERVAL_SECONDS tunes the scan poll.
#
# Requires bash >= 4.3 (wait -n, namerefs); scan mode additionally needs
# /proc (Linux).

pair_scheduler_init() {
    local max_jobs="$1" on_group_complete="$2" failure_counter="$3"
    if [[ ! "$max_jobs" =~ ^[1-9][0-9]*$ ]]; then
        echo "pair_scheduler_init: max_jobs must be a positive integer: '$max_jobs'" >&2
        return 1
    fi
    if ! declare -F "$on_group_complete" > /dev/null; then
        echo "pair_scheduler_init: completion hook is not a function: '$on_group_complete'" >&2
        return 1
    fi
    if [[ ! "$failure_counter" =~ ^[A-Za-z_][A-Za-z0-9_]*$ ]]; then
        echo "pair_scheduler_init: invalid failure counter name: '$failure_counter'" >&2
        return 1
    fi
    PAIR_SCHEDULER_MAX_JOBS="$max_jobs"
    PAIR_SCHEDULER_ON_GROUP_COMPLETE="$on_group_complete"
    PAIR_SCHEDULER_FAILURE_COUNTER="$failure_counter"
    PAIR_SCHEDULER_ACTIVE_JOBS=0
    PAIR_SCHEDULER_PEAK_ACTIVE_JOBS=0
    PAIR_SCHEDULER_COMPLETED_GROUPS=0
    # pid -> group key
    declare -gA PAIR_SCHEDULER_JOB_GROUP=()
    # group key -> number of started-but-unreaped jobs
    declare -gA PAIR_SCHEDULER_GROUP_PENDING=()
    # group key -> 1 once the runner will schedule no more jobs for it
    declare -gA PAIR_SCHEDULER_GROUP_CLOSED=()
    # group key -> opaque context handed back to the completion hook
    declare -gA PAIR_SCHEDULER_GROUP_CONTEXT=()
    # group keys in open order (for deterministic finalisation)
    PAIR_SCHEDULER_GROUP_ORDER=()

    local mode="${PAIR_SCHEDULER_WAIT_PID_MODE:-auto}"
    case "$mode" in
        auto)
            if (( BASH_VERSINFO[0] > 5 || (BASH_VERSINFO[0] == 5 && BASH_VERSINFO[1] >= 1) )); then
                PAIR_SCHEDULER_WAIT_PID_MODE_EFFECTIVE="wait-p"
            else
                PAIR_SCHEDULER_WAIT_PID_MODE_EFFECTIVE="scan"
            fi
            ;;
        wait-p|scan)
            PAIR_SCHEDULER_WAIT_PID_MODE_EFFECTIVE="$mode"
            ;;
        *)
            echo "pair_scheduler_init: unknown PAIR_SCHEDULER_WAIT_PID_MODE: '$mode'" >&2
            return 1
            ;;
    esac
    PAIR_SCHEDULER_POLL_INTERVAL_SECONDS="${PAIR_SCHEDULER_POLL_INTERVAL_SECONDS:-0.05}"
    if [[ "$PAIR_SCHEDULER_WAIT_PID_MODE_EFFECTIVE" == "scan" && ! -r /proc/self/stat ]]; then
        echo "pair_scheduler_init: scan mode needs /proc/<pid>/stat (bash >= 5.1 provides wait -n -p instead)" >&2
        return 1
    fi
    return 0
}

pair_scheduler_open_group() {
    local key="$1" context="${2:-}"
    if [[ -z "$key" ]]; then
        echo "pair_scheduler_open_group: empty group key" >&2
        return 1
    fi
    if [[ -n "${PAIR_SCHEDULER_GROUP_PENDING[$key]+x}" ]]; then
        echo "pair_scheduler_open_group: group already open: '$key'" >&2
        return 1
    fi
    PAIR_SCHEDULER_GROUP_PENDING["$key"]=0
    PAIR_SCHEDULER_GROUP_CLOSED["$key"]=0
    PAIR_SCHEDULER_GROUP_CONTEXT["$key"]="$context"
    PAIR_SCHEDULER_GROUP_ORDER+=("$key")
    return 0
}

# Block until fewer than PAIR_SCHEDULER_MAX_JOBS jobs are in flight.
pair_scheduler_wait_for_slot() {
    while (( PAIR_SCHEDULER_ACTIVE_JOBS >= PAIR_SCHEDULER_MAX_JOBS )); do
        _pair_scheduler_reap_one || return 0
    done
    return 0
}

# Record a background job (already started with `&`) for the given group.
pair_scheduler_start_job() {
    local key="$1" pid="$2"
    if [[ -z "${PAIR_SCHEDULER_GROUP_PENDING[$key]+x}" ]]; then
        echo "pair_scheduler_start_job: group is not open: '$key'" >&2
        return 1
    fi
    if (( PAIR_SCHEDULER_GROUP_CLOSED[$key] )); then
        echo "pair_scheduler_start_job: group already closed: '$key'" >&2
        return 1
    fi
    if [[ ! "$pid" =~ ^[1-9][0-9]*$ ]]; then
        echo "pair_scheduler_start_job: invalid pid '$pid' for group '$key'" >&2
        return 1
    fi
    PAIR_SCHEDULER_JOB_GROUP["$pid"]="$key"
    PAIR_SCHEDULER_GROUP_PENDING["$key"]=$((PAIR_SCHEDULER_GROUP_PENDING[$key] + 1))
    PAIR_SCHEDULER_ACTIVE_JOBS=$((PAIR_SCHEDULER_ACTIVE_JOBS + 1))
    if (( PAIR_SCHEDULER_ACTIVE_JOBS > PAIR_SCHEDULER_PEAK_ACTIVE_JOBS )); then
        PAIR_SCHEDULER_PEAK_ACTIVE_JOBS="$PAIR_SCHEDULER_ACTIVE_JOBS"
    fi
    return 0
}

# Declare that no more jobs will be started for the group.  Completes the
# group right away when nothing is pending.
pair_scheduler_close_group() {
    local key="$1"
    if [[ -z "${PAIR_SCHEDULER_GROUP_PENDING[$key]+x}" ]]; then
        echo "pair_scheduler_close_group: group is not open: '$key'" >&2
        return 1
    fi
    if (( PAIR_SCHEDULER_GROUP_CLOSED[$key] )); then
        return 0
    fi
    PAIR_SCHEDULER_GROUP_CLOSED["$key"]=1
    if (( PAIR_SCHEDULER_GROUP_PENDING[$key] == 0 )); then
        _pair_scheduler_complete_group "$key"
    fi
    return 0
}

# Reap every in-flight job (completing groups as they drain).
pair_scheduler_wait_for_all() {
    while (( PAIR_SCHEDULER_ACTIVE_JOBS > 0 )); do
        _pair_scheduler_reap_one || break
    done
    return 0
}

# Drain, then close any group the runner left open (e.g. when scheduling was
# aborted mid-function) so that its completion hook still fires.
pair_scheduler_finalize() {
    pair_scheduler_wait_for_all
    local key
    for key in "${PAIR_SCHEDULER_GROUP_ORDER[@]}"; do
        [[ -n "${PAIR_SCHEDULER_GROUP_PENDING[$key]+x}" ]] || continue
        pair_scheduler_close_group "$key"
    done
    return 0
}

# Stop every pair job in flight and everything it started, and reap them, for
# a runner that was told to stop (TERM / INT / HUP).  The runner calls this in
# its signal handler *before* it removes the run tmpdir: a pair that is
# stopped must end with no classified status, never with one that a
# classifier built after its tmpdir and checkpoint store were deleted under
# it (that status would look decided and resume would reuse it).
#
# Order: freeze the job subshells (SIGSTOP) so they start nothing new, collect
# their whole process tree, SIGKILL the subshells (so no classification can
# begin), TERM the rest (the supervisor stops its own child process group),
# give them GRACE seconds, SIGKILL whatever is left, then reap the jobs.
# A job's exit status here is not a pair failure and is not counted.
pair_scheduler_terminate_all() {
    local grace="${1:-30}" pid deadline
    [[ "$grace" =~ ^[0-9]+$ ]] || grace=30
    declare -p PAIR_SCHEDULER_JOB_GROUP > /dev/null 2>&1 || return 0
    local -a jobs=("${!PAIR_SCHEDULER_JOB_GROUP[@]}")
    (( ${#jobs[@]} > 0 )) || return 0
    kill -STOP "${jobs[@]}" 2>/dev/null || true
    local -a tree=()
    mapfile -t tree < <(_pair_scheduler_descendants "${jobs[@]}")
    kill -KILL "${jobs[@]}" 2>/dev/null || true
    if (( ${#tree[@]} > 0 )); then
        kill -TERM "${tree[@]}" 2>/dev/null || true
        deadline=$((SECONDS + grace))
        while (( SECONDS < deadline )); do
            _pair_scheduler_any_alive "${tree[@]}" || break
            sleep 0.2
        done
        kill -KILL "${tree[@]}" 2>/dev/null || true
    fi
    for pid in "${jobs[@]}"; do
        wait "$pid" 2>/dev/null || true
        unset 'PAIR_SCHEDULER_JOB_GROUP[$pid]'
    done
    PAIR_SCHEDULER_ACTIVE_JOBS=0
    return 0
}

# Every live descendant of the given PIDs (not the PIDs themselves), from one
# snapshot of the process table.
_pair_scheduler_descendants() {
    local -A children=()
    local pid ppid
    while read -r pid ppid; do
        children["$ppid"]+="$pid "
    done < <(ps -e -o pid= -o ppid= 2>/dev/null)
    local -a queue=("$@")
    local -A seen=()
    while (( ${#queue[@]} > 0 )); do
        pid="${queue[0]}"
        queue=("${queue[@]:1}")
        for ppid in ${children[$pid]:-}; do
            [[ -n "${seen[$ppid]+x}" ]] && continue
            seen["$ppid"]=1
            printf '%s\n' "$ppid"
            queue+=("$ppid")
        done
    done
}

_pair_scheduler_any_alive() {
    local pid
    for pid in "$@"; do
        # A zombie is already dead; only a running process keeps the wait going.
        _pair_scheduler_pid_finished "$pid" || return 0
    done
    return 1
}

_pair_scheduler_count_failure() {
    local -n _pair_scheduler_counter_ref="$PAIR_SCHEDULER_FAILURE_COUNTER"
    _pair_scheduler_counter_ref=$((_pair_scheduler_counter_ref + 1))
}

_pair_scheduler_complete_group() {
    local key="$1" context="${PAIR_SCHEDULER_GROUP_CONTEXT[$key]}"
    unset 'PAIR_SCHEDULER_GROUP_PENDING[$key]'
    unset 'PAIR_SCHEDULER_GROUP_CLOSED[$key]'
    unset 'PAIR_SCHEDULER_GROUP_CONTEXT[$key]'
    PAIR_SCHEDULER_COMPLETED_GROUPS=$((PAIR_SCHEDULER_COMPLETED_GROUPS + 1))
    "$PAIR_SCHEDULER_ON_GROUP_COMPLETE" "$key" "$context"
}

_pair_scheduler_job_done() {
    local pid="$1" status="$2" key
    key="${PAIR_SCHEDULER_JOB_GROUP[$pid]}"
    unset 'PAIR_SCHEDULER_JOB_GROUP[$pid]'
    PAIR_SCHEDULER_ACTIVE_JOBS=$((PAIR_SCHEDULER_ACTIVE_JOBS - 1))
    if (( status != 0 )); then
        _pair_scheduler_count_failure
    fi
    PAIR_SCHEDULER_GROUP_PENDING["$key"]=$((PAIR_SCHEDULER_GROUP_PENDING[$key] - 1))
    if (( PAIR_SCHEDULER_GROUP_CLOSED[$key] && PAIR_SCHEDULER_GROUP_PENDING[$key] == 0 )); then
        _pair_scheduler_complete_group "$key"
    fi
}

# True when the tracked child has exited (zombie or already gone) so that a
# `wait "$pid"` returns immediately with its status.
_pair_scheduler_pid_finished() {
    local pid="$1" stat state
    if ! read -r stat 2>/dev/null < "/proc/$pid/stat"; then
        return 0
    fi
    state="${stat##*) }"
    state="${state%% *}"
    [[ "$state" == "Z" ]]
}

# Reap one tracked job.  Returns 1 only when no tracked job can be reaped any
# more (no children left), after accounting the orphans as failures.
_pair_scheduler_reap_one() {
    local status pid tracked
    while (( PAIR_SCHEDULER_ACTIVE_JOBS > 0 )); do
        pid=""
        if [[ "$PAIR_SCHEDULER_WAIT_PID_MODE_EFFECTIVE" == "wait-p" ]]; then
            if wait -n -p pid; then status=0; else status=$?; fi
            # bash *unsets* the -p variable when it reaped nothing (no child
            # left, or the wait was interrupted by a signal), so the reads
            # below must not assume it still exists: the runners set -u, and
            # an unguarded "$pid" would abort the whole matrix run right here
            # instead of accounting the orphaned jobs as failures (#118).
            pid="${pid:-}"
            if (( status == 127 )) && [[ -z "$pid" ]]; then
                # No child left to wait for while jobs are still tracked: the
                # bookkeeping can no longer be trusted, so count them as failed.
                echo "pair_scheduler: wait -n found no children with $PAIR_SCHEDULER_ACTIVE_JOBS job(s) tracked" >&2
                for tracked in "${!PAIR_SCHEDULER_JOB_GROUP[@]}"; do
                    _pair_scheduler_job_done "$tracked" 1
                done
                return 1
            fi
            if [[ -n "$pid" && -n "${PAIR_SCHEDULER_JOB_GROUP[$pid]+x}" ]]; then
                _pair_scheduler_job_done "$pid" "$status"
                return 0
            fi
            # Either an untracked child was reaped or the wait was
            # interrupted by a signal (status > 128 without a pid); keep
            # waiting.
            continue
        fi
        # scan mode: find a finished tracked PID and wait for exactly that
        # one, so its status can never come from an untracked child.
        for tracked in "${!PAIR_SCHEDULER_JOB_GROUP[@]}"; do
            if _pair_scheduler_pid_finished "$tracked"; then
                pid="$tracked"
                break
            fi
        done
        if [[ -n "$pid" ]]; then
            if wait "$pid"; then status=0; else status=$?; fi
            _pair_scheduler_job_done "$pid" "$status"
            return 0
        fi
        sleep "$PAIR_SCHEDULER_POLL_INTERVAL_SECONDS"
    done
    return 1
}
