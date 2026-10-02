#!/usr/bin/env bash
# Run the fixed measurement subset described by
# scripts/function_tracer_pcode/reporting/eqbench_subset.json.
#
# Eq results go to $OUTPUT_BASE_DIR/eq and Neq results to $OUTPUT_BASE_DIR/neq;
# the runner console output of each half is kept in $OUTPUT_BASE_DIR/<half>.log.
# All settings come from the manifest; override individual ones through the
# environment (PARALLEL_JOBS, PAIR_PROCESS_TIMEOUT, ANALYSIS_TIMEOUT, EQBENCH_RESOURCE_ADMISSION,
# EQBENCH_BUILD_POLICY). SUBSET_SCOPE=eq|neq|all selects the halves to run.
# ANALYSIS_TIMEOUT=0 runs both halves without the analysis deadline (Issue #106);
# ANALYSIS_TIMEOUT / ANALYSIS_TIMEOUT_MARGIN default to the manifest's subset profile.
#
# Issue #123: the run records its own provenance.  SUBSET_BEFORE=<run dir> names
# the run this one is compared against; it is checked against the halves this
# run will actually produce before the first pair starts, and the transition
# report of every half and the soundness gate of this run are then written next
# to the results, so the comparison survives without a hand-written note.
# SUBSET_ISSUE / SUBSET_PR record what the run was made for.
#
# Issue #123 / PR-123-B: the finished run is then appended to the verification
# ledger (VERIFICATION_LEDGER, default logs/EqBench/verification_ledger.jsonl)
# with SUBSET_REQUESTED_SCOPE (default "subset") as the scope that was asked
# for.  None of this changes how a pair is judged:
# the reports are read from the results after the halves have finished, and
# their exit status is recorded in the manifest instead of becoming the exit
# status of this script.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/scripts/validation_matrix_common.sh" || exit 1
MANIFEST="${SUBSET_MANIFEST:-$SCRIPT_DIR/scripts/function_tracer_pcode/reporting/eqbench_subset.json}"
OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/EqBench/subset_current}"
SUBSET_SCOPE="${SUBSET_SCOPE:-all}"
SUBSET_BEFORE="${SUBSET_BEFORE:-}"
SUBSET_ISSUE="${SUBSET_ISSUE:-}"
SUBSET_PR="${SUBSET_PR:-}"
SUBSET_REQUESTED_SCOPE="${SUBSET_REQUESTED_SCOPE:-subset}"
DEFAULT_PYTHON_BIN="python3"
if [[ -x "$SCRIPT_DIR/.venv-pyghidra/bin/python" ]]; then
    DEFAULT_PYTHON_BIN="$SCRIPT_DIR/.venv-pyghidra/bin/python"
fi
# Not exported: each runner resolves its own interpreter the same way.
PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"

if [[ "$SUBSET_SCOPE" != "eq" && "$SUBSET_SCOPE" != "neq" && "$SUBSET_SCOPE" != "all" ]]; then
    echo "Error: SUBSET_SCOPE must be eq, neq or all" >&2
    exit 1
fi
# The halves to run are fixed by SUBSET_SCOPE alone, so they are known before
# anything expensive happens -- and the before run is checked against exactly
# those halves, never against a half this run will not produce.
halves=()
[[ "$SUBSET_SCOPE" == "eq" || "$SUBSET_SCOPE" == "all" ]] && halves+=(eq)
[[ "$SUBSET_SCOPE" == "neq" || "$SUBSET_SCOPE" == "all" ]] && halves+=(neq)

if [[ -n "$SUBSET_BEFORE" ]]; then
    # Resolve and check before the (long) halves run: a mistyped before run must
    # not be discovered only after the results are already produced.  What is
    # checked is that the reader behind outcome_transition can actually load the
    # half, not the provenance this change adds -- runs made before it stay
    # usable as a before.
    SUBSET_BEFORE="$(realpath -m "$SUBSET_BEFORE")"
    if [[ ! -d "$SUBSET_BEFORE" ]]; then
        echo "Error: SUBSET_BEFORE is not a directory: $SUBSET_BEFORE" >&2
        exit 1
    fi
    for half in "${halves[@]}"; do
        if ! before_half_pairs="$(validation_before_run_half_is_comparable \
            "$SUBSET_BEFORE/$half" "$PYTHON_BIN" "$SCRIPT_DIR")"; then
            echo "Error: SUBSET_BEFORE has no comparable $half half (SUBSET_SCOPE=$SUBSET_SCOPE):" \
                "$SUBSET_BEFORE/$half (see the reader error above)" >&2
            exit 1
        fi
        echo "Before run $half: $before_half_pairs comparable pairs"
    done
fi

# One value of a `key=value` manifest, keeping values that contain "=".
manifest_field() {
    local file="$1" key="$2"
    [[ -r "$file" ]] || return 1
    awk -F= -v key="$key" '
        $1 == key { value = substr($0, length(key) + 2); found = 1 }
        END { if (!found) exit 1; print value }
    ' "$file"
}

manifest_value() {
    python3 - "$MANIFEST" "$@" <<'PY'
import json, sys
manifest = json.load(open(sys.argv[1]))
kind, key = sys.argv[2], sys.argv[3]
if kind == "setting":
    print(manifest["run_settings"][key])
elif kind == "sample_filter":
    sources = manifest[key]["sources"]
    if key == "eq":
        # Eq sources are matched against the source file path (.../<sample>.c).
        print("/(" + "|".join(s.replace(".", r"\.") for s in sources) + r")\.c$")
    else:
        # Neq sources are matched against the sample label.
        print("^(" + "|".join(s.replace(".", r"\.") for s in sources) + ")$")
elif kind == "pair_filter":
    print(",".join(manifest[key]["pair_ids"]))
PY
}

export PARALLEL_JOBS="${PARALLEL_JOBS:-$(manifest_value setting PARALLEL_JOBS)}"
export PAIR_PROCESS_TIMEOUT="${PAIR_PROCESS_TIMEOUT:-$(manifest_value setting PAIR_PROCESS_TIMEOUT)}"
export EQBENCH_RESOURCE_ADMISSION="${EQBENCH_RESOURCE_ADMISSION:-$(manifest_value setting EQBENCH_RESOURCE_ADMISSION)}"
export EQBENCH_BUILD_POLICY="${EQBENCH_BUILD_POLICY:-$(manifest_value setting EQBENCH_BUILD_POLICY)}"
# Issue #15: passed through to both halves so the two run in the same mode
# and the manifest below can say which one it was.
export EQBENCH_IDENTICAL_FAST_PATH="${EQBENCH_IDENTICAL_FAST_PATH:-1}"
# Issue #106 PR-106-B: the subset's analysis deadline comes from the manifest unless
# the environment names one (0 = off).  It is exported so both halves run with the
# same value, and checked here with the runners' own rule before either half
# starts: an inconsistent combination fails before any pair, not in the second half.
# The subset profile has its own deadline and margin (the margin is measured per
# profile: its terms depend on the load and on the deadline itself), read from the
# manifest by the policy module.  The halves get the EFFECTIVE values, so both
# run with exactly what was checked here and record the same thing.
validation_resolve_analysis_timeout_policy "$PYTHON_BIN" "$MANIFEST" "$SCRIPT_DIR" || exit 1
export ANALYSIS_TIMEOUT="$ANALYSIS_TIMEOUT_SECONDS"
export ANALYSIS_TIMEOUT_MARGIN="$ANALYSIS_TIMEOUT_MARGIN_SECONDS"

mkdir -p "$OUTPUT_BASE_DIR"
OUTPUT_BASE_DIR="$(realpath -m "$OUTPUT_BASE_DIR")"
START_EPOCH="$(date +%s)"
START_TIME_UTC="$(validation_utc_timestamp)"
RUN_HOSTNAME="$(validation_run_hostname)"
RUN_GIT_STATE_LINES="$(validation_run_git_state_lines "$PYTHON_BIN" "$SCRIPT_DIR")"
echo "Subset manifest: $MANIFEST"
echo "Output base: $OUTPUT_BASE_DIR"
echo "Before run: ${SUBSET_BEFORE:-none}"
echo "PARALLEL_JOBS=$PARALLEL_JOBS PAIR_PROCESS_TIMEOUT=$PAIR_PROCESS_TIMEOUT ANALYSIS_TIMEOUT=${ANALYSIS_TIMEOUT_SECONDS}s (margin ${ANALYSIS_TIMEOUT_MARGIN_SECONDS}s) EQBENCH_RESOURCE_ADMISSION=$EQBENCH_RESOURCE_ADMISSION EQBENCH_BUILD_POLICY=$EQBENCH_BUILD_POLICY"

run_half() {
    local half="$1" start ec=0
    start="$(date +%s)"
    if [[ "$half" == "eq" ]]; then
        EQBENCH_RUN_SCOPE=REPRESENTATIVE \
        EQBENCH_SAMPLE_FILTER="$(manifest_value sample_filter eq)" \
        EQBENCH_PAIR_FILTER="$(manifest_value pair_filter eq)" \
        OUTPUT_BASE_DIR="$OUTPUT_BASE_DIR/eq" \
            "$SCRIPT_DIR/eqbench_run_all_32jobs.sh" || ec=$?
    else
        NEQ_RUN_SCOPE=REPRESENTATIVE \
        NEQ_SAMPLE_FILTER="$(manifest_value sample_filter neq)" \
        NEQ_PAIR_FILTER="$(manifest_value pair_filter neq)" \
        OUTPUT_BASE_DIR="$OUTPUT_BASE_DIR/neq" \
            "$SCRIPT_DIR/neqbench_run_all_32jobs.sh" || ec=$?
    fi
    echo "$(( $(date +%s) - start ))" > "$OUTPUT_BASE_DIR/$half.elapsed"
    return "$ec"
}

# The production runners schedule pairs across functions (Issue #26), so a
# single runner already fills PARALLEL_JOBS slots.  The halves therefore run
# one after the other: running them concurrently would put up to
# 2 x PARALLEL_JOBS pair processes on the host.  Console output of each half
# goes to $OUTPUT_BASE_DIR/<half>.log.
status=0
for half in "${halves[@]}"; do
    half_status=0
    run_half "$half" > "$OUTPUT_BASE_DIR/$half.log" 2>&1 || half_status=$?
    echo "Subset $half elapsed: $(cat "$OUTPUT_BASE_DIR/$half.elapsed")s (exit $half_status, log: $OUTPUT_BASE_DIR/$half.log)"
    (( half_status == 0 )) || status=$half_status
done

# The halves record their own effective settings; read them back instead of
# re-deriving the runner defaults here.  "mismatch" means the two halves ran
# with different values -- their own run_manifest.txt files stay authoritative.
half_setting() {
    local key="$1" value="" half half_value
    for half in "${halves[@]}"; do
        half_value="$(manifest_field "$OUTPUT_BASE_DIR/$half/run_manifest.txt" "$key")" || continue
        if [[ -z "$value" ]]; then
            value="$half_value"
        elif [[ "$value" != "$half_value" ]]; then
            printf 'mismatch'
            return 0
        fi
    done
    printf '%s' "${value:-unknown}"
}

# Persist this run's soundness gate next to the results.  The gate reads the
# finished pair statuses, so it can neither change nor delay a judgement; its
# exit status is recorded, not propagated.
SOUNDNESS_GATE_STATUS=0
gate_roots=()
for half in "${halves[@]}"; do gate_roots+=("$OUTPUT_BASE_DIR/$half"); done
(
    cd "$SCRIPT_DIR" && "$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.soundness_gate \
        "${gate_roots[@]}" --json "$OUTPUT_BASE_DIR/soundness_gate.json"
) > "$OUTPUT_BASE_DIR/soundness_gate.txt" 2>&1 || SOUNDNESS_GATE_STATUS=$?
echo "Soundness gate: exit $SOUNDNESS_GATE_STATUS (0=PASS 1=VIOLATION 2=EMPTY) -> $OUTPUT_BASE_DIR/soundness_gate.txt"

# Persist the before/after transition of every half when a before run is named.
declare -A TRANSITION_STATUS=()
if [[ -n "$SUBSET_BEFORE" ]]; then
    for half in "${halves[@]}"; do
        half_transition_status=0
        (
            cd "$SCRIPT_DIR" && "$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.outcome_transition \
                --before "$SUBSET_BEFORE/$half" --after "$OUTPUT_BASE_DIR/$half" \
                --json "$OUTPUT_BASE_DIR/outcome_transition_$half.json" --fail-on-change
        ) > "$OUTPUT_BASE_DIR/outcome_transition_$half.txt" 2>&1 || half_transition_status=$?
        TRANSITION_STATUS["$half"]=$half_transition_status
        echo "Outcome transition $half: exit $half_transition_status (0=no change 2=changed) -> $OUTPUT_BASE_DIR/outcome_transition_$half.txt"
    done
fi

# The before run's commit, when that run recorded one.  An older run predating
# this field leaves "unknown"; it is never guessed from anything else.
BEFORE_COMMIT=none
if [[ -n "$SUBSET_BEFORE" ]]; then
    BEFORE_COMMIT=unknown
    for candidate in \
        "$SUBSET_BEFORE/subset_manifest.txt" \
        "$SUBSET_BEFORE/eq/run_manifest.txt" \
        "$SUBSET_BEFORE/neq/run_manifest.txt"; do
        if before_commit_value="$(manifest_field "$candidate" git_commit)" \
            && [[ -n "$before_commit_value" ]]; then
            BEFORE_COMMIT="$before_commit_value"
            break
        fi
    done
fi

ELAPSED=$(( $(date +%s) - START_EPOCH ))
{
    echo "manifest=$MANIFEST"
    echo "manifest_sha256=$(sha256sum "$MANIFEST" | awk '{print $1}')"
    echo "scope=$SUBSET_SCOPE"
    echo "parallel_jobs=$PARALLEL_JOBS"
    echo "pair_process_timeout=$PAIR_PROCESS_TIMEOUT"
    echo "resource_admission=$EQBENCH_RESOURCE_ADMISSION"
    echo "build_policy=$EQBENCH_BUILD_POLICY"
    echo "equiv_timeout=$(half_setting equiv_timeout)"
    echo "decompile_timeout=$(half_setting decompile_timeout)"
    echo "pairwise_timeout=$(half_setting pairwise_timeout)"
    echo "pairwise_timeout_hard=$(half_setting pairwise_timeout_hard)"
    echo "pair_process_kill_after=$(half_setting pair_process_kill_after)"
    # Issue #106 PR-106-B: the effective values the halves recorded (never re-derived here)
    while IFS='=' read -r key _; do
        echo "$key=$(half_setting "$key")"
    done <<< "$ANALYSIS_TIMEOUT_MANIFEST_LINES"
    echo "identical_fast_path=$(half_setting identical_fast_path)"
    echo "analysis_config_schema=$(half_setting analysis_config_schema)"
    echo "$RUN_GIT_STATE_LINES"
    echo "start_time_utc=$START_TIME_UTC"
    echo "end_time_utc=$(validation_utc_timestamp)"
    echo "hostname=$RUN_HOSTNAME"
    echo "before_run=${SUBSET_BEFORE:-none}"
    echo "before_commit=$BEFORE_COMMIT"
    echo "issue=${SUBSET_ISSUE:-none}"
    echo "pr=${SUBSET_PR:-none}"
    echo "soundness_gate_status=$SOUNDNESS_GATE_STATUS"
    for half in "${halves[@]}"; do
        echo "outcome_transition_${half}_status=${TRANSITION_STATUS[$half]:-not_run}"
    done
    for half in "${halves[@]}"; do echo "${half}_elapsed_seconds=$(cat "$OUTPUT_BASE_DIR/$half.elapsed")"; done
    echo "elapsed_seconds=$ELAPSED"
    echo "exit_status=$status"
} > "$OUTPUT_BASE_DIR/subset_manifest.txt"
echo "Subset total elapsed: ${ELAPSED}s"

# Issue #123 / PR-123-B: record this run in the verification ledger.
#
# This runs last, after every pair has been judged and after the soundness and
# transition artifacts exist, and it only reads what those steps already wrote.
# A failure to record is a diagnostic, never a verdict: it does not touch any
# pair's outcome and it does not become the exit status of this script, because
# "we failed to write a note about the run" is not "the run failed".  The
# failure is left in the manifest (`ledger_record_status`) so that a row missing
# from the ledger can be explained instead of being silently absent.
LEDGER_PATH="${VERIFICATION_LEDGER:-$SCRIPT_DIR/logs/EqBench/verification_ledger.jsonl}"
LEDGER_STATUS=0
ledger_args=(--ledger "$LEDGER_PATH" record --run-dir "$OUTPUT_BASE_DIR"
             --requested-scope "${SUBSET_REQUESTED_SCOPE:-subset}")
[[ -n "$SUBSET_BEFORE" ]] && ledger_args+=(--before "$SUBSET_BEFORE")
[[ -n "$SUBSET_ISSUE" ]] && ledger_args+=(--issue "$SUBSET_ISSUE")
[[ -n "$SUBSET_PR" ]] && ledger_args+=(--pr "$SUBSET_PR")
(
    cd "$SCRIPT_DIR" && "$PYTHON_BIN" -m \
        scripts.function_tracer_pcode.reporting.verification_ledger "${ledger_args[@]}"
) > "$OUTPUT_BASE_DIR/verification_ledger_record.txt" 2>&1 || LEDGER_STATUS=$?
echo "Verification ledger: exit $LEDGER_STATUS (0=recorded) -> $LEDGER_PATH" \
     "(output: $OUTPUT_BASE_DIR/verification_ledger_record.txt)"
if (( LEDGER_STATUS != 0 )); then
    echo "Warning: the ledger record failed; the run result below is unaffected." >&2
    sed 's/^/  ledger: /' "$OUTPUT_BASE_DIR/verification_ledger_record.txt" >&2 || true
fi
{
    echo "ledger_path=$LEDGER_PATH"
    echo "ledger_record_status=$LEDGER_STATUS"
} >> "$OUTPUT_BASE_DIR/subset_manifest.txt"

exit "$status"
