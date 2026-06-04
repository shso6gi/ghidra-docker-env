#!/usr/bin/env bash
# Run the full function_call matrix with the normal current equivalence behavior.
#
# Producer validation uses phase2_run_function_call_full_matrix_pre_producer_32jobs.sh,
# which deliberately disables completed recovery proofs while keeping retry
# phases enabled.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"
source "$SCRIPT_DIR/scripts/validation_matrix_common.sh" || exit 1

DEFAULT_PYTHON_BIN="python3"
if [[ -x "$SCRIPT_DIR/.venv-pyghidra/bin/python" ]]; then
    DEFAULT_PYTHON_BIN="$SCRIPT_DIR/.venv-pyghidra/bin/python"
fi

export FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-full20}"
export PARALLEL_JOBS="${PARALLEL_JOBS:-32}"
export OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_full_current}"
export BASE_PATH="${BASE_PATH:-$SCRIPT_DIR/targets/cate1/function_call_test}"
export PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"
DEFAULT_VALIDATION_BEFORE_DIR="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/raw/logs/function_call"

baseline_log_root_has_pair_logs() {
    local root="$1"
    [[ -d "$root" ]] || return 1
    [[ -n "$(find "$root" -mindepth 2 -maxdepth 2 -type f -name "*.log" -print -quit 2>/dev/null)" ]]
}

if [[ -z "${VALIDATION_BEFORE_DIR:-}" ]] && baseline_log_root_has_pair_logs "$DEFAULT_VALIDATION_BEFORE_DIR"; then
    export VALIDATION_BEFORE_DIR="$DEFAULT_VALIDATION_BEFORE_DIR"
fi
PHASE2_GATE_BASELINE_DIR="${VALIDATION_BEFORE_DIR:-}"
export VALIDATION_AUTO_BEFORE_SNAPSHOT="${VALIDATION_AUTO_BEFORE_SNAPSHOT:-1}"
if [[ -n "${VALIDATION_BEFORE_DIR:-}" ]]; then
    export VALIDATION_REQUIRE_BEFORE_DELTA="${VALIDATION_REQUIRE_BEFORE_DELTA:-1}"
else
    export VALIDATION_REQUIRE_BEFORE_DELTA="${VALIDATION_REQUIRE_BEFORE_DELTA:-0}"
fi
export VALIDATION_REQUIRE_BASELINE_MATCH="${VALIDATION_REQUIRE_BASELINE_MATCH:-0}"
export VALIDATION_BASELINE_MATCH_SCOPE="${VALIDATION_BASELINE_MATCH_SCOPE:-all}"
export VALIDATION_BASELINE_MATCH_LEVEL="${VALIDATION_BASELINE_MATCH_LEVEL:-exact}"
export VALIDATION_SKIP_COMPLETED="${VALIDATION_SKIP_COMPLETED:-1}"
export VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS="${VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS:-0}"
export FUNCTION_CALL_EXTRA_EQUIV_ARGS="${FUNCTION_CALL_EXTRA_EQUIV_ARGS:-}"
export PHASE2_RUN_EXPECTED_MOVEMENT_GATE="${PHASE2_RUN_EXPECTED_MOVEMENT_GATE:-0}"
export PHASE2_RUN_KIND="${PHASE2_RUN_KIND:-phase2_function_call_full_matrix_current}"
export PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT="${PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT:-normal-current-baseline-comparison}"
export PHASE2_EXPECTED_REASON_MOVEMENT="${PHASE2_EXPECTED_REASON_MOVEMENT:-none-required-by-this-wrapper}"
export RUNNER_TMP_ROOT="${RUNNER_TMP_ROOT:-${TMPDIR:-/tmp}/ghidra-equivalence-function-call-full.$$}"

validation_prepare_before_after_logs
validation_finalize_before_after_config

mkdir -p "$OUTPUT_BASE_DIR"

BASELINE_NOTE="available"
if [[ -z "${PHASE2_GATE_BASELINE_DIR:-}" ]]; then
    BASELINE_NOTE="missing; summaries can be regenerated after copying logs to a machine with artifacts/baselines/observed-v0@0a53352"
fi

cat > "$OUTPUT_BASE_DIR/run_manifest.txt" <<EOF
run_kind=$PHASE2_RUN_KIND
target_reason=equivalence_blocking_unsafety
expected_final_result_movement=$PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT
expected_reason_movement=$PHASE2_EXPECTED_REASON_MOVEMENT
function_call_target_set=$FUNCTION_CALL_TARGET_SET
parallel_jobs=$PARALLEL_JOBS
output_base_dir=$OUTPUT_BASE_DIR
base_path=$BASE_PATH
python_bin=$PYTHON_BIN
validation_before_dir=${VALIDATION_BEFORE_DIR:-}
validation_auto_before_snapshot=$VALIDATION_AUTO_BEFORE_SNAPSHOT
validation_require_before_delta=$VALIDATION_REQUIRE_BEFORE_DELTA
validation_require_baseline_match=$VALIDATION_REQUIRE_BASELINE_MATCH
validation_baseline_match_scope=$VALIDATION_BASELINE_MATCH_SCOPE
validation_baseline_match_level=$VALIDATION_BASELINE_MATCH_LEVEL
validation_skip_completed=$VALIDATION_SKIP_COMPLETED
validation_require_phase2_object_keys=$VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS
function_call_extra_equiv_args=$FUNCTION_CALL_EXTRA_EQUIV_ARGS
phase2_run_expected_movement_gate=$PHASE2_RUN_EXPECTED_MOVEMENT_GATE
validation_before_source=$VALIDATION_BEFORE_SOURCE
validation_moved_output_dir=${VALIDATION_MOVED_OUTPUT_DIR:-}
phase2_gate_baseline_dir=${PHASE2_GATE_BASELINE_DIR:-}
runner_tmp_root=$RUNNER_TMP_ROOT
baseline_note=$BASELINE_NOTE
EOF

cat > "$OUTPUT_BASE_DIR/files_to_copy_for_codex.txt" <<EOF
Copy this whole directory back to the review machine:
  $OUTPUT_BASE_DIR

Minimum required files if copying selectively:
  run_manifest.txt
  overall_summary.txt
  phase2_gate/equivalence_blocking_unsafety_expected_movement.json
  files_to_copy_for_codex.txt
  */results_summary.txt
  */*.log

Optional but useful:
  stdout/stderr transcript from the command invocation, e.g. run_stdout.log

If overall_summary.txt, phase2_gate, or per-function results_summary.txt are
missing because the high-spec host did not have observed-v0 artifacts, copy the
raw *.log files anyway. They can be regenerated on the review machine.
EOF

bash "$SCRIPT_DIR/func_call_run_matrix_all_parallel_multifunc.sh"

if [[ "${VALIDATION_RUNNER_DRY_RUN:-0}" != "0" ]]; then
    echo "Phase 2 full matrix dry run finished before expected-movement gate."
    exit 0
fi

PHASE2_GATE_OUTPUT_DIR="${PHASE2_GATE_OUTPUT_DIR:-$OUTPUT_BASE_DIR/phase2_gate}"
if [[ "$PHASE2_RUN_EXPECTED_MOVEMENT_GATE" == "1" ]]; then
    mkdir -p "$PHASE2_GATE_OUTPUT_DIR"

    PHASE1_DIR="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/phase1"
    if [[ -f "$PHASE1_DIR/representative_manifest.json" ]]; then
        PHASE2_GATE_ARGS=(
            --phase1-dir "$PHASE1_DIR"
            --output-dir "$PHASE2_GATE_OUTPUT_DIR"
            --current-log-root "function_call=$OUTPUT_BASE_DIR"
            --baseline-match-scope "${PHASE2_GATE_BASELINE_MATCH_SCOPE:-all}"
        )
        if [[ -n "${PHASE2_GATE_BASELINE_DIR:-}" ]]; then
            PHASE2_GATE_ARGS+=(--baseline-log-root "function_call=$PHASE2_GATE_BASELINE_DIR")
            PHASE2_REQUIRE_READY=1
        else
            PHASE2_REQUIRE_READY=0
        fi
        if [[ "$PHASE2_REQUIRE_READY" == "1" ]]; then
            "$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase2_equivalence_blocking_unsafety \
                "${PHASE2_GATE_ARGS[@]}" \
                --require-ready
        else
            echo "Running Phase 2 gate without --require-ready because observed-v0 baseline logs are unavailable." >&2
            echo "Copy raw logs to a review machine with artifacts/baselines/observed-v0@0a53352/raw/logs/function_call and rerun the gate there." >&2
            "$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase2_equivalence_blocking_unsafety \
                "${PHASE2_GATE_ARGS[@]}"
        fi
    else
        echo "Skipping Phase 2 gate: $PHASE1_DIR/representative_manifest.json is missing." >&2
        echo "Copy logs to a review machine with artifacts/baselines/observed-v0@0a53352/phase1 and rerun the gate there." >&2
    fi
else
    if [[ "$PHASE2_RUN_KIND" == "phase2_function_call_full_matrix_pre_producer" ]]; then
        echo "Skipping Phase 2 expected-movement gate for full pre-producer matrix run."
        echo "Use phase2_run_function_call_pre_producer_gate_reduced_matrix.sh for the require-ready expected-movement gate."
    else
        echo "Skipping Phase 2 expected-movement gate for normal full matrix run."
        echo "Use phase2_run_function_call_full_matrix_pre_producer_32jobs.sh for producer validation."
    fi
fi

echo ""
echo "Full function_call matrix finished."
echo "Output directory: $OUTPUT_BASE_DIR"
echo "Phase 2 gate directory: $PHASE2_GATE_OUTPUT_DIR"
echo "Copy guidance: $OUTPUT_BASE_DIR/files_to_copy_for_codex.txt"
