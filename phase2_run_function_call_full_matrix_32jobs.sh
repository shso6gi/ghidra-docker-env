#!/usr/bin/env bash
# Run the full function_call Phase 2 pre-producer matrix on a high-spec host.
#
# This wrapper keeps semantic recovery disabled at the producer layer. It captures
# the expected Phase 2 movement for equivalence_blocking_unsafety:
# final results should not move, while the reason tuple may move to
# call_effect_summary_proof / object_evidence_collected / pending_proof.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

DEFAULT_PYTHON_BIN="python3"
if [[ -x "$SCRIPT_DIR/.venv-pyghidra/bin/python" ]]; then
    DEFAULT_PYTHON_BIN="$SCRIPT_DIR/.venv-pyghidra/bin/python"
fi

export FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-full20}"
export PARALLEL_JOBS="${PARALLEL_JOBS:-32}"
export OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_full_pre_producer}"
export BASE_PATH="${BASE_PATH:-$SCRIPT_DIR/targets/cate1/function_call_test}"
export PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"
DEFAULT_VALIDATION_BEFORE_DIR="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/raw/logs/function_call"
if [[ -z "${VALIDATION_BEFORE_DIR:-}" && -d "$DEFAULT_VALIDATION_BEFORE_DIR" ]]; then
    export VALIDATION_BEFORE_DIR="$DEFAULT_VALIDATION_BEFORE_DIR"
fi
export VALIDATION_AUTO_BEFORE_SNAPSHOT="${VALIDATION_AUTO_BEFORE_SNAPSHOT:-0}"
if [[ -n "${VALIDATION_BEFORE_DIR:-}" ]]; then
    export VALIDATION_REQUIRE_BEFORE_DELTA="${VALIDATION_REQUIRE_BEFORE_DELTA:-1}"
else
    export VALIDATION_REQUIRE_BEFORE_DELTA="${VALIDATION_REQUIRE_BEFORE_DELTA:-0}"
fi
export VALIDATION_REQUIRE_BASELINE_MATCH="${VALIDATION_REQUIRE_BASELINE_MATCH:-0}"
export VALIDATION_SKIP_COMPLETED="${VALIDATION_SKIP_COMPLETED:-1}"
export RUNNER_TMP_ROOT="${RUNNER_TMP_ROOT:-${TMPDIR:-/tmp}/ghidra-equivalence-function-call-full.$$}"

mkdir -p "$OUTPUT_BASE_DIR"

BASELINE_NOTE="available"
if [[ -z "${VALIDATION_BEFORE_DIR:-}" ]]; then
    BASELINE_NOTE="missing; summaries can be regenerated after copying logs to a machine with artifacts/baselines/observed-v0@0a53352"
fi

cat > "$OUTPUT_BASE_DIR/run_manifest.txt" <<EOF
run_kind=phase2_function_call_full_matrix_pre_producer
target_reason=equivalence_blocking_unsafety
expected_final_result_movement=none
expected_reason_movement=call_effect_summary_proof/object_evidence_collected/pending_proof
function_call_target_set=$FUNCTION_CALL_TARGET_SET
parallel_jobs=$PARALLEL_JOBS
output_base_dir=$OUTPUT_BASE_DIR
base_path=$BASE_PATH
python_bin=$PYTHON_BIN
validation_before_dir=${VALIDATION_BEFORE_DIR:-}
validation_auto_before_snapshot=$VALIDATION_AUTO_BEFORE_SNAPSHOT
validation_require_before_delta=$VALIDATION_REQUIRE_BEFORE_DELTA
validation_require_baseline_match=$VALIDATION_REQUIRE_BASELINE_MATCH
validation_skip_completed=$VALIDATION_SKIP_COMPLETED
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

"$SCRIPT_DIR/func_call_run_matrix_all_parallel_multifunc.sh"

PHASE2_GATE_OUTPUT_DIR="${PHASE2_GATE_OUTPUT_DIR:-$OUTPUT_BASE_DIR/phase2_gate}"
mkdir -p "$PHASE2_GATE_OUTPUT_DIR"

PHASE1_DIR="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/phase1"
if [[ -f "$PHASE1_DIR/representative_manifest.json" ]]; then
    PHASE2_GATE_ARGS=(
        --phase1-dir "$PHASE1_DIR"
        --output-dir "$PHASE2_GATE_OUTPUT_DIR"
        --current-log-root "function_call=$OUTPUT_BASE_DIR"
    )
    if [[ -n "${VALIDATION_BEFORE_DIR:-}" ]]; then
        PHASE2_GATE_ARGS+=(--baseline-log-root "function_call=$VALIDATION_BEFORE_DIR")
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

echo ""
echo "Full function_call matrix finished."
echo "Output directory: $OUTPUT_BASE_DIR"
echo "Phase 2 gate directory: $PHASE2_GATE_OUTPUT_DIR"
echo "Copy guidance: $OUTPUT_BASE_DIR/files_to_copy_for_codex.txt"
