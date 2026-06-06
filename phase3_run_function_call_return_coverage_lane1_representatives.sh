#!/usr/bin/env bash
# Run the concrete Phase 3 lane 1 return-coverage representatives and build
# the post-fix gate against the frozen pre-fix manifest.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

DEFAULT_PYTHON_BIN="python3"
if [[ -x "$SCRIPT_DIR/.venv-pyghidra/bin/python" ]]; then
    DEFAULT_PYTHON_BIN="$SCRIPT_DIR/.venv-pyghidra/bin/python"
fi

export FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-fc_recursive_sum,fc_is_even,fc_is_odd}"
export FUNCTION_CALL_PAIR_FILTER="${FUNCTION_CALL_PAIR_FILTER:-fc_recursive_sum:B11_B15,fc_is_even:B11_B12,fc_is_odd:B8_B15,fc_is_odd:B11_B16,fc_is_odd:B12_B16}"
export PARALLEL_JOBS="${PARALLEL_JOBS:-2}"
export OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_return_coverage_lane1_representatives}"
export BASE_PATH="${BASE_PATH:-$SCRIPT_DIR/targets/cate1/function_call_test}"
export PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"
export VALIDATION_AUTO_BEFORE_SNAPSHOT="${VALIDATION_AUTO_BEFORE_SNAPSHOT:-0}"
export VALIDATION_REQUIRE_BEFORE_DELTA="${VALIDATION_REQUIRE_BEFORE_DELTA:-0}"
export VALIDATION_REQUIRE_BASELINE_MATCH="${VALIDATION_REQUIRE_BASELINE_MATCH:-0}"
export VALIDATION_SKIP_COMPLETED="${VALIDATION_SKIP_COMPLETED:-0}"
export VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS="${VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS:-1}"
export VALIDATION_RUNNER_DRY_RUN="${VALIDATION_RUNNER_DRY_RUN:-0}"
export RUNNER_TMP_ROOT="${RUNNER_TMP_ROOT:-${TMPDIR:-/tmp}/ghidra-equivalence-function-call-phase3-lane1.$$}"

BASELINE_RAW_DIR="${BASELINE_RAW_DIR:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/raw}"
BASELINE_FUNCTION_CALL_LOG_ROOT="${BASELINE_FUNCTION_CALL_LOG_ROOT:-$BASELINE_RAW_DIR/logs/function_call}"
PHASE1_DIR="${PHASE1_DIR:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/phase1}"
PHASE1_FUNCTION_CALL_LOG_ROOT="${PHASE1_FUNCTION_CALL_LOG_ROOT:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_full_current}"
PHASE1_LOOP_LOG_ROOT="${PHASE1_LOOP_LOG_ROOT:-$BASELINE_RAW_DIR/logs/loop}"
PHASE3_MANIFEST_PATH="${PHASE3_MANIFEST_PATH:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_return_coverage_lane1_reclassification/return_coverage_lane1_representatives.json}"
PHASE3_MANIFEST_SHA256="${PHASE3_MANIFEST_SHA256:-eec876a6473ac4ac344d846bdffb93d7bbcf23d55559d0c6d58ee890304e6f5a}"
PHASE3_GATE_OUTPUT_DIR="${PHASE3_GATE_OUTPUT_DIR:-$OUTPUT_BASE_DIR/phase3_return_coverage_lane1_gate}"
PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"

if [[ ! -f "$PHASE3_MANIFEST_PATH" ]]; then
    echo "Error: Phase 3 lane 1 manifest not found: $PHASE3_MANIFEST_PATH" >&2
    exit 1
fi

ACTUAL_PHASE3_MANIFEST_SHA256="$(sha256sum "$PHASE3_MANIFEST_PATH" | awk '{print $1}')"
if [[ "$ACTUAL_PHASE3_MANIFEST_SHA256" != "$PHASE3_MANIFEST_SHA256" ]]; then
    echo "Error: Phase 3 lane 1 manifest sha256 mismatch." >&2
    echo "  expected: $PHASE3_MANIFEST_SHA256" >&2
    echo "  actual  : $ACTUAL_PHASE3_MANIFEST_SHA256" >&2
    exit 1
fi

mkdir -p "$OUTPUT_BASE_DIR"
cat > "$OUTPUT_BASE_DIR/run_manifest.txt" <<EOF
run_kind=phase3_return_coverage_lane1_representative_post_fix_gate
target_lane=return_coverage_gap_return_coverage_inconclusive
function_call_target_set=$FUNCTION_CALL_TARGET_SET
function_call_pair_filter=$FUNCTION_CALL_PAIR_FILTER
parallel_jobs=$PARALLEL_JOBS
output_base_dir=$OUTPUT_BASE_DIR
base_path=$BASE_PATH
python_bin=$PYTHON_BIN
validation_auto_before_snapshot=$VALIDATION_AUTO_BEFORE_SNAPSHOT
validation_require_before_delta=$VALIDATION_REQUIRE_BEFORE_DELTA
validation_require_baseline_match=$VALIDATION_REQUIRE_BASELINE_MATCH
validation_skip_completed=$VALIDATION_SKIP_COMPLETED
validation_require_phase2_object_keys=$VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS
validation_runner_dry_run=$VALIDATION_RUNNER_DRY_RUN
phase3_manifest_path=$PHASE3_MANIFEST_PATH
phase3_manifest_sha256=$PHASE3_MANIFEST_SHA256
phase3_gate_output_dir=$PHASE3_GATE_OUTPUT_DIR
phase3_require_ready=$PHASE3_REQUIRE_READY
baseline_function_call_log_root=$BASELINE_FUNCTION_CALL_LOG_ROOT
phase1_function_call_log_root=$PHASE1_FUNCTION_CALL_LOG_ROOT
phase1_loop_log_root=$PHASE1_LOOP_LOG_ROOT
runner_tmp_root=$RUNNER_TMP_ROOT
EOF

bash "$SCRIPT_DIR/func_call_run_matrix_all_parallel_multifunc.sh"

if [[ "$VALIDATION_RUNNER_DRY_RUN" != "0" ]]; then
    echo "Phase 3 lane 1 dry run finished before post-fix gate."
    exit 0
fi

mkdir -p "$PHASE3_GATE_OUTPUT_DIR"
PHASE3_GATE_ARGS=(
    --gate-stage post-fix
    --baseline-raw-dir "$BASELINE_RAW_DIR"
    --output-dir "$PHASE3_GATE_OUTPUT_DIR"
    --current-log-root "function_call=$OUTPUT_BASE_DIR"
    --baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"
    --phase1-dir "$PHASE1_DIR"
    --phase1-current-log-root "function_call=$PHASE1_FUNCTION_CALL_LOG_ROOT"
    --phase1-current-log-root "loop=$PHASE1_LOOP_LOG_ROOT"
    --phase3-manifest "$PHASE3_MANIFEST_PATH"
    --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"
)

if [[ "$PHASE3_REQUIRE_READY" != "0" ]]; then
    PHASE3_GATE_ARGS+=(--require-ready)
fi

"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase3_return_coverage_lane1 \
    "${PHASE3_GATE_ARGS[@]}"

cat > "$OUTPUT_BASE_DIR/files_to_copy_for_codex.txt" <<EOF
Copy this whole directory back to the review machine:
  $OUTPUT_BASE_DIR

Minimum required files if copying selectively:
  run_manifest.txt
  overall_summary.txt
  phase3_return_coverage_lane1_gate/return_coverage_lane1_post_fix_gate.json
  files_to_copy_for_codex.txt
  */results_summary.txt
  */*.log
EOF

echo ""
echo "Phase 3 lane 1 representative run finished."
echo "Output directory: $OUTPUT_BASE_DIR"
echo "Phase 3 gate directory: $PHASE3_GATE_OUTPUT_DIR"
