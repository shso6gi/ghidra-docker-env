#!/usr/bin/env bash
# Run the concrete Phase 3 lane 3 readonly identity representative and build
# the post-fix gate against the frozen pre-fix manifest.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

DEFAULT_PYTHON_BIN="python3"
if [[ -x "$SCRIPT_DIR/.venv-pyghidra/bin/python" ]]; then
    DEFAULT_PYTHON_BIN="$SCRIPT_DIR/.venv-pyghidra/bin/python"
fi

export LOOP_TARGET_SET="${LOOP_TARGET_SET:-lmb_sum_even_index_step2}"
export LOOP_PAIR_FILTER="${LOOP_PAIR_FILTER:-lmb_sum_even_index_step2:B10_B13}"
export PARALLEL_JOBS="${PARALLEL_JOBS:-1}"
export OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_readonly_identity_lane3_representatives}"
export BASE_PATH="${BASE_PATH:-$SCRIPT_DIR/targets/cate1/loop_method_b_test}"
export PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"
export VALIDATION_AUTO_BEFORE_SNAPSHOT="${VALIDATION_AUTO_BEFORE_SNAPSHOT:-0}"
export VALIDATION_REQUIRE_BEFORE_DELTA="${VALIDATION_REQUIRE_BEFORE_DELTA:-0}"
export VALIDATION_REQUIRE_BASELINE_MATCH="${VALIDATION_REQUIRE_BASELINE_MATCH:-0}"
export VALIDATION_SKIP_COMPLETED="${VALIDATION_SKIP_COMPLETED:-0}"
export VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS="${VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS:-1}"
export VALIDATION_RUNNER_DRY_RUN="${VALIDATION_RUNNER_DRY_RUN:-0}"
export RUNNER_TMP_ROOT="${RUNNER_TMP_ROOT:-${TMPDIR:-/tmp}/ghidra-equivalence-loop-phase3-lane3.$$}"

BASELINE_RAW_DIR="${BASELINE_RAW_DIR:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/raw}"
BASELINE_LOOP_LOG_ROOT="${BASELINE_LOOP_LOG_ROOT:-$BASELINE_RAW_DIR/logs/loop}"
PHASE3_MANIFEST_PATH="${PHASE3_MANIFEST_PATH:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_readonly_identity_lane3/readonly_identity_lane3_representatives.json}"
PHASE3_MANIFEST_SHA256="${PHASE3_MANIFEST_SHA256:-bca1a298585a58a6b0e27467fc7025387b641cbc639bc9aec859c8269abdf570}"
PHASE3_GATE_OUTPUT_DIR="${PHASE3_GATE_OUTPUT_DIR:-$OUTPUT_BASE_DIR/phase3_readonly_identity_lane3_gate}"
PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"

if [[ ! -f "$PHASE3_MANIFEST_PATH" ]]; then
    echo "Error: Phase 3 lane 3 manifest not found: $PHASE3_MANIFEST_PATH" >&2
    exit 1
fi

ACTUAL_PHASE3_MANIFEST_SHA256="$(sha256sum "$PHASE3_MANIFEST_PATH" | awk '{print $1}')"
if [[ "$ACTUAL_PHASE3_MANIFEST_SHA256" != "$PHASE3_MANIFEST_SHA256" ]]; then
    echo "Error: Phase 3 lane 3 manifest sha256 mismatch." >&2
    echo "  expected: $PHASE3_MANIFEST_SHA256" >&2
    echo "  actual  : $ACTUAL_PHASE3_MANIFEST_SHA256" >&2
    exit 1
fi

mkdir -p "$OUTPUT_BASE_DIR"
cat > "$OUTPUT_BASE_DIR/run_manifest.txt" <<EOF
run_kind=phase3_readonly_identity_lane3_representative_post_fix_gate
target_lane=readonly_identity_missing
loop_target_set=$LOOP_TARGET_SET
loop_pair_filter=$LOOP_PAIR_FILTER
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
baseline_loop_log_root=$BASELINE_LOOP_LOG_ROOT
runner_tmp_root=$RUNNER_TMP_ROOT
EOF

bash "$SCRIPT_DIR/loop_run_matrix_all_parallel_multifunc.sh"

if [[ "$VALIDATION_RUNNER_DRY_RUN" != "0" ]]; then
    echo "Phase 3 lane 3 dry run finished before post-fix gate."
    exit 0
fi

mkdir -p "$PHASE3_GATE_OUTPUT_DIR"
PHASE3_GATE_ARGS=(
    --gate-stage post-fix
    --baseline-raw-dir "$BASELINE_RAW_DIR"
    --output-dir "$PHASE3_GATE_OUTPUT_DIR"
    --current-log-root "loop=$OUTPUT_BASE_DIR"
    --baseline-log-root "loop=$BASELINE_LOOP_LOG_ROOT"
    --phase3-manifest "$PHASE3_MANIFEST_PATH"
    --phase3-manifest-sha256 "$PHASE3_MANIFEST_SHA256"
)

if [[ "$PHASE3_REQUIRE_READY" != "0" ]]; then
    PHASE3_GATE_ARGS+=(--require-ready)
fi

"$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase3_readonly_identity_lane3 \
    "${PHASE3_GATE_ARGS[@]}"

cat > "$OUTPUT_BASE_DIR/files_to_copy_for_codex.txt" <<EOF
Copy this whole directory back to the review machine:
  $OUTPUT_BASE_DIR

Minimum required files if copying selectively:
  run_manifest.txt
  overall_summary.txt
  phase3_readonly_identity_lane3_gate/readonly_identity_lane3_post_fix_gate.json
  files_to_copy_for_codex.txt
  */results_summary.txt
  */*.log
EOF

echo ""
echo "Phase 3 lane 3 representative run finished."
echo "Output directory: $OUTPUT_BASE_DIR"
echo "Phase 3 gate directory: $PHASE3_GATE_OUTPUT_DIR"
