#!/usr/bin/env bash
# Rebuild all Phase 3 post-fix gate JSON files from existing representative logs.
# This does not run Ghidra analysis; it only reads logs/equivalence_all and artifacts.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

select_python_bin() {
    local candidate
    if [[ -n "${PYTHON_BIN:-}" ]]; then
        echo "$PYTHON_BIN"
        return 0
    fi
    for candidate in         "$SCRIPT_DIR/.venv-pyghidra/bin/python"         "$SCRIPT_DIR/.venv/bin/python"         python3
    do
        if command -v "$candidate" >/dev/null 2>&1 && [[ -x "$(command -v "$candidate")" ]]; then
            echo "$candidate"
            return 0
        fi
    done
    echo python3
}

PYTHON_BIN="$(select_python_bin)"
BASELINE_RAW_DIR="${BASELINE_RAW_DIR:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/raw}"
BASELINE_FUNCTION_CALL_LOG_ROOT="${BASELINE_FUNCTION_CALL_LOG_ROOT:-$BASELINE_RAW_DIR/logs/function_call}"
BASELINE_LOOP_LOG_ROOT="${BASELINE_LOOP_LOG_ROOT:-$BASELINE_RAW_DIR/logs/loop}"
PHASE1_DIR="${PHASE1_DIR:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/phase1}"
PHASE1_FUNCTION_CALL_LOG_ROOT="${PHASE1_FUNCTION_CALL_LOG_ROOT:-$BASELINE_FUNCTION_CALL_LOG_ROOT}"
PHASE1_LOOP_LOG_ROOT="${PHASE1_LOOP_LOG_ROOT:-$BASELINE_LOOP_LOG_ROOT}"
PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"
PHASE3_GENERATE_MISSING_REPRESENTATIVE_LOGS="${PHASE3_GENERATE_MISSING_REPRESENTATIVE_LOGS:-0}"

require_ready_args=()
if [[ "$PHASE3_REQUIRE_READY" != "0" ]]; then
    require_ready_args+=(--require-ready)
fi

manifest_sha256() {
    sha256sum "$1" | awk '{print $1}'
}

require_manifest_logs() {
    local category="$1"
    local manifest="$2"
    local root="$3"
    local runner="$4"

    "$PYTHON_BIN" - "$category" "$manifest" "$root" "$runner" <<'PY'
import json
import sys
from pathlib import Path

category, manifest_path, root_path, runner = sys.argv[1:]
manifest = json.loads(Path(manifest_path).read_text())
root = Path(root_path)
missing = []
for entry in manifest.get("entries") or ():
    if not isinstance(entry, dict):
        continue
    if entry.get("category") != category:
        continue
    function = str(entry.get("function") or "")
    binary_pair = str(entry.get("binary_pair") or "")
    parts = binary_pair.split("_")
    if not function or len(parts) != 2:
        missing.append((entry.get("id"), function or "<missing>", binary_pair or "<missing>", "<malformed>"))
        continue
    left, right = parts
    candidates = (
        root / function / f"{function}_{left}_{right}.log",
        root / function / f"{function}_{right}_{left}.log",
    )
    if not any(candidate.is_file() for candidate in candidates):
        missing.append(
            (
                entry.get("id"),
                function,
                binary_pair,
                " or ".join(str(candidate) for candidate in candidates),
            )
        )

if missing:
    print("Error: required Phase 3 representative logs are missing for log-only gate rebuild.", file=sys.stderr)
    print(f"  category: {category}", file=sys.stderr)
    print(f"  root    : {root}", file=sys.stderr)
    print(f"  manifest: {manifest_path}", file=sys.stderr)
    print("  missing entries:", file=sys.stderr)
    for entry_id, function, binary_pair, candidates in missing:
        print(f"    - id={entry_id} function={function} binary_pair={binary_pair}", file=sys.stderr)
        print(f"      expected log: {candidates}", file=sys.stderr)
    print("", file=sys.stderr)
    print("This script does not run Ghidra analysis. Generate the missing representative logs first:", file=sys.stderr)
    print(f"  {runner}", file=sys.stderr)
    sys.exit(2)
PY
}

require_or_generate_manifest_logs() {
    local category="$1"
    local manifest="$2"
    local root="$3"
    local runner="$4"

    if require_manifest_logs "$category" "$manifest" "$root" "$runner"; then
        return 0
    fi

    if [[ "$PHASE3_GENERATE_MISSING_REPRESENTATIVE_LOGS" == "0" ]]; then
        return 2
    fi

    echo
    echo "Generating missing representative logs with: $runner"
    echo "============================================================"
    env VALIDATION_RUNNER_DRY_RUN=0 VALIDATION_SKIP_COMPLETED=0 "$runner"
    echo "============================================================"
    require_manifest_logs "$category" "$manifest" "$root" "$runner"
}

require_phase1_non_regression_logs() {
    "$PYTHON_BIN" - "$PHASE1_DIR" "$PHASE1_FUNCTION_CALL_LOG_ROOT" "$PHASE1_LOOP_LOG_ROOT" <<'PY'
import json
import sys
from pathlib import Path

phase1_dir, function_call_root, loop_root = sys.argv[1:]
roots = {
    "function_call": Path(function_call_root),
    "loop": Path(loop_root),
}
manifests = (
    Path(phase1_dir) / "positive_manifest.json",
    Path(phase1_dir) / "negative_manifest.json",
)
missing = []
for manifest_path in manifests:
    if not manifest_path.is_file():
        missing.append((str(manifest_path), "<manifest>", "<missing>", "<missing>"))
        continue
    manifest = json.loads(manifest_path.read_text())
    for entry in manifest.get("entries") or ():
        if not isinstance(entry, dict):
            continue
        category = str(entry.get("category") or "")
        if category == "synthetic_negative":
            continue
        root = roots.get(category)
        function = str(entry.get("function") or "")
        binary_pair = str(entry.get("binary_pair") or "")
        parts = binary_pair.split("_")
        if root is None or not function or len(parts) != 2:
            missing.append((entry.get("id"), category or "<missing>", function or "<missing>", binary_pair or "<missing>"))
            continue
        left, right = parts
        candidates = (
            root / function / f"{function}_{left}_{right}.log",
            root / function / f"{function}_{right}_{left}.log",
        )
        if not any(candidate.is_file() for candidate in candidates):
            missing.append(
                (
                    entry.get("id"),
                    category,
                    function,
                    binary_pair,
                    " or ".join(str(candidate) for candidate in candidates),
                )
            )

if missing:
    print("Error: required Phase 1 positive/negative non-regression logs are missing for lane 1 post-fix gate rebuild.", file=sys.stderr)
    print(f"  phase1_dir              : {phase1_dir}", file=sys.stderr)
    print(f"  function_call_log_root  : {function_call_root}", file=sys.stderr)
    print(f"  loop_log_root           : {loop_root}", file=sys.stderr)
    print("  missing entries:", file=sys.stderr)
    for item in missing:
        if len(item) == 4:
            entry_id, category, function, binary_pair = item
            print(f"    - id={entry_id} category={category} function={function} binary_pair={binary_pair}", file=sys.stderr)
            continue
        entry_id, category, function, binary_pair, candidates = item
        print(f"    - id={entry_id} category={category} function={function} binary_pair={binary_pair}", file=sys.stderr)
        print(f"      expected log: {candidates}", file=sys.stderr)
    print("", file=sys.stderr)
    print("Generate or copy the Phase 2 full-current function_call logs, or set PHASE1_FUNCTION_CALL_LOG_ROOT/PHASE1_LOOP_LOG_ROOT to the correct roots.", file=sys.stderr)
    sys.exit(2)
PY
}

run_gate() {
    echo
    echo "============================================================"
    echo "Running: $PYTHON_BIN -m $* ${require_ready_args[*]}"
    echo "============================================================"
    "$PYTHON_BIN" -m "$@" "${require_ready_args[@]}"
}

LANE1_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_return_coverage_lane1_reclassification/return_coverage_lane1_representatives.json"
LANE2_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_return_width_bridge_lane2/return_width_bridge_lane2_representatives.json"
LANE3_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_readonly_identity_lane3/readonly_identity_lane3_representatives.json"
LANE4_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_method_b_closure_lane4/method_b_closure_lane4_representatives.json"
LANE5_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_sat_unsafety_lane5/sat_unsafety_lane5_representatives.json"
LANE6_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_unresolved_expression_lane6/unresolved_expression_lane6_representatives.json"
LANE7_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_solver_rewrite_lane7/solver_rewrite_lane7_representatives.json"
LANE8_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_solver_rewrite_proof_lane8/solver_rewrite_proof_lane8_representatives.json"
LANE9_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_solver_timeout_lane9/solver_timeout_lane9_representatives.json"

echo "Preflight: checking required Phase 3 representative logs."
preflight_failed=0
require_phase1_non_regression_logs || preflight_failed=1
require_or_generate_manifest_logs function_call "$LANE1_MANIFEST" "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_return_coverage_lane1_representatives" "./phase3_run_function_call_return_coverage_lane1_representatives.sh" || preflight_failed=1
require_or_generate_manifest_logs function_call "$LANE2_MANIFEST" "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_return_width_bridge_lane2_representatives" "./phase3_run_function_call_return_width_bridge_lane2_representatives.sh" || preflight_failed=1
require_or_generate_manifest_logs loop "$LANE3_MANIFEST" "$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_readonly_identity_lane3_representatives" "./phase3_run_loop_readonly_identity_lane3_representatives.sh" || preflight_failed=1
require_or_generate_manifest_logs loop "$LANE4_MANIFEST" "$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_method_b_closure_lane4_representatives" "./phase3_run_loop_method_b_closure_lane4_representatives.sh" || preflight_failed=1
require_or_generate_manifest_logs function_call "$LANE5_MANIFEST" "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_sat_unsafety_lane5_representatives" "./phase3_run_function_call_sat_unsafety_lane5_representatives.sh" || preflight_failed=1
require_or_generate_manifest_logs function_call "$LANE6_MANIFEST" "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_unresolved_expression_lane6_representatives" "./phase3_run_function_call_unresolved_expression_lane6_representatives.sh" || preflight_failed=1
require_or_generate_manifest_logs loop "$LANE7_MANIFEST" "$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_solver_rewrite_lane7_representatives" "./phase3_run_loop_solver_rewrite_lane7_representatives.sh" || preflight_failed=1
require_or_generate_manifest_logs function_call "$LANE8_MANIFEST" "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_solver_rewrite_proof_lane8_representatives" "./phase3_run_function_call_solver_rewrite_proof_lane8_representatives.sh" || preflight_failed=1
require_or_generate_manifest_logs function_call "$LANE9_MANIFEST" "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_solver_timeout_lane9_representatives" "./phase3_run_function_call_solver_timeout_lane9_representatives.sh" || preflight_failed=1
if [[ "$preflight_failed" != "0" ]]; then
    echo "Error: log-only Phase 3 post-fix gate rebuild cannot continue until the missing representative logs are generated or copied." >&2
    echo "If this follows copy_full_rerun_artifacts.bat, the remote share did not contain the missing representative log directories." >&2
    echo "To let this script generate missing representative logs, run:" >&2
    echo "  PHASE3_GENERATE_MISSING_REPRESENTATIVE_LOGS=1 ./phase3_rebuild_all_post_fix_gates_from_logs.sh" >&2
    echo "Run the listed representative scripts on the analysis host, or run PARALLEL_JOBS=32 ./rerun_full_analysis.sh to regenerate them as part of the full sequence." >&2
    exit 2
fi

run_gate scripts.function_tracer_pcode.validation.phase3_return_coverage_lane1     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_return_coverage_lane1_representatives/phase3_return_coverage_lane1_gate"     --current-log-root "function_call=$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_return_coverage_lane1_representatives"     --baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"     --phase1-dir "$PHASE1_DIR"     --phase1-current-log-root "function_call=$PHASE1_FUNCTION_CALL_LOG_ROOT"     --phase1-current-log-root "loop=$PHASE1_LOOP_LOG_ROOT"     --phase3-manifest "$LANE1_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE1_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_return_width_bridge_lane2     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_return_width_bridge_lane2_representatives/phase3_return_width_bridge_lane2_gate"     --current-log-root "function_call=$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_return_width_bridge_lane2_representatives"     --baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"     --phase3-manifest "$LANE2_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE2_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_readonly_identity_lane3     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_readonly_identity_lane3_representatives/phase3_readonly_identity_lane3_gate"     --current-log-root "loop=$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_readonly_identity_lane3_representatives"     --baseline-log-root "loop=$BASELINE_LOOP_LOG_ROOT"     --phase3-manifest "$LANE3_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE3_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_method_b_closure_lane4     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_method_b_closure_lane4_representatives/phase3_method_b_closure_lane4_gate"     --current-log-root "loop=$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_method_b_closure_lane4_representatives"     --baseline-log-root "loop=$BASELINE_LOOP_LOG_ROOT"     --phase3-manifest "$LANE4_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE4_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_sat_unsafety_lane5     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_sat_unsafety_lane5_representatives/phase3_sat_unsafety_lane5_gate"     --current-log-root "function_call=$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_sat_unsafety_lane5_representatives"     --baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"     --phase3-manifest "$LANE5_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE5_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_unresolved_expression_lane6     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_unresolved_expression_lane6_representatives/phase3_unresolved_expression_lane6_gate"     --current-log-root "function_call=$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_unresolved_expression_lane6_representatives"     --baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"     --phase3-manifest "$LANE6_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE6_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_solver_rewrite_lane7     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_solver_rewrite_lane7_representatives/phase3_solver_rewrite_lane7_gate"     --current-log-root "loop=$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_solver_rewrite_lane7_representatives"     --baseline-log-root "loop=$BASELINE_LOOP_LOG_ROOT"     --phase3-manifest "$LANE7_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE7_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_solver_rewrite_proof_lane8     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_solver_rewrite_proof_lane8_representatives/phase3_solver_rewrite_proof_lane8_gate"     --current-log-root "function_call=$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_solver_rewrite_proof_lane8_representatives"     --baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"     --phase3-manifest "$LANE8_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE8_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_solver_timeout_lane9     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_solver_timeout_lane9_representatives/phase3_solver_timeout_lane9_gate"     --current-log-root "function_call=$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_solver_timeout_lane9_representatives"     --baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"     --phase3-manifest "$LANE9_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE9_MANIFEST")"

echo
PHASE3_INCLUDE_FULL_MATRIX_DELTA_GATES=1 "$SCRIPT_DIR/phase3_validate_all_post_fix_gates.sh"
