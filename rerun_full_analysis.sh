#!/usr/bin/env bash
# Run the full post-fix validation sequence on a prepared analysis host.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

select_python_bin() {
    local candidate

    if [[ -n "${PYTHON_BIN:-}" ]]; then
        echo "$PYTHON_BIN"
        return 0
    fi

    for candidate in \
        "$SCRIPT_DIR/.venv-pyghidra/bin/python" \
        "$SCRIPT_DIR/.venv/bin/python" \
        python3
    do
        if command -v "$candidate" >/dev/null 2>&1 && [[ -x "$(command -v "$candidate")" ]]; then
            echo "$candidate"
            return 0
        fi
    done

    echo "python3"
}

PYTHON_BIN="$(select_python_bin)"
PARALLEL_JOBS="${PARALLEL_JOBS:-30}"
VALIDATION_SKIP_COMPLETED="${VALIDATION_SKIP_COMPLETED:-0}"
VALIDATION_AUTO_BEFORE_SNAPSHOT="${VALIDATION_AUTO_BEFORE_SNAPSHOT:-0}"
RERUN_FULL_ANALYSIS_SKIP_NORMAL_FULL="${RERUN_FULL_ANALYSIS_SKIP_NORMAL_FULL:-0}"

export PYTHON_BIN
export PARALLEL_JOBS
export VALIDATION_SKIP_COMPLETED
export VALIDATION_AUTO_BEFORE_SNAPSHOT
export RERUN_FULL_ANALYSIS_SKIP_NORMAL_FULL

EXPECTED_LANE1_SHA256="eec876a6473ac4ac344d846bdffb93d7bbcf23d55559d0c6d58ee890304e6f5a"
LANE1_MANIFEST="artifacts/baselines/observed-v0@0a53352/audit/phase3_return_coverage_lane1_reclassification/return_coverage_lane1_representatives.json"

run_and_log() {
    local log_file="$1"
    shift

    echo ""
    echo "============================================================"
    echo "Running: $*"
    echo "Log: $log_file"
    echo "============================================================"

    "$@" 2>&1 | tee "$log_file"
}

require_file() {
    local path="$1"
    if [[ ! -f "$path" ]]; then
        echo "Error: required file not found: $path" >&2
        exit 1
    fi
}

if ! command -v "$PYTHON_BIN" >/dev/null 2>&1; then
    echo "Error: PYTHON_BIN was not found: $PYTHON_BIN" >&2
    echo "Set PYTHON_BIN=/path/to/python if Python is elsewhere." >&2
    exit 1
fi
if [[ ! -x "$(command -v "$PYTHON_BIN")" ]]; then
    echo "Error: PYTHON_BIN is not executable: $PYTHON_BIN" >&2
    echo "Set PYTHON_BIN=/path/to/python if Python is elsewhere." >&2
    exit 1
fi

require_file "$LANE1_MANIFEST"

if ! "$PYTHON_BIN" -c "import pyghidra, z3, yaml" >/dev/null 2>&1; then
    echo "Error: required Python modules are missing for: $PYTHON_BIN" >&2
    echo "Install them, for example:" >&2
    echo "  $PYTHON_BIN -m pip install -r requirements-test.txt pyghidra z3-solver" >&2
    exit 1
fi

echo "Repository: $SCRIPT_DIR"
echo "Python: $PYTHON_BIN"
echo "Parallel jobs: $PARALLEL_JOBS"
echo "Validation skip completed: $VALIDATION_SKIP_COMPLETED"
echo "Validation auto before snapshot: $VALIDATION_AUTO_BEFORE_SNAPSHOT"
echo "Skip normal full matrix: $RERUN_FULL_ANALYSIS_SKIP_NORMAL_FULL"

echo ""
echo "Phase 3 audit manifests:"
find artifacts/baselines/observed-v0@0a53352/audit -maxdepth 2 -type f | sort

ACTUAL_LANE1_SHA256="$(sha256sum "$LANE1_MANIFEST" | awk '{print $1}')"
echo ""
echo "Lane 1 manifest sha256: $ACTUAL_LANE1_SHA256"
if [[ "$ACTUAL_LANE1_SHA256" != "$EXPECTED_LANE1_SHA256" ]]; then
    echo "Error: Phase 3 lane 1 manifest sha256 mismatch." >&2
    echo "  expected: $EXPECTED_LANE1_SHA256" >&2
    echo "  actual  : $ACTUAL_LANE1_SHA256" >&2
    exit 1
fi

run_and_log unit_tests_stdout.log \
    "$PYTHON_BIN" -B -m pytest scripts/function_tracer_pcode/tests/unit -q

if [[ "$RERUN_FULL_ANALYSIS_SKIP_NORMAL_FULL" == "1" ]]; then
    echo ""
    echo "Skipping normal Phase 2 full matrix because RERUN_FULL_ANALYSIS_SKIP_NORMAL_FULL=1."
else
    run_and_log phase2_full_rerun_stdout.log \
        ./phase2_run_function_call_full_matrix_32jobs.sh
fi

run_and_log phase2_full_pre_producer_rerun_stdout.log \
    ./phase2_run_function_call_full_matrix_pre_producer_32jobs.sh

run_and_log phase3_run_function_call_return_coverage_lane1_representatives_stdout.log \
    ./phase3_run_function_call_return_coverage_lane1_representatives.sh

run_and_log phase3_run_function_call_return_width_bridge_lane2_representatives_stdout.log \
    ./phase3_run_function_call_return_width_bridge_lane2_representatives.sh

run_and_log phase3_run_loop_readonly_identity_lane3_representatives_stdout.log \
    ./phase3_run_loop_readonly_identity_lane3_representatives.sh

run_and_log phase3_run_loop_method_b_closure_lane4_representatives_stdout.log \
    ./phase3_run_loop_method_b_closure_lane4_representatives.sh

run_and_log phase3_run_function_call_sat_unsafety_lane5_representatives_stdout.log \
    ./phase3_run_function_call_sat_unsafety_lane5_representatives.sh

run_and_log phase3_run_function_call_unresolved_expression_lane6_representatives_stdout.log \
    ./phase3_run_function_call_unresolved_expression_lane6_representatives.sh

run_and_log phase3_run_loop_solver_rewrite_lane7_representatives_stdout.log \
    ./phase3_run_loop_solver_rewrite_lane7_representatives.sh

run_and_log phase3_run_function_call_solver_rewrite_proof_lane8_representatives_stdout.log \
    ./phase3_run_function_call_solver_rewrite_proof_lane8_representatives.sh

run_and_log phase3_run_function_call_solver_timeout_lane9_representatives_stdout.log \
    ./phase3_run_function_call_solver_timeout_lane9_representatives.sh

run_and_log phase3_lane_index_stdout.log \
    ./phase3_validate_all_lane_manifests.sh

run_and_log phase3_post_fix_gate_index_stdout.log \
    env PHASE3_INCLUDE_FULL_MATRIX_DELTA_GATES=1 ./phase3_validate_all_post_fix_gates.sh

echo ""
echo "Full rerun finished."
echo "Copy back *_stdout.log, unit_tests_stdout.log, and logs/equivalence_all/."
