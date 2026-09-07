#!/usr/bin/env bash

validation_prepare_before_after_logs() {
    VALIDATION_BEFORE_SOURCE="not configured"
    VALIDATION_MOVED_OUTPUT_DIR=""

    local execution_authority_root
    execution_authority_root="${VALIDATION_EXECUTION_AUTHORITY_ROOT:-${EQBENCH_RUN_TMPDIR:-${TMPDIR:-/tmp}/phase8-execution-authority-$$}}"
    mkdir -p "$execution_authority_root"
    chmod 700 "$execution_authority_root"
    export UNKNOWN_TAXONOMY_V2_WORKER_KEY_ID="phase8-matrix-worker-v1"
    export UNKNOWN_TAXONOMY_V2_WORKER_KEY_FILE="$execution_authority_root/worker.key"
    if [[ ! -s "$UNKNOWN_TAXONOMY_V2_WORKER_KEY_FILE" ]]; then
        umask 077
        head -c 32 /dev/urandom > "$UNKNOWN_TAXONOMY_V2_WORKER_KEY_FILE"
    fi

    if [[ -n "${VALIDATION_BEFORE_DIR:-}" ]]; then
        VALIDATION_BEFORE_SOURCE="configured"
    fi

    if [[ "${VALIDATION_AUTO_BEFORE_SNAPSHOT:-1}" == "0" || ! -d "$OUTPUT_BASE_DIR" ]]; then
        return 0
    fi

    local existing_validation_log
    existing_validation_log="$(find "$OUTPUT_BASE_DIR" -type f -name "*.log" -print -quit 2>/dev/null || true)"
    if [[ -z "$existing_validation_log" ]]; then
        return 0
    fi

    local tmp_root before_dir
    if ! tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/equivalence_before.XXXXXX")"; then
        echo "Error: failed to create temporary before/after log directory." >&2
        exit 1
    fi
    before_dir="${tmp_root}/$(basename "$OUTPUT_BASE_DIR")"
    if ! mv "$OUTPUT_BASE_DIR" "$before_dir"; then
        echo "Error: failed to move old output dir to $before_dir." >&2
        exit 1
    fi
    if ! mkdir -p "$OUTPUT_BASE_DIR"; then
        echo "Error: failed to recreate output dir $OUTPUT_BASE_DIR." >&2
        exit 1
    fi

    if [[ -z "${VALIDATION_BEFORE_DIR:-}" ]]; then
        VALIDATION_BEFORE_DIR="$before_dir"
        VALIDATION_BEFORE_SOURCE="auto moved old output"
    fi
    VALIDATION_MOVED_OUTPUT_DIR="$before_dir"
    export VALIDATION_BEFORE_DIR VALIDATION_BEFORE_SOURCE VALIDATION_MOVED_OUTPUT_DIR
}

validation_finalize_before_after_config() {
    VALIDATION_BEFORE_LABEL="(none)"
    if [[ -n "${VALIDATION_BEFORE_DIR:-}" ]]; then
        VALIDATION_BEFORE_LABEL="$VALIDATION_BEFORE_DIR"
    fi

    if [[ "${VALIDATION_REQUIRE_BEFORE_DELTA:-0}" != "0" && -z "${VALIDATION_BEFORE_DIR:-}" ]]; then
        echo "Error: VALIDATION_REQUIRE_BEFORE_DELTA requires VALIDATION_BEFORE_DIR or an auto before snapshot." >&2
        exit 1
    fi

    export VALIDATION_BEFORE_LABEL
}

validation_result_log_is_complete() {
    local log_file="$1"
    [[ -f "$log_file" ]] || return 1
    case "$(validation_batch_resume_policy "$(validation_classify_log_result "$log_file")")" in
        COMPLETE_EQ|COMPLETE_NOT_EQ|FAILED_INFRASTRUCTURE) return 0 ;;
        *) return 1 ;;
    esac
}

validation_batch_resume_policy() {
    local outcome="$1"
    if [[ "$outcome" == "INCOMPLETE" ]]; then
        echo "INCOMPLETE"
        return 0
    fi
    PYTHONWARNINGS="ignore::RuntimeWarning" "${PYTHON_BIN:-python3}" -m \
        scripts.function_tracer_pcode.authority.decision.production_cutover \
        --print-batch-resume-policy --outcome "$outcome"
}

validation_result_log_has_final_authority() {
    local log_file="$1"
    [[ -f "$log_file" ]] || return 1
    [[ "$(validation_classify_log_result "$log_file")" != "INCOMPLETE" ]]
}

validation_classify_log_result() {
    local log_file="$1"
    "${PYTHON_BIN:-python3}" -m \
        scripts.function_tracer_pcode.reporting.result_summary \
        --classify-log "$log_file"
}

validation_classify_log_display() {
    case "$(validation_classify_log_result "$1")" in
        EQ)
            echo "EQUIVALENT ✓"
            ;;
        NOT_EQ)
            echo "NOT EQUIVALENT ✗"
            ;;
        ERROR)
            echo "ERROR !"
            ;;
        TIMEOUT)
            echo "TIMEOUT"
            ;;
        UNKNOWN)
            echo "UNKNOWN"
            ;;
        *)
            echo "INCOMPLETE"
            ;;
    esac
}

# Issue #104 runner benchmark validation gate.
#
# Builds the function-level source diff manifest from the benchmark tree the
# runner actually compiled and classifies every canonical pair outcome under
# OUTPUT_BASE_DIR (Eq->NOT_EQ, Neq CONFIRMED_NOT_EQ->EQUIVALENT and
# unclassifiable Neq EQUIVALENT are hard violations; source-changed-but-
# unconfirmed EQUIVALENT is counted as suspicious).  The gate is an
# evaluation oracle only: it never feeds the checker and never rewrites a
# pair status.  Results are merged into run_health_summary.{json,txt} and
# written to benchmark_validation_gate.json / function_diff_manifest.json,
# which the execution receipt hashes.
#
#   validation_run_benchmark_gate <output_base_dir> <benchmark_root> <repo_root>
#
# Sets VALIDATION_BENCHMARK_GATE_STATUS (PASS|FAIL|EMPTY|SKIPPED|MANIFEST_FAILED)
# and VALIDATION_BENCHMARK_GATE_FAILURES (0/1).  Disabled with
# EQBENCH_BENCHMARK_GATE=0 (status SKIPPED, no failure).  Set
# EQBENCH_BENCHMARK_GATE_FAIL_ON_SUSPICIOUS=1 to also fail on suspicious rows.
validation_run_benchmark_gate() {
    local output_base_dir="$1" benchmark_root="$2" repo_root="$3"
    local python_bin="${PYTHON_BIN:-python3}"
    local manifest="$output_base_dir/function_diff_manifest.json"
    local report="$output_base_dir/benchmark_validation_gate.json"
    local ground_truth="$repo_root/scripts/eqbench/neq_ground_truth.tsv"
    local -a gate_args=()
    VALIDATION_BENCHMARK_GATE_STATUS=SKIPPED
    VALIDATION_BENCHMARK_GATE_FAILURES=0
    if [[ "${EQBENCH_BENCHMARK_GATE:-1}" == "0" ]]; then
        echo "Benchmark validation gate skipped (EQBENCH_BENCHMARK_GATE=0)."
        return 0
    fi
    local -a manifest_args=(--benchmark-root "$benchmark_root" --output "$manifest")
    if [[ -f "$ground_truth" ]]; then
        manifest_args+=(--ground-truth "$ground_truth")
    else
        manifest_args+=(--no-ground-truth)
    fi
    if ! "$python_bin" -B "$repo_root/scripts/eqbench/function_diff_manifest.py" "${manifest_args[@]}" \
        > "$output_base_dir/function_diff_manifest.summary.txt" 2> "$output_base_dir/function_diff_manifest.error"; then
        VALIDATION_BENCHMARK_GATE_STATUS=MANIFEST_FAILED
        VALIDATION_BENCHMARK_GATE_FAILURES=1
        echo "Benchmark validation gate: function diff manifest failed; see $output_base_dir/function_diff_manifest.error" >&2
        return 0
    fi
    cat "$output_base_dir/function_diff_manifest.summary.txt"
    if [[ "${EQBENCH_BENCHMARK_GATE_FAIL_ON_SUSPICIOUS:-0}" == "1" ]]; then
        gate_args+=(--fail-on-suspicious)
    fi
    local gate_exit=0
    (
        cd "$repo_root" && "$python_bin" -B -m scripts.function_tracer_pcode.reporting.benchmark_validation_gate \
            "$output_base_dir" \
            --manifest "$manifest" \
            --json "$report" \
            --health-summary-json "$output_base_dir/run_health_summary.json" \
            --health-summary-text "$output_base_dir/run_health_summary.txt" \
            ${gate_args[@]+"${gate_args[@]}"}
    ) > "$output_base_dir/benchmark_validation_gate.txt" 2>&1 || gate_exit=$?
    cat "$output_base_dir/benchmark_validation_gate.txt"
    case "$gate_exit" in
        0) VALIDATION_BENCHMARK_GATE_STATUS=PASS ;;
        1) VALIDATION_BENCHMARK_GATE_STATUS=FAIL; VALIDATION_BENCHMARK_GATE_FAILURES=1 ;;
        *) VALIDATION_BENCHMARK_GATE_STATUS=EMPTY; VALIDATION_BENCHMARK_GATE_FAILURES=1 ;;
    esac
    if (( VALIDATION_BENCHMARK_GATE_FAILURES > 0 )); then
        echo "Benchmark validation gate: $VALIDATION_BENCHMARK_GATE_STATUS (exit $gate_exit); see $report" >&2
    fi
    return 0
}

export -f validation_run_benchmark_gate
export -f validation_result_log_is_complete
export -f validation_result_log_has_final_authority
export -f validation_classify_log_result
export -f validation_classify_log_display
