#!/usr/bin/env bash

validation_prepare_before_after_logs() {
    VALIDATION_BEFORE_SOURCE="not configured"
    VALIDATION_MOVED_OUTPUT_DIR=""

    local execution_authority_root
    execution_authority_root="$OUTPUT_BASE_DIR/.phase8-execution-authority"
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
        scripts.function_tracer_pcode.equivalence.v2.phase8_cutover \
        --print-batch-resume-policy --outcome "$outcome"
}

validation_result_log_has_final_authority() {
    local log_file="$1"
    [[ -f "$log_file" ]] || return 1
    [[ "$(validation_classify_log_result "$log_file")" != "INCOMPLETE" ]]
}

validation_ensure_final_result_line() {
    local log_file="$1"
    local exit_code="$2"

    if (( exit_code == 0 )) || validation_result_log_has_final_authority "$log_file"; then
        return 0
    fi

    {
        echo ""
        echo "Pair process failed before emitting a final result line."
        echo "Exit code: $exit_code"
        echo "Result: ERROR (pair process exited before emitting a final result)"
    } >> "$log_file"
    PYTHONWARNINGS="ignore::RuntimeWarning" "${PYTHON_BIN:-python3}" -m \
        scripts.function_tracer_pcode.equivalence.v2.phase8_cutover \
        --emit-infrastructure-error-json \
        --result-occurrence-id "process-exit-${exit_code}-$(basename "$log_file")" \
        --error-kind "PAIR_PROCESS_EXIT_ERROR" \
        --error-detail "exit_code=${exit_code}" >> "$log_file"
}

validation_append_pair_process_timeout_payload() {
    local log_file="$1"

    {
        echo "=== EQUIVALENCE_RESULT_JSON_BEGIN ==="
        echo '{"is_equivalent": null, "is_timeout": true, "timeout_class": "pair_process_timeout"}'
        echo "=== EQUIVALENCE_RESULT_JSON_END ==="
    } >> "$log_file"
}

validation_classify_log_result() {
    local log_file="$1"
    "${PYTHON_BIN:-python3}" -m \
        scripts.function_tracer_pcode.validation.result_summary \
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

export -f validation_result_log_is_complete
export -f validation_result_log_has_final_authority
export -f validation_ensure_final_result_line
export -f validation_append_pair_process_timeout_payload
export -f validation_classify_log_result
export -f validation_classify_log_display
