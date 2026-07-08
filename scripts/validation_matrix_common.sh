#!/usr/bin/env bash

validation_prepare_before_after_logs() {
    VALIDATION_BEFORE_SOURCE="not configured"
    VALIDATION_MOVED_OUTPUT_DIR=""

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
    grep -qE "^Result: (EQUIVALENT|NOT EQUIVALENT|ERROR|TIMEOUT|UNKNOWN)" "$log_file"
}

validation_ensure_final_result_line() {
    local log_file="$1"
    local exit_code="$2"

    if (( exit_code == 0 )) || validation_result_log_is_complete "$log_file"; then
        return 0
    fi

    {
        echo ""
        echo "Pair process failed before emitting a final result line."
        echo "Exit code: $exit_code"
        echo "Result: ERROR (pair process exited before emitting a final result)"
    } >> "$log_file"
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
    local status

    status="$(awk '
        /^Result: EQUIVALENT/ { status = "EQ"; status_line = NR }
        /^Result: NOT EQUIVALENT/ { status = "NOT_EQ"; status_line = NR }
        /^Result: ERROR/ { status = "ERROR"; status_line = NR }
        /^Result: TIMEOUT/ { status = "TIMEOUT"; status_line = NR }
        /^Result: UNKNOWN/ { status = "UNKNOWN"; status_line = NR }
        /^=== EQUIVALENCE_RESULT_JSON_BEGIN ===$/ {
            in_json = 1
            json_has_lookup_miss = 0
            next
        }
        /^=== EQUIVALENCE_RESULT_JSON_END ===$/ && in_json {
            last_json_end = NR
            last_json_lookup_miss = json_has_lookup_miss
            in_json = 0
            next
        }
        in_json && /"failure_status"[[:space:]]*:[[:space:]]*"function_lookup_miss"/ {
            json_has_lookup_miss = 1
        }
        END {
            if (status == "") {
                status = "INCOMPLETE"
            }
            if (status == "ERROR" && last_json_lookup_miss && last_json_end > status_line) {
                status = "INCOMPLETE"
            }
            print status
        }
    ' "$log_file")"

    echo "$status"
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
export -f validation_ensure_final_result_line
export -f validation_append_pair_process_timeout_payload
export -f validation_classify_log_result
export -f validation_classify_log_display
