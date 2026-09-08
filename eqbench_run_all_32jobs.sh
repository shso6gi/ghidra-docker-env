#!/usr/bin/env bash
# Compile every EqBench Eq/newV.c or Eq/new.c sample into Eq/source and run a
# pairwise equivalence matrix for every non-main source-defined function.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"
source "$SCRIPT_DIR/scripts/validation_matrix_common.sh" || exit 1
source "$SCRIPT_DIR/scripts/eqbench/pair_scheduler.sh" || exit 1

if (( BASH_VERSINFO[0] < 4 || (BASH_VERSINFO[0] == 4 && BASH_VERSINFO[1] < 3) )); then
    echo "Error: bash 4.3 or newer is required for wait -n" >&2
    exit 1
fi

DEFAULT_PYTHON_BIN="python3"
if [[ -x "$SCRIPT_DIR/.venv-pyghidra/bin/python" ]]; then
    DEFAULT_PYTHON_BIN="$SCRIPT_DIR/.venv-pyghidra/bin/python"
fi

EQBENCH_ROOT="${EQBENCH_ROOT:-$SCRIPT_DIR/targets/EqBench/benchmarks}"
OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/EqBench/all_eq_matrix_current}"
PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"
PARALLEL_JOBS="${PARALLEL_JOBS:-32}"
PARALLEL_JOBS_REQUESTED="$PARALLEL_JOBS"
VALIDATION_SUMMARY_LEVEL="${VALIDATION_SUMMARY_LEVEL:-compact}"
EQBENCH_MAX_SAMPLES="${EQBENCH_MAX_SAMPLES:-0}"
EQBENCH_SAMPLE_FILTER="${EQBENCH_SAMPLE_FILTER:-}"
EQBENCH_PAIR_FILTER="${EQBENCH_PAIR_FILTER:-}"
EQBENCH_RERUN_MANIFEST="${EQBENCH_RERUN_MANIFEST:-}"
ERROR_RERUN_RUN_ID="${ERROR_RERUN_RUN_ID:-}"
EQBENCH_RUN_SCOPE="${EQBENCH_RUN_SCOPE:-REPRESENTATIVE}"
EQBENCH_BUILD_POLICY="${EQBENCH_BUILD_POLICY:-REUSE_OR_COMPILE}"
DRY_RUN="${DRY_RUN:-0}"
PAIR_PROCESS_TIMEOUT="${PAIR_PROCESS_TIMEOUT:-600s}"
PAIR_PROCESS_KILL_AFTER="${PAIR_PROCESS_KILL_AFTER:-30s}"
PAIR_PROCESS_TIMEOUT_SECONDS="${PAIR_PROCESS_TIMEOUT%s}"
PAIR_PROCESS_KILL_AFTER_SECONDS="${PAIR_PROCESS_KILL_AFTER%s}"
EQUIV_TIMEOUT="${EQUIV_TIMEOUT:-10}"
DECOMPILE_TIMEOUT="${DECOMPILE_TIMEOUT:-60}"
PAIRWISE_TIMEOUT="${PAIRWISE_TIMEOUT:-5}"
PAIRWISE_TIMEOUT_HARD="${PAIRWISE_TIMEOUT_HARD:-30}"
# Issue #131: 共通 dedup のケース数上限。既定は本番と同じ 16。調査で下げる場合も
# 子プロセスへ明示的に渡し、実行記録に有効値を残す。
FT_EXPANDER_DEDUP_CASE_LIMIT="${FT_EXPANDER_DEDUP_CASE_LIMIT:-16}"
export FT_EXPANDER_DEDUP_CASE_LIMIT
EQBENCH_RESOURCE_ADMISSION="${EQBENCH_RESOURCE_ADMISSION:-1}"
EQBENCH_CPU_TOKENS="${EQBENCH_CPU_TOKENS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || nproc 2>/dev/null || printf '1')}"
EQBENCH_PAIR_CPU_TOKENS="${EQBENCH_PAIR_CPU_TOKENS:-8}"
EQBENCH_PROGRESS_INTERVAL_SECONDS="${EQBENCH_PROGRESS_INTERVAL_SECONDS:-5}"
SKIP_COMPLETED_RESULTS="${SKIP_COMPLETED_RESULTS:-1}"
ERROR_ONLY_RERUN="${ERROR_ONLY_RERUN:-0}"
EQBENCH_DEBUG="${EQBENCH_DEBUG:-0}"
DEFAULT_TMPDIR="$SCRIPT_DIR/tmp"
if [[ -d /workspace && -w /workspace ]]; then
    DEFAULT_TMPDIR="/workspace/tmp"
fi
EQBENCH_TMPDIR="${EQBENCH_TMPDIR:-$DEFAULT_TMPDIR}"
EQBENCH_PRIVATE_AUTHORITY_ROOT="${EQBENCH_PRIVATE_AUTHORITY_ROOT:-$EQBENCH_TMPDIR/eqbench-private-authority}"

COMPILE_TEMPLATE="$SCRIPT_DIR/scripts/eqbench/compile_all_arm_mips.sh"
FUNCTION_LISTER="$SCRIPT_DIR/scripts/eqbench/list_c_functions.py"
FULL_SCOPE_EXPECTATION="$SCRIPT_DIR/scripts/function_tracer_pcode/reporting/eqbench_full_scope.json"

if [[ ! -f "$COMPILE_TEMPLATE" ]]; then
    echo "Error: compile template not found: $COMPILE_TEMPLATE" >&2
    exit 1
fi
if [[ ! -f "$FUNCTION_LISTER" ]]; then
    echo "Error: function lister not found: $FUNCTION_LISTER" >&2
    exit 1
fi
if [[ ! -f "$FULL_SCOPE_EXPECTATION" ]]; then
    echo "Error: full EqBench scope expectation not found: $FULL_SCOPE_EXPECTATION" >&2
    exit 1
fi
if [[ "$EQBENCH_RUN_SCOPE" != "REPRESENTATIVE" && "$EQBENCH_RUN_SCOPE" != "FULL_EQBENCH" ]]; then
    echo "Error: EQBENCH_RUN_SCOPE must be REPRESENTATIVE or FULL_EQBENCH" >&2
    exit 1
fi
if [[ "$EQBENCH_BUILD_POLICY" != "REUSE_OR_COMPILE" \
    && "$EQBENCH_BUILD_POLICY" != "PREBUILT_ONLY" \
    && "$EQBENCH_BUILD_POLICY" != "FRESH_ONLY" ]]; then
    echo "Error: EQBENCH_BUILD_POLICY must be REUSE_OR_COMPILE, PREBUILT_ONLY, or FRESH_ONLY" >&2
    exit 1
fi
if [[ ! "$EQBENCH_DEBUG" =~ ^[01]$ || ! "$SKIP_COMPLETED_RESULTS" =~ ^[01]$ \
    || ! "$ERROR_ONLY_RERUN" =~ ^[01]$ ]]; then
    echo "Error: EQBENCH_DEBUG, SKIP_COMPLETED_RESULTS, and ERROR_ONLY_RERUN must be 0 or 1" >&2
    exit 1
fi
if [[ ! "$EQBENCH_MAX_SAMPLES" =~ ^[0-9]+$ ]]; then
    echo "Error: EQBENCH_MAX_SAMPLES must be a non-negative integer" >&2
    exit 1
fi
if [[ ! "$PAIR_PROCESS_TIMEOUT_SECONDS" =~ ^[0-9]+([.][0-9]+)?$ ]] \
    || [[ ! "$PAIR_PROCESS_KILL_AFTER_SECONDS" =~ ^[0-9]+([.][0-9]+)?$ ]]; then
    echo "Error: pair process timeout values must be seconds, for example 300s" >&2
    exit 1
fi
if [[ ! "$PARALLEL_JOBS_REQUESTED" =~ ^[1-9][0-9]*$ \
    || ! "$EQBENCH_CPU_TOKENS" =~ ^[1-9][0-9]*$ \
    || ! "$EQBENCH_PAIR_CPU_TOKENS" =~ ^[1-9][0-9]*$ \
    || ! "$EQBENCH_PROGRESS_INTERVAL_SECONDS" =~ ^[1-9][0-9]*([.][0-9]+)?$ \
    || ! "$EQBENCH_RESOURCE_ADMISSION" =~ ^[01]$ ]]; then
    echo "Error: resource admission settings are invalid" >&2
    exit 1
fi
RESOURCE_ADMISSION_JOBS="$EQBENCH_CPU_TOKENS"
if (( EQBENCH_RESOURCE_ADMISSION == 1 )); then
    RESOURCE_ADMISSION_JOBS=$((EQBENCH_CPU_TOKENS / EQBENCH_PAIR_CPU_TOKENS))
    if (( RESOURCE_ADMISSION_JOBS < 1 )); then
        RESOURCE_ADMISSION_JOBS=1
    fi
    if (( PARALLEL_JOBS > RESOURCE_ADMISSION_JOBS )); then
        PARALLEL_JOBS="$RESOURCE_ADMISSION_JOBS"
    fi
fi

mkdir -p "$EQBENCH_TMPDIR"
chmod 1777 "$EQBENCH_TMPDIR" 2>/dev/null || true
if ! tmp_probe="$(mktemp "$EQBENCH_TMPDIR/eqbench-tmp.XXXXXX" 2>/dev/null)"; then
    echo "Error: cannot create temporary files in EQBENCH_TMPDIR=$EQBENCH_TMPDIR" >&2
    exit 1
fi
rm -f "$tmp_probe"
export TMPDIR="$EQBENCH_TMPDIR"
export TEMP="$EQBENCH_TMPDIR"
export TMP="$EQBENCH_TMPDIR"

cleanup_stale_codex_ghidra_tmp() {
    local root="$EQBENCH_TMPDIR/codex-ghidra"
    local candidate basename pid

    [[ -d "$root" && ! -L "$root" ]] || return 0
    while IFS= read -r -d '' candidate; do
        basename="${candidate##*/}"
        [[ "$basename" =~ ^pid-([0-9]+)$ ]] || continue
        pid="${BASH_REMATCH[1]}"
        if [[ ! -d "/proc/$pid" ]]; then
            rm -rf -- "$candidate" || \
                echo "Warning: could not remove stale PyGhidra temp directory: $candidate" >&2
        fi
    done < <(find "$root" -mindepth 1 -maxdepth 1 -type d -name 'pid-*' -print0)
    rmdir "$root" 2>/dev/null || true
}

cleanup_stale_codex_ghidra_tmp

EQBENCH_RUN_TMPDIR="$(mktemp -d "$EQBENCH_TMPDIR/eqbench-run.XXXXXX")"
PROCESS_AUTHORITY_CLEANUP_STOP_FILE="$EQBENCH_RUN_TMPDIR/process-authority-cleanup.stop"
cleanup_eqbench_run_tmpdir() {
    local run_tmpdir="${EQBENCH_RUN_TMPDIR:-}"
    [[ -n "$run_tmpdir" ]] || return 0
    [[ "${run_tmpdir%/*}" == "$EQBENCH_TMPDIR" ]] || return 0
    [[ "${run_tmpdir##*/}" == eqbench-run.* ]] || return 0
    rm -rf -- "$run_tmpdir"
    EQBENCH_RUN_TMPDIR=""
}
handle_eqbench_signal() {
    local exit_status="$1"
    trap - EXIT HUP INT TERM
    cleanup_eqbench_run_tmpdir
    exit "$exit_status"
}
trap cleanup_eqbench_run_tmpdir EXIT
trap 'handle_eqbench_signal 129' HUP
trap 'handle_eqbench_signal 130' INT
trap 'handle_eqbench_signal 143' TERM

IDS=(B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15 B16)
declare -A ARCH_BY_ID=(
    [B1]=arm64 [B2]=arm64 [B3]=arm64 [B4]=arm64
    [B5]=arm64 [B6]=arm64 [B7]=arm64 [B8]=arm64
    [B9]=mips64 [B10]=mips64 [B11]=mips64 [B12]=mips64
    [B13]=mips64 [B14]=mips64 [B15]=mips64 [B16]=mips64
)
declare -A COMPILER_BY_ID=(
    [B1]=clang [B2]=clang [B3]=clang [B4]=clang
    [B5]=gcc [B6]=gcc [B7]=gcc [B8]=gcc
    [B9]=clang [B10]=clang [B11]=clang [B12]=clang
    [B13]=gcc [B14]=gcc [B15]=gcc [B16]=gcc
)
declare -A OPT_BY_ID=(
    [B1]=O0 [B2]=O1 [B3]=O2 [B4]=O3
    [B5]=O0 [B6]=O1 [B7]=O2 [B8]=O3
    [B9]=O0 [B10]=O1 [B11]=O2 [B12]=O3
    [B13]=O0 [B14]=O1 [B15]=O2 [B16]=O3
)

RUN_PAIR_FAILURES=0
RUN_COMPILE_FAILURES=0
FUNCTION_CENSUS_FAILURES=0
MISSING_BINARY_COUNT=0
EXPECTED_BINARY_COUNT=0
COMPILED_BINARY_COUNT=0
TOTAL_PAIR_JOBS=0
TOTAL_SCHEDULED_PAIR_JOBS=0
TOTAL_SKIPPED_PAIR_JOBS=0
TOTAL_FUNCTIONS=0
TOTAL_SAMPLES=0
COMPLETED_SAMPLES=0
SKIPPED_SAMPLES=0

status_from_log() {
    local log_file="$1"
    case "$(validation_classify_log_result "$log_file")" in
        EQ)
            echo "EQUIVALENT"
            ;;
        NOT_EQ)
            echo "NOT EQUIVALENT"
            ;;
        ERROR)
            echo "ERROR"
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

pair_status_is_skippable_for_run_mode() {
    local log_file="$1"
    local pair_target_file="$2"
    local pair_status_file="${log_file%.log}.pair-status.json"
    local mode decision
    [[ -s "$log_file" && -s "$pair_status_file" ]] || return 1
    if [[ "$ERROR_ONLY_RERUN" == 1 ]]; then mode=ERROR_ONLY; else mode=NORMAL_RESUME; fi
    if decision="$("$PYTHON_BIN" -m \
        scripts.function_tracer_pcode.authority.decision.pair_status_authority \
        --validate-pair-status "$pair_status_file" \
        --pair-log "$log_file" \
        --public-key "$PAIR_STATUS_VERIFICATION_KEY_FILE" \
        --expected-pair-target "$pair_target_file" \
        "${PAIR_STATUS_RESUME_COMPAT_ARGS[@]}" \
        --resume-skip-mode "$mode" 2>/dev/null)"; then
        [[ "$decision" == SKIP ]] && return 0
    fi
    if [[ "$ERROR_ONLY_RERUN" == 1 ]] \
        && [[ "$("$PYTHON_BIN" -m \
            scripts.function_tracer_pcode.authority.decision.pair_status_authority \
            --legacy-pair-target-match "$pair_status_file" \
            --expected-pair-target "$pair_target_file" 2>/dev/null)" == MATCH ]] \
        && legacy_outcome="$("$PYTHON_BIN" -m \
            scripts.function_tracer_pcode.reporting.result_summary \
            --classify-log --allow-legacy-log "$log_file" 2>/dev/null)"; then
        case "$legacy_outcome" in
            EQ|NOT_EQ|UNKNOWN|TIMEOUT) return 0 ;;
        esac
    fi
    return 1
}

function_summary_all_pairs_reusable() {
    local function_dir="$1"
    local expected="$2"
    local summary="$function_dir/results_summary.txt"
    [[ -s "$summary" && "$expected" -gt 0 ]] || return 1
    awk -F: -v expected="$expected" '
        /^[[:space:]]*Total pairs[[:space:]]*:/ { gsub(/[[:space:]]/, "", $2); total=$2 }
        /^[[:space:]]*Error[[:space:]]*:/ { gsub(/[[:space:]]/, "", $2); error=$2 }
        /^[[:space:]]*Incomplete[[:space:]]*:/ { gsub(/[[:space:]]/, "", $2); incomplete=$2 }
        END { exit !(total == expected && error == 0 && incomplete == 0) }
    ' "$summary" || return 1
    [[ "$(find "$function_dir" -maxdepth 1 -type f -name '*.log' | wc -l)" -eq "$expected" \
        && "$(find "$function_dir" -maxdepth 1 -type f -name '*.pair-status.json' | wc -l)" -eq "$expected" ]]
}

summary_pair_files_reusable() {
    local log_file="$1" pair_status_file="$2"
    [[ -s "$log_file" && -s "$pair_status_file" ]] || return 1
    "$PYTHON_BIN" -c 'import json, sys; value=json.load(open(sys.argv[1], encoding="utf-8")); sys.exit(0 if isinstance(value, dict) else 1)' \
        "$pair_status_file" >/dev/null 2>&1
}

load_error_only_summary_pairs() {
    local function_dir="$1" summary="$1/results_summary.txt" error_count
    SUMMARY_ERROR_PAIRS_READY=0
    SUMMARY_ERROR_PAIRS=()
    [[ -s "$summary" ]] || return 0
    error_count="$(awk -F: '
        /^[[:space:]]*Error[[:space:]]*:/ { gsub(/[[:space:]]/, "", $2); print $2; exit }
    ' "$summary")"
    [[ "$error_count" =~ ^[0-9]+$ ]] || return 0
    (( error_count > 0 )) || return 0
    local -a error_pairs=()
    mapfile -t error_pairs < <("$PYTHON_BIN" -m \
        scripts.function_tracer_pcode.reporting.result_summary \
        --error-pairs --matrix EQ "$summary")
    if (( ${#error_pairs[@]} != error_count )); then
        echo "ERROR-only summary census mismatch: $summary (count=$error_count parsed=${#error_pairs[@]})" >&2
        return 1
    fi
    local pair
    for pair in "${error_pairs[@]}"; do SUMMARY_ERROR_PAIRS["$pair"]=1; done
    SUMMARY_ERROR_PAIRS_READY=1
}

validate_current_pair_status() {
    local pair_status_file="$1"
    local pair_target_file="$2"
    "$PYTHON_BIN" -m \
        scripts.function_tracer_pcode.authority.decision.pair_status_authority \
        --validate-pair-status "$pair_status_file" \
        --public-key "$PAIR_STATUS_VERIFICATION_KEY_FILE" \
        --expected-pair-target "$pair_target_file" --allow-operational-diagnostic
}

remove_pair_process_authority() {
    local checkpoint_root="$1"
    local execution_nonce="$2"
    "$PYTHON_BIN" -m \
        scripts.function_tracer_pcode.reporting.process_authority_cleanup \
        --tmp-root "$EQBENCH_TMPDIR" \
        --run-tmpdir "$EQBENCH_RUN_TMPDIR" \
        --checkpoint-root "$checkpoint_root" \
        --execution-nonce "$execution_nonce"
}

cleanup_pair_process_authority_with_run_health() {
    local checkpoint_root="$1"
    local execution_nonce="$2"
    local log_file="$3"
    local pair_status_file="$4"
    local sample_label="$5"
    local pair_label="$6"
    local cleanup_detail cleanup_ec

    if cleanup_detail="$(remove_pair_process_authority \
        "$checkpoint_root" "$execution_nonce" 2>&1)"; then
        return 0
    else
        cleanup_ec=$?
    fi
    echo "Run-health error: process-authority cleanup failed: $pair_status_file" >&2
    echo "$cleanup_detail" >&2
    {
        echo ""
        echo "Process-authority cleanup run-health failure:"
        echo "$cleanup_detail"
    } >> "$log_file"
    printf '%s\t%s\t%s\n' "$sample_label" "$pair_label" "$execution_nonce" \
        >> "$PROCESS_AUTHORITY_CLEANUP_FAILURES_FILE"
    printf '%s\t%s\t%s\n' "$sample_label" "$pair_label" "$execution_nonce" \
        > "$PROCESS_AUTHORITY_CLEANUP_STOP_FILE"
    return "$cleanup_ec"
}

pair_is_selected() {
    local pair_id="$1"
    [[ -z "$EQBENCH_PAIR_FILTER" ]] && return 0
    [[ ",$EQBENCH_PAIR_FILTER," == *",$pair_id,"* ]]
}

declare -A EQBENCH_RERUN_TARGETS=()
declare -A SUMMARY_ERROR_PAIRS=()
ERROR_RERUN_MANIFEST_SHA256=""
if [[ -n "$EQBENCH_RERUN_MANIFEST" ]]; then
    [[ -s "$EQBENCH_RERUN_MANIFEST" ]] || {
        echo "Error: EQBENCH_RERUN_MANIFEST is not a non-empty file" >&2
        exit 1
    }
    while IFS=$'\t' read -r lane sample function pair; do
        [[ "$lane" == "EQ" && -n "$sample" && -n "$function" && -n "$pair" ]] || continue
        EQBENCH_RERUN_TARGETS["$sample|$function|$pair"]=1
    done < "$EQBENCH_RERUN_MANIFEST"
    (( ${#EQBENCH_RERUN_TARGETS[@]} > 0 )) || {
        echo "Error: rerun manifest contains no EqBench targets" >&2
        exit 1
    }
    ERROR_RERUN_MANIFEST_SHA256="$(sha256sum "$EQBENCH_RERUN_MANIFEST" | awk '{print $1}')"
    [[ -n "$ERROR_RERUN_RUN_ID" ]] || {
        echo "Error: ERROR_RERUN_RUN_ID is required for a rerun manifest" >&2
        exit 1
    }
fi

rerun_target_is_selected() {
    local sample="$1" function="$2" pair="$3"
    [[ -z "$EQBENCH_RERUN_MANIFEST" ]] && return 0
    [[ -n "${EQBENCH_RERUN_TARGETS[$sample|$function|$pair]:-}" ]]
}

supervisor_projection_is_terminal() {
    "$PYTHON_BIN" -c \
        'import json,sys; p=json.load(open(sys.argv[1])); raise SystemExit(0 if p.get("status") in {"RESOLVED","TIMEOUT","ERROR"} else 1)' \
        "$1" 2>/dev/null
}

selected_pair_count() {
    local count=0 i j left_id right_id
    for ((i = 0; i < ${#IDS[@]} - 1; i++)); do
        left_id="${IDS[$i]}"
        for ((j = i + 1; j < ${#IDS[@]}; j++)); do
            right_id="${IDS[$j]}"
            pair_is_selected "${left_id}_${right_id}" || continue
            count=$((count + 1))
        done
    done
    printf '%s\n' "$count"
}

required_binary_ids() {
    local -A selected=()
    local i j left_id right_id
    for ((i = 0; i < ${#IDS[@]} - 1; i++)); do
        left_id="${IDS[$i]}"
        for ((j = i + 1; j < ${#IDS[@]}; j++)); do
            right_id="${IDS[$j]}"
            pair_is_selected "${left_id}_${right_id}" || continue
            selected["$left_id"]=1
            selected["$right_id"]=1
        done
    done
    for left_id in "${IDS[@]}"; do
        [[ -n "${selected[$left_id]:-}" ]] && printf '%s\n' "$left_id"
    done
}

EXPECTED_PAIRS_PER_FUNCTION="$(selected_pair_count)"

write_pair_progress_receipt() {
    local receipt_path="$1"
    local state="$2"
    local function_name="$3"
    local left_id="$4"
    local right_id="$5"
    local started_at="$6"
    local finished_at="$7"
    local elapsed_seconds="$8"
    local max_rss_kb="$9"
    local status="${10}"
    local error_kind="${11}"
    local child_returncode="${12}"
    local timed_command_pid="${13}"
    local temporary_path
    temporary_path="${receipt_path}.tmp.$$"
    "$PYTHON_BIN" - "$temporary_path" "$receipt_path" "$state" \
        "$function_name" "$left_id" "$right_id" "$started_at" \
        "$finished_at" "$elapsed_seconds" "$max_rss_kb" \
        "$status" "$error_kind" "$child_returncode" \
        "$timed_command_pid" \
        "$EQBENCH_CPU_TOKENS" "$EQBENCH_PAIR_CPU_TOKENS" \
        "$PARALLEL_JOBS_REQUESTED" "$PARALLEL_JOBS" <<'PY'
import json
import os
import sys

(
    temporary_path, receipt_path, state, function_name, left_id, right_id,
    started_at, finished_at, elapsed_seconds, max_rss_kb, status, error_kind,
    child_returncode, timed_command_pid, cpu_tokens, pair_cpu_tokens,
    requested_jobs, effective_jobs,
) = sys.argv[1:]

def number(value):
    if value in {"", "-", "None"}:
        return None
    try:
        return float(value) if "." in value else int(value)
    except ValueError:
        return None

payload = {
    "schema": "eqbench-pair-progress-receipt-v1",
    "state": state,
    "function_name": function_name,
    "left_binary_id": left_id,
    "right_binary_id": right_id,
    "started_at_epoch": number(started_at),
    "finished_at_epoch": number(finished_at),
    "elapsed_seconds": number(elapsed_seconds),
    "max_rss_kb": number(max_rss_kb),
    "status": None if status == "-" else status,
    "error_kind": None if error_kind == "-" else error_kind,
    "child_returncode": number(child_returncode),
    "cpu_tokens": int(cpu_tokens),
    "pair_cpu_tokens": int(pair_cpu_tokens),
    "parallel_jobs_requested": int(requested_jobs),
    "parallel_jobs_effective": int(effective_jobs),
    "writer_pid": os.getpid(),
    "timed_command_pid": number(timed_command_pid),
}
with open(temporary_path, "w", encoding="utf-8") as handle:
    json.dump(payload, handle, sort_keys=True, separators=(",", ":"))
    handle.write("\n")
    handle.flush()
    os.fsync(handle.fileno())
os.replace(temporary_path, receipt_path)
PY
}

run_pair() {
    local sample_label="$1"
    local function_name="$2"
    local left_id="$3"
    local right_id="$4"
    local left_bin="$5"
    local right_bin="$6"
    local output_dir="$7"
    local count="$8"
    local total="$9"
    local pair_target_file="${10}"
    local log_file="${output_dir}/${function_name}_${left_id}_${right_id}.log"
    local pair_tmpdir
    pair_tmpdir="$(mktemp -d "$EQBENCH_RUN_TMPDIR/pair.XXXXXX")"
    local runtime_metrics_dir progress_receipt runtime_metrics_file
    runtime_metrics_dir="${output_dir}/.runtime-metrics"
    mkdir -p "$runtime_metrics_dir"
    progress_receipt="${runtime_metrics_dir}/${function_name}_${left_id}_${right_id}.progress.json"
    runtime_metrics_file="${runtime_metrics_dir}/${function_name}_${left_id}_${right_id}.runtime.json"
    local started_at finished_at elapsed_seconds max_rss_kb
    started_at="$(date +%s.%N)"
    write_pair_progress_receipt "$progress_receipt" "RUNNING" \
        "$function_name" "$left_id" "$right_id" "$started_at" \
        "-" "-" "-" "-" "-" "-" "-"
    local result_entry_occurrence_nonce
    result_entry_occurrence_nonce="$("$PYTHON_BIN" -c \
        'import secrets; print(secrets.token_hex(24))')"
    local identity_line result_occurrence_id source_snapshot_fingerprint stream_id
    identity_line="$(PYTHONWARNINGS="ignore::RuntimeWarning" "$PYTHON_BIN" -m \
        scripts.function_tracer_pcode.authority.decision.production_cutover \
        --print-production-execution-identity \
        --binary1-path "$left_bin" --binary2-path "$right_bin" \
        --binary1-id "$left_id" --binary2-id "$right_id" \
        --function-name1 "$function_name" --function-name2 "$function_name" \
        --result-entry-occurrence-nonce "$result_entry_occurrence_nonce")"
    IFS=$'\t' read -r result_occurrence_id source_snapshot_fingerprint stream_id \
        <<< "$identity_line"
    local execution_nonce checkpoint_root authority_output
    execution_nonce="${result_occurrence_id#production-pilot-}"
    checkpoint_root="${EQBENCH_RUN_TMPDIR}/process-authority"
    authority_output="${checkpoint_root}/${execution_nonce}/supervisor-projection.json"
    mkdir -p "$checkpoint_root"

    local -a equiv_cmd=(
        env "TMPDIR=$pair_tmpdir" "TEMP=$pair_tmpdir" "TMP=$pair_tmpdir"
        "UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE=$result_entry_occurrence_nonce"
        "FT_EXPANDER_DEDUP_CASE_LIMIT=$FT_EXPANDER_DEDUP_CASE_LIMIT"
        "$PYTHON_BIN" -m scripts.function_tracer_pcode.cli.main
        --equiv "$left_bin" "$right_bin" \
        --binary-ids "$left_id" "$right_id" \
        -f "$function_name" --emit-result-json
        --equiv-timeout "$EQUIV_TIMEOUT"
        --timeout "$DECOMPILE_TIMEOUT"
        --pairwise-timeout "$PAIRWISE_TIMEOUT"
        --pairwise-timeout-hard "$PAIRWISE_TIMEOUT_HARD"
    )
    if [[ "$EQBENCH_DEBUG" == "1" ]]; then
        equiv_cmd+=( -d )
    fi

    local -a supervisor_cmd=(
        "$PYTHON_BIN" -m
        scripts.function_tracer_pcode.authority.process.supervisor_command
        --checkpoint-root "$checkpoint_root"
        --authority-output "$authority_output"
        --working-directory "$SCRIPT_DIR"
        --execution-nonce "$execution_nonce"
        --result-occurrence-id "$result_occurrence_id"
        --source-snapshot-fingerprint "$source_snapshot_fingerprint"
        --stream-id "$stream_id"
        --deadline-policy-digest "$PAIR_PROCESS_DEADLINE_POLICY_DIGEST"
        --supervisor-signing-key-id "$PROCESS_SUPERVISOR_KEY_ID"
        --supervisor-signing-key-file "$PROCESS_SUPERVISOR_KEY_FILE"
        --worker-signing-key-id "$PROCESS_WORKER_KEY_ID"
        --worker-signing-key-file "$PROCESS_WORKER_KEY_FILE"
        --timeout-seconds "$PAIR_PROCESS_TIMEOUT_SECONDS"
        --kill-grace-seconds "$PAIR_PROCESS_KILL_AFTER_SECONDS"
        --allow-child-exit-resolution
        -- "${equiv_cmd[@]}"
    )

    local ec command_pid resource_metrics_file
    resource_metrics_file="${pair_tmpdir}/resource-usage.txt"
    /usr/bin/time -f 'elapsed_seconds=%e\nmax_rss_kb=%M' \
        -o "$resource_metrics_file" "${supervisor_cmd[@]}" \
        > "$log_file" 2>&1 &
    command_pid=$!
    # Refresh the RUNNING receipt from a helper loop while waiting on the pair
    # process itself: polling the process with `sleep` held every scheduler
    # slot for up to EQBENCH_PROGRESS_INTERVAL_SECONDS after the pair had
    # already finished (Issue #14).
    (
        while kill -0 "$command_pid" 2>/dev/null; do
            sleep "$EQBENCH_PROGRESS_INTERVAL_SECONDS" &
            wait $! 2>/dev/null || break
            kill -0 "$command_pid" 2>/dev/null || break
            write_pair_progress_receipt "$progress_receipt" "RUNNING" \
                "$function_name" "$left_id" "$right_id" "$started_at" \
                "-" "-" "-" "-" "-" "-" "$command_pid"
        done
    ) &
    local progress_writer_pid=$!
    if wait "$command_pid"; then
        ec=0
    else
        ec=$?
    fi
    pkill -P "$progress_writer_pid" 2>/dev/null || true
    kill "$progress_writer_pid" 2>/dev/null || true
    wait "$progress_writer_pid" 2>/dev/null || true
    if ! supervisor_projection_is_terminal "$authority_output"; then
        echo "Supervisor recovery: resuming non-terminal projection before classification" \
            >> "$log_file"
        if "${supervisor_cmd[@]}" >> "$log_file" 2>&1; then
            ec=0
        else
            ec=$?
        fi
    fi
    finished_at="$(date +%s.%N)"
    elapsed_seconds="$(awk -F= '$1 == "elapsed_seconds" {print $2}' "$resource_metrics_file" 2>/dev/null || true)"
    max_rss_kb="$(awk -F= '$1 == "max_rss_kb" {print $2}' "$resource_metrics_file" 2>/dev/null || true)"
    [[ -n "$elapsed_seconds" ]] || elapsed_seconds="-"
    [[ -n "$max_rss_kb" ]] || max_rss_kb="-"
    rm -rf -- "$pair_tmpdir"

    if (( ec == 124 || ec == 137 )); then
        {
            echo ""
            echo "Pair process timeout: exceeded PAIR_PROCESS_TIMEOUT=$PAIR_PROCESS_TIMEOUT"
            echo "Timeout kill-after: PAIR_PROCESS_KILL_AFTER=$PAIR_PROCESS_KILL_AFTER"
            echo "Result: TIMEOUT (pair process exceeded wall-clock time limit)"
        } >> "$log_file"
    fi

    local pair_status_file classification_ec status error_kind child_returncode
    local pair_status_validation_ec pair_status_validation_detail
    local cleanup_ec run_pair_ec
    pair_status_file="${output_dir}/${function_name}_${left_id}_${right_id}.pair-status.json"
    if PYTHONWARNINGS="ignore::RuntimeWarning" "$PYTHON_BIN" -m \
        scripts.function_tracer_pcode.authority.decision.canonical_result \
        --classify-pair-log "$log_file" \
        --supervisor-projection "$authority_output" \
        --checkpoint-root "$checkpoint_root" \
        --execution-nonce "$execution_nonce" \
        --supervisor-signing-key-id "$PROCESS_SUPERVISOR_KEY_ID" \
        --supervisor-signing-key-file "$PROCESS_SUPERVISOR_KEY_FILE" \
        --worker-signing-key-id "$PROCESS_WORKER_KEY_ID" \
        --worker-signing-key-file "$PROCESS_WORKER_KEY_FILE" \
        --pair-status-signing-private-key-file "$PAIR_STATUS_SIGNING_PRIVATE_KEY_FILE" \
        --pair-status-verification-key-file "$PAIR_STATUS_VERIFICATION_KEY_FILE" \
        --pair-execution-target-file "$pair_target_file" --classification-diagnostic-log "$log_file" \
        > "$pair_status_file"; then
        classification_ec=0
    else
        classification_ec=$?
    fi
    if pair_status_validation_detail="$(validate_current_pair_status \
        "$pair_status_file" "$pair_target_file" 2>&1)"; then
        pair_status_validation_ec=0
        status="$pair_status_validation_detail"
        error_kind="$("$PYTHON_BIN" -c \
            'import json,sys; p=json.load(open(sys.argv[1])); print(p.get("error_kind") or "-")' \
            "$pair_status_file")"
        child_returncode="$("$PYTHON_BIN" -c \
            'import json,sys; p=json.load(open(sys.argv[1])); print(p.get("child_returncode", "-"))' \
            "$pair_status_file")"
    else
        pair_status_validation_ec=$?
        status="ERROR"
        error_kind="PAIR_STATUS_AUTHORITY_INVALID"
        child_returncode="-"
        echo "Error: generated pair status failed authority validation: $pair_status_file" >&2
        echo "$pair_status_validation_detail" >&2
        {
            echo ""
            echo "Pair-status authority validation failed:"
            echo "$pair_status_validation_detail"
        } >> "$log_file"
    fi
    if (( pair_status_validation_ec != 0 && classification_ec == 0 )); then
        classification_ec="$pair_status_validation_ec"
    fi
    if cleanup_pair_process_authority_with_run_health \
        "$checkpoint_root" "$execution_nonce" "$log_file" "$pair_status_file" \
        "$sample_label" "${function_name}_${left_id}_${right_id}"; then
        cleanup_ec=0
    else
        cleanup_ec=$?
    fi
    write_pair_progress_receipt "$progress_receipt" "COMPLETED" \
        "$function_name" "$left_id" "$right_id" "$started_at" \
        "$finished_at" "$elapsed_seconds" "$max_rss_kb" \
        "$status" "$error_kind" "$child_returncode" "$command_pid"
    cp "$progress_receipt" "$runtime_metrics_file"
    printf '[%s] [%s %s/%s] %s <-> %s : %s' \
        "$sample_label" "$function_name" "$count" "$total" "$left_id" "$right_id" "$status"
    printf ' (error_kind=%s child_exit=%s supervisor_exit=%s)' \
        "$error_kind" "$child_returncode" "$ec"
    printf '\n'
    run_pair_ec="$classification_ec"
    if (( cleanup_ec != 0 && run_pair_ec == 0 )); then
        run_pair_ec="$cleanup_ec"
    fi
    return "$run_pair_ec"
}

# Per-function summary, produced by the cross-function pair scheduler once
# every pair job of the function directory (the group key) has been reaped.
write_function_results_summary() {
    local output_function_dir="$1" function_name="$2"
    local -a function_logs
    local function_log_list
    shopt -s nullglob
    function_logs=("$output_function_dir"/*.log)
    shopt -u nullglob
    if (( ${#function_logs[@]} == 0 )); then
        return 0
    fi
    function_log_list="$output_function_dir/.summary-log-paths.list0"
    write_log_list0 "$function_log_list" "${function_logs[@]}"
    write_summary_file "$output_function_dir/results_summary.txt" \
        "$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.result_summary \
            --function-summary \
            --canonical-only \
            --function-name "$function_name" \
            --summary-level "$VALIDATION_SUMMARY_LEVEL" \
            --log-list0 "$function_log_list"
}

binary_name_for_id() {
    local source_base="$1"
    local id="$2"
    printf '%s-%s-%s-%s' "$source_base" "${ARCH_BY_ID[$id]}" "${COMPILER_BY_ID[$id]}" "${OPT_BY_ID[$id]}"
}

write_summary_file() {
    local output_file="$1"
    shift
    local tmp_file status
    tmp_file="$(mktemp "${output_file}.tmp.XXXXXX")" || return 1
    if "$@" > "$tmp_file"; then
        if mv -f "$tmp_file" "$output_file"; then
            if cat "$output_file"; then
                return 0
            else
                status=$?
                echo "Error: cannot display generated summary $output_file (exit=$status)" >&2
                return "$status"
            fi
        else
            status=$?
            rm -f "$tmp_file"
            echo "Error: cannot install generated summary $output_file (exit=$status)" >&2
            return "$status"
        fi
    else
        status=$?
    fi
    rm -f "$tmp_file"
    echo "Error: summary generation failed for $output_file (exit=$status)" >&2
    return "$status"
}

write_log_list0() {
    local output_file="$1"
    shift
    printf '%s\0' "$@" > "$output_file"
}

pair_scheduler_init "$PARALLEL_JOBS" write_function_results_summary RUN_PAIR_FAILURES

mapfile -t ALL_SAMPLE_SOURCES < <(
    find "$EQBENCH_ROOT" \
        -path '*/Eq/source/*' -prune -o \
        \( -path '*/Eq/newV.c' -o -path '*/Eq/new.c' \) \
        -type f -print | sort
)
PREFILTER_SOURCE_PATHS=()
for source_path in "${ALL_SAMPLE_SOURCES[@]}"; do
    PREFILTER_SOURCE_PATHS+=("${source_path#$EQBENCH_ROOT/}")
done
PREFILTER_SOURCE_CENSUS_FILE="$EQBENCH_RUN_TMPDIR/prefilter_source_paths.txt"
printf '%s\n' "${PREFILTER_SOURCE_PATHS[@]}" > "$PREFILTER_SOURCE_CENSUS_FILE"
PREFILTER_SOURCE_CENSUS_DIGEST="$(sha256sum "$PREFILTER_SOURCE_CENSUS_FILE" | awk '{print $1}')"

if [[ "$EQBENCH_RUN_SCOPE" == "FULL_EQBENCH" ]]; then
    if (( EQBENCH_MAX_SAMPLES != 0 )) || [[ -n "$EQBENCH_SAMPLE_FILTER" || -n "$EQBENCH_PAIR_FILTER" ]]; then
        echo "Error: FULL_EQBENCH requires EQBENCH_MAX_SAMPLES=0 and empty sample/pair filters" >&2
        exit 1
    fi
    mapfile -t EXPECTED_FULL_SOURCES < <(
        "$PYTHON_BIN" -c \
            'import json,sys; print("\n".join(json.load(open(sys.argv[1]))["source_paths"]))' \
            "$FULL_SCOPE_EXPECTATION"
    )
    if (( ${#PREFILTER_SOURCE_PATHS[@]} != ${#EXPECTED_FULL_SOURCES[@]} )); then
        echo "Error: FULL_EQBENCH source count differs from frozen expectation" >&2
        exit 1
    fi
    for ((source_index = 0; source_index < ${#EXPECTED_FULL_SOURCES[@]}; source_index++)); do
        if [[ "${PREFILTER_SOURCE_PATHS[$source_index]}" != "${EXPECTED_FULL_SOURCES[$source_index]}" ]]; then
            echo "Error: FULL_EQBENCH source census differs at index $source_index" >&2
            exit 1
        fi
    done
    declare -A EXPECTED_FUNCTIONS_BY_SOURCE=()
    while IFS=$'\t' read -r expected_source expected_functions; do
        EXPECTED_FUNCTIONS_BY_SOURCE["$expected_source"]="$expected_functions"
    done < <(
        "$PYTHON_BIN" -c \
            'import json,sys; p=json.load(open(sys.argv[1])); [print(k+"\t"+",".join(v)) for k,v in p["expected_functions"].items()]' \
            "$FULL_SCOPE_EXPECTATION"
    )
fi

SAMPLE_SOURCES=("${ALL_SAMPLE_SOURCES[@]}")

if [[ -n "$EQBENCH_SAMPLE_FILTER" ]]; then
    mapfile -t SAMPLE_SOURCES < <(printf '%s\n' "${SAMPLE_SOURCES[@]}" | grep -E -- "$EQBENCH_SAMPLE_FILTER" || true)
fi
if (( EQBENCH_MAX_SAMPLES > 0 && ${#SAMPLE_SOURCES[@]} > EQBENCH_MAX_SAMPLES )); then
    SAMPLE_SOURCES=("${SAMPLE_SOURCES[@]:0:EQBENCH_MAX_SAMPLES}")
fi

mkdir -p "$OUTPUT_BASE_DIR"
OUTPUT_BASE_DIR="$(realpath -m "$OUTPUT_BASE_DIR")"
EQBENCH_PRIVATE_AUTHORITY_ROOT="$(realpath -m "$EQBENCH_PRIVATE_AUTHORITY_ROOT")"
if [[ "$EQBENCH_PRIVATE_AUTHORITY_ROOT" == "$OUTPUT_BASE_DIR" \
    || "$EQBENCH_PRIVATE_AUTHORITY_ROOT" == "$OUTPUT_BASE_DIR/"* ]]; then
    echo "Error: private authority root must be outside OUTPUT_BASE_DIR" >&2
    exit 1
fi
AUTHORITY_KEYSET_ID="${EQBENCH_AUTHORITY_KEYSET_ID:-$(printf '%s' "$OUTPUT_BASE_DIR" | sha256sum | awk '{print $1}')}"
if [[ ! "$AUTHORITY_KEYSET_ID" =~ ^[A-Za-z0-9._-]+$ ]]; then
    echo "Error: EQBENCH_AUTHORITY_KEYSET_ID contains unsafe characters" >&2
    exit 1
fi
PROCESS_AUTHORITY_ROOT="$EQBENCH_PRIVATE_AUTHORITY_ROOT/$AUTHORITY_KEYSET_ID"
PROCESS_SUPERVISOR_KEY_ID="eqbench-phase8-supervisor-v1"
PROCESS_WORKER_KEY_ID="eqbench-phase8-worker-v1"
PROCESS_SUPERVISOR_KEY_FILE="$PROCESS_AUTHORITY_ROOT/supervisor.key"
PROCESS_WORKER_KEY_FILE="$PROCESS_AUTHORITY_ROOT/worker.key"
PAIR_STATUS_SIGNING_PRIVATE_KEY_FILE="$PROCESS_AUTHORITY_ROOT/pair-status-ed25519.key"
PAIR_STATUS_VERIFICATION_KEY_FILE="$OUTPUT_BASE_DIR/pair-status-verification-key.json"
existing_authority_evidence="$(find "$OUTPUT_BASE_DIR" \
    \( -name '*.pair-status.json' -o -name 'pair-status-verification-key.json' \
       -o -path '*/.process-authority/*' \) -print -quit)"
if [[ -n "$existing_authority_evidence" ]]; then
    if [[ ! -s "$PROCESS_SUPERVISOR_KEY_FILE" \
        || ! -s "$PROCESS_WORKER_KEY_FILE" \
        || ! -s "$PAIR_STATUS_SIGNING_PRIVATE_KEY_FILE" \
        || ! -s "$PAIR_STATUS_VERIFICATION_KEY_FILE" ]]; then
        echo "Error: existing authority evidence has no complete retained private keyset" >&2
        echo "Authority keyset: $AUTHORITY_KEYSET_ID" >&2
        exit 1
    fi
fi
mkdir -p "$PROCESS_AUTHORITY_ROOT"
chmod 700 "$PROCESS_AUTHORITY_ROOT"
if [[ -z "$existing_authority_evidence" ]]; then
    umask 077
    [[ -s "$PROCESS_SUPERVISOR_KEY_FILE" ]] || head -c 32 /dev/urandom > "$PROCESS_SUPERVISOR_KEY_FILE"
    [[ -s "$PROCESS_WORKER_KEY_FILE" ]] || head -c 32 /dev/urandom > "$PROCESS_WORKER_KEY_FILE"
    if [[ ! -s "$PAIR_STATUS_SIGNING_PRIVATE_KEY_FILE" ]]; then
        "$PYTHON_BIN" -m \
            scripts.function_tracer_pcode.authority.decision.pair_status_authority \
            --generate-private-key "$PAIR_STATUS_SIGNING_PRIVATE_KEY_FILE" \
            --write-public-key "$PAIR_STATUS_VERIFICATION_KEY_FILE" >/dev/null
    elif [[ ! -s "$PAIR_STATUS_VERIFICATION_KEY_FILE" ]]; then
        "$PYTHON_BIN" -m \
            scripts.function_tracer_pcode.authority.decision.pair_status_authority \
            --export-public-from-private "$PAIR_STATUS_SIGNING_PRIVATE_KEY_FILE" \
            --write-public-key "$PAIR_STATUS_VERIFICATION_KEY_FILE" >/dev/null
    fi
fi
"$PYTHON_BIN" -m \
    scripts.function_tracer_pcode.authority.decision.pair_status_authority \
    --validate-private-key "$PAIR_STATUS_SIGNING_PRIVATE_KEY_FILE" \
    --public-key "$PAIR_STATUS_VERIFICATION_KEY_FILE" >/dev/null
EXPECTED_PAIR_STATUS_PATHS_FILE="$OUTPUT_BASE_DIR/expected_pair_status_paths.txt"
: > "$EXPECTED_PAIR_STATUS_PATHS_FILE"
VERIFIED_SKIPPED_PAIR_STATUS_PATHS_FILE="$OUTPUT_BASE_DIR/verified_skipped_pair_status_paths.txt"
: > "$VERIFIED_SKIPPED_PAIR_STATUS_PATHS_FILE"
cp "$PREFILTER_SOURCE_CENSUS_FILE" "$OUTPUT_BASE_DIR/prefilter_source_paths.txt"
COMPILE_FAILURE_SAMPLES_FILE="$OUTPUT_BASE_DIR/compile_failure_samples.txt"
: > "$COMPILE_FAILURE_SAMPLES_FILE"
MISSING_BINARY_AXES_FILE="$OUTPUT_BASE_DIR/missing_binary_axes.txt"
: > "$MISSING_BINARY_AXES_FILE"
FUNCTION_CENSUS_FAILURES_FILE="$OUTPUT_BASE_DIR/function_census_failures.txt"
: > "$FUNCTION_CENSUS_FAILURES_FILE"
PROCESS_AUTHORITY_CLEANUP_FAILURES_FILE="$OUTPUT_BASE_DIR/process_authority_cleanup_failures.txt"
: > "$PROCESS_AUTHORITY_CLEANUP_FAILURES_FILE"
USED_BUILD_RECEIPTS_FILE="$OUTPUT_BASE_DIR/used_build_receipts.jsonl"
: > "$USED_BUILD_RECEIPTS_FILE"
ANALYSIS_SOURCE_DIGEST_START="$("$PYTHON_BIN" -m \
    scripts.function_tracer_pcode.reporting.execution_identity \
    --repo-root "$SCRIPT_DIR" --print-source-digest)"
PAIR_PROCESS_DEADLINE_POLICY_DIGEST="$(printf '%s' \
    "phase8:${PAIR_PROCESS_TIMEOUT_SECONDS}:${PAIR_PROCESS_KILL_AFTER_SECONDS}" \
    | sha256sum | awk '{print $1}')"
export PROCESS_SUPERVISOR_KEY_ID PROCESS_WORKER_KEY_ID
export PROCESS_SUPERVISOR_KEY_FILE PROCESS_WORKER_KEY_FILE
export PAIR_STATUS_SIGNING_PRIVATE_KEY_FILE PAIR_STATUS_VERIFICATION_KEY_FILE
export PAIR_PROCESS_DEADLINE_POLICY_DIGEST

RUN_MANIFEST_FILE="$OUTPUT_BASE_DIR/run_manifest.txt"
PREVIOUS_RUN_MANIFEST_FILE="$EQBENCH_RUN_TMPDIR/previous-run-manifest.txt"
if [[ -s "$RUN_MANIFEST_FILE" ]]; then
    cp "$RUN_MANIFEST_FILE" "$PREVIOUS_RUN_MANIFEST_FILE"
fi
cat > "$RUN_MANIFEST_FILE" <<EOF
run_kind=eqbench_all_eq_matrix_current
run_scope=$EQBENCH_RUN_SCOPE
build_policy=$EQBENCH_BUILD_POLICY
eqbench_root=$EQBENCH_ROOT
output_base_dir=$OUTPUT_BASE_DIR
python_bin=$PYTHON_BIN
parallel_jobs=$PARALLEL_JOBS
parallel_jobs_requested=$PARALLEL_JOBS_REQUESTED
resource_admission_enabled=$EQBENCH_RESOURCE_ADMISSION
resource_admission_jobs=$RESOURCE_ADMISSION_JOBS
cpu_tokens=$EQBENCH_CPU_TOKENS
pair_cpu_tokens=$EQBENCH_PAIR_CPU_TOKENS
progress_interval_seconds=$EQBENCH_PROGRESS_INTERVAL_SECONDS
validation_summary_level=$VALIDATION_SUMMARY_LEVEL
pair_process_timeout=$PAIR_PROCESS_TIMEOUT
pair_process_kill_after=$PAIR_PROCESS_KILL_AFTER
pair_process_timeout_seconds=$PAIR_PROCESS_TIMEOUT_SECONDS
pair_process_kill_after_seconds=$PAIR_PROCESS_KILL_AFTER_SECONDS
equiv_timeout=$EQUIV_TIMEOUT
decompile_timeout=$DECOMPILE_TIMEOUT
pairwise_timeout=$PAIRWISE_TIMEOUT
pairwise_timeout_hard=$PAIRWISE_TIMEOUT_HARD
expander_dedup_case_limit=$FT_EXPANDER_DEDUP_CASE_LIMIT
skip_completed_results=$SKIP_COMPLETED_RESULTS
error_only_rerun=$ERROR_ONLY_RERUN
debug=$EQBENCH_DEBUG
eqbench_tmpdir=$EQBENCH_TMPDIR
authority_keyset_id=$AUTHORITY_KEYSET_ID
compile_axes=arm64,mips64 x clang,gcc x O0,O1,O2,O3
prefilter_source_count=${#PREFILTER_SOURCE_PATHS[@]}
prefilter_source_census_digest=$PREFILTER_SOURCE_CENSUS_DIGEST
max_samples=$EQBENCH_MAX_SAMPLES
target_sources=${#SAMPLE_SOURCES[@]}
function_policy=all top-level source-defined functions except main
binary_policy=verified build receipt first; isolated fresh build fallback
sample_filter=$EQBENCH_SAMPLE_FILTER
pair_filter=$EQBENCH_PAIR_FILTER
analysis_source_digest_start=$ANALYSIS_SOURCE_DIGEST_START
dry_run=$DRY_RUN
EOF
ANALYSIS_CONFIG_DIGEST="$("$PYTHON_BIN" -m \
    scripts.function_tracer_pcode.reporting.execution_receipt \
    --run-manifest "$RUN_MANIFEST_FILE" --print-analysis-config-digest)"
printf 'analysis_config_digest=%s\n' "$ANALYSIS_CONFIG_DIGEST" >> "$RUN_MANIFEST_FILE"
PAIR_STATUS_RESUME_COMPAT_ARGS=()
SUMMARY_SHORTCUT_AUTHORIZED=0
if compatible_identity="$("$PYTHON_BIN" -m \
    scripts.function_tracer_pcode.reporting.execution_receipt \
    --run-manifest "$RUN_MANIFEST_FILE" \
    --resume-compatibility-root "$OUTPUT_BASE_DIR" \
    --current-source-digest "$ANALYSIS_SOURCE_DIGEST_START" \
    --print-compatible-analysis-config-digest 2>/dev/null)"; then
    IFS=$'\t' read -r compatible_config_digest compatible_source_digest <<< "$compatible_identity"
    PAIR_STATUS_RESUME_COMPAT_ARGS=(
        --compatible-analysis-config-digest "$compatible_config_digest"
        --compatible-analysis-source-digest "$compatible_source_digest"
    )
    if [[ "$compatible_source_digest" == "$ANALYSIS_SOURCE_DIGEST_START" ]]; then
        SUMMARY_SHORTCUT_AUTHORIZED=1
    fi
fi
if [[ -s "$PREVIOUS_RUN_MANIFEST_FILE" ]]; then
    if previous_manifest_identity="$("$PYTHON_BIN" -m \
        scripts.function_tracer_pcode.reporting.execution_receipt \
        --run-manifest "$RUN_MANIFEST_FILE" \
        --resume-compatibility-manifest "$PREVIOUS_RUN_MANIFEST_FILE" \
        --print-compatible-manifest-analysis-identity 2>/dev/null)"; then
        IFS=$'\t' read -r previous_config_digest previous_source_digest \
            <<< "$previous_manifest_identity"
        # A previous manifest is a compatibility hint for pair-level signed
        # validation when publication/receipt JSON is absent.  Do not replace
        # a stronger publication identity if one was already accepted.
        if (( ${#PAIR_STATUS_RESUME_COMPAT_ARGS[@]} == 0 )); then
            PAIR_STATUS_RESUME_COMPAT_ARGS=(
                --compatible-analysis-config-digest "$previous_config_digest"
                --compatible-analysis-source-digest "$previous_source_digest"
            )
        fi
        previous_source_end="$(awk -F= '$1 == "analysis_source_digest_end" { print $2 }' \
            "$PREVIOUS_RUN_MANIFEST_FILE")"
        if [[ "$previous_source_digest" == "$ANALYSIS_SOURCE_DIGEST_START" \
            && "$previous_source_end" == "$ANALYSIS_SOURCE_DIGEST_START" \
            && "$previous_config_digest" == "$ANALYSIS_CONFIG_DIGEST" ]]; then
            SUMMARY_SHORTCUT_AUTHORIZED=1
        fi
    fi
fi

echo "============================================================"
echo "EqBench all-sample matrix"
echo "============================================================"
echo "EqBench root: $EQBENCH_ROOT"
echo "Output base: $OUTPUT_BASE_DIR"
echo "Python: $PYTHON_BIN"
echo "Parallel jobs: $PARALLEL_JOBS"
echo "Parallel jobs requested: $PARALLEL_JOBS_REQUESTED"
echo "Resource admission: enabled=$EQBENCH_RESOURCE_ADMISSION cpu_tokens=$EQBENCH_CPU_TOKENS pair_cpu_tokens=$EQBENCH_PAIR_CPU_TOKENS admission_jobs=$RESOURCE_ADMISSION_JOBS"
echo "Progress receipts: interval=${EQBENCH_PROGRESS_INTERVAL_SECONDS}s (wall/RSS per pair)"
echo "Pair process timeout: $PAIR_PROCESS_TIMEOUT (kill after $PAIR_PROCESS_KILL_AFTER)"
echo "Equiv timeout: $EQUIV_TIMEOUT"
echo "Decompile timeout: $DECOMPILE_TIMEOUT"
echo "Pairwise timeout: $PAIRWISE_TIMEOUT (hard $PAIRWISE_TIMEOUT_HARD)"
echo "Skip completed results: $SKIP_COMPLETED_RESULTS"
echo "ERROR-only rerun: $ERROR_ONLY_RERUN"
echo "Temporary directory: $EQBENCH_TMPDIR"
echo "Run temporary directory: $EQBENCH_RUN_TMPDIR"
echo "Target sources: ${#SAMPLE_SOURCES[@]}"
echo "Run scope: $EQBENCH_RUN_SCOPE (prefilter census: ${#PREFILTER_SOURCE_PATHS[@]})"
echo "Build policy: $EQBENCH_BUILD_POLICY"
echo "Dry run: $DRY_RUN"
echo "============================================================"

if (( DRY_RUN != 0 )); then
    printf '%s\n' "${SAMPLE_SOURCES[@]}" > "$OUTPUT_BASE_DIR/dry_run_sources.txt"
    echo "Dry run wrote: $OUTPUT_BASE_DIR/dry_run_sources.txt"
    exit 0
fi
mapfile -t REQUIRED_BINARY_IDS < <(required_binary_ids)

for source_path in "${SAMPLE_SOURCES[@]}"; do
    if [[ -s "$PROCESS_AUTHORITY_CLEANUP_STOP_FILE" ]]; then
        echo "Stopping new pair scheduling after process-authority cleanup failure." >&2
        break
    fi
    eq_dir="$(dirname "$source_path")"
    source_name="$(basename "$source_path")"
    source_base="${source_name%.c}"
    rel_eq_dir="${eq_dir#$EQBENCH_ROOT/}"
    sample_label="$rel_eq_dir/$source_base"
    source_dir="$eq_dir/source"
    output_sample_dir="$OUTPUT_BASE_DIR/$rel_eq_dir/$source_base"
    compile_log="$output_sample_dir/compile_all.log"
    functions_file="$output_sample_dir/functions.txt"

    TOTAL_SAMPLES=$((TOTAL_SAMPLES + 1))
    mkdir -p "$source_dir" "$output_sample_dir"

    if ! cmp -s "$source_path" "$source_dir/$source_name"; then
        cp "$source_path" "$source_dir/$source_name"
    fi
    cp "$COMPILE_TEMPLATE" "$source_dir/compile_all.sh"
    chmod +x "$source_dir/compile_all.sh"

    echo ""
    echo "============================================================"
    echo "[$TOTAL_SAMPLES/${#SAMPLE_SOURCES[@]}] Sample: $sample_label"
    echo "Source dir: $source_dir"
    echo "Output dir: $output_sample_dir"
    echo "============================================================"

    mapfile -t FUNCTIONS < <("$PYTHON_BIN" "$FUNCTION_LISTER" "$source_dir/$source_name" | sort -u)
    printf '%s\n' "${FUNCTIONS[@]}" > "$functions_file"
    if [[ "$EQBENCH_RUN_SCOPE" == "FULL_EQBENCH" ]]; then
        actual_functions="$(IFS=,; echo "${FUNCTIONS[*]}")"
        source_census_path="${source_path#$EQBENCH_ROOT/}"
        expected_functions="${EXPECTED_FUNCTIONS_BY_SOURCE[$source_census_path]:-}"
        if [[ "$actual_functions" != "$expected_functions" ]]; then
            printf '%s\n' "$sample_label" >> "$FUNCTION_CENSUS_FAILURES_FILE"
            FUNCTION_CENSUS_FAILURES=$((FUNCTION_CENSUS_FAILURES + 1))
            RUN_PAIR_FAILURES=$((RUN_PAIR_FAILURES + 1))
            echo "Function census authority failure: sample=$sample_label" >&2
        fi
    fi

    if (( ${#FUNCTIONS[@]} == 0 )); then
        echo "No non-main functions found; skipping sample."
        SKIPPED_SAMPLES=$((SKIPPED_SAMPLES + 1))
        continue
    fi

    echo "Functions: ${FUNCTIONS[*]}"

    sample_expected_pairs=0
    for function_name in "${FUNCTIONS[@]}"; do
        TOTAL_FUNCTIONS=$((TOTAL_FUNCTIONS + 1))
        output_function_dir="$output_sample_dir/$function_name"
        mkdir -p "$output_function_dir"
        for ((i = 0; i < ${#IDS[@]} - 1; i++)); do
            left_id="${IDS[$i]}"
            for ((j = i + 1; j < ${#IDS[@]}; j++)); do
                right_id="${IDS[$j]}"
                pair_is_selected "${left_id}_${right_id}" || continue
                rerun_target_is_selected "$sample_label" "$function_name" "${left_id}_${right_id}" || continue
                pair_status_file="${output_function_dir}/${function_name}_${left_id}_${right_id}.pair-status.json"
                printf '%s\n' "${pair_status_file#$OUTPUT_BASE_DIR/}" >> "$EXPECTED_PAIR_STATUS_PATHS_FILE"
                TOTAL_PAIR_JOBS=$((TOTAL_PAIR_JOBS + 1))
                sample_expected_pairs=$((sample_expected_pairs + 1))
            done
        done
    done

    validation_binary_ids=("${REQUIRED_BINARY_IDS[@]}")
    if [[ "$EQBENCH_RUN_SCOPE" == "FULL_EQBENCH" ]]; then
        validation_binary_ids=("${IDS[@]}")
    fi
    build_receipt_file="$source_dir/.${source_base}.eqbench-build-receipt.json"
    build_receipt_args=()
    for binary_id in "${validation_binary_ids[@]}"; do
        build_receipt_args+=(--binary-id "$binary_id")
    done
    require_fresh_args=()
    if [[ "$EQBENCH_RUN_SCOPE" == "FULL_EQBENCH" ]]; then
        require_fresh_args+=(--require-fresh)
    fi
    build_ready=0
    compile_exit_status=0
    receipt_json=""

    if [[ "$EQBENCH_BUILD_POLICY" != "FRESH_ONLY" && -s "$build_receipt_file" ]]; then
        if receipt_json="$("$PYTHON_BIN" -m \
            scripts.function_tracer_pcode.reporting.eqbench_build_receipt \
            --repo-root "$SCRIPT_DIR" --receipt "$build_receipt_file" --validate \
            "${require_fresh_args[@]}" "${build_receipt_args[@]}" 2>/dev/null)"; then
            build_ready=1
            printf 'build_resolution=VERIFIED_RECEIPT_REUSE\ncompile_invoked=0\n' > "$compile_log"
        fi
    fi

    if (( build_ready == 0 )) && [[ "$EQBENCH_RUN_SCOPE" == "REPRESENTATIVE" \
        && "$EQBENCH_BUILD_POLICY" != "FRESH_ONLY" ]]; then
        adopted_inputs_complete=1
        for binary_id in "${validation_binary_ids[@]}"; do
            binary_name="$(binary_name_for_id "$source_base" "$binary_id")"
            [[ -f "$source_dir/$binary_name" ]] || adopted_inputs_complete=0
        done
        if (( adopted_inputs_complete != 0 )); then
            if receipt_json="$("$PYTHON_BIN" -m \
                scripts.function_tracer_pcode.reporting.eqbench_build_receipt \
                --repo-root "$SCRIPT_DIR" --receipt "$build_receipt_file" --materialize \
                --provenance-kind ADOPTED_PREBUILT --sample-identity "$sample_label" \
                --source "$source_path" --compile-script "$COMPILE_TEMPLATE" \
                --binary-root "$source_dir" --target-binary-root "$source_dir" \
                "${build_receipt_args[@]}")"; then
                build_ready=1
                printf 'build_resolution=ADOPTED_PREBUILT\ncompile_invoked=0\n' > "$compile_log"
            fi
        fi
    fi

    if (( build_ready == 0 )) && [[ "$EQBENCH_BUILD_POLICY" != "PREBUILT_ONLY" ]]; then
        fresh_build_dir="$EQBENCH_RUN_TMPDIR/fresh-builds/$TOTAL_SAMPLES"
        mkdir -p "$fresh_build_dir"
        cp "$source_path" "$fresh_build_dir/$source_name"
        cp "$COMPILE_TEMPLATE" "$fresh_build_dir/compile_all.sh"
        chmod +x "$fresh_build_dir/compile_all.sh"
        (cd "$fresh_build_dir" && ./compile_all.sh "$source_name") > "$compile_log" 2>&1 || compile_exit_status=$?
        if (( compile_exit_status == 0 )); then
            fresh_receipt="$fresh_build_dir/build-receipt.json"
            fresh_receipt_args=()
            for binary_id in "${IDS[@]}"; do
                fresh_receipt_args+=(--binary-id "$binary_id")
            done
            if "$PYTHON_BIN" -m \
                scripts.function_tracer_pcode.reporting.eqbench_build_receipt \
                --repo-root "$SCRIPT_DIR" --receipt "$fresh_receipt" --materialize \
                --provenance-kind FRESH_COMPILE --sample-identity "$sample_label" \
                --source "$source_path" --compile-script "$COMPILE_TEMPLATE" \
                --binary-root "$fresh_build_dir" --target-binary-root "$source_dir" \
                "${fresh_receipt_args[@]}" >/dev/null; then
                install_failed=0
                for binary_id in "${IDS[@]}"; do
                    binary_name="$(binary_name_for_id "$source_base" "$binary_id")"
                    install_path="$source_dir/.${binary_name}.eqbench-new"
                    if ! cp "$fresh_build_dir/$binary_name" "$install_path" \
                        || ! mv -f -- "$install_path" "$source_dir/$binary_name"; then
                        install_failed=1
                        break
                    fi
                done
                if (( install_failed == 0 )) \
                    && cp "$fresh_receipt" "${build_receipt_file}.new" \
                    && mv -f -- "${build_receipt_file}.new" "$build_receipt_file"; then
                    if receipt_json="$("$PYTHON_BIN" -m \
                        scripts.function_tracer_pcode.reporting.eqbench_build_receipt \
                        --repo-root "$SCRIPT_DIR" --receipt "$build_receipt_file" --validate \
                        "${require_fresh_args[@]}" "${build_receipt_args[@]}")"; then
                        build_ready=1
                    fi
                else
                    compile_exit_status=1
                fi
            else
                compile_exit_status=1
            fi
        fi
    elif (( build_ready == 0 )); then
        compile_exit_status=125
        printf 'build_resolution=PREBUILT_AUTHORITY_UNAVAILABLE\ncompile_invoked=0\n' > "$compile_log"
    fi

    sample_missing_binary_count=0
    EXPECTED_BINARY_COUNT=$((EXPECTED_BINARY_COUNT + ${#validation_binary_ids[@]}))
    for binary_id in "${validation_binary_ids[@]}"; do
        binary_name="$(binary_name_for_id "$source_base" "$binary_id")"
        binary_path="$source_dir/$binary_name"
        if [[ ! -f "$binary_path" ]]; then
            printf '%s/%s\n' "$sample_label" "$binary_id" >> "$MISSING_BINARY_AXES_FILE"
            sample_missing_binary_count=$((sample_missing_binary_count + 1))
        fi
    done
    MISSING_BINARY_COUNT=$((MISSING_BINARY_COUNT + sample_missing_binary_count))
    if (( build_ready == 0 )); then
        printf '%s\n' "$sample_label" >> "$COMPILE_FAILURE_SAMPLES_FILE"
        RUN_COMPILE_FAILURES=$((RUN_COMPILE_FAILURES + 1))
        failure_jobs=$sample_expected_pairs
        (( failure_jobs > 0 )) || failure_jobs=1
        RUN_PAIR_FAILURES=$((RUN_PAIR_FAILURES + failure_jobs))
        echo "Build authority failure: sample=$sample_label exit=$compile_exit_status missing=$sample_missing_binary_count/${#validation_binary_ids[@]}; existing binaries were not moved. Log: $compile_log" >&2
        continue
    fi
    COMPILED_BINARY_COUNT=$((COMPILED_BINARY_COUNT + ${#validation_binary_ids[@]}))
    printf '%s\n' "$receipt_json" >> "$USED_BUILD_RECEIPTS_FILE"
    COMPLETED_SAMPLES=$((COMPLETED_SAMPLES + 1))

    for function_name in "${FUNCTIONS[@]}"; do
        if [[ -s "$PROCESS_AUTHORITY_CLEANUP_STOP_FILE" ]]; then
            echo "Stopping new pair scheduling after process-authority cleanup failure." >&2
            break
        fi
        output_function_dir="$output_sample_dir/$function_name"
        pair_count=0
        total_pairs=0

        for ((i = 0; i < ${#IDS[@]} - 1; i++)); do
            left_id="${IDS[$i]}"
            for ((j = i + 1; j < ${#IDS[@]}; j++)); do
                right_id="${IDS[$j]}"
                pair_is_selected "${left_id}_${right_id}" || continue
                rerun_target_is_selected "$sample_label" "$function_name" "${left_id}_${right_id}" || continue
                total_pairs=$((total_pairs + 1))
            done
        done

        if (( total_pairs == 0 )); then
            echo "[$sample_label] [$function_name] No complete binary pairs found; skipping."
            continue
        fi

        if [[ ("$SUMMARY_SHORTCUT_AUTHORIZED" == 1 || "$ERROR_ONLY_RERUN" == 1) ]] \
            && [[ "$SKIP_COMPLETED_RESULTS" != "0" || "$ERROR_ONLY_RERUN" != "0" ]] \
            && function_summary_all_pairs_reusable "$output_function_dir" "$total_pairs"; then
            while IFS= read -r pair_status_file; do
                printf '%s\n' "${pair_status_file#$OUTPUT_BASE_DIR/}" >> "$VERIFIED_SKIPPED_PAIR_STATUS_PATHS_FILE"
            done < <(find "$output_function_dir" -maxdepth 1 -type f -name '*.pair-status.json' -print | sort)
            TOTAL_SKIPPED_PAIR_JOBS=$((TOTAL_SKIPPED_PAIR_JOBS + total_pairs))
            echo "[$sample_label] [$function_name] Summary shortcut: skipped $total_pairs/$total_pairs pairs"
            continue
        fi

        skipped_completed_pairs=0
        SUMMARY_ERROR_PAIRS_READY=0
        SUMMARY_ERROR_PAIRS=()
        if [[ "$ERROR_ONLY_RERUN" == 1 ]] && ! load_error_only_summary_pairs "$output_function_dir"; then
            RUN_PAIR_FAILURES=$((RUN_PAIR_FAILURES + 1))
            continue
        fi
        if (( SUMMARY_ERROR_PAIRS_READY )); then
            error_pair_list="$(printf '%s\n' "${!SUMMARY_ERROR_PAIRS[@]}" | sort | paste -sd, -)"
            echo "[$sample_label] [$function_name] ERROR-only summary: selected ${#SUMMARY_ERROR_PAIRS[@]}/$total_pairs ERROR pair(s): $error_pair_list"
        fi
        pair_scheduler_open_group "$output_function_dir" "$function_name"
        for ((i = 0; i < ${#IDS[@]} - 1; i++)); do
            left_id="${IDS[$i]}"
            left_name="$(binary_name_for_id "$source_base" "$left_id")"
            left_bin="$source_dir/$left_name"

            for ((j = i + 1; j < ${#IDS[@]}; j++)); do
                right_id="${IDS[$j]}"
                right_name="$(binary_name_for_id "$source_base" "$right_id")"
                right_bin="$source_dir/$right_name"
                pair_is_selected "${left_id}_${right_id}" || continue
                rerun_target_is_selected "$sample_label" "$function_name" "${left_id}_${right_id}" || continue

                pair_count=$((pair_count + 1))
                log_file="${output_function_dir}/${function_name}_${left_id}_${right_id}.log"
                pair_status_file="${log_file%.log}.pair-status.json"
                summary_force_schedule=0
                if (( SUMMARY_ERROR_PAIRS_READY )) \
                    && [[ -n "${SUMMARY_ERROR_PAIRS[${left_id}_${right_id}]:-}" ]]; then
                    # The historical function summary is the ERROR-only
                    # scheduling authority.  Do not let a stale/valid
                    # terminal status or a different analysis digest hide
                    # a pair explicitly classified as ERROR there.
                    summary_force_schedule=1
                elif (( SUMMARY_ERROR_PAIRS_READY )); then
                    if summary_pair_files_reusable "$log_file" "$pair_status_file"; then
                        skipped_completed_pairs=$((skipped_completed_pairs + 1))
                        TOTAL_SKIPPED_PAIR_JOBS=$((TOTAL_SKIPPED_PAIR_JOBS + 1))
                        printf '%s\n' "${pair_status_file#$OUTPUT_BASE_DIR/}" >> "$VERIFIED_SKIPPED_PAIR_STATUS_PATHS_FILE"
                        continue
                    fi
                    # A summary non-ERROR pair with a missing or malformed
                    # artifact is incomplete and must be repaired.
                    summary_force_schedule=1
                fi
                pair_target_file="$EQBENCH_RUN_TMPDIR/${TOTAL_PAIR_JOBS}-${function_name}-${left_id}-${right_id}.pair-target.json"
                "$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.execution_identity \
                    --repo-root "$SCRIPT_DIR" --build-pair-target \
                    --sample-identity "$sample_label" \
                    --output-sample-relative-path "$rel_eq_dir/$source_base" \
                    --function-name "$function_name" \
                    --left-binary-id "$left_id" --right-binary-id "$right_id" \
                    --source-path "$source_path" \
                    --left-binary-path "$left_bin" --right-binary-path "$right_bin" \
                    --analysis-source-digest "$ANALYSIS_SOURCE_DIGEST_START" \
                    --analysis-config-digest "$ANALYSIS_CONFIG_DIGEST" \
                    > "$pair_target_file"
                if (( ! summary_force_schedule )) \
                    && [[ "$SKIP_COMPLETED_RESULTS" != "0" || "$ERROR_ONLY_RERUN" != "0" ]] \
                    && pair_status_is_skippable_for_run_mode "$log_file" "$pair_target_file"; then
                    skipped_completed_pairs=$((skipped_completed_pairs + 1))
                    TOTAL_SKIPPED_PAIR_JOBS=$((TOTAL_SKIPPED_PAIR_JOBS + 1))
                    printf '%s\n' "${pair_status_file#$OUTPUT_BASE_DIR/}" >> "$VERIFIED_SKIPPED_PAIR_STATUS_PATHS_FILE"
                    continue
                fi

                pair_scheduler_wait_for_slot
                if [[ -s "$PROCESS_AUTHORITY_CLEANUP_STOP_FILE" ]]; then
                    echo "Stopping new pair scheduling after process-authority cleanup failure." >&2
                    break 2
                fi
                TOTAL_SCHEDULED_PAIR_JOBS=$((TOTAL_SCHEDULED_PAIR_JOBS + 1))
                run_pair "$sample_label" "$function_name" "$left_id" "$right_id" \
                    "$left_bin" "$right_bin" "$output_function_dir" "$pair_count" "$total_pairs" \
                    "$pair_target_file" &
                pair_scheduler_start_job "$output_function_dir" "$!"
            done
        done

        if (( skipped_completed_pairs > 0 )); then
            echo "[$sample_label] [$function_name] Skipped completed pairs: $skipped_completed_pairs/$total_pairs"
        fi

        # The function summary is written by the scheduler's completion hook
        # once the last pair of this function has been reaped; pairs of the
        # following functions are scheduled meanwhile.
        pair_scheduler_close_group "$output_function_dir"
    done
done

pair_scheduler_finalize

PROCESS_AUTHORITY_CLEANUP_FAILURES="$(
    awk 'NF { count += 1 } END { print count + 0 }' \
        "$PROCESS_AUTHORITY_CLEANUP_FAILURES_FILE"
)"

mapfile -t ALL_LOG_FILES < <(
    find "$OUTPUT_BASE_DIR" -type f -name "*.log" \
        ! -name "compile_all.log" \
        ! -name "run_stdout.log" \
        -print | sort
)
if (( ${#ALL_LOG_FILES[@]} > 0 )); then
    overall_log_list="$OUTPUT_BASE_DIR/.overall-summary-log-paths.list0"
    write_log_list0 "$overall_log_list" "${ALL_LOG_FILES[@]}"
    write_summary_file "$OUTPUT_BASE_DIR/overall_summary.txt" \
        "$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.result_summary \
            --overall-summary \
            --canonical-only \
            --summary-level "$VALIDATION_SUMMARY_LEVEL" \
            --health-summary-json "$OUTPUT_BASE_DIR/run_health_summary.json" \
            --health-summary-text "$OUTPUT_BASE_DIR/run_health_summary.txt" \
            --log-list0 "$overall_log_list"
fi

# Issue #104: benchmark validation gate over the canonical pair outcomes
# (after the health summary it extends, before the receipt that hashes it).
validation_run_benchmark_gate "$OUTPUT_BASE_DIR" "$EQBENCH_ROOT" "$SCRIPT_DIR"

cat >> "$OUTPUT_BASE_DIR/run_manifest.txt" <<EOF
completed_samples=$COMPLETED_SAMPLES
skipped_samples=$SKIPPED_SAMPLES
total_functions=$TOTAL_FUNCTIONS
total_pair_jobs=$TOTAL_PAIR_JOBS
total_scheduled_pair_jobs=$TOTAL_SCHEDULED_PAIR_JOBS
total_skipped_pair_jobs=$TOTAL_SKIPPED_PAIR_JOBS
expected_pairs_per_function=120
expected_binary_count=$EXPECTED_BINARY_COUNT
compiled_binary_count=$COMPILED_BINARY_COUNT
compile_failure_count=$RUN_COMPILE_FAILURES
missing_binary_count=$MISSING_BINARY_COUNT
function_census_failure_count=$FUNCTION_CENSUS_FAILURES
process_authority_cleanup_failure_count=$PROCESS_AUTHORITY_CLEANUP_FAILURES
run_pair_failures=$RUN_PAIR_FAILURES
benchmark_gate_status=$VALIDATION_BENCHMARK_GATE_STATUS
benchmark_gate_failures=$VALIDATION_BENCHMARK_GATE_FAILURES
analysis_source_digest_end=$("$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.execution_identity --repo-root "$SCRIPT_DIR" --print-source-digest)
EOF

FINAL_RUN_EXIT_STATUS=0
if (( RUN_PAIR_FAILURES > 0 || RUN_COMPILE_FAILURES > 0 || MISSING_BINARY_COUNT > 0 || FUNCTION_CENSUS_FAILURES > 0 || VALIDATION_BENCHMARK_GATE_FAILURES > 0 )); then
    FINAL_RUN_EXIT_STATUS=1
fi

"$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.execution_receipt \
    --repo-root "$SCRIPT_DIR" \
    --private-key "$PAIR_STATUS_SIGNING_PRIVATE_KEY_FILE" \
    --public-key "$PAIR_STATUS_VERIFICATION_KEY_FILE" \
    --output "$OUTPUT_BASE_DIR/validation-execution-receipt.json" \
    --matrix-root "$OUTPUT_BASE_DIR" \
    --source-digest-start "$ANALYSIS_SOURCE_DIGEST_START" \
    --analysis-config-digest "$ANALYSIS_CONFIG_DIGEST" \
    --exit-status "$FINAL_RUN_EXIT_STATUS" \
    -- "env" "PARALLEL_JOBS=$PARALLEL_JOBS" \
    "PARALLEL_JOBS_REQUESTED=$PARALLEL_JOBS_REQUESTED" \
    "EQBENCH_RESOURCE_ADMISSION=$EQBENCH_RESOURCE_ADMISSION" \
    "EQBENCH_CPU_TOKENS=$EQBENCH_CPU_TOKENS" \
    "EQBENCH_PAIR_CPU_TOKENS=$EQBENCH_PAIR_CPU_TOKENS" \
    "EQBENCH_PROGRESS_INTERVAL_SECONDS=$EQBENCH_PROGRESS_INTERVAL_SECONDS" \
    "EQBENCH_RUN_SCOPE=$EQBENCH_RUN_SCOPE" \
    "EQBENCH_BUILD_POLICY=$EQBENCH_BUILD_POLICY" \
    "EQBENCH_MAX_SAMPLES=$EQBENCH_MAX_SAMPLES" \
    "EQBENCH_SAMPLE_FILTER=$EQBENCH_SAMPLE_FILTER" \
    "EQBENCH_PAIR_FILTER=$EQBENCH_PAIR_FILTER" \
    "ERROR_RERUN_MANIFEST_SHA256=$ERROR_RERUN_MANIFEST_SHA256" \
    "ERROR_RERUN_RUN_ID=$ERROR_RERUN_RUN_ID" \
    "EQBENCH_DEBUG=$EQBENCH_DEBUG" \
    "DRY_RUN=$DRY_RUN" \
    "SKIP_COMPLETED_RESULTS=$SKIP_COMPLETED_RESULTS" \
    "ERROR_ONLY_RERUN=$ERROR_ONLY_RERUN" \
    "VALIDATION_SUMMARY_LEVEL=$VALIDATION_SUMMARY_LEVEL" \
    "EQBENCH_BENCHMARK_GATE=${EQBENCH_BENCHMARK_GATE:-1}" \
    "EQBENCH_BENCHMARK_GATE_FAIL_ON_SUSPICIOUS=${EQBENCH_BENCHMARK_GATE_FAIL_ON_SUSPICIOUS:-0}" \
    "EQBENCH_GROUND_TRUTH_FILE=${EQBENCH_GROUND_TRUTH_FILE:-}" \
    "EQUIV_TIMEOUT=$EQUIV_TIMEOUT" \
    "DECOMPILE_TIMEOUT=$DECOMPILE_TIMEOUT" \
    "PAIRWISE_TIMEOUT=$PAIRWISE_TIMEOUT" \
    "PAIRWISE_TIMEOUT_HARD=$PAIRWISE_TIMEOUT_HARD" \
    "FT_EXPANDER_DEDUP_CASE_LIMIT=$FT_EXPANDER_DEDUP_CASE_LIMIT" \
    "PAIR_PROCESS_TIMEOUT=$PAIR_PROCESS_TIMEOUT" \
    "PAIR_PROCESS_KILL_AFTER=$PAIR_PROCESS_KILL_AFTER" \
    "./eqbench_run_all_32jobs.sh"

echo ""
echo "EqBench all-sample matrix finished."
echo "Output directory: $OUTPUT_BASE_DIR"
echo "Overall summary: $OUTPUT_BASE_DIR/overall_summary.txt"
echo "Run manifest: $OUTPUT_BASE_DIR/run_manifest.txt"
echo "Peak concurrent pair jobs: $PAIR_SCHEDULER_PEAK_ACTIVE_JOBS (PARALLEL_JOBS=$PARALLEL_JOBS)"

if (( FINAL_RUN_EXIT_STATUS > 0 )); then
    echo "Error: $RUN_PAIR_FAILURES pair job(s) failed canonical classification or run-health checks." >&2
    if (( VALIDATION_BENCHMARK_GATE_FAILURES > 0 )); then
        echo "Error: benchmark validation gate $VALIDATION_BENCHMARK_GATE_STATUS; see $OUTPUT_BASE_DIR/benchmark_validation_gate.txt" >&2
    fi
    if (( PROCESS_AUTHORITY_CLEANUP_FAILURES > 0 )); then
        echo "Error: $PROCESS_AUTHORITY_CLEANUP_FAILURES process-authority cleanup run-health failure(s)." >&2
    fi
    exit "$FINAL_RUN_EXIT_STATUS"
fi
