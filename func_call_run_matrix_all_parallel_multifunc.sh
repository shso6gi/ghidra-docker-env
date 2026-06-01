#!/usr/bin/env bash
# ------------------------------------------------------------
#  バイナリ間の等価性判定スクリプト（並列版・複数関数対応）
#  bash 4.3 以上が必要（wait -n を使用）
# ------------------------------------------------------------

# ---------------------- 設定 ----------------------
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"
source "$SCRIPT_DIR/scripts/validation_matrix_common.sh" || exit 1

CONFIGURED_TARGET_FUNCS=(
    "fc_read_after_void"
)

# Fallback only. Full/manifest runs prefer raw/function_call_20_manifest.json.
FULL20_TARGET_FUNCS=(
    "fc_wrap_add_then_bias"
    "fc_wrap_scaled_delta"
    "fc_equiv_direct"
    "fc_equiv_call_chain"
    "fc_equiv_two_stage"
    "fc_nonequiv_near_miss"
    "fc_select_simple"
    "fc_branch_chain"
    "fc_guarded_call"
    "fc_long_divmod_mix"
    "fc_long_branch_dispatch"
    "fc_widen_then_bias"
    "fc_read_after_void"
    "fc_recursive_sum"
    "fc_is_even"
    "fc_is_odd"
    "fc_dispatch_indirect"
    "fc_apply_indirect"
    "fc_recorded_chain"
    "fc_recorded_branch"
)

PHASE2_TARGET_FUNCS=(
    "fc_apply_indirect"
    "fc_dispatch_indirect"
    "fc_recursive_sum"
)

OUTPUT_BASE_DIR=${OUTPUT_BASE_DIR:-"$SCRIPT_DIR/logs/equivalence_all/function_call_test"}
BASE_PATH=${BASE_PATH:-"$SCRIPT_DIR/targets/cate1/function_call_test"}
PYTHON_BIN=${PYTHON_BIN:-python3}
FUNCTION_CALL_MANIFEST=${FUNCTION_CALL_MANIFEST:-"$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/raw/function_call_20_manifest.json"}

manifest_query() {
    local query="$1"
    shift
    if [[ ! -f "$FUNCTION_CALL_MANIFEST" ]]; then
        return 1
    fi
    "$PYTHON_BIN" - "$FUNCTION_CALL_MANIFEST" "$query" "$@" <<'PY'
import json
import sys

manifest_path, query, *args = sys.argv[1:]
with open(manifest_path, "r", encoding="utf-8") as handle:
    manifest = json.load(handle)

if query == "functions":
    for item in manifest.get("functions") or ():
        function = item.get("function")
        if function:
            print(function)
elif query == "binary_ids":
    for binary_id in manifest.get("binary_ids") or ():
        print(binary_id)
elif query == "pairs":
    function_name = args[0]
    found = False
    for item in manifest.get("functions") or ():
        if item.get("function") != function_name:
            continue
        found = True
        for pair in item.get("binary_pairs") or ():
            if "_" not in pair:
                continue
            left, right = pair.split("_", 1)
            print(f"{left}\t{right}")
        break
    if not found:
        raise SystemExit(2)
else:
    raise SystemExit(f"unknown manifest query: {query}")
PY
}

FUNCTION_CALL_TARGET_SET=${FUNCTION_CALL_TARGET_SET:-configured}
case "$FUNCTION_CALL_TARGET_SET" in
    configured)
        TARGET_FUNCS=("${CONFIGURED_TARGET_FUNCS[@]}")
        ;;
    full20|full|all|manifest)
        if mapfile -t TARGET_FUNCS < <(manifest_query functions) && (( ${#TARGET_FUNCS[@]} > 0 )); then
            :
        else
            TARGET_FUNCS=("${FULL20_TARGET_FUNCS[@]}")
        fi
        ;;
    phase2|equivalence_blocking_unsafety)
        TARGET_FUNCS=("${PHASE2_TARGET_FUNCS[@]}")
        ;;
    *)
        IFS=',' read -r -a TARGET_FUNCS <<< "$FUNCTION_CALL_TARGET_SET"
        ;;
esac

PARALLEL_JOBS=${PARALLEL_JOBS:-32}  # 同時実行数。環境変数で上書き可能
VALIDATION_BEFORE_DIR=${VALIDATION_BEFORE_DIR:-}  # before/after UNKNOWN reason 差分の比較元ログ
VALIDATION_AUTO_BEFORE_SNAPSHOT=${VALIDATION_AUTO_BEFORE_SNAPSHOT:-1}
VALIDATION_REQUIRE_BEFORE_DELTA=${VALIDATION_REQUIRE_BEFORE_DELTA:-0}  # Set to 1 for Plan 16 evidence runs.
VALIDATION_REQUIRE_BASELINE_MATCH=${VALIDATION_REQUIRE_BASELINE_MATCH:-0}  # Set to 1 for exact canonical reproduction gates.
VALIDATION_BASELINE_MATCH_SCOPE=${VALIDATION_BASELINE_MATCH_SCOPE:-all}  # Use after-pairs for filtered representative preflight runs.
VALIDATION_SKIP_COMPLETED=${VALIDATION_SKIP_COMPLETED:-0}  # Set to 1 to resume long matrix runs.
VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS=${VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS:-0}  # Set to 1 for Phase 2 producer reruns.
VALIDATION_RUNNER_DRY_RUN=${VALIDATION_RUNNER_DRY_RUN:-0}  # Set to 1 to print fixed pair order without running Ghidra.
FUNCTION_CALL_PAIR_FILTER=${FUNCTION_CALL_PAIR_FILTER:-}  # Comma-separated function:B1_B2 entries for representative reruns.
FUNCTION_CALL_EXTRA_EQUIV_ARGS=${FUNCTION_CALL_EXTRA_EQUIV_ARGS:-}  # Extra CLI args appended to each equivalence run.
RUNNER_TMP_ROOT=${RUNNER_TMP_ROOT:-"${TMPDIR:-/tmp}/ghidra-equivalence-function-call.$$"}

# bash バージョンチェック（wait -n は 4.3+ 必須）
if (( BASH_VERSINFO[0] < 4 || ( BASH_VERSINFO[0] == 4 && BASH_VERSINFO[1] < 3 ) )); then
    echo "Error: bash 4.3 以上が必要です（現在: $BASH_VERSION）" >&2
    exit 1
fi

# ---------------------- バイナリ定義 ----------------------
declare -A BINARY_MAP=(
    [B1]="function_call_test-arm64-clang-O0"
    [B2]="function_call_test-arm64-clang-O1"
    [B3]="function_call_test-arm64-clang-O2"
    [B4]="function_call_test-arm64-clang-O3"
    [B5]="function_call_test-arm64-gcc-O0"
    [B6]="function_call_test-arm64-gcc-O1"
    [B7]="function_call_test-arm64-gcc-O2"
    [B8]="function_call_test-arm64-gcc-O3"

    [B9]="function_call_test-mips64-clang-O0"
    [B10]="function_call_test-mips64-clang-O1"
    [B11]="function_call_test-mips64-clang-O2"
    [B12]="function_call_test-mips64-clang-O3"
    [B13]="function_call_test-mips64-gcc-O0"
    [B14]="function_call_test-mips64-gcc-O1"
    [B15]="function_call_test-mips64-gcc-O2"
    [B16]="function_call_test-mips64-gcc-O3"

    # [B17]="function_call_test-x86_64-clang-O0"
    # [B18]="function_call_test-x86_64-clang-O1"
    # [B19]="function_call_test-x86_64-clang-O2"
    # [B20]="function_call_test-x86_64-clang-O3"
    # [B21]="function_call_test-x86_64-gcc-O0"
    # [B22]="function_call_test-x86_64-gcc-O1"
    # [B23]="function_call_test-x86_64-gcc-O2"
    # [B24]="function_call_test-x86_64-gcc-O3"
)

# Fallback binary order only. The observed-v0 manifest owns full-run pair order.
BINARY_ID_ORDER=(
    "B1"
    "B2"
    "B3"
    "B4"
    "B5"
    "B6"
    "B7"
    "B8"
    "B9"
    "B10"
    "B11"
    "B12"
    "B13"
    "B14"
    "B15"
    "B16"
)

if mapfile -t MANIFEST_BINARY_IDS < <(manifest_query binary_ids) && (( ${#MANIFEST_BINARY_IDS[@]} > 0 )); then
    BINARY_ID_ORDER=("${MANIFEST_BINARY_IDS[@]}")
fi

declare -A ORDERED_BINARY_IDS=()
for BINARY_ID in "${BINARY_ID_ORDER[@]}"; do
    if [[ -z "${BINARY_MAP[$BINARY_ID]+defined}" ]]; then
        echo "Error: BINARY_ID_ORDER contains unknown id: $BINARY_ID" >&2
        exit 1
    fi
    ORDERED_BINARY_IDS["$BINARY_ID"]=1
done
for BINARY_ID in "${!BINARY_MAP[@]}"; do
    if [[ -z "${ORDERED_BINARY_IDS[$BINARY_ID]+defined}" ]]; then
        echo "Error: BINARY_MAP id missing from BINARY_ID_ORDER: $BINARY_ID" >&2
        exit 1
    fi
done

IDS=("${BINARY_ID_ORDER[@]}")

TOTAL_PAIRS=$(( ${#IDS[@]} * (${#IDS[@]} - 1) / 2 ))

validation_prepare_before_after_logs
validation_finalize_before_after_config

echo "============================================================"
echo "  Equivalence Check Script (Multi-function)"
echo "============================================================"
echo "Target functions: ${TARGET_FUNCS[*]}"
echo "Target function set: $FUNCTION_CALL_TARGET_SET"
echo "Number of functions: ${#TARGET_FUNCS[@]}"
echo "Pairs per function: $TOTAL_PAIRS"
echo "Parallel jobs: $PARALLEL_JOBS"
echo "Python: $PYTHON_BIN"
echo "Output base dir: $OUTPUT_BASE_DIR"
echo "Binary base path: $BASE_PATH"
echo "Function call manifest: $FUNCTION_CALL_MANIFEST"
echo "Binary ID order: ${IDS[*]}"
echo "Per-pair TMPDIR root: $RUNNER_TMP_ROOT"
echo "Skip completed logs: $VALIDATION_SKIP_COMPLETED"
echo "Require Phase 2 object keys on skipped logs: $VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS"
echo "Runner dry run: $VALIDATION_RUNNER_DRY_RUN"
echo "Function/pair filter: ${FUNCTION_CALL_PAIR_FILTER:-<none>}"
echo "Extra equivalence args: ${FUNCTION_CALL_EXTRA_EQUIV_ARGS:-<none>}"
echo "Validation before dir: $VALIDATION_BEFORE_LABEL [$VALIDATION_BEFORE_SOURCE]"
if [[ -n "${VALIDATION_MOVED_OUTPUT_DIR:-}" ]]; then
    echo "Moved old output dir: $VALIDATION_MOVED_OUTPUT_DIR"
fi
echo "Require before/after delta: $VALIDATION_REQUIRE_BEFORE_DELTA"
echo "Require baseline match: $VALIDATION_REQUIRE_BASELINE_MATCH"
echo "Baseline match scope: $VALIDATION_BASELINE_MATCH_SCOPE"
echo "============================================================"
echo ""

print_fixed_pair_order() {
    local target_func row_id col_id log_name

    for target_func in "${TARGET_FUNCS[@]}"; do
        while IFS=$'\t' read -r row_id col_id; do
            [[ -n "$row_id" && -n "$col_id" ]] || continue
            log_name="${target_func}_${row_id}_${col_id}.log"
            printf "%s %s %s %s\n" "$target_func" "$row_id" "$col_id" "$log_name"
        done < <(collect_pair_specs "$target_func")
    done
}

# ---------------------- ワーカー関数 ----------------------
run_pair() {
    local ROW_ID="$1"
    local COL_ID="$2"
    local BIN1="$3"
    local BIN2="$4"
    local COUNT="$5"
    local TOTAL="$6"
    local TARGET_FUNC="$7"
    local OUTPUT_DIR="$8"
    local LOG_FILE="${OUTPUT_DIR}/${TARGET_FUNC}_${ROW_ID}_${COL_ID}.log"

    if [[ "$VALIDATION_SKIP_COMPLETED" != "0" && -f "$LOG_FILE" ]] \
        && grep -q "^=== EQUIVALENCE_RESULT_JSON_END ===" "$LOG_FILE"; then
        local reuse_gate_args=(--log "$LOG_FILE")
        if [[ "$VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS" != "0" ]]; then
            reuse_gate_args+=(--require-phase2-object-keys)
        fi
        local reuse_failure=""
        if ! reuse_failure="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.log_reuse_gate "${reuse_gate_args[@]}" 2>&1)"; then
            echo "[$COUNT/$TOTAL] $ROW_ID ↔ $COL_ID : stale completed log; rerunning (${reuse_failure//$'\n'/, })"
        else
            local skipped_status
            if grep -q "^Result: EQUIVALENT" "$LOG_FILE"; then
                skipped_status="EQUIVALENT ✓"
            elif grep -q "^Result: NOT EQUIVALENT" "$LOG_FILE"; then
                skipped_status="NOT EQUIVALENT ✗"
            elif grep -q "^Result: ERROR" "$LOG_FILE"; then
                skipped_status="ERROR !"
            elif grep -q "^Result: TIMEOUT" "$LOG_FILE"; then
                skipped_status="TIMEOUT"
            elif grep -q "^Result: UNKNOWN" "$LOG_FILE"; then
                skipped_status="UNKNOWN"
            else
                skipped_status="INCOMPLETE"
            fi
            echo "[$COUNT/$TOTAL] $ROW_ID ↔ $COL_ID : $skipped_status (skipped)"
            return 0
        fi
    fi

    local PAIR_TMPDIR="${RUNNER_TMP_ROOT}/${TARGET_FUNC}_${ROW_ID}_${COL_ID}"
    mkdir -p "$PAIR_TMPDIR"

    local -a EXTRA_EQUIV_ARGS=()
    if [[ -n "$FUNCTION_CALL_EXTRA_EQUIV_ARGS" ]]; then
        read -r -a EXTRA_EQUIV_ARGS <<< "$FUNCTION_CALL_EXTRA_EQUIV_ARGS"
    fi

    TMPDIR="$PAIR_TMPDIR" "$PYTHON_BIN" -m scripts.function_tracer_pcode.cli.main \
        --equiv "$BASE_PATH/$BIN1" "$BASE_PATH/$BIN2" \
        --binary-ids "$ROW_ID" "$COL_ID" \
        -f "$TARGET_FUNC" -d --emit-result-json "${EXTRA_EQUIV_ARGS[@]}" \
        > "$LOG_FILE" 2>&1
    local ec=$?

    local status
    if grep -q "^Result: EQUIVALENT" "$LOG_FILE"; then
        status="EQUIVALENT ✓"
    elif grep -q "^Result: NOT EQUIVALENT" "$LOG_FILE"; then
        status="NOT EQUIVALENT ✗"
    elif grep -q "^Result: ERROR" "$LOG_FILE"; then
        status="ERROR !"
    elif grep -q "^Result: TIMEOUT" "$LOG_FILE"; then
        status="TIMEOUT"
    elif grep -q "^Result: UNKNOWN" "$LOG_FILE"; then
        status="UNKNOWN"
    else
        status="INCOMPLETE"
    fi

    local msg="[$COUNT/$TOTAL] $ROW_ID ↔ $COL_ID : $status"
    (( ec != 0 )) && msg+="  (exit=$ec)"
    echo "$msg"
}

export -f run_pair
export BASE_PATH PYTHON_BIN RUNNER_TMP_ROOT VALIDATION_SKIP_COMPLETED FUNCTION_CALL_EXTRA_EQUIV_ARGS

write_summary_file() {
    local output_file="$1"
    shift
    local tmp_file
    tmp_file="$(mktemp "${output_file}.tmp.XXXXXX")" || return 1
    "$@" > "$tmp_file"
    local status=$?
    if (( status == 0 )); then
        tee "$output_file" < "$tmp_file"
        local tee_status=$?
        rm -f "$tmp_file"
        return "$tee_status"
    fi
    rm -f "$tmp_file"
    echo "Error: summary generation failed for $output_file (exit=$status); leaving existing summary unchanged." >&2
    return "$status"
}

calculate_elapsed_seconds() {
    local start_ts="$1"
    local end_ts="$2"

    awk -v start="$start_ts" -v end="$end_ts" 'BEGIN {
        elapsed = end - start
        if (elapsed < 0) {
            elapsed = 0
        }
        printf "%.3f", elapsed
    }'
}

format_duration() {
    local total_seconds="${1:-0}"

    awk -v total="$total_seconds" 'BEGIN {
        hours = int(total / 3600)
        minutes = int((total - (hours * 3600)) / 60)
        seconds = total - (hours * 3600) - (minutes * 60)

        if (hours > 0) {
            printf "%dh %02dm %06.3fs", hours, minutes, seconds
        } else if (minutes > 0) {
            printf "%dm %06.3fs", minutes, seconds
        } else {
            printf "%.3fs", seconds
        }
    }'
}

classify_log_result() {
    local log_file="$1"

    if grep -q "^Result: EQUIVALENT" "$log_file"; then
        echo "EQ"
    elif grep -q "^Result: NOT EQUIVALENT" "$log_file"; then
        echo "NOT_EQ"
    elif grep -q "^Result: ERROR" "$log_file"; then
        echo "ERROR"
    elif grep -q "^Result: TIMEOUT" "$log_file"; then
        echo "TIMEOUT"
    elif grep -q "^Result: UNKNOWN" "$log_file"; then
        echo "UNKNOWN"
    else
        echo "INCOMPLETE"
    fi
}

summarize_log_time_lines() {
    local -a log_files=("$@")

    if (( ${#log_files[@]} == 0 )); then
        return 0
    fi

    awk '
        /^Total time: [0-9.]+ seconds$/ {
            value = $3 + 0
            count++
            sum += value

            if (count == 1 || value < min) {
                min = value
            }
            if (count == 1 || value > max) {
                max = value
            }
        }
        END {
            if (count > 0) {
                printf "%d\t%.3f\t%.3f\t%.3f\t%.3f\n", \
                    count, sum, sum / count, min, max
            }
        }
    ' "${log_files[@]}"
}

print_log_time_summary_block() {
    local indent="$1"
    shift
    local -a log_files=("$@")
    local summary_line

    summary_line=$(summarize_log_time_lines "${log_files[@]}")
    if [[ -z "$summary_line" ]]; then
        return 0
    fi

    local timed_logs sum_seconds avg_seconds min_seconds max_seconds
    IFS=$'\t' read -r timed_logs sum_seconds avg_seconds min_seconds max_seconds <<< "$summary_line"

    echo ""
    echo "${indent}Per-pair Solver Time Summary:"
    printf "%s  LOGS=%3d | SUM=%8.3fs, AVG=%7.3fs, MIN=%7.3fs, MAX=%7.3fs\n" \
        "$indent" "$timed_logs" "$sum_seconds" "$avg_seconds" "$min_seconds" "$max_seconds"
}

summarize_phase_usage_lines() {
    local -a log_files=("$@")

    if (( ${#log_files[@]} == 0 )); then
        return 0
    fi

    awk '
        /^[[:space:]]+P[0-9A-Z_]+: (USED|NO_CHANGES|NOT_REACHED)/ {
            line = $0
            sub(/^[[:space:]]+/, "", line)

            phase = line
            sub(/:.*/, "", phase)

            status = line
            sub(/^[^:]+: /, "", status)
            sub(/ .*/, "", status)

            total_logs[phase]++
            status_counts[phase, status]++
            phases[phase] = 1

            meta = line
            sub(/^[^(]*\(/, "", meta)
            sub(/\).*/, "", meta)
            if (meta != line) {
                meta_count = split(meta, items, /, /)
                for (i = 1; i <= meta_count; i++) {
                    split(items[i], kv, "=")
                    key = kv[1]
                    value = kv[2] + 0

                    if (key == "attempts") attempt_counts[phase] += value
                    else if (key == "rechecks") recheck_counts[phase] += value
                    else if (key == "no_changes") no_change_counts[phase] += value
                    else if (key == "unsat") unsat_counts[phase] += value
                    else if (key == "sat") sat_counts[phase] += value
                    else if (key == "sat_phase4b") sat_phase4b_counts[phase] += value
                    else if (key == "unknown") unknown_counts[phase] += value
                    else if (key == "timeout") timeout_counts[phase] += value
                    else if (key == "critical") critical_counts[phase] += value
                }
            }
        }
        END {
            for (phase in phases) {
                printf "%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n", \
                    phase, total_logs[phase] + 0, \
                    status_counts[phase, "USED"] + 0, \
                    status_counts[phase, "NO_CHANGES"] + 0, \
                    status_counts[phase, "NOT_REACHED"] + 0, \
                    attempt_counts[phase] + 0, \
                    recheck_counts[phase] + 0, \
                    unsat_counts[phase] + 0, \
                    sat_counts[phase] + 0, \
                    sat_phase4b_counts[phase] + 0, \
                    unknown_counts[phase] + 0, \
                    timeout_counts[phase] + 0, \
                    critical_counts[phase] + 0
            }
        }
    ' "${log_files[@]}" | sort
}

print_phase_usage_summary_block() {
    local indent="$1"
    shift
    local -a log_files=("$@")
    local summary_lines

    summary_lines=$(summarize_phase_usage_lines "${log_files[@]}")
    if [[ -z "$summary_lines" ]]; then
        return 0
    fi

    echo ""
    echo "${indent}Phase Usage Summary:"

    while IFS=$'\t' read -r phase total used no_changes not_reached attempts rechecks unsat sat sat_phase4b unknown timeout critical; do
        [[ -n "$phase" ]] || continue
        printf "%s  - %-22s LOGS=%3d | USED=%3d, NO_CHANGES=%3d, NOT_REACHED=%3d | ATTEMPTS=%3d, RECHECKS=%3d | UNSAT=%3d, SAT=%3d, SAT->Phase4B=%3d, UNKNOWN=%3d, TIMEOUT=%3d, CRITICAL=%3d\n" \
            "$indent" "$phase" "$total" "$used" "$no_changes" "$not_reached" "$attempts" "$rechecks" "$unsat" "$sat" "$sat_phase4b" "$unknown" "$timeout" "$critical"
    done <<< "$summary_lines"
}

summarize_pairwise_normalization_lines() {
    local -a log_files=("$@")

    if (( ${#log_files[@]} == 0 )); then
        return 0
    fi

    awk '
        /^[[:space:]]+attempts=[0-9]+, changed=[0-9]+, no_change=[0-9]+, unsat=[0-9]+, sat=[0-9]+, unknown=[0-9]+/ {
            line = $0
            sub(/^[[:space:]]+/, "", line)
            line_count++
            item_count = split(line, items, /, /)
            for (i = 1; i <= item_count; i++) {
                split(items[i], kv, "=")
                totals[kv[1]] += kv[2] + 0
            }
        }
        END {
            if (line_count > 0) {
                printf "%d\t%d\t%d\t%d\t%d\t%d\t%d\n", \
                    line_count, \
                    totals["attempts"] + 0, \
                    totals["changed"] + 0, \
                    totals["no_change"] + 0, \
                    totals["unsat"] + 0, \
                    totals["sat"] + 0, \
                    totals["unknown"] + 0
            }
        }
    ' "${log_files[@]}"
}

print_pairwise_normalization_summary_block() {
    local indent="$1"
    shift
    local -a log_files=("$@")
    local summary_line

    summary_line=$(summarize_pairwise_normalization_lines "${log_files[@]}")
    if [[ -z "$summary_line" ]]; then
        return 0
    fi

    IFS=$'\t' read -r logs attempts changed no_change unsat sat unknown <<< "$summary_line"
    echo ""
    echo "${indent}Pairwise Timeout Normalization Summary:"
    printf "%s  LOGS=%3d | ATTEMPTS=%3d, CHANGED=%3d, NO_CHANGE=%3d | UNSAT=%3d, SAT=%3d, UNKNOWN=%3d\n" \
        "$indent" "$logs" "$attempts" "$changed" "$no_change" "$unsat" "$sat" "$unknown"
}

collect_unfiltered_pair_specs() {
    local target_func="$1"
    local row_id col_id manifest_pairs

    if manifest_pairs="$(manifest_query pairs "$target_func" 2>/dev/null)" && [[ -n "$manifest_pairs" ]]; then
        while IFS=$'\t' read -r row_id col_id; do
            [[ -n "$row_id" && -n "$col_id" ]] || continue
            printf '%s\t%s\n' "$row_id" "$col_id"
        done <<< "$manifest_pairs"
        return 0
    fi

    for ((i=0; i<${#IDS[@]}-1; i++)); do
        row_id="${IDS[$i]}"
        for ((j=i+1; j<${#IDS[@]}; j++)); do
            col_id="${IDS[$j]}"
            printf '%s\t%s\n' "$row_id" "$col_id"
        done
    done
}

collect_pair_specs() {
    local target_func="$1"
    local row_id col_id

    while IFS=$'\t' read -r row_id col_id; do
        [[ -n "$row_id" && -n "$col_id" ]] || continue
        if function_call_pair_filter_allows "$target_func" "$row_id" "$col_id"; then
            printf '%s\t%s\n' "$row_id" "$col_id"
        fi
    done < <(collect_unfiltered_pair_specs "$target_func")
}

function_call_pair_filter_entries() {
    local compact_filter entry
    local -a raw_entries=()

    compact_filter="${FUNCTION_CALL_PAIR_FILTER//[[:space:]]/}"
    IFS=',' read -r -a raw_entries <<< "$compact_filter"
    for entry in "${raw_entries[@]}"; do
        [[ -n "$entry" ]] || continue
        printf '%s\n' "$entry"
    done
}

function_call_pair_filter_entry_matches() {
    local entry="$1"
    local target_func="$2"
    local row_id="$3"
    local col_id="$4"
    local entry_func=""
    local entry_pair="$entry"
    local left_id right_id

    if [[ "$entry" == *:* ]]; then
        entry_func="${entry%%:*}"
        entry_pair="${entry#*:}"
        [[ -n "$entry_func" && -n "$entry_pair" ]] || return 1
        [[ "$entry_func" == "$target_func" ]] || return 1
    fi

    [[ "$entry_pair" == *_* ]] || return 1
    left_id="${entry_pair%%_*}"
    right_id="${entry_pair#*_}"
    [[ -n "$left_id" && -n "$right_id" ]] || return 1

    if [[ "$left_id" == "$row_id" && "$right_id" == "$col_id" ]]; then
        return 0
    fi
    if [[ "$left_id" == "$col_id" && "$right_id" == "$row_id" ]]; then
        return 0
    fi
    return 1
}

function_call_pair_filter_allows() {
    local target_func="$1"
    local row_id="$2"
    local col_id="$3"
    local compact_filter="${FUNCTION_CALL_PAIR_FILTER//[[:space:]]/}"
    local filter_entry

    if [[ -z "$compact_filter" ]]; then
        return 0
    fi

    while IFS= read -r filter_entry; do
        if function_call_pair_filter_entry_matches "$filter_entry" "$target_func" "$row_id" "$col_id"; then
            return 0
        fi
    done < <(function_call_pair_filter_entries)

    return 1
}

validate_function_call_pair_filter() {
    local compact_filter="${FUNCTION_CALL_PAIR_FILTER//[[:space:]]/}"
    local target_func row_id col_id filter_entry
    local -a filter_entries=()
    local -a selected_pairs=()
    local -A filter_entry_matched=()

    if [[ -z "$compact_filter" ]]; then
        return 0
    fi

    mapfile -t filter_entries < <(function_call_pair_filter_entries)
    if (( ${#filter_entries[@]} == 0 )); then
        echo "Error: FUNCTION_CALL_PAIR_FILTER did not contain any pair entries: $FUNCTION_CALL_PAIR_FILTER" >&2
        return 1
    fi

    for filter_entry in "${filter_entries[@]}"; do
        filter_entry_matched["$filter_entry"]=0
    done

    for target_func in "${TARGET_FUNCS[@]}"; do
        mapfile -t selected_pairs < <(collect_pair_specs "$target_func")
        if (( ${#selected_pairs[@]} == 0 )); then
            echo "Error: FUNCTION_CALL_PAIR_FILTER selected zero pairs for target function: $target_func" >&2
            echo "  filter: $FUNCTION_CALL_PAIR_FILTER" >&2
            return 1
        fi

        while IFS=$'\t' read -r row_id col_id; do
            [[ -n "$row_id" && -n "$col_id" ]] || continue
            for filter_entry in "${filter_entries[@]}"; do
                if function_call_pair_filter_entry_matches "$filter_entry" "$target_func" "$row_id" "$col_id"; then
                    filter_entry_matched["$filter_entry"]=1
                fi
            done
        done < <(collect_unfiltered_pair_specs "$target_func")
    done

    for filter_entry in "${filter_entries[@]}"; do
        if [[ "${filter_entry_matched[$filter_entry]}" != "1" ]]; then
            echo "Error: FUNCTION_CALL_PAIR_FILTER entry did not match any selected target function pair: $filter_entry" >&2
            echo "  target functions: ${TARGET_FUNCS[*]}" >&2
            return 1
        fi
    done
}

collect_expected_log_files() {
    local output_dir="$1"
    local target_func="$2"
    local row_id col_id log_file

    while IFS=$'\t' read -r row_id col_id; do
        [[ -n "$row_id" && -n "$col_id" ]] || continue
        log_file="${output_dir}/${target_func}_${row_id}_${col_id}.log"
        if [[ -f "$log_file" ]]; then
            printf '%s\n' "$log_file"
        fi
    done < <(collect_pair_specs "$target_func")
}

collect_all_expected_log_files() {
    local target_func

    for target_func in "${TARGET_FUNCS[@]}"; do
        collect_expected_log_files "${OUTPUT_BASE_DIR}/${target_func}" "$target_func"
    done
}

if ! validate_function_call_pair_filter; then
    exit 1
fi

if [[ "$VALIDATION_RUNNER_DRY_RUN" != "0" ]]; then
    echo "Dry run fixed pair order:"
    print_fixed_pair_order
    exit 0
fi

# ---------------------- 関数ごとの処理 ----------------------
FUNC_INDEX=0
TOTAL_FUNCS=${#TARGET_FUNCS[@]}
declare -A FUNC_WALL_TIME_SECONDS=()

for TARGET_FUNC in "${TARGET_FUNCS[@]}"; do
    FUNC_INDEX=$((FUNC_INDEX + 1))
    func_start_ts=$(date +%s.%N)

    # 関数ごとの出力ディレクトリを設定
    OUTPUT_DIR="${OUTPUT_BASE_DIR}/${TARGET_FUNC}"
    mkdir -p "$OUTPUT_DIR"

    # サブシェルにエクスポート
    export OUTPUT_DIR TARGET_FUNC

    echo "============================================================"
    echo "[$FUNC_INDEX/$TOTAL_FUNCS] Processing function: $TARGET_FUNC"
    echo "Output directory: $OUTPUT_DIR"
    echo "============================================================"

    # ---------------------- 並列実行ループ ----------------------
    COUNT=0
    active_jobs=0
    mapfile -t PAIR_SPECS < <(collect_pair_specs "$TARGET_FUNC")
    FUNC_TOTAL_PAIRS=${#PAIR_SPECS[@]}

    for PAIR_SPEC in "${PAIR_SPECS[@]}"; do
        IFS=$'\t' read -r ROW_ID COL_ID <<< "$PAIR_SPEC"
        [[ -n "$ROW_ID" && -n "$COL_ID" ]] || continue
        BIN1="${BINARY_MAP[$ROW_ID]}"

        if [[ ! -f "$BASE_PATH/$BIN1" ]]; then
            echo "Error: $BASE_PATH/$BIN1 not found – skipping all pairs involving $ROW_ID"
            continue
        fi

        BIN2="${BINARY_MAP[$COL_ID]}"

        if [[ ! -f "$BASE_PATH/$BIN2" ]]; then
            echo "Error: $BASE_PATH/$BIN2 not found – skipping $ROW_ID↔$COL_ID"
            continue
        fi

        COUNT=$((COUNT + 1))

        if (( active_jobs >= PARALLEL_JOBS )); then
            wait -n
            active_jobs=$(( active_jobs - 1 ))
        fi

        run_pair "$ROW_ID" "$COL_ID" "$BIN1" "$BIN2" "$COUNT" "$FUNC_TOTAL_PAIRS" "$TARGET_FUNC" "$OUTPUT_DIR" &
        active_jobs=$(( active_jobs + 1 ))
    done

    wait
    echo ""
    func_end_ts=$(date +%s.%N)
    func_elapsed_seconds=$(calculate_elapsed_seconds "$func_start_ts" "$func_end_ts")
    FUNC_WALL_TIME_SECONDS["$TARGET_FUNC"]="$func_elapsed_seconds"

    # ---------------------- 結果集計 ----------------------
    # 結果集計ファイルのパス
    RESULT_FILE="${OUTPUT_DIR}/results_summary.txt"

    echo "--- Results for $TARGET_FUNC ---"

    declare -a EQ_PAIRS=()
    declare -a NON_EQ_PAIRS=()
    declare -a ERROR_PAIRS=()
    declare -a UNKNOWN_PAIRS=()
    declare -a TIMEOUT_PAIRS=()
    declare -a INCOMPLETE_PAIRS=()

    for PAIR_SPEC in "${PAIR_SPECS[@]}"; do
        IFS=$'\t' read -r ROW_ID COL_ID <<< "$PAIR_SPEC"
        [[ -n "$ROW_ID" && -n "$COL_ID" ]] || continue
        LOG_FILE="${OUTPUT_DIR}/${TARGET_FUNC}_${ROW_ID}_${COL_ID}.log"

        if [[ ! -f "$LOG_FILE" ]]; then
            continue
        fi

        case "$(classify_log_result "$LOG_FILE")" in
            EQ)
            EQ_PAIRS+=("$ROW_ID ↔ $COL_ID")
            ;;
            NOT_EQ)
            NON_EQ_PAIRS+=("$ROW_ID ↔ $COL_ID")
            ;;
            ERROR)
            ERROR_PAIRS+=("$ROW_ID ↔ $COL_ID")
            ;;
            TIMEOUT)
            TIMEOUT_PAIRS+=("$ROW_ID ↔ $COL_ID")
            ;;
            UNKNOWN)
            UNKNOWN_PAIRS+=("$ROW_ID ↔ $COL_ID")
            ;;
            INCOMPLETE)
            INCOMPLETE_PAIRS+=("$ROW_ID ↔ $COL_ID")
            ;;
            *)
            INCOMPLETE_PAIRS+=("$ROW_ID ↔ $COL_ID")
            ;;
        esac
    done

    # --- tee を使って画面とファイルの両方に出力 ---
    mapfile -t FUNC_LOG_FILES < <(collect_expected_log_files "$OUTPUT_DIR" "$TARGET_FUNC")

    FUNCTION_SUMMARY_ARGS=(
        --function-summary
        --function-name "$TARGET_FUNC"
        --elapsed-seconds "$func_elapsed_seconds"
    )
    if [[ -n "$VALIDATION_BEFORE_DIR" ]]; then
        FUNCTION_SUMMARY_ARGS+=(--before-dir "${VALIDATION_BEFORE_DIR}/${TARGET_FUNC}")
    fi
    if [[ "$VALIDATION_REQUIRE_BEFORE_DELTA" != "0" ]]; then
        FUNCTION_SUMMARY_ARGS+=(--require-before-dir)
    fi
    if [[ "$VALIDATION_REQUIRE_BASELINE_MATCH" != "0" ]]; then
        FUNCTION_SUMMARY_ARGS+=(--require-baseline-match)
    fi
    FUNCTION_SUMMARY_ARGS+=(--baseline-match-scope "$VALIDATION_BASELINE_MATCH_SCOPE")
    if ! write_summary_file "$RESULT_FILE" \
        python3 -m scripts.function_tracer_pcode.validation.result_summary \
            "${FUNCTION_SUMMARY_ARGS[@]}" \
            "${FUNC_LOG_FILES[@]}"; then
        exit 1
    fi

done

# ---------------------- 全体サマリー ----------------------
# 全体サマリーの保存先
SUMMARY_FILE="${OUTPUT_BASE_DIR}/overall_summary.txt"

mapfile -t ALL_LOG_FILES < <(collect_all_expected_log_files)

OVERALL_SUMMARY_ARGS=(--overall-summary)
if [[ -n "$VALIDATION_BEFORE_DIR" ]]; then
    OVERALL_SUMMARY_ARGS+=(--before-dir "$VALIDATION_BEFORE_DIR")
fi
if [[ "$VALIDATION_REQUIRE_BEFORE_DELTA" != "0" ]]; then
    OVERALL_SUMMARY_ARGS+=(--require-before-dir)
fi
if [[ "$VALIDATION_REQUIRE_BASELINE_MATCH" != "0" ]]; then
    OVERALL_SUMMARY_ARGS+=(--require-baseline-match)
fi
OVERALL_SUMMARY_ARGS+=(--baseline-match-scope "$VALIDATION_BASELINE_MATCH_SCOPE")
for TARGET_FUNC in "${TARGET_FUNCS[@]}"; do
    OVERALL_SUMMARY_ARGS+=(--function-wall-time "$TARGET_FUNC=${FUNC_WALL_TIME_SECONDS[$TARGET_FUNC]:-0}")
done
if ! write_summary_file "$SUMMARY_FILE" \
    python3 -m scripts.function_tracer_pcode.validation.result_summary \
        "${OVERALL_SUMMARY_ARGS[@]}" \
        "${ALL_LOG_FILES[@]}"; then
    exit 1
fi
