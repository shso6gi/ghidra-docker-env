#!/usr/bin/env bash
# ------------------------------------------------------------
#  バイナリ間の等価性判定スクリプト（並列版・複数関数対応）
#  bash 4.3 以上が必要（wait -n を使用）
# ------------------------------------------------------------

# ---------------------- 設定 ----------------------
# 対象関数を配列で指定
TARGET_FUNCS=(
    # "ptr_call_leaf"
    # "ptr_call_chain"
    # "ptr_select_path"
    # "ptr_nested_dispatch"
    # "ptr_read_after_store"
    # "ptr_update_in_place"
    # "ptr_alias_adjust"
    # "ptr_copy_or_accumulate"
    #"ptr_sum_window"
    #"ptr_stride_pick"
    #"ptr_choose_target"
    #"ptr_double_indirect_write"
    #"ptr_box_follow_link"
    #"ptr_box_mutate"
    #"ptr_dispatch_callback"
    "ptr_call_and_store"
    #"ptr_branch_on_loaded_value"
    # 必要に応じて追加
)

OUTPUT_BASE_DIR="/workspaces/ghidra-docker-env/logs/equivalence_all/pointer_call_test"
BASE_PATH="/workspaces/ghidra-docker-env/targets/cate1/pointer_call_test"
PARALLEL_JOBS=${PARALLEL_JOBS:-32}  # 同時実行数。環境変数で上書き可能
VALIDATION_BEFORE_DIR=${VALIDATION_BEFORE_DIR:-}  # before/after UNKNOWN reason 差分の比較元ログ
VALIDATION_AUTO_BEFORE_SNAPSHOT=${VALIDATION_AUTO_BEFORE_SNAPSHOT:-1}
VALIDATION_REQUIRE_BEFORE_DELTA=${VALIDATION_REQUIRE_BEFORE_DELTA:-0}  # Set to 1 for Plan 16 evidence runs.
VALIDATION_REQUIRE_BASELINE_MATCH=${VALIDATION_REQUIRE_BASELINE_MATCH:-0}  # Set to 1 for exact canonical reproduction gates.

# bash バージョンチェック（wait -n は 4.3+ 必須）
if (( BASH_VERSINFO[0] < 4 || ( BASH_VERSINFO[0] == 4 && BASH_VERSINFO[1] < 3 ) )); then
    echo "Error: bash 4.3 以上が必要です（現在: $BASH_VERSION）" >&2
    exit 1
fi

# ---------------------- バイナリ定義 ----------------------
declare -A BINARY_MAP=(
    [B1]="pointer_call_test-arm64-clang-O0"
    [B2]="pointer_call_test-arm64-clang-O1"
    [B3]="pointer_call_test-arm64-clang-O2"
    [B4]="pointer_call_test-arm64-clang-O3"
    [B5]="pointer_call_test-arm64-gcc-O0"
    [B6]="pointer_call_test-arm64-gcc-O1"
    [B7]="pointer_call_test-arm64-gcc-O2"
    [B8]="pointer_call_test-arm64-gcc-O3"

    [B9]="pointer_call_test-mips64-clang-O0"
    [B10]="pointer_call_test-mips64-clang-O1"
    [B11]="pointer_call_test-mips64-clang-O2"
    [B12]="pointer_call_test-mips64-clang-O3"
    [B13]="pointer_call_test-mips64-gcc-O0"
    [B14]="pointer_call_test-mips64-gcc-O1"
    [B15]="pointer_call_test-mips64-gcc-O2"
    [B16]="pointer_call_test-mips64-gcc-O3"

    # [B17]="pointer_call_test-x86_64-clang-O0"
    # [B18]="pointer_call_test-x86_64-clang-O1"
    # [B19]="pointer_call_test-x86_64-clang-O2"
    # [B20]="pointer_call_test-x86_64-clang-O3"
    # [B21]="pointer_call_test-x86_64-gcc-O0"
    # [B22]="pointer_call_test-x86_64-gcc-O1"
    # [B23]="pointer_call_test-x86_64-gcc-O2"
    # [B24]="pointer_call_test-x86_64-gcc-O3"
)

IDS=(${!BINARY_MAP[@]})
IFS=$'\n' IDS=($(sort <<<"${IDS[*]}"))
unset IFS

TOTAL_PAIRS=$(( ${#IDS[@]} * (${#IDS[@]} - 1) / 2 ))

VALIDATION_BEFORE_SOURCE="not configured"
if [[ -n "$VALIDATION_BEFORE_DIR" ]]; then
    VALIDATION_BEFORE_SOURCE="configured"
elif [[ "$VALIDATION_AUTO_BEFORE_SNAPSHOT" != "0" && -d "$OUTPUT_BASE_DIR" ]]; then
    EXISTING_VALIDATION_LOG="$(find "$OUTPUT_BASE_DIR" -type f -name "*.log" -print -quit 2>/dev/null || true)"
    if [[ -n "$EXISTING_VALIDATION_LOG" ]]; then
        VALIDATION_BEFORE_DIR="$(mktemp -d "${TMPDIR:-/tmp}/equivalence_before.XXXXXX")"
        cp -a "$OUTPUT_BASE_DIR"/. "$VALIDATION_BEFORE_DIR"/
        VALIDATION_BEFORE_SOURCE="auto snapshot"
    fi
fi
VALIDATION_BEFORE_LABEL="(none)"
if [[ -n "$VALIDATION_BEFORE_DIR" ]]; then
    VALIDATION_BEFORE_LABEL="$VALIDATION_BEFORE_DIR"
fi
if [[ "$VALIDATION_REQUIRE_BEFORE_DELTA" != "0" && -z "$VALIDATION_BEFORE_DIR" ]]; then
    echo "Error: VALIDATION_REQUIRE_BEFORE_DELTA requires VALIDATION_BEFORE_DIR or an auto before snapshot." >&2
    exit 1
fi

echo "============================================================"
echo "  Equivalence Check Script (Multi-function)"
echo "============================================================"
echo "Target functions: ${TARGET_FUNCS[*]}"
echo "Number of functions: ${#TARGET_FUNCS[@]}"
echo "Pairs per function: $TOTAL_PAIRS"
echo "Parallel jobs: $PARALLEL_JOBS"
echo "Validation before dir: $VALIDATION_BEFORE_LABEL [$VALIDATION_BEFORE_SOURCE]"
echo "Require before/after delta: $VALIDATION_REQUIRE_BEFORE_DELTA"
echo "Require baseline match: $VALIDATION_REQUIRE_BASELINE_MATCH"
echo "============================================================"
echo ""

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

    python3 -m scripts.function_tracer_pcode.cli.main \
        --equiv "$BASE_PATH/$BIN1" "$BASE_PATH/$BIN2" \
        -f "$TARGET_FUNC" -d --emit-result-json \
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
export BASE_PATH

write_summary_file() {
    local output_file="$1"
    shift
    local tmp_file
    tmp_file="$(mktemp "${output_file}.tmp.XXXXXX")" || return 1
    if "$@" > "$tmp_file"; then
        tee "$output_file" < "$tmp_file"
        local tee_status=$?
        rm -f "$tmp_file"
        return "$tee_status"
    fi
    local status=$?
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

    for ((i=0; i<${#IDS[@]}-1; i++)); do
        ROW_ID="${IDS[$i]}"
        BIN1="${BINARY_MAP[$ROW_ID]}"

        if [[ ! -f "$BASE_PATH/$BIN1" ]]; then
            echo "Error: $BASE_PATH/$BIN1 not found – skipping all pairs involving $ROW_ID"
            continue
        fi

        for ((j=i+1; j<${#IDS[@]}; j++)); do
            COL_ID="${IDS[$j]}"
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

            run_pair "$ROW_ID" "$COL_ID" "$BIN1" "$BIN2" "$COUNT" "$TOTAL_PAIRS" "$TARGET_FUNC" "$OUTPUT_DIR" &
            active_jobs=$(( active_jobs + 1 ))
        done
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

    for ((i=0; i<${#IDS[@]}-1; i++)); do
        ROW_ID="${IDS[$i]}"
        for ((j=i+1; j<${#IDS[@]}; j++)); do
            COL_ID="${IDS[$j]}"
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
    done

    # --- tee を使って画面とファイルの両方に出力 ---
    shopt -s nullglob
    FUNC_LOG_FILES=("$OUTPUT_DIR"/*.log)
    shopt -u nullglob

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

mapfile -t ALL_LOG_FILES < <(find "$OUTPUT_BASE_DIR" -type f -name "*.log" | sort)

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
for TARGET_FUNC in "${TARGET_FUNCS[@]}"; do
    OVERALL_SUMMARY_ARGS+=(--function-wall-time "$TARGET_FUNC=${FUNC_WALL_TIME_SECONDS[$TARGET_FUNC]:-0}")
done
if ! write_summary_file "$SUMMARY_FILE" \
    python3 -m scripts.function_tracer_pcode.validation.result_summary \
        "${OVERALL_SUMMARY_ARGS[@]}" \
        "${ALL_LOG_FILES[@]}"; then
    exit 1
fi
