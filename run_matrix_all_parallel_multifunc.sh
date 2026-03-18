#!/usr/bin/env bash
# ------------------------------------------------------------
#  バイナリ間の等価性判定スクリプト（並列版・複数関数対応）
#  bash 4.3 以上が必要（wait -n を使用）
# ------------------------------------------------------------

# ---------------------- 設定 ----------------------
# 対象関数を配列で指定
TARGET_FUNCS=(
    "branch_eq"
    "branch_ne"
    "branch_lt"
    "branch_le"
    "branch_gt"
    "branch_ge"
    "branch_zero"
    "branch_nonzero"
    "branch_not"
    "branch_closed_range"
    "branch_half_open_range"
    "branch_disjoint_range"
    "branch_signed_compare"
    "branch_unsigned_compare"
    "branch_signed_unsigned_mix"
    # "branch_short_circuit_and"
    # "branch_short_circuit_or"
    "branch_nested_boolean"
    "branch_sign_bucket"
    "branch_priority_select"
    "branch_nested_if"
    "branch_guard_clauses"
    "branch_ternary_basic"
    "branch_ternary_nested"
    # "branch_ternary_with_side_effect"
    "branch_switch_dense"
    "branch_switch_sparse"
    "branch_switch_fallthrough"
    "branch_for_accumulate"
    "branch_continue_break"
    # "branch_while_state"
    # "branch_do_while"
    # "branch_pointer_check"
    # "branch_array_scan"
    "branch_bitmask"
    "branch_shift_sign"
    "branch_difference_check"
    "branch_sum_parity"
    "branch_multi_guard"
    "branch_probe"
    # 必要に応じて追加
)

OUTPUT_BASE_DIR="/workspaces/ghidra-docker-env/logs/equivalence_all/branch_condition_test"
BASE_PATH="/workspaces/ghidra-docker-env/targets/cate1/branch_condition_test"
PARALLEL_JOBS=${PARALLEL_JOBS:-10}  # 同時実行数。環境変数で上書き可能

# bash バージョンチェック（wait -n は 4.3+ 必須）
if (( BASH_VERSINFO[0] < 4 || ( BASH_VERSINFO[0] == 4 && BASH_VERSINFO[1] < 3 ) )); then
    echo "Error: bash 4.3 以上が必要です（現在: $BASH_VERSION）" >&2
    exit 1
fi

# ---------------------- バイナリ定義 ----------------------
declare -A BINARY_MAP=(
    [B1]="branch_condition_test-arm64-clang-O0"
    [B2]="branch_condition_test-arm64-clang-O1"
    [B3]="branch_condition_test-arm64-clang-O2"
    [B4]="branch_condition_test-arm64-clang-O3"
    [B5]="branch_condition_test-arm64-gcc-O0"
    [B6]="branch_condition_test-arm64-gcc-O1"
    [B7]="branch_condition_test-arm64-gcc-O2"
    [B8]="branch_condition_test-arm64-gcc-O3"

    [B9]="branch_condition_test-mips64-clang-O0"
    [B10]="branch_condition_test-mips64-clang-O1"
    [B11]="branch_condition_test-mips64-clang-O2"
    [B12]="branch_condition_test-mips64-clang-O3"
    [B13]="branch_condition_test-mips64-gcc-O0"
    [B14]="branch_condition_test-mips64-gcc-O1"
    [B15]="branch_condition_test-mips64-gcc-O2"
    [B16]="branch_condition_test-mips64-gcc-O3"

    # [B17]="branch_condition_test-x86_64-clang-O0"
    # [B18]="branch_condition_test-x86_64-clang-O1"
    # [B19]="branch_condition_test-x86_64-clang-O2"
    # [B20]="branch_condition_test-x86_64-clang-O3"
    # [B21]="branch_condition_test-x86_64-gcc-O0"
    # [B22]="branch_condition_test-x86_64-gcc-O1"
    # [B23]="branch_condition_test-x86_64-gcc-O2"
    # [B24]="branch_condition_test-x86_64-gcc-O3"
)

IDS=(${!BINARY_MAP[@]})
IFS=$'\n' IDS=($(sort <<<"${IDS[*]}"))
unset IFS

TOTAL_PAIRS=$(( ${#IDS[@]} * (${#IDS[@]} - 1) / 2 ))

echo "============================================================"
echo "  Equivalence Check Script (Multi-function)"
echo "============================================================"
echo "Target functions: ${TARGET_FUNCS[*]}"
echo "Number of functions: ${#TARGET_FUNCS[@]}"
echo "Pairs per function: $TOTAL_PAIRS"
echo "Parallel jobs: $PARALLEL_JOBS"
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
        -f "$TARGET_FUNC" -d \
        > "$LOG_FILE" 2>&1
    local ec=$?

    local status
    if grep -q "^Result: EQUIVALENT" "$LOG_FILE"; then
        status="EQUIVALENT ✓"
    elif grep -q "^Result: NOT EQUIVALENT" "$LOG_FILE"; then
        status="NOT EQUIVALENT ✗"
    elif grep -q "^Result: ERROR" "$LOG_FILE"; then
        status="ERROR !"
    else
        status="UNKNOWN / TIMEOUT"
    fi

    local msg="[$COUNT/$TOTAL] $ROW_ID ↔ $COL_ID : $status"
    (( ec != 0 )) && msg+="  (exit=$ec)"
    echo "$msg"
}

export -f run_pair
export BASE_PATH

classify_log_result() {
    local log_file="$1"

    if grep -q "^Result: EQUIVALENT" "$log_file"; then
        echo "EQ"
    elif grep -q "^Result: NOT EQUIVALENT" "$log_file"; then
        echo "NOT_EQ"
    elif grep -q "^Result: ERROR" "$log_file"; then
        echo "ERROR"
    else
        echo "UNKNOWN"
    fi
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

for TARGET_FUNC in "${TARGET_FUNCS[@]}"; do
    FUNC_INDEX=$((FUNC_INDEX + 1))
    
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

    # ---------------------- 結果集計 ----------------------
    # 結果集計ファイルのパス
    RESULT_FILE="${OUTPUT_DIR}/results_summary.txt"

    echo "--- Results for $TARGET_FUNC ---"

    declare -a EQ_PAIRS=()
    declare -a NON_EQ_PAIRS=()
    declare -a ERROR_PAIRS=()
    declare -a UNKNOWN_PAIRS=()

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
                *)
                UNKNOWN_PAIRS+=("$ROW_ID ↔ $COL_ID")
                ;;
            esac
        done
    done

    # --- tee を使って画面とファイルの両方に出力 ---
    shopt -s nullglob
    FUNC_LOG_FILES=("$OUTPUT_DIR"/*.log)
    shopt -u nullglob

    {
        echo "--- Results for $TARGET_FUNC ---"
        echo "  Total pairs     : ${#FUNC_LOG_FILES[@]}"
        echo "  Equivalent     : ${#EQ_PAIRS[@]}"
        echo "  Not equivalent : ${#NON_EQ_PAIRS[@]}"
        echo "  Error          : ${#ERROR_PAIRS[@]}"
        echo "  Unknown/Timeout: ${#UNKNOWN_PAIRS[@]}"

        print_phase_usage_summary_block "  " "${FUNC_LOG_FILES[@]}"
        print_pairwise_normalization_summary_block "  " "${FUNC_LOG_FILES[@]}"

        if (( ${#NON_EQ_PAIRS[@]} > 0 )); then
            echo ""
            echo "  NOT EQUIVALENT pairs:"
            for pair in "${NON_EQ_PAIRS[@]}"; do
                echo "    - $pair"
            done
        fi

        if (( ${#ERROR_PAIRS[@]} > 0 )); then
            echo ""
            echo "  ERROR pairs:"
            for pair in "${ERROR_PAIRS[@]}"; do
                echo "    - $pair"
            done
        fi

        if (( ${#UNKNOWN_PAIRS[@]} > 0 )); then
            echo ""
            echo "  UNKNOWN / TIMEOUT pairs:"
            for pair in "${UNKNOWN_PAIRS[@]}"; do
                echo "    - $pair"
            done
        fi

        if (( ${#NON_EQ_PAIRS[@]} == 0 && ${#ERROR_PAIRS[@]} == 0 && ${#UNKNOWN_PAIRS[@]} == 0 )); then
            echo ""
            echo "  ✓ All compared pairs are EQUIVALENT."
        fi

        echo ""
    } | tee "$RESULT_FILE"

done

# ---------------------- 全体サマリー ----------------------
# 全体サマリーの保存先
SUMMARY_FILE="${OUTPUT_BASE_DIR}/overall_summary.txt"

mapfile -t ALL_LOG_FILES < <(find "$OUTPUT_BASE_DIR" -type f -name "*.log" | sort)

{
    echo "============================================================"
    echo "  All functions processed: ${#TARGET_FUNCS[@]} function(s)"
    echo "============================================================"
    for TARGET_FUNC in "${TARGET_FUNCS[@]}"; do
        OUTPUT_DIR="${OUTPUT_BASE_DIR}/${TARGET_FUNC}"
        shopt -s nullglob
        FUNC_LOG_FILES=("$OUTPUT_DIR"/*.log)
        shopt -u nullglob

        eq_count=0
        non_eq_count=0
        error_count=0
        unknown_count=0
        total_logs=${#FUNC_LOG_FILES[@]}

        for LOG_FILE in "${FUNC_LOG_FILES[@]}"; do
            case "$(classify_log_result "$LOG_FILE")" in
                EQ)
                    eq_count=$((eq_count + 1))
                    ;;
                NOT_EQ)
                    non_eq_count=$((non_eq_count + 1))
                    ;;
                ERROR)
                    error_count=$((error_count + 1))
                    ;;
                *)
                    unknown_count=$((unknown_count + 1))
                    ;;
            esac
        done

        printf "  %-30s : TOTAL=%3d, EQ=%3d, NOT_EQ=%3d, ERROR=%3d, UNKNOWN=%3d\n" \
            "$TARGET_FUNC" "$total_logs" "$eq_count" "$non_eq_count" "$error_count" "$unknown_count"
    done
    print_phase_usage_summary_block "  " "${ALL_LOG_FILES[@]}"
    print_pairwise_normalization_summary_block "  " "${ALL_LOG_FILES[@]}"
    echo "============================================================"
} | tee "$SUMMARY_FILE"
