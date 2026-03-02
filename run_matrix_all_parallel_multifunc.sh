#!/usr/bin/env bash
# ------------------------------------------------------------
#  バイナリ間の等価性判定スクリプト（並列版・複数関数対応）
#  bash 4.3 以上が必要（wait -n を使用）
# ------------------------------------------------------------

# ---------------------- 設定 ----------------------
# 対象関数を配列で指定
TARGET_FUNCS=(
    "modulo_mixed"
    "chained_divide"
    "chained_modulo"
    "complex_arithmetic"
    "conditional_divide"
    "signed_divide_logic"
    "safe_divide"
    "divide_by_power_of_2"
    "modulo_power_of_2"
    "bitwise_and_divide"
    "unsigned_divide"
    "unsigned_modulo"
    "signed_unsigned_mix"
    "divide_int64"
    "modulo_uint64"
    "widen_divide"
    "calculate_average"
    "calculate_percentage"
    "divide_ceiling"
    "divide_round"
    "divide_by_3"
    "divide_by_7"
    "divide_by_10"
    "modulo_by_10"
    "divide_by_1000"
    "nested_divide"
    "nested_divmod"
    "compound_divide"
    "compound_modulo"
    "ternary_divide"
    "ternary_modulo"
    # 必要に応じて追加
)

OUTPUT_BASE_DIR="/workspaces/ghidra-docker-env/logs/equivalence_all/arithmetic_long_test"
BASE_PATH="/workspaces/ghidra-docker-env/targets/cate1/arithmetic_long_test"
PARALLEL_JOBS=${PARALLEL_JOBS:-32}  # 同時実行数。環境変数で上書き可能

# bash バージョンチェック（wait -n は 4.3+ 必須）
if (( BASH_VERSINFO[0] < 4 || ( BASH_VERSINFO[0] == 4 && BASH_VERSINFO[1] < 3 ) )); then
    echo "Error: bash 4.3 以上が必要です（現在: $BASH_VERSION）" >&2
    exit 1
fi

# ---------------------- バイナリ定義 ----------------------
declare -A BINARY_MAP=(
    [B1]="arithmetic_long_test-arm64-clang-O0"
    [B2]="arithmetic_long_test-arm64-clang-O1"
    [B3]="arithmetic_long_test-arm64-clang-O2"
    [B4]="arithmetic_long_test-arm64-clang-O3"
    [B5]="arithmetic_long_test-arm64-gcc-O0"
    [B6]="arithmetic_long_test-arm64-gcc-O1"
    [B7]="arithmetic_long_test-arm64-gcc-O2"
    [B8]="arithmetic_long_test-arm64-gcc-O3"

    [B9]="arithmetic_long_test-mips64-clang-O0"
    [B10]="arithmetic_long_test-mips64-clang-O1"
    [B11]="arithmetic_long_test-mips64-clang-O2"
    [B12]="arithmetic_long_test-mips64-clang-O3"
    [B13]="arithmetic_long_test-mips64-gcc-O0"
    [B14]="arithmetic_long_test-mips64-gcc-O1"
    [B15]="arithmetic_long_test-mips64-gcc-O2"
    [B16]="arithmetic_long_test-mips64-gcc-O3"

    [B17]="arithmetic_long_test-x86_64-clang-O0"
    [B18]="arithmetic_long_test-x86_64-clang-O1"
    [B19]="arithmetic_long_test-x86_64-clang-O2"
    [B20]="arithmetic_long_test-x86_64-clang-O3"
    [B21]="arithmetic_long_test-x86_64-gcc-O0"
    [B22]="arithmetic_long_test-x86_64-gcc-O1"
    [B23]="arithmetic_long_test-x86_64-gcc-O2"
    [B24]="arithmetic_long_test-x86_64-gcc-O3"
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
        -f "$TARGET_FUNC" \
        --retry-with-int \
        > "$LOG_FILE" 2>&1
    local ec=$?

    local status
    if grep -q "Result: EQUIVALENT" "$LOG_FILE"; then
        status="EQUIVALENT ✓"
    elif grep -q "Result: NOT EQUIVALENT" "$LOG_FILE"; then
        status="NOT EQUIVALENT ✗"
    else
        status="UNKNOWN / TIMEOUT"
    fi

    local msg="[$COUNT/$TOTAL] $ROW_ID ↔ $COL_ID : $status"
    (( ec != 0 )) && msg+="  (exit=$ec)"
    echo "$msg"
}

export -f run_pair
export BASE_PATH

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
    declare -a UNKNOWN_PAIRS=()

    for ((i=0; i<${#IDS[@]}-1; i++)); do
        ROW_ID="${IDS[$i]}"
        for ((j=i+1; j<${#IDS[@]}; j++)); do
            COL_ID="${IDS[$j]}"
            LOG_FILE="${OUTPUT_DIR}/${TARGET_FUNC}_${ROW_ID}_${COL_ID}.log"

            if [[ ! -f "$LOG_FILE" ]]; then
                continue
            fi

            if grep -q "Result: EQUIVALENT" "$LOG_FILE"; then
                EQ_PAIRS+=("$ROW_ID ↔ $COL_ID")
            elif grep -q "Result: NOT EQUIVALENT" "$LOG_FILE"; then
                NON_EQ_PAIRS+=("$ROW_ID ↔ $COL_ID")
            else
                UNKNOWN_PAIRS+=("$ROW_ID ↔ $COL_ID")
            fi
        done
    done

    # --- tee を使って画面とファイルの両方に出力 ---
    {
        echo "--- Results for $TARGET_FUNC ---"
        echo "  Equivalent     : ${#EQ_PAIRS[@]}"
        echo "  Not equivalent : ${#NON_EQ_PAIRS[@]}"
        echo "  Unknown/Timeout: ${#UNKNOWN_PAIRS[@]}"

        if (( ${#NON_EQ_PAIRS[@]} > 0 )); then
            echo ""
            echo "  NOT EQUIVALENT pairs:"
            for pair in "${NON_EQ_PAIRS[@]}"; do
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

        if (( ${#NON_EQ_PAIRS[@]} == 0 && ${#UNKNOWN_PAIRS[@]} == 0 )); then
            echo ""
            echo "  ✓ All compared pairs are EQUIVALENT."
        fi

        echo ""
    } | tee "$RESULT_FILE"

done

# ---------------------- 全体サマリー ----------------------
# 全体サマリーの保存先
SUMMARY_FILE="${OUTPUT_BASE_DIR}/overall_summary.txt"

{
    echo "============================================================"
    echo "  All functions processed: ${#TARGET_FUNCS[@]} function(s)"
    echo "============================================================"
    for TARGET_FUNC in "${TARGET_FUNCS[@]}"; do
        OUTPUT_DIR="${OUTPUT_BASE_DIR}/${TARGET_FUNC}"
        eq_count=$(grep -l "Result: EQUIVALENT" "$OUTPUT_DIR"/*.log 2>/dev/null | wc -l)
        non_eq_count=$(grep -l "Result: NOT EQUIVALENT" "$OUTPUT_DIR"/*.log 2>/dev/null | wc -l)
        total_logs=$(ls "$OUTPUT_DIR"/*.log 2>/dev/null | wc -l)
        unknown_count=$((total_logs - eq_count - non_eq_count))
        
        printf "  %-30s : EQ=%3d, NOT_EQ=%3d, UNKNOWN=%3d\n" \
            "$TARGET_FUNC" "$eq_count" "$non_eq_count" "$unknown_count"
    done
    echo "============================================================"
} | tee "$SUMMARY_FILE"