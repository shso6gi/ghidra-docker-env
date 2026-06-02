#!/bin/bash

# コンパイルする.cファイルを指定（引数がなければカレントディレクトリの最初の.cファイル）
SOURCE_FILE="${1:-$(ls *.c 2>/dev/null | head -n 1)}"

# ソースファイルが存在しない場合はエラー
if [ -z "$SOURCE_FILE" ] || [ ! -f "$SOURCE_FILE" ]; then
    echo "エラー: C言語のソースファイルが見つかりません"
    echo "使用方法: $0 [source_file.c]"
    exit 1
fi

# ベースファイル名（拡張子なし）
BASENAME="${SOURCE_FILE%.c}"

# アーキテクチャの配列
ARCHITECTURES=("x86_64" "arm64" "mips64")

# コンパイラの配列
COMPILERS=("gcc" "clang")

# 最適化レベルの配列
OPTIMIZATION_LEVELS=("O0" "O1" "O2" "O3")

# コンパイル成功・失敗のカウンター
SUCCESS_COUNT=0
FAIL_COUNT=0

echo "========================================="
echo "C言語プログラム一括コンパイルスクリプト"
echo "========================================="
echo "ソースファイル: $SOURCE_FILE"
echo "合計パターン数: $((${#ARCHITECTURES[@]} * ${#COMPILERS[@]} * ${#OPTIMIZATION_LEVELS[@]}))"
echo "========================================="
echo ""

# 三重ループでコンパイル
for arch in "${ARCHITECTURES[@]}"; do
    for compiler in "${COMPILERS[@]}"; do
        for opt in "${OPTIMIZATION_LEVELS[@]}"; do
            # 出力ファイル名を生成
            OUTPUT_FILE="${BASENAME}-${arch}-${compiler}-${opt}"

            # コンパイラのフラグを設定
            CROSS_COMPILER=""
            ARCH_FLAG=""

            case "$arch" in
                "x86_64")
                    ARCH_FLAG="-m64"
                    CROSS_COMPILER="$compiler"
                    ;;
                "arm64")
                    if [ "$compiler" = "gcc" ]; then
                        CROSS_COMPILER="aarch64-linux-gnu-gcc"
                        ARCH_FLAG="-march=armv8-a"
                    else
                        CROSS_COMPILER="clang"
                        ARCH_FLAG="--target=aarch64-linux-gnu -march=armv8-a"
                    fi
                    ;;
                "mips64")
                    if [ "$compiler" = "gcc" ]; then
                        CROSS_COMPILER="mips64-linux-gnuabi64-gcc"
                        ARCH_FLAG="-mabi=64"
                    else
                        CROSS_COMPILER="clang"
                        ARCH_FLAG="--target=mips64-linux-gnuabi64 -mabi=64"
                    fi
                    ;;
            esac

            # コンパイルコマンドを構築
            COMPILE_CMD="$CROSS_COMPILER $ARCH_FLAG -${opt} $SOURCE_FILE -o $OUTPUT_FILE"

            # コンパイル実行
            echo -n "コンパイル中: $OUTPUT_FILE ... "
            if eval $COMPILE_CMD 2>/dev/null; then
                echo "✓ 成功"
                SUCCESS_COUNT=$((SUCCESS_COUNT + 1))
            else
                echo "✗ 失敗"
                FAIL_COUNT=$((FAIL_COUNT + 1))
            fi
        done
    done
done

# 生成されたファイルの一覧表示
if [ $SUCCESS_COUNT -gt 0 ]; then
    echo ""
    echo "生成されたバイナリファイル:"
    ls -lh ${BASENAME}-* 2>/dev/null | grep -v "\.c$"

echo ""
echo "========================================="
echo "コンパイル結果"
echo "========================================="
echo "成功: $SUCCESS_COUNT"
echo "失敗: $FAIL_COUNT"
echo "合計: $((SUCCESS_COUNT + FAIL_COUNT))"
echo "========================================="

fi