#!/usr/bin/env bash
# Compile one EqBench C source with the repository's EqBench binary naming
# convention, limited to the arm64/mips64 axes used by the equivalence matrix.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DEFAULT_TMPDIR="$SCRIPT_DIR/tmp"
if [[ -d /workspace && -w /workspace ]]; then
    DEFAULT_TMPDIR="/workspace/tmp"
fi
EQBENCH_TMPDIR="${EQBENCH_TMPDIR:-${TMPDIR:-$DEFAULT_TMPDIR}}"
mkdir -p "$EQBENCH_TMPDIR"
chmod 1777 "$EQBENCH_TMPDIR" 2>/dev/null || true
if ! tmp_probe="$(mktemp "$EQBENCH_TMPDIR/eqbench-compile.XXXXXX" 2>/dev/null)"; then
    echo "Error: cannot create temporary files in EQBENCH_TMPDIR=$EQBENCH_TMPDIR" >&2
    exit 1
fi
rm -f "$tmp_probe"
export TMPDIR="$EQBENCH_TMPDIR"
export TEMP="$EQBENCH_TMPDIR"
export TMP="$EQBENCH_TMPDIR"

SOURCE_FILE="${1:-$(find . -maxdepth 1 -type f -name '*.c' -printf '%f\n' | sort | head -n 1)}"

if [[ -z "$SOURCE_FILE" || ! -f "$SOURCE_FILE" ]]; then
    echo "Error: C source file not found" >&2
    echo "Usage: $0 [source_file.c]" >&2
    exit 1
fi

BASENAME="${SOURCE_FILE%.c}"

if grep -Eq '(^|[[:space:]])main[[:space:]]*\(' "$SOURCE_FILE"; then
    COMPILE_ONLY=0
    OUTPUT_KIND="executable"
else
    COMPILE_ONLY=1
    OUTPUT_KIND="object"
fi

ARCHITECTURES=("arm64" "mips64")
COMPILERS=("clang" "gcc")
OPTIMIZATION_LEVELS=("O0" "O1" "O2" "O3")

SUCCESS_COUNT=0
FAIL_COUNT=0

echo "========================================="
echo "EqBench compile_all.sh"
echo "========================================="
echo "Source file: $SOURCE_FILE"
echo "Output kind: $OUTPUT_KIND"
echo "Temporary directory: $EQBENCH_TMPDIR"
echo "Axes: ${ARCHITECTURES[*]} / ${COMPILERS[*]} / ${OPTIMIZATION_LEVELS[*]}"
echo "Total patterns: $((${#ARCHITECTURES[@]} * ${#COMPILERS[@]} * ${#OPTIMIZATION_LEVELS[@]}))"
echo "========================================="

for arch in "${ARCHITECTURES[@]}"; do
    for compiler in "${COMPILERS[@]}"; do
        for opt in "${OPTIMIZATION_LEVELS[@]}"; do
            OUTPUT_FILE="${BASENAME}-${arch}-${compiler}-${opt}"
            CROSS_COMPILER=""
            ARCH_ARGS=()

            case "$arch:$compiler" in
                arm64:gcc)
                    CROSS_COMPILER="aarch64-linux-gnu-gcc"
                    ARCH_ARGS=("-march=armv8-a")
                    ;;
                arm64:clang)
                    CROSS_COMPILER="clang"
                    ARCH_ARGS=("--target=aarch64-linux-gnu" "-march=armv8-a")
                    ;;
                mips64:gcc)
                    CROSS_COMPILER="mips64-linux-gnuabi64-gcc"
                    ARCH_ARGS=("-mabi=64")
                    ;;
                mips64:clang)
                    CROSS_COMPILER="clang"
                    ARCH_ARGS=("--target=mips64-linux-gnuabi64" "-mabi=64")
                    ;;
            esac

            if [[ "$COMPILE_ONLY" == "1" ]]; then
                CMD=("$CROSS_COMPILER" "${ARCH_ARGS[@]}" "-${opt}" "-c" "$SOURCE_FILE" "-o" "$OUTPUT_FILE")
            else
                CMD=("$CROSS_COMPILER" "${ARCH_ARGS[@]}" "-${opt}" "$SOURCE_FILE" "-o" "$OUTPUT_FILE")
            fi

            printf 'Compiling: %s ... ' "$OUTPUT_FILE"
            if "${CMD[@]}" > "${OUTPUT_FILE}.compile.log" 2>&1; then
                echo "ok"
                SUCCESS_COUNT=$((SUCCESS_COUNT + 1))
            else
                echo "failed"
                FAIL_COUNT=$((FAIL_COUNT + 1))
            fi
        done
    done
done

echo ""
echo "========================================="
echo "Compile result"
echo "========================================="
echo "Success: $SUCCESS_COUNT"
echo "Failed: $FAIL_COUNT"
echo "Total: $((SUCCESS_COUNT + FAIL_COUNT))"
echo "========================================="

if (( FAIL_COUNT > 0 )); then
    exit 1
fi
