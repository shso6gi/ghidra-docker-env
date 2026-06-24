#!/usr/bin/env bash
# Run the small REVE/barthe f affine-loop representative set.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

DEFAULT_PYTHON_BIN="python3"
if [[ -x "$SCRIPT_DIR/.venv-pyghidra/bin/python" ]]; then
    DEFAULT_PYTHON_BIN="$SCRIPT_DIR/.venv-pyghidra/bin/python"
fi

PYTHON_BIN="${PYTHON_BIN:-$DEFAULT_PYTHON_BIN}"
OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/EqBench/benchmarks/REVE/barthe/phase3_f_affine_representatives}"
EQ_BASE_PATH="${EQ_BASE_PATH:-$SCRIPT_DIR/targets/EqBench/benchmarks/REVE/barthe/Eq/source}"
NEQ_BASE_PATH="${NEQ_BASE_PATH:-$SCRIPT_DIR/targets/EqBench/benchmarks/REVE/barthe/Neq/source}"
GENERATED_NEQ_DIR="${GENERATED_NEQ_DIR:-$OUTPUT_BASE_DIR/generated_neq}"
MANIFEST_PATH="${MANIFEST_PATH:-$SCRIPT_DIR/scripts/function_tracer_pcode/validation/barthe_f_affine_representatives.json}"
REQUIRE_NEGATIVE_BINARIES="${REQUIRE_NEGATIVE_BINARIES:-1}"

declare -A BINARY_MAP=(
    [B1]="newV-arm64-clang-O0"
    [B2]="newV-arm64-clang-O1"
    [B6]="newV-arm64-gcc-O1"
    [B8]="newV-arm64-gcc-O3"
    [B9]="newV-mips64-clang-O0"
    [B10]="newV-mips64-clang-O1"
    [B14]="newV-mips64-gcc-O1"
    [XG0]="newV-x86_64-gcc-O0"
    [XG1]="newV-x86_64-gcc-O1"
)

compile_neq_binary() {
    local binary_name="$1"
    local source_prefix="${binary_name%%-*}"
    local variant="${binary_name#${source_prefix}-}"
    local arch compiler opt
    IFS="-" read -r arch compiler opt <<< "$variant"
    local source_dir
    source_dir="$(dirname "$NEQ_BASE_PATH")"
    local source_file="$source_dir/${source_prefix}.c"
    local output_file="$GENERATED_NEQ_DIR/$binary_name"

    if [[ ! -f "$source_file" ]]; then
        echo "compile_neq=FAIL binary=$binary_name reason=missing_source source=$source_file" | tee -a "$summary_file"
        return 1
    fi

    mkdir -p "$GENERATED_NEQ_DIR"
    local compiler_cmd
    local -a flags
    case "$arch:$compiler" in
        x86_64:gcc)
            compiler_cmd="gcc"
            flags=(-m64)
            ;;
        x86_64:clang)
            compiler_cmd="clang"
            flags=(-m64)
            ;;
        arm64:gcc)
            compiler_cmd="aarch64-linux-gnu-gcc"
            flags=(-march=armv8-a)
            ;;
        arm64:clang)
            compiler_cmd="clang"
            flags=(--target=aarch64-linux-gnu -march=armv8-a)
            ;;
        mips64:gcc)
            compiler_cmd="mips64-linux-gnuabi64-gcc"
            flags=(-mabi=64)
            ;;
        mips64:clang)
            compiler_cmd="clang"
            flags=(--target=mips64-linux-gnuabi64 -mabi=64)
            ;;
        *)
            echo "compile_neq=FAIL binary=$binary_name reason=unsupported_variant variant=$variant" | tee -a "$summary_file"
            return 1
            ;;
    esac
    if ! command -v "$compiler_cmd" >/dev/null 2>&1; then
        echo "compile_neq=FAIL binary=$binary_name reason=missing_compiler compiler=$compiler_cmd" | tee -a "$summary_file"
        return 1
    fi
    if "$compiler_cmd" "${flags[@]}" "-$opt" -c "$source_file" -o "$output_file" >/dev/null 2>&1; then
        chmod +x "$output_file"
        echo "compile_neq=PASS binary=$binary_name source=$source_file output=$output_file" | tee -a "$summary_file"
        return 0
    fi
    echo "compile_neq=FAIL binary=$binary_name reason=compiler_failed compiler=$compiler_cmd" | tee -a "$summary_file"
    return 1
}

ensure_neq_binaries() {
    local left_bin="$1"
    local right_bin="$2"
    local ok=0
    compile_neq_binary "$left_bin" || ok=1
    compile_neq_binary "$right_bin" || ok=1
    return "$ok"
}

CASES=(
    "eq|B1|B6|EQUIVALENT|barthe-f-b1-b6-timeout"
    "eq|B1|B14|EQUIVALENT|barthe-f-b1-b14-sat-unsafety"
    "neq|XG0|XG1|NOT_EQ_OR_UNKNOWN|barthe-neq-f-x86_64-gcc-near-miss"
)

BACKLOG_CASES=(
    "eq|B2|B8|barthe-f-b2-b8-gcc-optimized|backlog: gcc-O3 vector accumulator prefix proof is required before this can be a sound EQ gate"
    "eq|B8|B9|barthe-f-b8-b9-optimized-cross-arch|backlog: gcc-O3 vector accumulator prefix proof is required before this can be a sound EQ gate"
    "eq|B10|B14|barthe-f-b10-b14-mips64-optimized|optional backlog: optimized MIPS shape remains outside the default smoke gate"
)

mkdir -p "$OUTPUT_BASE_DIR"

summary_file="$OUTPUT_BASE_DIR/results_summary.txt"
: > "$summary_file"

{
    echo "run_kind=barthe_f_affine_representatives"
    echo "manifest_path=$MANIFEST_PATH"
    echo "eq_base_path=$EQ_BASE_PATH"
    echo "neq_base_path=$NEQ_BASE_PATH"
    echo "generated_neq_dir=$GENERATED_NEQ_DIR"
    echo "python_bin=$PYTHON_BIN"
    echo "output_base_dir=$OUTPUT_BASE_DIR"
    echo "required_cases=${#CASES[@]}"
    echo "backlog_cases=${#BACKLOG_CASES[@]}"
    echo ""
} | tee -a "$summary_file"

failures=0
skips=0

classify_result() {
    local log_file="$1"
    if grep -q "^Result: EQUIVALENT" "$log_file"; then
        echo "EQUIVALENT"
    elif grep -q "^Result: NOT EQUIVALENT" "$log_file"; then
        echo "NOT_EQ"
    elif grep -q "^Result: TIMEOUT" "$log_file"; then
        echo "TIMEOUT"
    elif grep -q "^Result: UNKNOWN" "$log_file"; then
        echo "UNKNOWN"
    elif grep -q "^Result: ERROR" "$log_file"; then
        echo "ERROR"
    else
        echo "INCOMPLETE"
    fi
}

validate_result_json() {
    local log_file="$1"
    local expected="$2"
    local case_id="$3"
    local manifest_path="$4"
    "$PYTHON_BIN" - "$log_file" "$expected" "$case_id" "$manifest_path" <<'PY'
import json
import sys
from pathlib import Path

log_file, expected, case_id, manifest_path = sys.argv[1:5]
text = Path(log_file).read_text(encoding="utf-8", errors="replace")
begin = "=== EQUIVALENCE_RESULT_JSON_BEGIN ==="
end = "=== EQUIVALENCE_RESULT_JSON_END ==="
if begin not in text or end not in text:
    print(f"json_check=FAIL case={case_id} reason=result_json_missing")
    sys.exit(1)
payload_text = text.split(begin, 1)[1].split(end, 1)[0].strip()
try:
    payload = json.loads(payload_text)
except json.JSONDecodeError as exc:
    print(f"json_check=FAIL case={case_id} reason=result_json_unparseable detail={exc}")
    sys.exit(1)

try:
    manifest = json.loads(Path(manifest_path).read_text(encoding="utf-8"))
except (OSError, json.JSONDecodeError) as exc:
    print(f"json_check=FAIL case={case_id} reason=manifest_unreadable detail={exc}")
    sys.exit(1)

case_config = None
for section in ("positive_representatives", "negative_representatives"):
    for item in manifest.get(section, []) or []:
        if item.get("id") == case_id:
            case_config = item
            break
    if case_config is not None:
        break
if case_config is None:
    print(f"json_check=FAIL case={case_id} reason=manifest_case_missing")
    sys.exit(1)

stage_path = payload.get("stage_path") or []
pairwise_stats = payload.get("pairwise_stats") or {}
unknown_reasons = payload.get("unknown_reasons") or []
errors = []

if expected == "EQUIVALENT":
    after = case_config.get("after") or {}
    expected_stage_path = after.get("stage_path")
    expected_unknown_reasons = after.get("unknown_reasons")
    expected_pairwise_stats = after.get("pairwise_stats") or {}
    if payload.get("is_equivalent") is not True:
        errors.append(f"is_equivalent={payload.get('is_equivalent')!r}")
    if expected_stage_path is None:
        errors.append("manifest_after_stage_path_missing")
    elif stage_path != expected_stage_path:
        errors.append(f"stage_path={stage_path!r}")
    if expected_unknown_reasons is None:
        errors.append("manifest_after_unknown_reasons_missing")
    elif unknown_reasons != expected_unknown_reasons:
        errors.append(f"unknown_reasons={unknown_reasons!r}")
    for key, expected_value in expected_pairwise_stats.items():
        if int(pairwise_stats.get(key) or 0) != int(expected_value):
            errors.append(f"{key}={pairwise_stats.get(key)!r}")
    if int(pairwise_stats.get("unsat_pairs") or 0) <= 0:
        errors.append(f"unsat_pairs={pairwise_stats.get('unsat_pairs')!r}")
elif expected == "NOT_EQ_OR_UNKNOWN":
    if payload.get("is_equivalent") is True:
        errors.append("negative_promoted_to_equivalent")
    elif payload.get("is_equivalent") is None:
        expected_reason = case_config.get("expected_unknown_reason")
        if not isinstance(expected_reason, dict):
            errors.append("manifest_expected_unknown_reason_missing")
            expected_reason = {}
        if len(unknown_reasons) != 1:
            errors.append(f"unknown_reason_count={len(unknown_reasons)!r}")
        else:
            reason = unknown_reasons[0] or {}
            for key, expected_value in expected_reason.items():
                actual_value = reason.get(key)
                if actual_value != expected_value:
                    errors.append(f"{key}={actual_value!r}")
else:
    errors.append(f"unsupported_expected={expected!r}")

if errors:
    print(f"json_check=FAIL case={case_id} " + " ".join(errors))
    sys.exit(1)
print(
    f"json_check=PASS case={case_id} "
    f"is_equivalent={payload.get('is_equivalent')!r} "
    f"stage_path={stage_path!r} "
    f"pairwise_stats={pairwise_stats!r} "
    f"unknown_reasons={len(unknown_reasons)}"
)
PY
}

expectation_passed() {
    local expected="$1"
    local actual="$2"
    case "$expected" in
        EQUIVALENT)
            [[ "$actual" == "EQUIVALENT" ]]
            ;;
        NOT_EQ_OR_UNKNOWN)
            [[ "$actual" == "NOT_EQ" || "$actual" == "UNKNOWN" || "$actual" == "TIMEOUT" ]]
            ;;
        *)
            return 1
            ;;
    esac
}

for entry in "${CASES[@]}"; do
    IFS="|" read -r kind left_id right_id expected case_id <<< "$entry"
    left_bin="${BINARY_MAP[$left_id]}"
    right_bin="${BINARY_MAP[$right_id]}"
    if [[ "$kind" == "eq" ]]; then
        base_path="$EQ_BASE_PATH"
    else
        base_path="$GENERATED_NEQ_DIR"
        right_bin="${right_bin/#newV-/oldV-}"
    fi

    case_dir="$OUTPUT_BASE_DIR/$case_id"
    mkdir -p "$case_dir"
    log_file="$case_dir/f_${left_id}_${right_id}.log"

    if [[ "$kind" == "neq" ]]; then
        ensure_neq_binaries "$left_bin" "$right_bin" || true
    fi

    if [[ ! -x "$base_path/$left_bin" || ! -x "$base_path/$right_bin" ]]; then
        if [[ "$kind" == "neq" && "$REQUIRE_NEGATIVE_BINARIES" != "0" ]]; then
            message="FAIL $case_id $left_id/$right_id negative_unavailable missing binaries under $base_path"
            failures=$((failures + 1))
        else
            message="SKIP $case_id $left_id/$right_id missing binaries under $base_path"
        fi
        echo "$message" | tee -a "$summary_file"
        skips=$((skips + 1))
        continue
    fi

    set +e
    "$PYTHON_BIN" -m scripts.function_tracer_pcode.cli.main \
        --equiv "$base_path/$left_bin" "$base_path/$right_bin" \
        -f f -d --emit-result-json \
        > "$log_file" 2>&1
    command_status=$?
    set -e

    actual="$(classify_result "$log_file")"
    json_check_output=""
    json_check_status=1
    if expectation_passed "$expected" "$actual"; then
        set +e
        json_check_output="$(validate_result_json "$log_file" "$expected" "$case_id" "$MANIFEST_PATH" 2>&1)"
        json_check_status=$?
        set -e
    fi
    if expectation_passed "$expected" "$actual" && [[ "$json_check_status" -eq 0 ]]; then
        status="PASS"
    else
        status="FAIL"
        failures=$((failures + 1))
    fi
    if [[ -n "$json_check_output" ]]; then
        echo "$json_check_output" | tee -a "$summary_file"
    fi
    echo "$status $case_id $left_id/$right_id expected=$expected actual=$actual exit=$command_status log=$log_file" | tee -a "$summary_file"
done

for entry in "${BACKLOG_CASES[@]}"; do
    IFS="|" read -r kind left_id right_id case_id note <<< "$entry"
    echo "BACKLOG_NOT_RUN $case_id $left_id/$right_id kind=$kind note=$note" | tee -a "$summary_file"
done

{
    echo ""
    echo "Summary: failures=$failures skips=$skips output=$OUTPUT_BASE_DIR"
} | tee -a "$summary_file"

if (( failures > 0 )); then
    exit 1
fi
