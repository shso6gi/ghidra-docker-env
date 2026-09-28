#!/usr/bin/env bash
# NeqBench primary NOT_EQ evaluation: changed/caller-closure functions and
# same-ISA pairs (8 x 8 ARM64 plus 8 x 8 MIPS64 = 128 pairs/function).

set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"
source "$SCRIPT_DIR/scripts/validation_matrix_common.sh"
source "$SCRIPT_DIR/scripts/eqbench/pair_scheduler.sh"

default_value() {
    local name="$1" value="$2"
    if [[ ! -v "$name" ]]; then printf -v "$name" '%s' "$value"; fi
}
if [[ -x "$SCRIPT_DIR/.venv-pyghidra/bin/python" ]]; then PYTHON_BIN="$SCRIPT_DIR/.venv-pyghidra/bin/python"; else default_value PYTHON_BIN python3; fi
default_value NEQ_ROOT "$SCRIPT_DIR/targets/EqBench/benchmarks"
default_value OUTPUT_BASE_DIR "$SCRIPT_DIR/logs/EqBench/all_neq_same_isa_closure_current"
default_value NEQ_RUN_SCOPE FULL_NEQ
default_value NEQ_BUILD_POLICY REUSE_OR_COMPILE
default_value NEQ_SAMPLE_FILTER ""
default_value NEQ_MAX_SAMPLES 0
default_value NEQ_PAIR_FILTER ""
default_value NEQ_RERUN_MANIFEST ""
default_value ERROR_RERUN_RUN_ID ""
default_value PARALLEL_JOBS 32
default_value EQBENCH_RESOURCE_ADMISSION 1
default_value EQBENCH_CPU_TOKENS "$(getconf _NPROCESSORS_ONLN 2>/dev/null || nproc 2>/dev/null || printf 1)"
default_value EQBENCH_PAIR_CPU_TOKENS 8
default_value EQBENCH_DEBUG 0
default_value SKIP_COMPLETED_RESULTS 1
default_value ERROR_ONLY_RERUN 0
# Issue #15: 0 passes --no-identical-fast-path, so byte-identical inputs go
# through the ordinary pipeline (the oracle).  Part of the analysis config
# identity, so an ON pair status is never reused for an OFF run.
default_value EQBENCH_IDENTICAL_FAST_PATH 1
default_value DRY_RUN 0
default_value EQUIV_TIMEOUT 10
default_value DECOMPILE_TIMEOUT 60
default_value PAIRWISE_TIMEOUT 5
default_value PAIRWISE_TIMEOUT_HARD 30
# Issue #131: 共通 dedup のケース数上限。既定は本番と同じ 16。
# 要求値と実効値を分けて持つ（規則は解析器側と 1 本化。Eq runner と同じ扱い）。
FT_EXPANDER_DEDUP_CASE_LIMIT_REQUESTED="${FT_EXPANDER_DEDUP_CASE_LIMIT-}"
FT_EXPANDER_DEDUP_CASE_LIMIT="$(validation_positive_int_setting \
    "$FT_EXPANDER_DEDUP_CASE_LIMIT_REQUESTED" 16)"
export FT_EXPANDER_DEDUP_CASE_LIMIT
# Issue #47 (PR-B): eligible external placeholder callee の束縛ゼロ解析再利用と、その
# shadow validation。既定は解析器と同じ（再利用 ON / shadow OFF）。shadow は回帰検査用で、
# 有効にすると従来解析も併走するため削減効果は測れない。
FT_CALLEE_UNBOUND_REUSE="${FT_CALLEE_UNBOUND_REUSE:-1}"
FT_CALLEE_UNBOUND_REUSE_SHADOW="${FT_CALLEE_UNBOUND_REUSE_SHADOW:-0}"
export FT_CALLEE_UNBOUND_REUSE FT_CALLEE_UNBOUND_REUSE_SHADOW
default_value PAIR_PROCESS_TIMEOUT 600s
default_value PAIR_PROCESS_KILL_AFTER 30s
# Issue #124 PR-124-C: deadline の何秒前に stack dump を要求するか（診断のみ）。
# deadline の総予算・起点・kill 手順はこの値で変わらない。
default_value PAIR_STACK_DUMP_LEAD 2s
default_value VALIDATION_SUMMARY_LEVEL compact
if [[ ! -v EQBENCH_TMPDIR ]]; then
    if [[ -d /workspace && -w /workspace ]]; then EQBENCH_TMPDIR=/workspace/tmp; else EQBENCH_TMPDIR="$SCRIPT_DIR/tmp"; fi
fi
default_value EQBENCH_PRIVATE_AUTHORITY_ROOT "$EQBENCH_TMPDIR/eqbench-private-authority-neq"
COMPILE_TEMPLATE="$SCRIPT_DIR/scripts/eqbench/compile_all_arm_mips.sh"
FUNCTION_LISTER="$SCRIPT_DIR/scripts/eqbench/list_c_functions.py"
FUNCTION_SELECTOR="$SCRIPT_DIR/scripts/eqbench/select_neq_functions.py"
EXPECTED_FULL_SOURCE_PAIRS=125

[[ "$NEQ_RUN_SCOPE" == FULL_NEQ || "$NEQ_RUN_SCOPE" == REPRESENTATIVE ]] || exit 1
[[ "$NEQ_BUILD_POLICY" == REUSE_OR_COMPILE || "$NEQ_BUILD_POLICY" == FRESH_ONLY ]] || exit 1
[[ "$NEQ_MAX_SAMPLES" =~ ^[0-9]+$ && "$PARALLEL_JOBS" =~ ^[1-9][0-9]*$ ]] || exit 1
[[ "$SKIP_COMPLETED_RESULTS" =~ ^[01]$ && "$ERROR_ONLY_RERUN" =~ ^[01]$ ]] || exit 1
[[ "$EQBENCH_IDENTICAL_FAST_PATH" =~ ^[01]$ ]] || { echo "EQBENCH_IDENTICAL_FAST_PATH must be 0 or 1" >&2; exit 1; }
[[ -f "$COMPILE_TEMPLATE" && -f "$FUNCTION_LISTER" && -f "$FUNCTION_SELECTOR" ]] || exit 1
NEQ_ROOT="$(realpath -m "$NEQ_ROOT")"
case "$NEQ_ROOT" in "$SCRIPT_DIR"/*) ;; *) echo "NEQ_ROOT must be inside repository" >&2; exit 1 ;; esac
[[ -d "$NEQ_ROOT" ]] || exit 1
if [[ "$NEQ_RUN_SCOPE" == FULL_NEQ && "$NEQ_MAX_SAMPLES" != 0 ]]; then exit 1; fi
if [[ "$NEQ_RUN_SCOPE" == FULL_NEQ && ( -n "$NEQ_SAMPLE_FILTER" || -n "$NEQ_PAIR_FILTER" ) ]]; then exit 1; fi
PAIR_PROCESS_TIMEOUT_SECONDS="$(printf '%s' "$PAIR_PROCESS_TIMEOUT" | sed 's/s$//')"
PAIR_PROCESS_KILL_AFTER_SECONDS="$(printf '%s' "$PAIR_PROCESS_KILL_AFTER" | sed 's/s$//')"
PAIR_STACK_DUMP_LEAD_SECONDS="$(printf '%s' "$PAIR_STACK_DUMP_LEAD" | sed 's/s$//')"

RESOURCE_ADMISSION_JOBS="$EQBENCH_CPU_TOKENS"
if (( EQBENCH_RESOURCE_ADMISSION == 1 )); then
    RESOURCE_ADMISSION_JOBS=$((EQBENCH_CPU_TOKENS / EQBENCH_PAIR_CPU_TOKENS))
    (( RESOURCE_ADMISSION_JOBS > 0 )) || RESOURCE_ADMISSION_JOBS=1
    (( PARALLEL_JOBS <= RESOURCE_ADMISSION_JOBS )) || PARALLEL_JOBS="$RESOURCE_ADMISSION_JOBS"
fi

IDS="B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15 B16"
SAME_ISA_GROUPS=("B1 B2 B3 B4 B5 B6 B7 B8" "B9 B10 B11 B12 B13 B14 B15 B16")
BINARY_ID_ARGS=()
for id in $IDS; do BINARY_ID_ARGS+=(--binary-id "$id"); done
binary_name() {
    local variant="$1" id="$2" arch compiler opt
    case "$id" in
        B1) arch=arm64; compiler=clang; opt=O0 ;; B2) arch=arm64; compiler=clang; opt=O1 ;;
        B3) arch=arm64; compiler=clang; opt=O2 ;; B4) arch=arm64; compiler=clang; opt=O3 ;;
        B5) arch=arm64; compiler=gcc; opt=O0 ;; B6) arch=arm64; compiler=gcc; opt=O1 ;;
        B7) arch=arm64; compiler=gcc; opt=O2 ;; B8) arch=arm64; compiler=gcc; opt=O3 ;;
        B9) arch=mips64; compiler=clang; opt=O0 ;; B10) arch=mips64; compiler=clang; opt=O1 ;;
        B11) arch=mips64; compiler=clang; opt=O2 ;; B12) arch=mips64; compiler=clang; opt=O3 ;;
        B13) arch=mips64; compiler=gcc; opt=O0 ;; B14) arch=mips64; compiler=gcc; opt=O1 ;;
        B15) arch=mips64; compiler=gcc; opt=O2 ;; B16) arch=mips64; compiler=gcc; opt=O3 ;;
        *) return 1 ;;
    esac
    printf '%s-%s-%s-%s' "$variant" "$arch" "$compiler" "$opt"
}
ANALYSIS_PAIR_IDS=()
for same_isa_group in "${SAME_ISA_GROUPS[@]}"; do
    for left_binary_id in $same_isa_group; do
        for right_binary_id in $same_isa_group; do
            ANALYSIS_PAIR_IDS+=("N_${left_binary_id}_O_${right_binary_id}")
        done
    done
done
declare -A ANALYSIS_PAIR_SET=()
for analysis_pair in "${ANALYSIS_PAIR_IDS[@]}"; do
    ANALYSIS_PAIR_SET["$analysis_pair"]=1
done
if [[ -n "$NEQ_PAIR_FILTER" ]]; then
    IFS=',' read -r -a requested_pairs <<< "$NEQ_PAIR_FILTER"
    for requested_pair in "${requested_pairs[@]}"; do
        [[ -n "${ANALYSIS_PAIR_SET[$requested_pair]:-}" ]] || {
            echo "NEQ_PAIR_FILTER contains a non-primary-matrix pair: $requested_pair" >&2
            exit 1
        }
    done
fi
pair_selected() { [[ -z "$NEQ_PAIR_FILTER" || ",$NEQ_PAIR_FILTER," == *",$1,"* ]]; }
declare -A NEQ_RERUN_TARGETS=()
ERROR_RERUN_MANIFEST_SHA256=""
if [[ -n "$NEQ_RERUN_MANIFEST" ]]; then
    [[ -s "$NEQ_RERUN_MANIFEST" ]] || {
        echo "NEQ_RERUN_MANIFEST is not a non-empty file" >&2
        exit 1
    }
    while IFS=$'\t' read -r lane sample function pair; do
        [[ "$lane" == "NEQ" && -n "$sample" && -n "$function" && -n "$pair" ]] || continue
        NEQ_RERUN_TARGETS["$sample|$function|$pair"]=1
    done < "$NEQ_RERUN_MANIFEST"
    (( ${#NEQ_RERUN_TARGETS[@]} > 0 )) || {
        echo "rerun manifest contains no NeqBench targets" >&2
        exit 1
    }
    ERROR_RERUN_MANIFEST_SHA256="$(sha256sum "$NEQ_RERUN_MANIFEST" | awk '{print $1}')"
    [[ -n "$ERROR_RERUN_RUN_ID" ]] || {
        echo "ERROR_RERUN_RUN_ID is required for a rerun manifest" >&2
        exit 1
    }
fi
rerun_target_selected() {
    local sample="$1" function="$2" pair="$3"
    [[ -z "$NEQ_RERUN_MANIFEST" ]] && return 0
    [[ -n "${NEQ_RERUN_TARGETS[$sample|$function|$pair]:-}" ]]
}
supervisor_projection_is_terminal() {
    "$PYTHON_BIN" -c \
        'import json,sys; p=json.load(open(sys.argv[1])); raise SystemExit(0 if p.get("status") in {"RESOLVED","TIMEOUT","ERROR"} else 1)' \
        "$1" 2>/dev/null
}
pair_count() {
    local count=0 pair
    for pair in "${ANALYSIS_PAIR_IDS[@]}"; do
        pair_selected "$pair" && count=$((count + 1))
    done
    printf '%s\n' "$count"
}
rerun_pair_count() {
    local sample="$1" function="$2" count=0 pair
    for pair in "${ANALYSIS_PAIR_IDS[@]}"; do
        pair_selected "$pair" || continue
        rerun_target_selected "$sample" "$function" "$pair" || continue
        count=$((count + 1))
    done
    printf '%s\n' "$count"
}

EXPECTED_PAIRS_PER_FUNCTION="$(pair_count)"

mkdir -p "$EQBENCH_TMPDIR"; chmod 1777 "$EQBENCH_TMPDIR" 2>/dev/null || true
probe="$(mktemp "$EQBENCH_TMPDIR/neqbench-tmp.XXXXXX")"; rm -f "$probe"
export TMPDIR="$EQBENCH_TMPDIR" TEMP="$EQBENCH_TMPDIR" TMP="$EQBENCH_TMPDIR"
RUN_TMP="$(mktemp -d "$EQBENCH_TMPDIR/neqbench-run.XXXXXX")"
cleanup() { [[ -d "$RUN_TMP" ]] && rm -rf -- "$RUN_TMP"; }
trap cleanup EXIT
trap 'exit 129' HUP; trap 'exit 130' INT; trap 'exit 143' TERM

mkdir -p "$OUTPUT_BASE_DIR"; OUTPUT_BASE_DIR="$(realpath -m "$OUTPUT_BASE_DIR")"
if [[ -s "$OUTPUT_BASE_DIR/run_manifest.txt" ]] \
    && grep -q '^run_kind=neqbench_all_cross_matrix_current$' "$OUTPUT_BASE_DIR/run_manifest.txt"; then
    echo "Existing output uses the old 256-pair cross-ISA scope: $OUTPUT_BASE_DIR" >&2
    echo "Use a fresh OUTPUT_BASE_DIR for the same-ISA caller-closure evaluation." >&2
    exit 1
fi
# Issue #170: keyset（秘密鍵の置き場所）は共通の owner が組み立てて判定する（正規化した private
# root の直下の 1 component で、OUTPUT と分離している。`//`、`..`、相対 path、symlink の綴りでも
# 秘密鍵が OUTPUT に書かれない）。runner は root/id を自分で組み立てない。
KEYSET="$(printf '%s' "$OUTPUT_BASE_DIR" | sha256sum | awk '{print $1}')"
AUTHORITY_ROOT="$(validation_resolve_authority_keyset \
    "$EQBENCH_PRIVATE_AUTHORITY_ROOT" "$KEYSET" "$OUTPUT_BASE_DIR")" || exit 1
CENSUS="$OUTPUT_BASE_DIR/neq_source_pairs.tsv"; : > "$CENSUS"
SOURCE_PAIR_COUNT=0
while IFS= read -r dir; do
    [[ -n "$dir" ]] || continue
    rel="$(printf '%s' "$dir" | sed "s#^$NEQ_ROOT/##")"
    if [[ -f "$dir/newV.c" && -f "$dir/oldV.c" ]]; then new=newV; old=oldV
    elif [[ -f "$dir/new.c" && -f "$dir/old.c" ]]; then new=new; old=old
    else echo "Incomplete Neq pair: $dir" >&2; exit 1; fi
    label="$rel/$new-$old"
    [[ -z "$NEQ_SAMPLE_FILTER" || "$label" =~ $NEQ_SAMPLE_FILTER ]] || continue
    SOURCE_PAIR_COUNT=$((SOURCE_PAIR_COUNT + 1))
    printf '%s\t%s\t%s\n' "$label" "$dir/$new.c" "$dir/$old.c" >> "$CENSUS"
    if (( NEQ_MAX_SAMPLES > 0 && SOURCE_PAIR_COUNT >= NEQ_MAX_SAMPLES )); then break; fi
done < <(find "$NEQ_ROOT" -type d -name Neq -print | sort)
(( SOURCE_PAIR_COUNT > 0 )) || exit 1
if [[ "$NEQ_RUN_SCOPE" == FULL_NEQ && "$SOURCE_PAIR_COUNT" != "$EXPECTED_FULL_SOURCE_PAIRS" ]]; then
    echo "FULL_NEQ source census must contain exactly $EXPECTED_FULL_SOURCE_PAIRS source pairs; got $SOURCE_PAIR_COUNT" >&2
    exit 1
fi
CENSUS_DIGEST="$(sha256sum "$CENSUS" | awk '{print $1}')"
PREFILTER_SOURCE_CENSUS_FILE="$OUTPUT_BASE_DIR/prefilter_source_paths.txt"
cut -f1 "$CENSUS" > "$PREFILTER_SOURCE_CENSUS_FILE"
PREFILTER_SOURCE_CENSUS_DIGEST="$(sha256sum "$PREFILTER_SOURCE_CENSUS_FILE" | awk '{print $1}')"

FUNCTION_SELECTION_CENSUS_FILE="$OUTPUT_BASE_DIR/neq_function_selection.tsv"
FUNCTION_SELECTION_FAILURES_FILE="$OUTPUT_BASE_DIR/function_selection_failures.txt"
: > "$FUNCTION_SELECTION_CENSUS_FILE"
: > "$FUNCTION_SELECTION_FAILURES_FILE"
printf 'sample\tall_functions\tchanged_functions\tcaller_closure_functions\tselected_functions\n' \
    > "$FUNCTION_SELECTION_CENSUS_FILE"
TOTAL_PLANNED_FUNCTIONS=0
TOTAL_PLANNED_PAIR_JOBS=0
FUNCTION_SELECTION_INDEX=0
while IFS="$(printf '\t')" read -r sample new_source old_source; do
    [[ -n "$sample" ]] || continue
    FUNCTION_SELECTION_INDEX=$((FUNCTION_SELECTION_INDEX + 1))
    selection_dir="$OUTPUT_BASE_DIR/$sample"
    mkdir -p "$selection_dir"
    if ! "$PYTHON_BIN" "$FUNCTION_SELECTOR" \
        --new-source "$new_source" --old-source "$old_source" \
        --all-output "$selection_dir/functions.all.txt" \
        --changed-output "$selection_dir/changed_functions.txt" \
        --caller-output "$selection_dir/caller_closure.txt" \
        --selected-output "$selection_dir/functions.txt" \
        > "$selection_dir/function-selection-summary.txt" \
        2> "$selection_dir/function-selection.error"; then
        printf '%s\n' "$sample" >> "$FUNCTION_SELECTION_FAILURES_FILE"
        echo "Function selection failed for $sample; see $selection_dir/function-selection.error" >&2
        exit 1
    fi
    all_function_count="$(wc -l < "$selection_dir/functions.all.txt")"
    changed_function_count="$(wc -l < "$selection_dir/changed_functions.txt")"
    caller_closure_count="$(wc -l < "$selection_dir/caller_closure.txt")"
    selected_function_count="$(wc -l < "$selection_dir/functions.txt")"
    printf '%s\t%s\t%s\t%s\t%s\n' \
        "$sample" "$all_function_count" "$changed_function_count" \
        "$caller_closure_count" "$selected_function_count" \
        >> "$FUNCTION_SELECTION_CENSUS_FILE"
    TOTAL_PLANNED_FUNCTIONS=$((TOTAL_PLANNED_FUNCTIONS + selected_function_count))
    TOTAL_PLANNED_PAIR_JOBS=$((TOTAL_PLANNED_PAIR_JOBS + selected_function_count * EXPECTED_PAIRS_PER_FUNCTION))
    printf '[SELECTION %s/%s] %s: all=%s changed=%s caller_closure=%s selected=%s\n' \
        "$FUNCTION_SELECTION_INDEX" "$SOURCE_PAIR_COUNT" "$sample" \
        "$all_function_count" "$changed_function_count" \
        "$caller_closure_count" "$selected_function_count"
done < "$CENSUS"
if [[ -n "$NEQ_RERUN_MANIFEST" ]]; then
    TOTAL_PLANNED_PAIR_JOBS=${#NEQ_RERUN_TARGETS[@]}
    TOTAL_PLANNED_FUNCTIONS="$(awk -F '\t' '$1 == "NEQ" {seen[$2 FS $3]=1} END {print length(seen)}' "$NEQ_RERUN_MANIFEST")"
fi
FUNCTION_SELECTION_CENSUS_DIGEST="$(sha256sum "$FUNCTION_SELECTION_CENSUS_FILE" | awk '{print $1}')"

if (( DRY_RUN == 1 )); then
    cp "$CENSUS" "$OUTPUT_BASE_DIR/dry_run_sources.txt"
    echo "selected_sources=$SOURCE_PAIR_COUNT"
    echo "selected_functions=$TOTAL_PLANNED_FUNCTIONS"
    echo "planned_pair_jobs=$TOTAL_PLANNED_PAIR_JOBS"
    echo "pairs_per_function=$EXPECTED_PAIRS_PER_FUNCTION"
    exit 0
fi

SUPERVISOR_KEY_ID=eqbench-neq-supervisor-v1; WORKER_KEY_ID=eqbench-neq-worker-v1
SUPERVISOR_KEY="$AUTHORITY_ROOT/supervisor.key"; WORKER_KEY="$AUTHORITY_ROOT/worker.key"
PAIR_PRIVATE_KEY="$AUTHORITY_ROOT/pair-status-ed25519.key"; PAIR_PUBLIC_KEY="$OUTPUT_BASE_DIR/pair-status-verification-key.json"
# Issue #170: 鍵を読む・書く・検証する区間だけ keyset の lock を保持する（窓の中で `&` を使わない）。
validation_lock_authority_keyset "$AUTHORITY_ROOT" "$OUTPUT_BASE_DIR" || exit 1
existing_status="$(find "$OUTPUT_BASE_DIR" -type f -name '*.pair-status.json' -print -quit)"
if [[ -n "$existing_status" && ( ! -s "$SUPERVISOR_KEY" || ! -s "$WORKER_KEY" || ! -s "$PAIR_PRIVATE_KEY" || ! -s "$PAIR_PUBLIC_KEY" ) ]]; then
    echo "Existing Neq authority evidence has no complete retained keyset" >&2
    exit 1
fi
PROCESS_KEY_WRITTEN=0
[[ -s "$SUPERVISOR_KEY" && -s "$WORKER_KEY" ]] || PROCESS_KEY_WRITTEN=1
validation_materialize_process_key "$SUPERVISOR_KEY" || exit 1
validation_materialize_process_key "$WORKER_KEY" || exit 1
validation_materialize_pair_status_keypair "$PYTHON_BIN" "$PAIR_PRIVATE_KEY" "$PAIR_PUBLIC_KEY" || exit 1
validation_unlock_authority_keyset || exit 1
# HMAC 鍵を新しく書いた run は、以降の書き込みも umask 077 で行う（main と同じ）。
if (( PROCESS_KEY_WRITTEN == 1 )); then umask 077; fi

PROCESS_CLEANUP_FAILURES="$OUTPUT_BASE_DIR/process_authority_cleanup_failures.txt"; : > "$PROCESS_CLEANUP_FAILURES"
# Issue #124 PR-124-C: cleanup 前に確認した dump 退避状態（診断のみ。cleanup 失敗
# の file とは別。あちらは run を止める判定と receipt の hash に使われる）。
STACK_DUMP_ARTIFACT_STATE_FILE="$OUTPUT_BASE_DIR/stack_dump_artifact_state.tsv"; : > "$STACK_DUMP_ARTIFACT_STATE_FILE"
EXPECTED_STATUS="$OUTPUT_BASE_DIR/expected_pair_status_paths.txt"; : > "$EXPECTED_STATUS"
VERIFIED_SKIPPED_STATUS="$OUTPUT_BASE_DIR/verified_skipped_pair_status_paths.txt"; : > "$VERIFIED_SKIPPED_STATUS"
COMPILE_FAILURE_SAMPLES_FILE="$OUTPUT_BASE_DIR/compile_failure_samples.txt"; : > "$COMPILE_FAILURE_SAMPLES_FILE"
MISSING_BINARY_AXES_FILE="$OUTPUT_BASE_DIR/missing_binary_axes.txt"; : > "$MISSING_BINARY_AXES_FILE"
FUNCTION_CENSUS_FAILURES_FILE="$OUTPUT_BASE_DIR/function_census_failures.txt"; : > "$FUNCTION_CENSUS_FAILURES_FILE"
USED_BUILD_RECEIPTS_FILE="$OUTPUT_BASE_DIR/used_build_receipts.jsonl"; : > "$USED_BUILD_RECEIPTS_FILE"

write_source_manifest() {
    local out="$1" new_source="$2" old_source="$3" tmp="$1.tmp.$$"
    "$PYTHON_BIN" - "$tmp" "$out" "$SCRIPT_DIR" "$new_source" "$old_source" <<'PY'
import hashlib, json, os, sys
from pathlib import Path
tmp, out, repo, new_path, old_path = sys.argv[1:]
root = Path(repo).resolve()
def item(kind, raw):
    path = Path(raw).resolve(strict=True)
    return {"variant": kind, "path": path.relative_to(root).as_posix(), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
data = {"schema": "neq-source-pair-manifest-v1", "sources": [item("new", new_path), item("old", old_path)]}
with open(tmp, "w", encoding="utf-8") as f:
    json.dump(data, f, indent=2, sort_keys=True); f.write("\n"); f.flush(); os.fsync(f.fileno())
os.replace(tmp, out)
PY
}
record_missing_variant_axes() {
    local sample="$1" variant="$2" source_dir="$3" id name
    for id in $IDS; do
        name="$(binary_name "$variant" "$id")"
        if [[ ! -f "$source_dir/$name" ]]; then
            printf '%s/%s/%s\n' "$sample" "$variant" "$id" >> "$MISSING_BINARY_AXES_FILE"
            MISSING_BINARY_COUNT=$((MISSING_BINARY_COUNT + 1))
        fi
    done
}

prepare_variant() {
    local source="$1" variant="$2" source_dir="$3" sample="$4"
    local build_dir build_receipt_file receipt_json id name install_failed
    local require_fresh_args=()
    VARIANT_BUILD_RECEIPT_JSON=""
    VARIANT_BUILD_RESOLUTION=""
    build_receipt_file="$source_dir/.$variant.eqbench-build-receipt.json"
    if [[ "$NEQ_RUN_SCOPE" == FULL_NEQ ]]; then
        require_fresh_args+=(--require-fresh)
    fi

    if [[ "$NEQ_BUILD_POLICY" != FRESH_ONLY && -s "$build_receipt_file" ]]; then
        if receipt_json="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.eqbench_build_receipt \
            --repo-root "$SCRIPT_DIR" --receipt "$build_receipt_file" --validate \
            "${require_fresh_args[@]}" "${BINARY_ID_ARGS[@]}" 2>/dev/null)"; then
            VARIANT_BUILD_RECEIPT_JSON="$receipt_json"
            VARIANT_BUILD_RESOLUTION=VERIFIED_RECEIPT_REUSE
            return 0
        fi
    fi

    if [[ "$NEQ_BUILD_POLICY" != FRESH_ONLY && "$NEQ_RUN_SCOPE" == REPRESENTATIVE ]]; then
        install_failed=0
        for id in $IDS; do
            name="$(binary_name "$variant" "$id")"
            [[ -f "$source_dir/$name" ]] || { install_failed=1; break; }
        done
        if (( install_failed == 0 )); then
            if receipt_json="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.eqbench_build_receipt \
                --repo-root "$SCRIPT_DIR" --receipt "$build_receipt_file" --materialize \
                --provenance-kind ADOPTED_PREBUILT --sample-identity "$sample/$variant" \
                --source "$source" --compile-script "$COMPILE_TEMPLATE" \
                --binary-root "$source_dir" --target-binary-root "$source_dir" \
                "${BINARY_ID_ARGS[@]}")"; then
                VARIANT_BUILD_RECEIPT_JSON="$receipt_json"
                VARIANT_BUILD_RESOLUTION=ADOPTED_PREBUILT
                return 0
            fi
        fi
    fi

    build_dir="$RUN_TMP/build/$CURRENT_PAIR_INDEX/$variant"
    mkdir -p "$build_dir"
    cp "$source" "$build_dir/$variant.c"
    cp "$COMPILE_TEMPLATE" "$build_dir/compile_all.sh"
    chmod +x "$build_dir/compile_all.sh"
    if ! (cd "$build_dir" && ./compile_all.sh "$variant.c") > "$OUTPUT_SAMPLE/compile_$variant.log" 2>&1; then
        return 1
    fi
    for id in $IDS; do
        name="$(binary_name "$variant" "$id")"
        cp "$build_dir/$name" "$source_dir/.$name.new"
        mv -f "$source_dir/.$name.new" "$source_dir/$name"
    done
    if ! receipt_json="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.eqbench_build_receipt \
        --repo-root "$SCRIPT_DIR" --receipt "$build_receipt_file" --materialize \
        --provenance-kind FRESH_COMPILE --sample-identity "$sample/$variant" \
        --source "$source" --compile-script "$COMPILE_TEMPLATE" \
        --binary-root "$build_dir" --target-binary-root "$source_dir" \
        "${BINARY_ID_ARGS[@]}")"; then
        return 1
    fi
    VARIANT_BUILD_RECEIPT_JSON="$receipt_json"
    VARIANT_BUILD_RESOLUTION=FRESH_COMPILE
}

pair_status_is_skippable_for_run_mode() {
    local log="$1" target="$2" status mode decision
    status="$(printf '%s' "$log" | sed 's/\.log$/.pair-status.json/')"
    [[ -s "$log" && -s "$status" ]] || return 1
    if [[ "$ERROR_ONLY_RERUN" == 1 ]]; then mode=ERROR_ONLY; else mode=NORMAL_RESUME; fi
    if decision="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.authority.decision.pair_status_authority \
        --validate-pair-status "$status" \
        --pair-log "$log" \
        --public-key "$PAIR_PUBLIC_KEY" \
        --expected-pair-target "$target" \
        "${PAIR_STATUS_RESUME_COMPAT_ARGS[@]}" \
        --resume-skip-mode "$mode" 2>/dev/null)"; then
        [[ "$decision" == SKIP ]] && return 0
    fi
    if [[ "$ERROR_ONLY_RERUN" == 1 ]] \
        && [[ "$("$PYTHON_BIN" -m scripts.function_tracer_pcode.authority.decision.pair_status_authority \
            --legacy-pair-target-match "$status" --expected-pair-target "$target" \
            2>/dev/null)" == MATCH ]] \
        && legacy_outcome="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.result_summary \
            --classify-log --allow-legacy-log "$log" 2>/dev/null)"; then
        case "$legacy_outcome" in
            EQ|NOT_EQ|UNKNOWN|TIMEOUT) return 0 ;;
        esac
    fi
    return 1
}
function_summary_all_pairs_reusable() {
    local function_dir="$1" expected="$2" summary="$1/results_summary.txt"
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
    local log="$1" status="$2"
    [[ -s "$log" && -s "$status" ]] || return 1
    "$PYTHON_BIN" -c 'import json, sys; value=json.load(open(sys.argv[1], encoding="utf-8")); sys.exit(0 if isinstance(value, dict) else 1)' \
        "$status" >/dev/null 2>&1
}
declare -A SUMMARY_ERROR_PAIRS=()
SUMMARY_ERROR_PAIRS_READY=0

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
        --error-pairs --matrix NEQ "$summary")
    if (( ${#error_pairs[@]} != error_count )); then
        echo "ERROR-only summary census mismatch: $summary (count=$error_count parsed=${#error_pairs[@]})" >&2
        return 1
    fi
    local pair
    for pair in "${error_pairs[@]}"; do SUMMARY_ERROR_PAIRS["$pair"]=1; done
    SUMMARY_ERROR_PAIRS_READY=1
}
progress_update() {
    local sample="$1" function="$2" left_id="$3" right_id="$4" status="$5"
    {
        flock -x 9
        local completed remaining
        completed="$(cat "$PROGRESS_COUNT_FILE")"
        completed=$((completed + 1))
        printf '%s\n' "$completed" > "$PROGRESS_COUNT_FILE"
        remaining=$((TOTAL_PLANNED_PAIR_JOBS - completed))
        printf '[PROGRESS] completed=%s/%s remaining=%s sample=%s function=%s pair=%s<->%s status=%s\n' \
            "$completed" "$TOTAL_PLANNED_PAIR_JOBS" "$remaining" \
            "$sample" "$function" "$left_id" "$right_id" "$status"
    } 9>"$PROGRESS_LOCK_FILE"
}
progress_skip_function() {
    local sample="$1" function="$2" count="$3"
    {
        flock -x 9
        local completed remaining
        completed="$(cat "$PROGRESS_COUNT_FILE")"
        completed=$((completed + count))
        printf '%s\n' "$completed" > "$PROGRESS_COUNT_FILE"
        remaining=$((TOTAL_PLANNED_PAIR_JOBS - completed))
        printf '[PROGRESS] completed=%s/%s remaining=%s sample=%s function=%s status=SUMMARY_SKIPPED count=%s\n' \
            "$completed" "$TOTAL_PLANNED_PAIR_JOBS" "$remaining" "$sample" "$function" "$count"
    } 9>"$PROGRESS_LOCK_FILE"
}
run_pair() {
    local sample_position="${11}" function_position="${12}" function_total="${13}"
    local sample="$1" function="$2" left_id="$3" right_id="$4" left="$5" right="$6" out="$7" count="$8" total="$9" target="${10}"
    local log="$out/$function"_"$left_id"_"$right_id.log" pair_tmp="$(mktemp -d "$RUN_TMP/pair.XXXXXX")"
    # Issue #124 PR-124-B: skip 判定は呼び出し側で済んでいる。新しい child を起こす
    # 前に前回 execution の journal を捨て、`.log` の `>` と同じ境界にする
    # （残すと seq が巻き戻り、古い readiness 行が current のものに見える）。
    local journal_file="${log%.log}.stage.jsonl"
    rm -f -- "$journal_file"
    # 同じ境界で、journal が正本として宣言する dump 退避先の残骸も捨てる
    # （退避そのものは PR-124-C。残すと前回の dump が current の dump に見える）。
    local metrics_dir dump_artifact
    metrics_dir="$out/.runtime-metrics"; mkdir -p "$metrics_dir"
    dump_artifact="$metrics_dir/$function"_"$left_id"_"$right_id.stack-dump.txt"
    rm -f -- "$dump_artifact"
    # Issue #124 PR-124-C: supervisor が書く診断 sidecar の残骸も同じ境界で捨てる。
    local dump_status
    dump_status="$metrics_dir/$function"_"$left_id"_"$right_id.stack-dump.status.json"
    rm -f -- "$dump_status"
    local nonce identity result_id source_fp stream exec_nonce checkpoint authority status_file detail ec=0
    nonce="$("$PYTHON_BIN" -c 'import secrets; print(secrets.token_hex(24))')"
    identity="$(PYTHONWARNINGS=ignore::RuntimeWarning "$PYTHON_BIN" -m scripts.function_tracer_pcode.authority.decision.production_cutover --print-production-execution-identity --binary1-path "$left" --binary2-path "$right" --binary1-id "$left_id" --binary2-id "$right_id" --function-name1 "$function" --function-name2 "$function" --result-entry-occurrence-nonce "$nonce")"
    IFS=$'\t' read -r result_id source_fp stream <<< "$identity"
    exec_nonce="$(printf '%s' "$result_id" | sed 's/^production-pilot-//')"; checkpoint="$RUN_TMP/process-authority"; authority="$checkpoint/$exec_nonce/supervisor-projection.json"; mkdir -p "$checkpoint"
    # Issue #124 PR-124-B: journal は log の隣、stack dump の一時先は checkpoint
    # 配下（cleanup で消える）、journal に正本として渡す退避先は run dir 配下。
    # 退避そのものは supervisor 側の責務（PR-124-C）。
    local dump_tmp
    dump_tmp="$checkpoint/$exec_nonce/stack-dump.txt"
    local -a supervisor_cmd=("$PYTHON_BIN" -m scripts.function_tracer_pcode.authority.process.supervisor_command --checkpoint-root "$checkpoint" --authority-output "$authority" --working-directory "$SCRIPT_DIR" --execution-nonce "$exec_nonce" --result-occurrence-id "$result_id" --source-snapshot-fingerprint "$source_fp" --stream-id "$stream" --deadline-policy-digest "$(printf 'neq:%s:%s' "$PAIR_PROCESS_TIMEOUT_SECONDS" "$PAIR_PROCESS_KILL_AFTER_SECONDS" | sha256sum | awk '{print $1}')" --supervisor-signing-key-id "$SUPERVISOR_KEY_ID" --supervisor-signing-key-file "$SUPERVISOR_KEY" --worker-signing-key-id "$WORKER_KEY_ID" --worker-signing-key-file "$WORKER_KEY" --timeout-seconds "$PAIR_PROCESS_TIMEOUT_SECONDS" --kill-grace-seconds "$PAIR_PROCESS_KILL_AFTER_SECONDS" --allow-child-exit-resolution --stage-journal "$journal_file" --stack-dump-file "$dump_tmp" --stack-dump-artifact "$dump_artifact" --diagnostic-status-output "$dump_status" --stack-dump-lead-seconds "$PAIR_STACK_DUMP_LEAD_SECONDS" -- env TMPDIR="$pair_tmp" TEMP="$pair_tmp" TMP="$pair_tmp" UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE="$nonce" FT_EXPANDER_DEDUP_CASE_LIMIT="$FT_EXPANDER_DEDUP_CASE_LIMIT" FT_CALLEE_UNBOUND_REUSE="$FT_CALLEE_UNBOUND_REUSE" FT_CALLEE_UNBOUND_REUSE_SHADOW="$FT_CALLEE_UNBOUND_REUSE_SHADOW" "$PYTHON_BIN" -m scripts.function_tracer_pcode.cli.main --equiv "$left" "$right" --binary-ids "$left_id" "$right_id" -f "$function" --emit-result-json --equiv-timeout "$EQUIV_TIMEOUT" --timeout "$DECOMPILE_TIMEOUT" --pairwise-timeout "$PAIRWISE_TIMEOUT" --pairwise-timeout-hard "$PAIRWISE_TIMEOUT_HARD" --stage-journal "$journal_file" --stack-dump-file "$dump_tmp" --stack-dump-artifact "$dump_artifact")
    if [[ "$EQBENCH_IDENTICAL_FAST_PATH" == "0" ]]; then supervisor_cmd+=( --no-identical-fast-path ); fi
    if [[ "$EQBENCH_DEBUG" == "1" ]]; then supervisor_cmd+=( -d ); fi
    "${supervisor_cmd[@]}" > "$log" 2>&1 || ec=$?
    if ! supervisor_projection_is_terminal "$authority"; then
        echo "Supervisor recovery: resuming non-terminal projection before classification" >> "$log"
        if "${supervisor_cmd[@]}" >> "$log" 2>&1; then ec=0; else ec=$?; fi
    fi
    status_file="$out/$function"_"$left_id"_"$right_id.pair-status.json"
    "$PYTHON_BIN" -m scripts.function_tracer_pcode.authority.decision.canonical_result --classify-pair-log "$log" --supervisor-projection "$authority" --checkpoint-root "$checkpoint" --execution-nonce "$exec_nonce" --supervisor-signing-key-id "$SUPERVISOR_KEY_ID" --supervisor-signing-key-file "$SUPERVISOR_KEY" --worker-signing-key-id "$WORKER_KEY_ID" --worker-signing-key-file "$WORKER_KEY" --pair-status-signing-private-key-file "$PAIR_PRIVATE_KEY" --pair-status-verification-key-file "$PAIR_PUBLIC_KEY" --pair-execution-target-file "$target" --classification-diagnostic-log "$log" > "$status_file" || ec=1
    if detail="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.authority.decision.pair_status_authority --validate-pair-status "$status_file" --public-key "$PAIR_PUBLIC_KEY" --expected-pair-target "$target" --allow-operational-diagnostic 2>&1)"; then
        status="$detail"
        ec=0
    else
        status=ERROR
        ec=1
    fi
    # Issue #124 PR-124-C: cleanup より前に dump 退避状態を確認して記録する。
    # cleanup 自体は従来どおり必ず実行し、失敗の扱いも変えない。
    validation_record_stack_dump_state "$STACK_DUMP_ARTIFACT_STATE_FILE" "$sample" "$function"_"$left_id"_"$right_id" "$dump_status" "$dump_artifact" "$log"
    "$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.process_authority_cleanup --tmp-root "$EQBENCH_TMPDIR" --run-tmpdir "$RUN_TMP" --checkpoint-root "$checkpoint" --execution-nonce "$exec_nonce" || { printf '%s\t%s\t%s\n' "$sample" "$function" "$exec_nonce" >> "$PROCESS_CLEANUP_FAILURES"; ec=1; }
    rm -rf "$pair_tmp"
    progress_update "$sample" "$function" "$left_id" "$right_id" "$status"
    printf '[%s/%s] [%s %s/%s pair=%s/%s] %s <-> %s : %s\n' \
        "$sample_position" "$SOURCE_PAIR_COUNT" "$sample" \
        "$function_position" "$function_total" "$count" "$total" \
        "$left_id" "$right_id" "$status"
    return "$ec"
}
# Per-function summary, produced by the cross-function pair scheduler once
# every pair job of the function directory (the group key) has been reaped.
write_function_results_summary() {
    local function_dir="$1" function="$2"
    find "$function_dir" -maxdepth 1 -type f -name '*.log' -print0 > "$function_dir/.summary-log-paths.list0"
    "$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.result_summary --function-summary --canonical-only --function-name "$function" --summary-level compact --log-list0 "$function_dir/.summary-log-paths.list0" > "$function_dir/results_summary.txt" || true
}
pair_scheduler_init "$PARALLEL_JOBS" write_function_results_summary RUN_PAIR_FAILURES

ANALYSIS_SOURCE_DIGEST="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.execution_identity --repo-root "$SCRIPT_DIR" --print-source-digest)"
# Issue #123: この run を出した作業ツリー・時刻・ホストを manifest に残す。
# analysis_config_digest は固定 key 集合からしか作られないので、これらの行を
# 足しても判定系 digest は変わらない。
RUN_START_TIME_UTC="$(validation_utc_timestamp)"
RUN_HOSTNAME="$(validation_run_hostname)"
RUN_GIT_STATE_LINES="$(validation_run_git_state_lines "$PYTHON_BIN" "$SCRIPT_DIR")"
RUN_MANIFEST="$OUTPUT_BASE_DIR/run_manifest.txt"
PREVIOUS_RUN_MANIFEST="$RUN_TMP/previous-run-manifest.txt"
if [[ -s "$RUN_MANIFEST" ]]; then cp "$RUN_MANIFEST" "$PREVIOUS_RUN_MANIFEST"; fi
# ERROR_ONLY_RERUN is receipt-bound scheduling policy, not part of the
# semantic analysis-config digest used by reusable pair targets.
cat > "$RUN_MANIFEST" <<EOF
run_kind=neqbench_all_same_isa_function_closure_current
run_scope=$NEQ_RUN_SCOPE
build_policy=$NEQ_BUILD_POLICY
neq_root=$NEQ_ROOT
output_base_dir=$OUTPUT_BASE_DIR
parallel_jobs=$PARALLEL_JOBS
resource_admission_jobs=$RESOURCE_ADMISSION_JOBS
validation_summary_level=$VALIDATION_SUMMARY_LEVEL
pair_process_timeout=$PAIR_PROCESS_TIMEOUT
pair_process_kill_after=$PAIR_PROCESS_KILL_AFTER
pair_stack_dump_lead=$PAIR_STACK_DUMP_LEAD
pair_process_timeout_seconds=$PAIR_PROCESS_TIMEOUT_SECONDS
pair_process_kill_after_seconds=$PAIR_PROCESS_KILL_AFTER_SECONDS
equiv_timeout=$EQUIV_TIMEOUT
decompile_timeout=$DECOMPILE_TIMEOUT
pairwise_timeout=$PAIRWISE_TIMEOUT
pairwise_timeout_hard=$PAIRWISE_TIMEOUT_HARD
expander_dedup_case_limit_requested=$(validation_manifest_value "$FT_EXPANDER_DEDUP_CASE_LIMIT_REQUESTED")
expander_dedup_case_limit_effective=$FT_EXPANDER_DEDUP_CASE_LIMIT
callee_unbound_reuse=$FT_CALLEE_UNBOUND_REUSE
callee_unbound_reuse_shadow=$FT_CALLEE_UNBOUND_REUSE_SHADOW
skip_completed_results=$SKIP_COMPLETED_RESULTS
error_only_rerun=$ERROR_ONLY_RERUN
debug=$EQBENCH_DEBUG
analysis_config_schema=eqbench-analysis-config-v3
identical_fast_path=$EQBENCH_IDENTICAL_FAST_PATH
max_samples=$NEQ_MAX_SAMPLES
sample_filter=$NEQ_SAMPLE_FILTER
pair_filter=$NEQ_PAIR_FILTER
dry_run=$DRY_RUN
prefilter_source_count=$SOURCE_PAIR_COUNT
prefilter_source_census_digest=$PREFILTER_SOURCE_CENSUS_DIGEST
target_sources=$SOURCE_PAIR_COUNT
expected_full_source_pairs=$EXPECTED_FULL_SOURCE_PAIRS
function_policy=changed_functions_plus_recursive_source_callers
function_selection_census_file=$(basename "$FUNCTION_SELECTION_CENSUS_FILE")
function_selection_census_digest=$FUNCTION_SELECTION_CENSUS_DIGEST
compile_axes=arm64,mips64 x clang,gcc x O0,O1,O2,O3
new_binary_count=16
old_binary_count=16
same_isa_pair_policy=arm64_B1_B8_and_mips64_B9_B16
expected_same_isa_pairs_per_function=128
expected_arm64_pairs_per_function=64
expected_mips64_pairs_per_function=64
planned_functions=$TOTAL_PLANNED_FUNCTIONS
planned_pair_jobs=$TOTAL_PLANNED_PAIR_JOBS
source_pair_count=$SOURCE_PAIR_COUNT
source_pair_census_digest=$CENSUS_DIGEST
runner_script_sha256=$(sha256sum "$SCRIPT_DIR/neqbench_run_all_32jobs.sh" | awk '{print $1}')
start_time_utc=$RUN_START_TIME_UTC
hostname=$RUN_HOSTNAME
$RUN_GIT_STATE_LINES
analysis_source_digest_start=$ANALYSIS_SOURCE_DIGEST
EOF
CONFIG_DIGEST="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.execution_receipt --run-manifest "$RUN_MANIFEST" --print-analysis-config-digest)"
printf 'analysis_config_digest=%s\n' "$CONFIG_DIGEST" >> "$RUN_MANIFEST"
PAIR_STATUS_RESUME_COMPAT_ARGS=()
SUMMARY_SHORTCUT_AUTHORIZED=0
if compatible_identity="$("$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.execution_receipt \
    --run-manifest "$RUN_MANIFEST" --resume-compatibility-root "$OUTPUT_BASE_DIR" \
    --current-source-digest "$ANALYSIS_SOURCE_DIGEST" \
    --print-compatible-analysis-config-digest 2>/dev/null)"; then
    IFS=$'\t' read -r compatible_config_digest compatible_source_digest <<< "$compatible_identity"
    PAIR_STATUS_RESUME_COMPAT_ARGS=(
        --compatible-analysis-config-digest "$compatible_config_digest"
        --compatible-analysis-source-digest "$compatible_source_digest"
    )
    if [[ "$compatible_source_digest" == "$ANALYSIS_SOURCE_DIGEST" ]]; then
        SUMMARY_SHORTCUT_AUTHORIZED=1
    fi
fi
if [[ -s "$PREVIOUS_RUN_MANIFEST" ]]; then
    if previous_manifest_identity="$("$PYTHON_BIN" -m \
        scripts.function_tracer_pcode.reporting.execution_receipt \
        --run-manifest "$RUN_MANIFEST" \
        --resume-compatibility-manifest "$PREVIOUS_RUN_MANIFEST" \
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
            "$PREVIOUS_RUN_MANIFEST")"
        if [[ "$previous_source_digest" == "$ANALYSIS_SOURCE_DIGEST" \
            && "$previous_source_end" == "$ANALYSIS_SOURCE_DIGEST" \
            && "$previous_config_digest" == "$CONFIG_DIGEST" ]]; then
            SUMMARY_SHORTCUT_AUTHORIZED=1
        fi
    fi
fi

PROGRESS_COUNT_FILE="$RUN_TMP/progress.completed"
PROGRESS_LOCK_FILE="$RUN_TMP/progress.lock"
printf '0\n' > "$PROGRESS_COUNT_FILE"
touch "$PROGRESS_LOCK_FILE"
printf '[PROGRESS] planned samples=%s functions=%s pair_jobs=%s pairs_per_function=%s remaining=%s\n' \
    "$SOURCE_PAIR_COUNT" "$TOTAL_PLANNED_FUNCTIONS" \
    "$TOTAL_PLANNED_PAIR_JOBS" "$EXPECTED_PAIRS_PER_FUNCTION" \
    "$TOTAL_PLANNED_PAIR_JOBS"

RUN_PAIR_FAILURES=0
RUN_COMPILE_FAILURES=0
FUNCTION_CENSUS_FAILURES=0
MISSING_BINARY_COUNT=0
EXPECTED_BINARY_COUNT=0
COMPILED_BINARY_COUNT=0
TOTAL_FUNCTIONS=0
COMPLETED_SAMPLES=0
SKIPPED_SAMPLES=0
TOTAL_PAIR_JOBS=0
TOTAL_SCHEDULED_PAIR_JOBS=0
TOTAL_SKIPPED_PAIR_JOBS=0
CURRENT_PAIR_INDEX=0
CURRENT_SAMPLE_INDEX=0
while IFS="$(printf '\t')" read -r sample new_source old_source; do
    [[ -n "$sample" ]] || continue
    CURRENT_SAMPLE_INDEX=$((CURRENT_SAMPLE_INDEX + 1))
    dir="$(dirname "$new_source")"; new="$(basename "$new_source" .c)"; old="$(basename "$old_source" .c)"
    source_dir="$dir/source"; OUTPUT_SAMPLE="$OUTPUT_BASE_DIR/$sample"; mkdir -p "$source_dir" "$OUTPUT_SAMPLE"
    cmp -s "$new_source" "$source_dir/$new.c" || cp "$new_source" "$source_dir/$new.c"
    cmp -s "$old_source" "$source_dir/$old.c" || cp "$old_source" "$source_dir/$old.c"
    cp "$COMPILE_TEMPLATE" "$source_dir/compile_all.sh"; chmod +x "$source_dir/compile_all.sh"
    manifest="$source_dir/.$new-$old.neq-source-pair-manifest.json"; write_source_manifest "$manifest" "$new_source" "$old_source"
    CURRENT_PAIR_INDEX=$((CURRENT_PAIR_INDEX + 1))
    "$PYTHON_BIN" "$FUNCTION_LISTER" "$new_source" | sort -u > "$RUN_TMP/new.functions"
    "$PYTHON_BIN" "$FUNCTION_LISTER" "$old_source" | sort -u > "$RUN_TMP/old.functions"
    if ! cmp -s "$RUN_TMP/new.functions" "$RUN_TMP/old.functions"; then
        diff -u "$RUN_TMP/new.functions" "$RUN_TMP/old.functions" > "$OUTPUT_SAMPLE/function-census.diff" || true
        printf '%s\n' "$sample" >> "$FUNCTION_CENSUS_FAILURES_FILE"
        FUNCTION_CENSUS_FAILURES=$((FUNCTION_CENSUS_FAILURES + 1))
        RUN_PAIR_FAILURES=$((RUN_PAIR_FAILURES + 1))
        continue
    fi
    functions_file="$OUTPUT_SAMPLE/functions.txt"
    function_total="$(wc -l < "$functions_file")"
    function_position=0
    EXPECTED_BINARY_COUNT=$((EXPECTED_BINARY_COUNT + 32))
    new_ready=1
    if ! prepare_variant "$new_source" "$new" "$source_dir" "$sample"; then
        new_ready=0
        printf '%s/%s\n' "$sample" "$new" >> "$COMPILE_FAILURE_SAMPLES_FILE"
        RUN_COMPILE_FAILURES=$((RUN_COMPILE_FAILURES + 1))
        record_missing_variant_axes "$sample" "$new" "$source_dir"
    else
        COMPILED_BINARY_COUNT=$((COMPILED_BINARY_COUNT + 16))
        printf '%s\n' "$VARIANT_BUILD_RECEIPT_JSON" >> "$USED_BUILD_RECEIPTS_FILE"
    fi
    old_ready=1
    if ! prepare_variant "$old_source" "$old" "$source_dir" "$sample"; then
        old_ready=0
        printf '%s/%s\n' "$sample" "$old" >> "$COMPILE_FAILURE_SAMPLES_FILE"
        RUN_COMPILE_FAILURES=$((RUN_COMPILE_FAILURES + 1))
        record_missing_variant_axes "$sample" "$old" "$source_dir"
    else
        COMPILED_BINARY_COUNT=$((COMPILED_BINARY_COUNT + 16))
        printf '%s\n' "$VARIANT_BUILD_RECEIPT_JSON" >> "$USED_BUILD_RECEIPTS_FILE"
    fi
    if (( new_ready == 0 || old_ready == 0 )); then
        RUN_PAIR_FAILURES=$((RUN_PAIR_FAILURES + 1))
        continue
    fi
    COMPLETED_SAMPLES=$((COMPLETED_SAMPLES + 1))
    while IFS= read -r function; do
        [[ -n "$function" ]] || continue
        function_position=$((function_position + 1))
        TOTAL_FUNCTIONS=$((TOTAL_FUNCTIONS + 1))
        function_dir="$OUTPUT_SAMPLE/$function"; mkdir -p "$function_dir"; total="$(rerun_pair_count "$sample" "$function")"; count=0
        if [[ ("$SUMMARY_SHORTCUT_AUTHORIZED" == 1 || "$ERROR_ONLY_RERUN" == 1) ]] \
            && [[ "$SKIP_COMPLETED_RESULTS" != 0 || "$ERROR_ONLY_RERUN" != 0 ]] \
            && function_summary_all_pairs_reusable "$function_dir" "$total"; then
            while IFS= read -r status_file; do
                printf '%s\n' "${status_file#$OUTPUT_BASE_DIR/}" >> "$EXPECTED_STATUS"
                printf '%s\n' "${status_file#$OUTPUT_BASE_DIR/}" >> "$VERIFIED_SKIPPED_STATUS"
            done < <(find "$function_dir" -maxdepth 1 -type f -name '*.pair-status.json' -print | sort)
            TOTAL_PAIR_JOBS=$((TOTAL_PAIR_JOBS + total))
            TOTAL_SKIPPED_PAIR_JOBS=$((TOTAL_SKIPPED_PAIR_JOBS + total))
            progress_skip_function "$sample" "$function" "$total"
            printf '[%s/%s] [%s %s/%s] summary shortcut: skipped %s/%s pairs\n' \
                "$CURRENT_SAMPLE_INDEX" "$SOURCE_PAIR_COUNT" "$sample" \
                "$function_position" "$function_total" "$total" "$total"
            continue
        fi
        SUMMARY_ERROR_PAIRS_READY=0
        SUMMARY_ERROR_PAIRS=()
        if [[ "$ERROR_ONLY_RERUN" == 1 ]] && ! load_error_only_summary_pairs "$function_dir"; then
            RUN_PAIR_FAILURES=$((RUN_PAIR_FAILURES + 1))
            continue
        fi
        if (( SUMMARY_ERROR_PAIRS_READY )); then
            error_pair_list="$(printf '%s\n' "${!SUMMARY_ERROR_PAIRS[@]}" | sort | paste -sd, -)"
            printf '[%s] [%s] ERROR-only summary: selected %s/%s ERROR pair(s): %s\n' \
                "$sample" "$function" "${#SUMMARY_ERROR_PAIRS[@]}" "$total" "$error_pair_list"
        fi
        pair_scheduler_open_group "$function_dir" "$function"
        for pair in "${ANALYSIS_PAIR_IDS[@]}"; do
            pair_selected "$pair" || continue
            rerun_target_selected "$sample" "$function" "$pair" || continue
            left_id="${pair%%_O_*}"; right_id="O_${pair#*_O_}"
            left_binary_id="${left_id#N_}"; right_binary_id="${right_id#O_}"
            left="$source_dir/$(binary_name "$new" "$left_binary_id")"; right="$source_dir/$(binary_name "$old" "$right_binary_id")"; count=$((count + 1)); TOTAL_PAIR_JOBS=$((TOTAL_PAIR_JOBS + 1))
            log="$function_dir/$function"_"$pair.log"; status_file="$function_dir/$function"_"$pair.pair-status.json"
            summary_force_schedule=0
            if (( SUMMARY_ERROR_PAIRS_READY )) \
                && [[ -n "${SUMMARY_ERROR_PAIRS[$pair]:-}" ]]; then
                # The historical function summary is the ERROR-only
                # scheduling authority.  Do not let a stale/valid
                # terminal status or a different analysis digest hide
                # a pair explicitly classified as ERROR there.
                summary_force_schedule=1
            elif (( SUMMARY_ERROR_PAIRS_READY )); then
                if summary_pair_files_reusable "$log" "$status_file"; then
                    printf '%s\n' "${status_file#$OUTPUT_BASE_DIR/}" >> "$VERIFIED_SKIPPED_STATUS"
                    TOTAL_SKIPPED_PAIR_JOBS=$((TOTAL_SKIPPED_PAIR_JOBS + 1))
                    progress_update "$sample" "$function" "$left_id" "$right_id" "SKIPPED"
                    continue
                fi
                # A summary non-ERROR pair with a missing or malformed
                # artifact is incomplete and must be repaired.
                summary_force_schedule=1
            fi
            target="$RUN_TMP/$TOTAL_PAIR_JOBS.target.json"
            printf '%s\n' "$status_file" | sed "s#^$OUTPUT_BASE_DIR/##" >> "$EXPECTED_STATUS"
            "$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.execution_identity --repo-root "$SCRIPT_DIR" --build-pair-target --sample-identity "$sample" --output-sample-relative-path "$sample" --function-name "$function" --left-binary-id "$left_id" --right-binary-id "$right_id" --source-path "$manifest" --left-binary-path "$left" --right-binary-path "$right" --analysis-source-digest "$ANALYSIS_SOURCE_DIGEST" --analysis-config-digest "$CONFIG_DIGEST" > "$target"
            if (( ! summary_force_schedule )) \
                && [[ "$SKIP_COMPLETED_RESULTS" != 0 || "$ERROR_ONLY_RERUN" != 0 ]] \
                && pair_status_is_skippable_for_run_mode "$log" "$target"; then
                printf '%s\n' "${status_file#$OUTPUT_BASE_DIR/}" >> "$VERIFIED_SKIPPED_STATUS"
                TOTAL_SKIPPED_PAIR_JOBS=$((TOTAL_SKIPPED_PAIR_JOBS + 1))
                progress_update "$sample" "$function" "$left_id" "$right_id" "SKIPPED"
                continue
            fi
            pair_scheduler_wait_for_slot
            TOTAL_SCHEDULED_PAIR_JOBS=$((TOTAL_SCHEDULED_PAIR_JOBS + 1))
            run_pair "$sample" "$function" "$left_id" "$right_id" "$left" "$right" "$function_dir" "$count" "$total" "$target" \
                "$CURRENT_SAMPLE_INDEX" "$function_position" "$function_total" &
            pair_scheduler_start_job "$function_dir" "$!"
        done
        # results_summary.txt is written by the scheduler's completion hook
        # once the last pair of this function has been reaped.
        pair_scheduler_close_group "$function_dir"
    done < "$functions_file"
done < "$CENSUS"
pair_scheduler_finalize
find "$OUTPUT_BASE_DIR" -type f -name '*.log' ! -name 'compile_*.log' ! -name 'run_stdout.log' -print0 > "$OUTPUT_BASE_DIR/.overall-summary-log-paths.list0"
"$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.result_summary \
    --overall-summary --canonical-only --summary-level "$VALIDATION_SUMMARY_LEVEL" \
    --health-summary-json "$OUTPUT_BASE_DIR/run_health_summary.json" \
    --health-summary-text "$OUTPUT_BASE_DIR/run_health_summary.txt" \
    --log-list0 "$OUTPUT_BASE_DIR/.overall-summary-log-paths.list0" \
    > "$OUTPUT_BASE_DIR/overall_summary.txt" || true
# Issue #104: benchmark validation gate (after the health summary, before the receipt).
validation_run_benchmark_gate "$OUTPUT_BASE_DIR" "$NEQ_ROOT" "$SCRIPT_DIR"
# Issue #124 PR-124-C: TIMEOUT 診断を run_health_summary へ merge（gate の直後）。
validation_run_timeout_hotspot_summary "$OUTPUT_BASE_DIR" "$SCRIPT_DIR"
cat >> "$RUN_MANIFEST" <<EOF
completed_samples=$COMPLETED_SAMPLES
skipped_samples=$SKIPPED_SAMPLES
total_functions=$TOTAL_FUNCTIONS
total_pair_jobs=$TOTAL_PAIR_JOBS
total_scheduled_pair_jobs=$TOTAL_SCHEDULED_PAIR_JOBS
total_skipped_pair_jobs=$TOTAL_SKIPPED_PAIR_JOBS
progress_completed_pair_jobs=$(cat "$PROGRESS_COUNT_FILE")
expected_pairs_per_function=$EXPECTED_PAIRS_PER_FUNCTION
expected_binary_count=$EXPECTED_BINARY_COUNT
compiled_binary_count=$COMPILED_BINARY_COUNT
compile_failure_count=$RUN_COMPILE_FAILURES
missing_binary_count=$MISSING_BINARY_COUNT
function_census_failure_count=$FUNCTION_CENSUS_FAILURES
run_pair_failures=$RUN_PAIR_FAILURES
run_failures=$RUN_PAIR_FAILURES
benchmark_gate_status=$VALIDATION_BENCHMARK_GATE_STATUS
benchmark_gate_failures=$VALIDATION_BENCHMARK_GATE_FAILURES
analysis_source_digest_end=$("$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.execution_identity --repo-root "$SCRIPT_DIR" --print-source-digest)
end_time_utc=$(validation_utc_timestamp)
EOF
exit_status=0
if (( RUN_PAIR_FAILURES > 0 || RUN_COMPILE_FAILURES > 0 || MISSING_BINARY_COUNT > 0 || FUNCTION_CENSUS_FAILURES > 0 || VALIDATION_BENCHMARK_GATE_FAILURES > 0 )); then
    exit_status=1
fi
"$PYTHON_BIN" -m scripts.function_tracer_pcode.reporting.execution_receipt --repo-root "$SCRIPT_DIR" --private-key "$PAIR_PRIVATE_KEY" --public-key "$PAIR_PUBLIC_KEY" --output "$OUTPUT_BASE_DIR/validation-execution-receipt.json" --matrix-root "$OUTPUT_BASE_DIR" --source-digest-start "$ANALYSIS_SOURCE_DIGEST" --analysis-config-digest "$CONFIG_DIGEST" --exit-status "$exit_status" -- "env" "NEQ_RUN_SCOPE=$NEQ_RUN_SCOPE" "NEQ_BUILD_POLICY=$NEQ_BUILD_POLICY" "ERROR_RERUN_MANIFEST_SHA256=$ERROR_RERUN_MANIFEST_SHA256" "ERROR_RERUN_RUN_ID=$ERROR_RERUN_RUN_ID" "SKIP_COMPLETED_RESULTS=$SKIP_COMPLETED_RESULTS" "ERROR_ONLY_RERUN=$ERROR_ONLY_RERUN" "EQBENCH_BENCHMARK_GATE=${EQBENCH_BENCHMARK_GATE:-1}" "EQBENCH_BENCHMARK_GATE_FAIL_ON_SUSPICIOUS=${EQBENCH_BENCHMARK_GATE_FAIL_ON_SUSPICIOUS:-0}" "EQBENCH_GROUND_TRUTH_FILE=${EQBENCH_GROUND_TRUTH_FILE:-}" "./neqbench_run_all_32jobs.sh"
echo "NeqBench same-ISA caller-closure matrix finished: $OUTPUT_BASE_DIR"
if (( VALIDATION_BENCHMARK_GATE_FAILURES > 0 )); then
    echo "Error: benchmark validation gate $VALIDATION_BENCHMARK_GATE_STATUS; see $OUTPUT_BASE_DIR/benchmark_validation_gate.txt" >&2
fi
echo "Peak concurrent pair jobs: $PAIR_SCHEDULER_PEAK_ACTIVE_JOBS (PARALLEL_JOBS=$PARALLEL_JOBS)"
exit "$exit_status"
