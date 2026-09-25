#!/usr/bin/env bash

# Issue #131: 正の整数設定の「要求値」から「実効値」を求める。
#
# 判定規則は解析器側 (`config/settings.py::_positive_int_setting`) と 1 本化する:
# 検証そのものをその関数へ委譲し、runner 側で規則を二重実装しない。unset / 空白のみ /
# 非整数 / 0 以下は既定値へ戻る。委譲に失敗した場合も既定値を返すので、runner が子へ
# 渡す値は常に正の整数であり、子プロセスがその値を再検証しても同じ値になる。
validation_positive_int_setting() {
    local requested="${1-}"
    local default_value_arg="$2"
    local python_bin="${3:-${PYTHON_BIN:-python3}}"
    local repo_root="${4:-${SCRIPT_DIR:-.}}"
    local effective
    effective="$(
        cd "$repo_root" 2>/dev/null &&
        "$python_bin" -B -c '
import sys
from scripts.function_tracer_pcode.config.settings import _positive_int_setting
name = "SETTING"
print(_positive_int_setting(name, int(sys.argv[2]), {name: sys.argv[1]}))
' "$requested" "$default_value_arg" 2>/dev/null
    )" || effective=""
    if [[ "$effective" =~ ^[1-9][0-9]*$ ]]; then
        printf '%s\n' "$effective"
    else
        printf '%s\n' "$default_value_arg"
    fi
}

# 実行記録の 1 行に安全に埋め込める形へ整える（改行・復帰を潰す）。
validation_manifest_value() {
    printf '%s' "${1-}" | tr '\r\n' '  '
}

validation_prepare_before_after_logs() {
    VALIDATION_BEFORE_SOURCE="not configured"
    VALIDATION_MOVED_OUTPUT_DIR=""

    local execution_authority_root
    execution_authority_root="${VALIDATION_EXECUTION_AUTHORITY_ROOT:-${EQBENCH_RUN_TMPDIR:-${TMPDIR:-/tmp}/phase8-execution-authority-$$}}"
    mkdir -p "$execution_authority_root"
    chmod 700 "$execution_authority_root"
    export UNKNOWN_TAXONOMY_V2_WORKER_KEY_ID="phase8-matrix-worker-v1"
    export UNKNOWN_TAXONOMY_V2_WORKER_KEY_FILE="$execution_authority_root/worker.key"
    if [[ ! -s "$UNKNOWN_TAXONOMY_V2_WORKER_KEY_FILE" ]]; then
        umask 077
        head -c 32 /dev/urandom > "$UNKNOWN_TAXONOMY_V2_WORKER_KEY_FILE"
    fi

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
    case "$(validation_batch_resume_policy "$(validation_classify_log_result "$log_file")")" in
        COMPLETE_EQ|COMPLETE_NOT_EQ|FAILED_INFRASTRUCTURE) return 0 ;;
        *) return 1 ;;
    esac
}

validation_batch_resume_policy() {
    local outcome="$1"
    if [[ "$outcome" == "INCOMPLETE" ]]; then
        echo "INCOMPLETE"
        return 0
    fi
    PYTHONWARNINGS="ignore::RuntimeWarning" "${PYTHON_BIN:-python3}" -m \
        scripts.function_tracer_pcode.authority.decision.production_cutover \
        --print-batch-resume-policy --outcome "$outcome"
}

validation_result_log_has_final_authority() {
    local log_file="$1"
    [[ -f "$log_file" ]] || return 1
    [[ "$(validation_classify_log_result "$log_file")" != "INCOMPLETE" ]]
}

validation_classify_log_result() {
    local log_file="$1"
    "${PYTHON_BIN:-python3}" -m \
        scripts.function_tracer_pcode.reporting.result_summary \
        --classify-log "$log_file"
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

# Issue #104 runner benchmark validation gate.
#
# Builds the function-level source diff manifest from the benchmark tree the
# runner actually compiled and classifies every canonical pair outcome under
# OUTPUT_BASE_DIR (Eq->NOT_EQ, Neq CONFIRMED_NOT_EQ->EQUIVALENT and
# unclassifiable Neq EQUIVALENT are hard violations; source-changed-but-
# unconfirmed EQUIVALENT is counted as suspicious).  The gate is an
# evaluation oracle only: it never feeds the checker and never rewrites a
# pair status.  Results are merged into run_health_summary.{json,txt} and
# written to benchmark_validation_gate.json / function_diff_manifest.json,
# which the execution receipt hashes.
#
#   validation_run_benchmark_gate <output_base_dir> <benchmark_root> <repo_root>
#
# Sets VALIDATION_BENCHMARK_GATE_STATUS (PASS|FAIL|EMPTY|SKIPPED|MANIFEST_FAILED)
# and VALIDATION_BENCHMARK_GATE_FAILURES (0/1).  Disabled with
# EQBENCH_BENCHMARK_GATE=0 (status SKIPPED, no failure).  Set
# EQBENCH_BENCHMARK_GATE_FAIL_ON_SUSPICIOUS=1 to also fail on suspicious rows.
# The reviewed ground truth defaults to scripts/eqbench/neq_ground_truth.tsv;
# EQBENCH_GROUND_TRUTH_FILE overrides it (e.g. an empty file for a synthetic
# benchmark root).  A ground-truth path that does not exist, or an annotation
# that resolves to no function of the benchmark root, fails the manifest
# build (MANIFEST_FAILED): the runner never falls back to --no-ground-truth
# and never passes --allow-unresolved-annotations.
validation_run_benchmark_gate() {
    local output_base_dir="$1" benchmark_root="$2" repo_root="$3"
    local python_bin="${PYTHON_BIN:-python3}"
    local manifest="$output_base_dir/function_diff_manifest.json"
    local report="$output_base_dir/benchmark_validation_gate.json"
    local ground_truth="${EQBENCH_GROUND_TRUTH_FILE:-$repo_root/scripts/eqbench/neq_ground_truth.tsv}"
    local -a gate_args=()
    VALIDATION_BENCHMARK_GATE_STATUS=SKIPPED
    VALIDATION_BENCHMARK_GATE_FAILURES=0
    if [[ "${EQBENCH_BENCHMARK_GATE:-1}" == "0" ]]; then
        echo "Benchmark validation gate skipped (EQBENCH_BENCHMARK_GATE=0)."
        return 0
    fi
    if [[ ! -f "$ground_truth" ]]; then
        # The reviewed annotation file is part of the gate's authority: a
        # missing (or mistyped) path must not silently degrade to "no truth".
        VALIDATION_BENCHMARK_GATE_STATUS=MANIFEST_FAILED
        VALIDATION_BENCHMARK_GATE_FAILURES=1
        echo "Benchmark validation gate: ground-truth file not found: $ground_truth" >&2
        return 0
    fi
    local -a manifest_args=(--benchmark-root "$benchmark_root" --output "$manifest" --ground-truth "$ground_truth")
    if ! "$python_bin" -B "$repo_root/scripts/eqbench/function_diff_manifest.py" "${manifest_args[@]}" \
        > "$output_base_dir/function_diff_manifest.summary.txt" 2> "$output_base_dir/function_diff_manifest.error"; then
        VALIDATION_BENCHMARK_GATE_STATUS=MANIFEST_FAILED
        VALIDATION_BENCHMARK_GATE_FAILURES=1
        echo "Benchmark validation gate: function diff manifest failed; see $output_base_dir/function_diff_manifest.error" >&2
        return 0
    fi
    cat "$output_base_dir/function_diff_manifest.summary.txt"
    if [[ "${EQBENCH_BENCHMARK_GATE_FAIL_ON_SUSPICIOUS:-0}" == "1" ]]; then
        gate_args+=(--fail-on-suspicious)
    fi
    local gate_exit=0
    (
        cd "$repo_root" && "$python_bin" -B -m scripts.function_tracer_pcode.reporting.benchmark_validation_gate \
            "$output_base_dir" \
            --manifest "$manifest" \
            --json "$report" \
            --health-summary-json "$output_base_dir/run_health_summary.json" \
            --health-summary-text "$output_base_dir/run_health_summary.txt" \
            ${gate_args[@]+"${gate_args[@]}"}
    ) > "$output_base_dir/benchmark_validation_gate.txt" 2>&1 || gate_exit=$?
    cat "$output_base_dir/benchmark_validation_gate.txt"
    case "$gate_exit" in
        0) VALIDATION_BENCHMARK_GATE_STATUS=PASS ;;
        1) VALIDATION_BENCHMARK_GATE_STATUS=FAIL; VALIDATION_BENCHMARK_GATE_FAILURES=1 ;;
        *) VALIDATION_BENCHMARK_GATE_STATUS=EMPTY; VALIDATION_BENCHMARK_GATE_FAILURES=1 ;;
    esac
    if (( VALIDATION_BENCHMARK_GATE_FAILURES > 0 )); then
        echo "Benchmark validation gate: $VALIDATION_BENCHMARK_GATE_STATUS (exit $gate_exit); see $report" >&2
    fi
    return 0
}

# Issue #124 PR-124-C: cleanup 前の stack dump 退避確認と、TIMEOUT 診断の集計。
#
# pair の cleanup 順序は必ず
#   1) diagnostic / dump artifact の保存・存在確認
#   2) 必要な status の記録
#   3) process_authority_cleanup
#   4) checkpoint 削除（3 の中）
# の順。dump の退避そのものは supervisor が自プロセス終了前に済ませているので、
# ここでやるのは「退避できたか」の確認と記録だけ。**確認できなくても cleanup は
# 必ず実行する**（既存の run-health 契約を変えない）。退避の失敗を
# `process_authority_cleanup_failures.txt` へは書かない: あの file は run を止める
# STOP 判定と execution receipt の hash 対象で、診断の失敗を混ぜると
# cleanup 失敗の意味が変わってしまう。診断は専用の TSV と pair log に残す。
#
#   validation_record_stack_dump_state <state_tsv> <sample> <pair> <status_json> <artifact> <log>
validation_record_stack_dump_state() {
    local state_file="$1" sample_label="$2" pair_label="$3"
    local status_json="$4" artifact_file="$5" log_file="$6"
    local python_bin="${PYTHON_BIN:-python3}"
    local artifact_state="unknown" artifact_present="no" status_present="no"
    local artifact_bytes="-"
    if [[ -f "$artifact_file" ]]; then
        artifact_present="yes"
        artifact_bytes="$(wc -c < "$artifact_file" 2>/dev/null || echo -)"
    fi
    if [[ -s "$status_json" ]]; then
        status_present="yes"
        artifact_state="$("$python_bin" -c '
import json, sys
try:
    payload = json.load(open(sys.argv[1], encoding="utf-8"))
except (OSError, ValueError):
    print("unreadable")
else:
    value = payload.get("artifact_status") if isinstance(payload, dict) else None
    print(value if isinstance(value, str) and value else "unknown")
' "$status_json" 2>/dev/null || echo unknown)"
    fi
    [[ -n "$state_file" ]] && printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$sample_label" "$pair_label" "$artifact_state" "$artifact_present" \
        "$status_present" "$artifact_bytes" >> "$state_file"
    if [[ "$artifact_state" != "copied" && "$artifact_state" != "unset" ]]; then
        {
            echo ""
            echo "Stack dump artifact state before cleanup: $artifact_state" \
                 "(artifact_present=$artifact_present status_present=$status_present)"
        } >> "$log_file"
    fi
    return 0
}

# TIMEOUT 診断（`timeout_kind` / `timeout_hotspots`）を run_health_summary へ merge。
# gate の直後に呼ぶ。読むのは run dir に残る file だけなので、run 終了後に同じ
# コマンドを流せば同じ表が再現できる。集計の失敗で run を落とさない。
#
#   validation_run_timeout_hotspot_summary <output_base_dir> <repo_root>
validation_run_timeout_hotspot_summary() {
    local output_base_dir="$1" repo_root="$2"
    local python_bin="${PYTHON_BIN:-python3}"
    VALIDATION_TIMEOUT_HOTSPOT_STATUS=SKIPPED
    if [[ "${EQBENCH_TIMEOUT_HOTSPOT_SUMMARY:-1}" == "0" ]]; then
        echo "Timeout hotspot summary skipped (EQBENCH_TIMEOUT_HOTSPOT_SUMMARY=0)."
        return 0
    fi
    local exit_code=0
    (
        cd "$repo_root" && "$python_bin" -B -m \
            scripts.function_tracer_pcode.reporting.timeout_hotspot_summary \
            "$output_base_dir" \
            --json "$output_base_dir/timeout_hotspot_summary.json" \
            --health-summary-json "$output_base_dir/run_health_summary.json" \
            --health-summary-text "$output_base_dir/run_health_summary.txt"
    ) > "$output_base_dir/timeout_hotspot_summary.txt" 2>&1 || exit_code=$?
    cat "$output_base_dir/timeout_hotspot_summary.txt"
    if (( exit_code == 0 )); then
        VALIDATION_TIMEOUT_HOTSPOT_STATUS=OK
    else
        VALIDATION_TIMEOUT_HOTSPOT_STATUS=FAILED
        echo "Timeout hotspot summary: exit $exit_code (diagnostic only)" >&2
    fi
    return 0
}

# Issue #123: run provenance（いつ・どこで・どの作業ツリーで走ったか）を
# 3 本の runner で同じ規則にするための小さな共有関数。判定には一切使わず、
# manifest に残す診断情報だけを作る。
validation_utc_timestamp() {
    date -u +%Y-%m-%dT%H:%M:%SZ
}

validation_run_hostname() {
    uname -n 2>/dev/null || echo unknown
}

# 作業ツリーの git 素性を run_manifest / subset_manifest の行として返す。
# provenance の取得失敗で run を落とさない。取得できない場合も欄を空にせず
# unavailable / unknown を書く: 空欄を「汚れていなかった」と誤読させないため。
validation_run_git_state_lines() {
    local python_bin="${1:-${PYTHON_BIN:-python3}}"
    local repo_root="${2:-${SCRIPT_DIR:-.}}"
    local lines=""
    lines="$(cd "$repo_root" && "$python_bin" -m \
        scripts.function_tracer_pcode.reporting.execution_identity \
        --repo-root "$repo_root" --print-git-state 2>/dev/null)" || lines=""
    if [[ -z "$lines" ]]; then
        lines=$'git_commit=unavailable\ngit_dirty=unknown\ngit_dirty_files_digest=unavailable'
    fi
    printf '%s\n' "$lines"
}

# Issue #123: before run の half が「比較対象」として使えるかどうか。
#
# 判定規則を shell 側に書き写さない: transition / gate が実際に通す reader
# （`reporting.pair_outcomes.load_pair_outcomes()`）へ `--validate-comparison-tree`
# で委譲し、そこを唯一の正とする。payload からも path からも identity を復元できない
# pair-status や、同じ pair の status が 2 つある tree は reader が拒否するので、
# ここでも通さない。run_manifest.txt や provenance は transition に不要なので要求
# しない: それらを持たない過去の run（PR #150 以前）も before として使える。
# after との pair 集合の一致は実行前には決められないので要求しない（欠けは従来どおり
# transition 表の MISSING 行として出る）。
# 成功時は pair 件数を stdout に出す。拒否の理由は reader の stderr をそのまま通す。
validation_before_run_half_is_comparable() {
    local half_dir="$1"
    local python_bin="${2:-${PYTHON_BIN:-python3}}"
    local repo_root="${3:-${SCRIPT_DIR:-.}}"
    (cd "$repo_root" && "$python_bin" -m \
        scripts.function_tracer_pcode.reporting.pair_outcomes \
        --validate-comparison-tree "$half_dir")
}

# Issue #170: 秘密鍵の keyset（`<realpath(private root)>/<KEYSET_ID>`）は出力 dir とは
# 別の共有資源で、別の出力・別 container・rename した出力から同じ keyset を指せる。
# そのため keyset directory の inode を flock で排他し、鍵を読む・書く・検証する区間
# （evidence guard、HMAC 鍵、pair-status 鍵の具体化）だけを保持する。
#
# - keyset の component が symlink なら拒否する。存在しなければ `mkdir -p -m 700` で作る。
# - lock は上限付きで待つ（`VALIDATION_KEYSET_LOCK_WAIT_SECONDS`、既定 120 秒）。
#   超えたら「held by another run for too long」で 1 を返し、keyset には何も書かない。
# - `chmod 700` は lock を取った後に行う（拒否された run が keyset の ctime を変えない）。
# - lock の保持中に別の keyset lock は取らない（2 を返す）。保持中は `&` で子を起動
#   しない: fd を受け継ぐのは同期的な helper だけで、unlock より前に終了する。
validation_lock_authority_keyset() {
    local dir="$1"
    local wait_seconds="${VALIDATION_KEYSET_LOCK_WAIT_SECONDS:-120}"
    local lock_fd flock_status
    if [[ -n "${VALIDATION_KEYSET_LOCK_FD:-}" ]]; then
        echo "Error: an authority keyset lock is already held; refusing a second keyset lock: $dir" >&2
        return 2
    fi
    if [[ ! "$wait_seconds" =~ ^[0-9]+([.][0-9]+)?$ ]]; then
        echo "Error: VALIDATION_KEYSET_LOCK_WAIT_SECONDS must be a non-negative number of seconds" >&2
        return 1
    fi
    if [[ -L "$dir" ]]; then
        echo "Error: authority keyset must not be a symlink: $dir" >&2
        return 1
    fi
    if ! mkdir -p -m 700 -- "$dir" 2>/dev/null || [[ -L "$dir" || ! -d "$dir" ]]; then
        echo "Error: authority keyset is not a directory and cannot be created as one: $dir" >&2
        return 1
    fi
    if ! exec {lock_fd}<"$dir"; then
        echo "Error: authority keyset cannot be opened for locking: $dir" >&2
        return 1
    fi
    flock_status=0
    flock -E 75 -w "$wait_seconds" "$lock_fd" || flock_status=$?
    if (( flock_status != 0 )); then
        exec {lock_fd}<&-
        if (( flock_status == 75 )); then
            echo "Error: authority keyset is held by another run for too long (${wait_seconds}s): $dir" >&2
        else
            echo "Error: authority keyset cannot be locked (flock exit $flock_status): $dir" >&2
        fi
        return 1
    fi
    # lock を取った inode が今の path の inode であること（待っている間の差し替えを拒否）。
    if [[ -L "$dir" || ! "$dir" -ef "/dev/fd/$lock_fd" ]]; then
        exec {lock_fd}<&-
        echo "Error: authority keyset was replaced while waiting for its lock: $dir" >&2
        return 1
    fi
    if ! chmod 700 -- "$dir"; then
        exec {lock_fd}<&-
        echo "Error: authority keyset permissions cannot be restricted: $dir" >&2
        return 1
    fi
    VALIDATION_KEYSET_LOCK_FD="$lock_fd"
    VALIDATION_KEYSET_LOCK_DIR="$dir"
}

# keyset lock の fd を閉じる（= lock を解放する）。保持していなければ何もしない。
validation_unlock_authority_keyset() {
    if [[ -n "${VALIDATION_KEYSET_LOCK_FD:-}" ]]; then
        exec {VALIDATION_KEYSET_LOCK_FD}<&-
    fi
    VALIDATION_KEYSET_LOCK_FD=""
    VALIDATION_KEYSET_LOCK_DIR=""
}

# Issue #170: pair-status 署名鍵の具体化規則の唯一の owner（Eq / Neq 共通）。
#
# - 秘密鍵が空（無い）: 生成し、公開鍵も書く。
# - 秘密鍵だけある（出力 dir を消して取り直した等）: 秘密鍵から公開鍵を書き直す。
# - どの場合も最後に対を validate する。秘密鍵を書くのは空と判定したときだけで、
#   validate の後は書き換えない。
# 秘密鍵を置く keyset の lock（validation_lock_authority_keyset）を保持したまま呼ぶ。
# CLI が失敗したら traceback は出さず、その stderr の最後の行を理由として 1 行で出し、
# 1 を返す。
validation_materialize_pair_status_keypair() {
    local python_bin="$1" private_key="$2" public_key="$3"
    local module=scripts.function_tracer_pcode.authority.decision.pair_status_authority
    local error_output
    if [[ -z "${VALIDATION_KEYSET_LOCK_DIR:-}" \
        || ! "$(dirname -- "$private_key")" -ef "$VALIDATION_KEYSET_LOCK_DIR" ]]; then
        echo "Error: pair-status keypair must be materialized while holding its keyset lock: $private_key" >&2
        return 2
    fi
    if [[ ! -s "$private_key" ]]; then
        if ! error_output="$("$python_bin" -m "$module" \
            --generate-private-key "$private_key" \
            --write-public-key "$public_key" 2>&1 >/dev/null)"; then
            echo "Error: pair-status keypair cannot be generated: $(printf '%s\n' "$error_output" | tail -n 1)" >&2
            return 1
        fi
    elif [[ ! -s "$public_key" ]]; then
        if ! error_output="$("$python_bin" -m "$module" \
            --export-public-from-private "$private_key" \
            --write-public-key "$public_key" 2>&1 >/dev/null)"; then
            echo "Error: pair-status public key cannot be exported from the retained private key: $(printf '%s\n' "$error_output" | tail -n 1)" >&2
            return 1
        fi
    fi
    if ! error_output="$("$python_bin" -m "$module" \
        --validate-private-key "$private_key" \
        --public-key "$public_key" 2>&1 >/dev/null)"; then
        echo "Error: pair-status private key and public key are not a valid pair: $(printf '%s\n' "$error_output" | tail -n 1)" >&2
        echo "Private key: $private_key" >&2
        echo "Public key: $public_key" >&2
        return 1
    fi
}

export -f validation_positive_int_setting
export -f validation_manifest_value
export -f validation_run_benchmark_gate
export -f validation_result_log_is_complete
export -f validation_result_log_has_final_authority
export -f validation_classify_log_result
export -f validation_classify_log_display
