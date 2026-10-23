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

# Issue #106 PR-106-B: 解析の期限（ANALYSIS_TIMEOUT）と process の期限の整合。
#
# 規則（書式・既定・OFF・`ANALYSIS_TIMEOUT + ANALYSIS_TIMEOUT_MARGIN <= PAIR_PROCESS_TIMEOUT`）は
# `reporting/runner_timeout_policy.py` にだけあり、ここは呼んで結果を変数へ移すだけ。
# 未指定・空の ANALYSIS_TIMEOUT / ANALYSIS_TIMEOUT_MARGIN は profile の既定になる: 第 2 引数に
# profile の manifest（固定 subset の eqbench_subset.json）を渡せばその run_settings、空なら full。
# 失敗（不正値・不整合・Python を呼べない）は 1 を返す: 呼び出し側は pair を始めずに exit 1 する
# （`validation_positive_int_setting` と違って既定値へ戻さない。期限の取り違えは静かに直さない）。
#
# 成功すると次を設定する:
#   ANALYSIS_TIMEOUT_MANIFEST_LINES  run manifest に書く key=value 行（key の一覧も module が持つ）
#   ANALYSIS_TIMEOUT_SECONDS         実効値（0 = OFF）
#   ANALYSIS_TIMEOUT_MARGIN_SECONDS  実効の余裕
#   ANALYSIS_TIMEOUT_CLI_ARGS        pair の CLI へ足す引数（OFF なら空の配列）
validation_resolve_analysis_timeout_policy() {
    local python_bin="$1"
    local profile_manifest="${2-}"
    local repo_root="${3:-${SCRIPT_DIR:-.}}"
    local -a default_args=()
    if [[ -n "$profile_manifest" ]]; then
        default_args=(--profile-manifest "$profile_manifest")
    fi
    local lines
    lines="$(
        cd "$repo_root" &&
        "$python_bin" -B -m scripts.function_tracer_pcode.reporting.runner_timeout_policy \
            resolve \
            --analysis-timeout "${ANALYSIS_TIMEOUT-}" \
            --analysis-timeout-margin "${ANALYSIS_TIMEOUT_MARGIN-}" \
            --pair-process-timeout "${PAIR_PROCESS_TIMEOUT-}" \
            ${default_args[@]+"${default_args[@]}"}
    )" || return 1
    local timeout enabled margin
    timeout="$(printf '%s\n' "$lines" | awk -F= '$1 == "analysis_timeout" {print $2}')"
    enabled="$(printf '%s\n' "$lines" | awk -F= '$1 == "analysis_timeout_enabled" {print $2}')"
    margin="$(printf '%s\n' "$lines" | awk -F= '$1 == "analysis_timeout_margin" {print $2}')"
    if [[ ! "$timeout" =~ ^[0-9]+([.][0-9]+)?$ || ! "$enabled" =~ ^[01]$ \
        || ! "$margin" =~ ^[0-9]+([.][0-9]+)?$ ]]; then
        echo "Error: the analysis timeout policy printed no effective values" >&2
        return 1
    fi
    ANALYSIS_TIMEOUT_MANIFEST_LINES="$lines"
    ANALYSIS_TIMEOUT_SECONDS="$timeout"
    ANALYSIS_TIMEOUT_MARGIN_SECONDS="$margin"
    ANALYSIS_TIMEOUT_CLI_ARGS=()
    if [[ "$enabled" == "1" ]]; then
        ANALYSIS_TIMEOUT_CLI_ARGS=(--analysis-timeout "$timeout")
    fi
}

_VALIDATION_REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# ---------------------------------------------------------------------------
# Issue #160: FULL scope の評価 tree（Eq / Neq 共通）
#
# FULL scope の tree は「現在の source・config・入力 binary で評価した pair だけ」を持つ。
#   - 実行する pair を絞る入力（件数上限・sample / pair filter・rerun manifest・ERROR-only）を
#     FULL では 1 つも受け付けない（validation_refuse_narrowed_full_scope）。
#   - 出力先は、何かを書く前に受理判定する（validation_admit_full_scope_output）。判定規則は
#     reporting/execution_receipt.py::full_scope_output_admission だけが持ち、ここは呼ぶだけ。
#   - resume 時の pair の再利用も同じ module が FULL では source / config をまたがせない
#     （cross_identity_resume_is_permitted）。runner 側に identity の規則を書かない。
# ---------------------------------------------------------------------------

# FULL scope で、実行対象を絞る入力が 1 つでも有効なら理由を出して 1 を返す（pair を始める前に呼ぶ）。
# FULL でない scope では何もしない。
#   validation_refuse_narrowed_full_scope <scope> <max_samples> <sample_filter> <pair_filter> \
#       <rerun_manifest> <error_only_rerun>
validation_refuse_narrowed_full_scope() {
    local scope="$1" max_samples="$2" sample_filter="$3" pair_filter="$4"
    local rerun_manifest="$5" error_only_rerun="$6"
    local -a active=()
    [[ "$scope" == FULL_EQBENCH || "$scope" == FULL_NEQ ]] || return 0
    [[ "$max_samples" == 0 ]] || active+=("a sample limit ($max_samples)")
    [[ -z "$sample_filter" ]] || active+=("a sample filter")
    [[ -z "$pair_filter" ]] || active+=("a pair filter")
    [[ -z "$rerun_manifest" ]] || active+=("a rerun manifest")
    [[ "$error_only_rerun" == 0 ]] || active+=("ERROR-only rerun")
    (( ${#active[@]} == 0 )) && return 0
    local joined
    joined="$(printf '%s, ' "${active[@]}")"
    echo "Error: $scope runs every pair of the frozen census; refusing ${joined%, } (use a REPRESENTATIVE scope for a narrowed or rerun tree)" >&2
    return 1
}

# FULL scope の出力先の受理判定（書き込みの前に呼ぶ）。candidate は出力先の外に置いた、これから
# 置く run manifest。成功すると VALIDATION_OUTPUT_ADMISSION に FRESH / SAME_IDENTITY_RESUME を入れて
# 0 を返す。REFUSE（または判定できない）なら理由を出して 1 を返す: 呼び出し側は出力先に何も書かずに
# exit する。
#   validation_admit_full_scope_output <python_bin> <output_dir> <candidate_manifest>
validation_admit_full_scope_output() {
    local python_bin="$1" output_dir="$2" candidate="$3" line decision reason status=0
    [[ "$python_bin" != */* || "$python_bin" == /* ]] || python_bin="$PWD/$python_bin"
    line="$(cd "$_VALIDATION_REPO_ROOT" && "$python_bin" -B -m \
        scripts.function_tracer_pcode.reporting.execution_receipt \
        --repo-root "$_VALIDATION_REPO_ROOT" --full-scope-output-admission \
        --output-dir "$output_dir" --run-manifest "$candidate" 2>&1)" || status=$?
    decision="${line%%$'\t'*}"
    reason="${line#*$'\t'}"
    if (( status != 0 )) || [[ "$decision" != FRESH && "$decision" != SAME_IDENTITY_RESUME ]]; then
        echo "Error: FULL-scope output directory refused; nothing was written to it: $output_dir" >&2
        echo "Reason: $(printf '%s\n' "${reason:-exit $status}" | tail -n 1)" >&2
        echo "Use a new, empty OUTPUT_BASE_DIR, or resume it with the exact run identity that wrote it." >&2
        return 1
    fi
    VALIDATION_OUTPUT_ADMISSION="$decision"
    echo "FULL-scope output admission: $decision ($reason): $output_dir"
}

# ---------------------------------------------------------------------------
# Issue #160: pair ごとの runtime receipt（Eq / Neq 共通の writer と execution 境界）
#
# schema・path・execution_nonce による束縛は reporting/pair_runtime_receipt.py が持つ。
# receipt は診断で、pair-status / canonical result / 署名 / ledger の入力にならない。
# 書けなくても pair と run の exit code は変えない（警告だけ出して 0 を返す）。
# ---------------------------------------------------------------------------

# 1 回の supervisor 呼び出しを測る GNU time の前置き。使い方: "${VALIDATION_SUPERVISOR_TIME[@]}" -o <usage> <cmd...>
# 同じ execution の呼び出し（初回と、非終端 projection からの各再開）はそれぞれ別の usage file に
# 書き、全部を writer の --resource-usage へ渡す。集約（経過時間は和、最大 RSS は最大、1 つでも
# 読めなければ null）は pair_runtime_receipt.aggregate_resource_usage が持つ。format はその parser が
# 読む形（同 module の RUNTIME_USAGE_TIME_FORMAT と同じ。test で固定）。
VALIDATION_SUPERVISOR_TIME=(/usr/bin/time -f 'elapsed_seconds=%e\nmax_rss_kb=%M')

# run の開始時に 1 回呼び、run manifest の runtime_run_id と各 receipt の --run-id に使う。
# receipt がこの run の計測か（再利用した pair の、以前の run の計測か）を consumer が区別する根拠。
#   RUNTIME_RUN_ID="$(validation_new_runtime_run_id "$PYTHON_BIN")" || exit 1
validation_new_runtime_run_id() {
    local python_bin="$1" run_id
    [[ "$python_bin" != */* || "$python_bin" == /* ]] || python_bin="$PWD/$python_bin"
    run_id="$(cd "$_VALIDATION_REPO_ROOT" && "$python_bin" -B -m \
        scripts.function_tracer_pcode.reporting.pair_runtime_receipt new-run-id)" || run_id=""
    if [[ ! "$run_id" =~ ^[0-9a-f]{32}$ ]]; then
        echo "Error: cannot create the runtime run id" >&2
        return 1
    fi
    printf '%s\n' "$run_id"
}

# receipt を 1 つ書く。値はすべて引数で渡す（runner の global を読まない）。
# 引数は pair_runtime_receipt の `write` subcommand の option をそのまま渡す。
#   validation_write_pair_runtime_receipt <python_bin> --metrics-dir D --stem S --state RUNNING|COMPLETED \
#       --function-name F --left-binary-id L --right-binary-id R --execution-nonce N --run-id RUN \
#       [--resource-usage <usage file of each supervisor invocation> ...] [--<field> V ...]
validation_write_pair_runtime_receipt() {
    local python_bin="$1"
    shift
    [[ "$python_bin" != */* || "$python_bin" == /* ]] || python_bin="$PWD/$python_bin"
    if ! (cd "$_VALIDATION_REPO_ROOT" && "$python_bin" -B -m \
        scripts.function_tracer_pcode.reporting.pair_runtime_receipt write "$@"); then
        echo "Warning: pair runtime receipt was not written (diagnostic only): $*" >&2
    fi
    return 0
}

# ---------------------------------------------------------------------------
# 中断と確定の境界（評価計画 v2 PR-A）。2 本の runner はここだけを呼ぶ。
# ---------------------------------------------------------------------------

# 停止を確かめられなかった（所有している process が残る、または所有かどうかを確かめられない
# process がある）ときの runner の exit code。run の一時 dir は残す。
VALIDATION_STOP_UNCONFIRMED_EXIT=75

# この runner の execution が起こす process の所有権を取る。runner の先頭で、何かを起動する
# 前に `validation_claim_process_ownership "<runner script の絶対 path>" "$@"` と呼ぶ。
# owner token を**環境変数として持たせたうえで runner 自身を exec し直す**。bash の export は
# 自分の /proc/<pid>/environ を変えないので、exec し直さないと、exec を経ない fork（subshell、
# pair job、progress の loop）の environ に token が現れず、親を失ったときに見つけられない。
# exec し直した後は、fork だけの子も exec した子も token を持つ（scripts/eqbench/runner_processes.py）。
# 入れ子の runner は自分の token で exec し直すので、外側の process は止めない。
validation_claim_process_ownership() {
    local script="$1"
    shift
    if [[ "${EQBENCH_PROCESS_OWNER_ROOT:-}" == "$$" ]] && _validation_owner_token_in_own_environ; then
        export EQBENCH_PROCESS_OWNER_TOKEN EQBENCH_PROCESS_OWNER_ROOT
        return 0
    fi
    local token
    token="$("${PYTHON_BIN:-python3}" -c 'import secrets; print(secrets.token_hex(16))')" || return 1
    [[ "$token" =~ ^[0-9a-f]{32}$ ]] || return 1
    exec env EQBENCH_PROCESS_OWNER_TOKEN="$token" EQBENCH_PROCESS_OWNER_ROOT="$$" \
        "$BASH" "$script" "$@"
}

_validation_owner_token_in_own_environ() {
    [[ "${EQBENCH_PROCESS_OWNER_TOKEN:-}" =~ ^[0-9a-f]{32}$ ]] || return 1
    tr '\0' '\n' < "/proc/$$/environ" \
        | grep -qxF "EQBENCH_PROCESS_OWNER_TOKEN=$EQBENCH_PROCESS_OWNER_TOKEN"
}

# 所有している process を凍結し、SIGKILL し、消えたことを確かめる。残った process、または
# 所有かどうかを確かめられない process があれば非 0 を返す（呼び出し側は tmp を消さない）。
validation_stop_owned_processes() {
    local python_bin="${1:-${PYTHON_BIN:-python3}}"
    [[ -n "${EQBENCH_PROCESS_OWNER_TOKEN:-}" && -n "${EQBENCH_PROCESS_OWNER_ROOT:-}" ]] || return 1
    [[ "$python_bin" != */* || "$python_bin" == /* ]] || python_bin="$PWD/$python_bin"
    (cd "$_VALIDATION_REPO_ROOT" && "$python_bin" -B -m scripts.eqbench.runner_processes stop \
        --token "$EQBENCH_PROCESS_OWNER_TOKEN" --root "$EQBENCH_PROCESS_OWNER_ROOT")
}

# runner の TERM / INT / HUP の handler。以後の停止要求は無視し（停止は 1 回だけ）、
# 所有している process がすべて止まったことを確かめてから、run の一時 dir を消す関数
# <cleanup> を呼んで <exit_status> で終わる。確かめられなければ一時 dir を残し、
# VALIDATION_STOP_UNCONFIRMED_EXIT で終わる。
#   trap 'validation_handle_stop_signal 143 <cleanup>' TERM
validation_handle_stop_signal() {
    local exit_status="$1" cleanup="$2"
    trap '' HUP INT TERM
    trap - EXIT
    _validation_stop_then_cleanup "$cleanup" || exit_status="$VALIDATION_STOP_UNCONFIRMED_EXIT"
    exit "$exit_status"
}

# runner の EXIT の handler。正常終了でも、途中の失敗（set -e など）で抜けるときも、
# 所有している process が残っていれば止めて確かめてから一時 dir を消す。
#   trap 'validation_handle_exit <cleanup>' EXIT
validation_handle_exit() {
    local exit_status=$? cleanup="$1"
    trap '' HUP INT TERM
    trap - EXIT
    _validation_stop_then_cleanup "$cleanup" || exit_status="$VALIDATION_STOP_UNCONFIRMED_EXIT"
    exit "$exit_status"
}

_validation_stop_then_cleanup() {
    local cleanup="$1"
    if validation_stop_owned_processes; then
        "$cleanup" || true
        return 0
    fi
    echo "Error: the processes of this run could not all be confirmed stopped; the run tmpdir is kept" >&2
    return 1
}

# pair の execution 境界を開く。前回 execution の pair-status（atomic な公開の書きかけの
# 一時 file を含む）、stage journal、stack dump とその状態、分類失敗の record、runtime
# receipt を消し、**消えたことを確かめる**。1 つでも残れば非 0 を返し、残った path を
# stderr に書く。呼び出し側は解析を始めてはならない（残った前回の結果を、今回の結果と
# 取り違えないため）。
#   validation_open_pair_execution <pair の output dir> <pair stem>
validation_open_pair_execution() {
    local directory="$1" stem="$2" metrics path
    metrics="$directory/.runtime-metrics"
    mkdir -p -- "$metrics" 2>/dev/null
    local -a paths=(
        "$directory/$stem.pair-status.json"
        "$directory/$stem.stage.jsonl"
        "$metrics/$stem.stack-dump.txt"
        "$metrics/$stem.stack-dump.status.json"
        "$metrics/$stem.classification-failure.json"
        "$metrics/$stem.progress.json"
        "$metrics/$stem.runtime.json"
    )
    local -a partials=()
    shopt -s nullglob
    partials=("$directory/.$stem.pair-status.json."*)
    shopt -u nullglob
    rm -f -- "${paths[@]}" "${partials[@]}" 2>/dev/null
    local -a remaining=()
    for path in "${paths[@]}"; do
        if [[ -e "$path" || -L "$path" ]]; then remaining+=("$path"); fi
    done
    shopt -s nullglob
    for path in "$directory/.$stem.pair-status.json."*; do remaining+=("$path"); done
    shopt -u nullglob
    if (( ${#remaining[@]} > 0 )); then
        printf 'Error: pair execution boundary could not remove: %s\n' "${remaining[@]}" >&2
        return 1
    fi
    if [[ ! -d "$metrics" || ! -w "$metrics" || ! -w "$directory" ]]; then
        echo "Error: pair execution boundary: output directory is not writable: $directory" >&2
        return 1
    fi
    return 0
}

# 分類器が公開した pair-status を、この execution の結果として読む。署名・期待する
# target・正規の終端・**この execution の nonce** がすべて確かめられたときだけ確定とし、
# それ以外（status が無い・分類失敗の診断・壊れている・別の target / 別の execution）は
# INCOMPLETE にする。stdout に "<状態>\t<error_kind>\t<child rc>" を 1 行書き、確定なら
# 0、未完了なら 3 を返す。理由は stderr に書く。
#   validation_resolve_pair_execution <python> <status> <target> <public key> <nonce> <classification-failure record>
validation_resolve_pair_execution() {
    local python_bin="$1"
    shift
    [[ "$python_bin" != */* || "$python_bin" == /* ]] || python_bin="$PWD/$python_bin"
    (cd "$_VALIDATION_REPO_ROOT" && "$python_bin" -B -m \
        scripts.function_tracer_pcode.authority.decision.pair_status_authority \
        --resolve-pair-execution "$1" --expected-pair-target "$2" --public-key "$3" \
        --expected-execution-nonce "$4" --classification-failure-record "$5")
}

# 実行記録（run_manifest.txt など）を丸ごと置き換える / 追記する。どちらも同じ dir の一時
# file に書いてから rename するので、途中で kill されても書きかけの file は残らない。
validation_install_file_atomically() {
    local source="$1" destination="$2" temporary
    temporary="$(mktemp "${destination%/*}/.${destination##*/}.XXXXXX")" || return 1
    if cp -- "$source" "$temporary" \
        && chmod "$(printf '%o' $((0666 & ~$(umask))))" "$temporary" \
        && mv -f -- "$temporary" "$destination"; then
        return 0
    fi
    rm -f -- "$temporary"
    return 1
}

# stdin を destination の末尾に足した内容で destination を置き換える。
validation_append_file_atomically() {
    local destination="$1" temporary
    temporary="$(mktemp "${destination%/*}/.${destination##*/}.XXXXXX")" || return 1
    if { if [[ -e "$destination" ]]; then cat -- "$destination"; fi; cat; } > "$temporary" \
        && chmod "$(printf '%o' $((0666 & ~$(umask))))" "$temporary" \
        && mv -f -- "$temporary" "$destination"; then
        return 0
    fi
    rm -f -- "$temporary"
    return 1
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

# ---------------------------------------------------------------------------
# Issue #170: 秘密鍵の keyset と鍵の具体化（Eq / Neq 共通の唯一の owner）
#
# 配置の契約:
#   keyset        = <realpath -m(private root)>/<keyset id>。keyset id は 1 つの path component
#                   （[A-Za-z0-9._-]、`.` と `..` は不可）。keyset は symlink でない。
#                   keyset と OUTPUT は分離している: 同一でも、keyset が OUTPUT の中でも、
#                   OUTPUT が keyset の中でもない（canonical な綴りと、存在する祖先の inode の両方で判定）。
#   秘密鍵・HMAC 鍵 = keyset の直下の file（したがって OUTPUT の外）。
#   公開鍵        = OUTPUT の中の file（したがって keyset の外）。
#
# keyset identity の判定は _validation_check_authority_keyset だけが持つ。
#   validation_resolve_authority_keyset が root と id から keyset を組み立てて判定し、
#   validation_lock_authority_keyset は渡された keyset を同じ判定にかけ直す（手で組み立てた
#   path も同じ規則で判定されるので、別の意味を持てない）。鍵を書く直前にも同じ判定をする。
#
# lock capability:
#   lock は keyset を開いた fd（primary）とその dup（shadow）で排他 flock を保持し、非 export の
#   配列 _VALIDATION_KEYSET_LOCK に (primary, shadow, lock の dev:ino, keyset, OUTPUT) を記録する。
#   記録は kernel と照合する材料で、それ自体は証明ではない。所有の証明は
#   「primary と shadow の両方の open file description が、記録した dev:ino の排他 flock を所有
#    している」こと（/proc/self/fdinfo の lock 行は、その open file description が所有する lock
#    だけを出す）。排他 flock を所有できる open file description は 1 つだけなので、両者は同じ
#   open file description（= lock が作ったもの）である。片方の fd 番号が閉じられて別の file に
#   再利用されても、dev:ino か lock 行が一致しない。同じ keyset を開き直して lock しようとしても、
#   残った方が lock を保持しているので取れない。
#   （証明が区別しないのは、呼び出し側が自分で keyset を開いて排他 flock を取り、その fd の組を
#    state に書いた場合だけである。その fd の組は実際に keyset の排他を保持しているので、
#    「keyset の inode ごとに鍵操作は 1 つ」は崩れない。）
#   - unlock は所有の証明が成り立つときだけ fd を閉じる（自分が取得した lock 以外は閉じない）。
#   - 鍵を書く helper は、所有の証明、記録した keyset が今もその inode を指すこと、identity の
#     判定を確かめ、keyset の path ではなく /dev/fd/<primary>/<name>（lock した inode）に書く。
#
# 呼び出し側の契約（新しい runner もこれだけ守ればよい）:
#   keyset="$(validation_resolve_authority_keyset "$root" "$keyset_id" "$OUTPUT_BASE_DIR")" || exit 1
#   validation_lock_authority_keyset "$keyset" "$OUTPUT_BASE_DIR" || exit 1
#   ...（"$keyset/<name>" を読む evidence guard）
#   validation_materialize_process_key "$keyset/<name>.key" || exit 1
#   validation_materialize_pair_status_keypair "$python" "$keyset/<name>.key" "$OUTPUT_BASE_DIR/<public>.json" || exit 1
#   validation_unlock_authority_keyset || exit 1
# - lock と unlock の間で `&` を使わない（fd を受け継ぐのは同期的な子だけにする）。
# - helper が失敗したら exit する（process の終了で lock は解放される）。
# - 誤用（lock 無し、別の keyset の鍵、stale / 偽造 / 環境由来の state、2 つ目の lock）は 2、
#   設定・環境の問題（identity の違反、timeout、書けない、鍵が壊れている）は 1 を返す。
# - 相対 path は呼び出し側の cwd で解決する（runner は SCRIPT_DIR に cd してから呼ぶ）。
# ---------------------------------------------------------------------------

_VALIDATION_KEY_AUTHORITY_REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
_VALIDATION_PAIR_STATUS_KEY_MODULE=scripts.function_tracer_pcode.authority.decision.pair_status_authority

# 内部: keyset id と鍵の名前に使える 1 つの path component か。
_validation_path_component_is_valid() {
    [[ "${1-}" =~ ^[A-Za-z0-9._-]+$ && "$1" != "." && "$1" != ".." ]]
}

# 内部: 絶対 path a と b が重なる（同一、または一方が他方の祖先）か。canonical な綴りの前方一致と、
# 存在する祖先（自身を含む）の inode（bind mount などの別名）の両方で判定する。
_validation_paths_overlap() {
    local a="$1" b="$2" near far p
    [[ "$a" == "$b" || "$a" == "$b/"* || "$b" == "$a/"* ]] && return 0
    for near in "$a" "$b"; do
        if [[ "$near" == "$a" ]]; then far="$b"; else far="$a"; fi
        p="$near"
        while :; do
            [[ -e "$p" && "$p" -ef "$far" ]] && return 0
            [[ "$p" == / ]] && break
            p="${p%/*}"
            [[ -n "$p" ]] || p=/
        done
    done
    return 1
}

# keyset identity の判定（唯一の owner）。満たさなければ理由を出して 1 を返す。書き込みはしない。
_validation_check_authority_keyset() {
    local keyset="$1" output="$2" resolved_output
    if [[ "$keyset" != /* ]] || ! _validation_path_component_is_valid "${keyset##*/}"; then
        echo "Error: authority keyset must be <canonical private root>/<one path component>: $keyset" >&2
        return 1
    fi
    if [[ -L "$keyset" ]]; then
        echo "Error: authority keyset must not be a symlink: $keyset" >&2
        return 1
    fi
    if [[ "$(realpath -m -- "$keyset" 2>/dev/null)" != "$keyset" ]]; then
        echo "Error: authority keyset must be a canonical path: $keyset" >&2
        return 1
    fi
    if [[ -z "$output" ]] || ! resolved_output="$(realpath -m -- "$output")"; then
        echo "Error: OUTPUT_BASE_DIR cannot be resolved: $output" >&2
        return 1
    fi
    if _validation_paths_overlap "$keyset" "$resolved_output"; then
        echo "Error: private authority keyset must be outside OUTPUT_BASE_DIR and must not contain it: keyset=$keyset OUTPUT_BASE_DIR=$resolved_output" >&2
        return 1
    fi
}

# private root と keyset id から keyset を組み立て（唯一の組み立て箇所）、identity を判定して
# stdout に出す。書き込みはしない。
validation_resolve_authority_keyset() {
    local root="$1" keyset_id="$2" output="$3" resolved_root keyset
    if ! _validation_path_component_is_valid "$keyset_id"; then
        echo "Error: authority keyset id must be one path component of [A-Za-z0-9._-] other than . and ..: $keyset_id" >&2
        return 1
    fi
    if [[ -z "$root" ]] || ! resolved_root="$(realpath -m -- "$root")"; then
        echo "Error: private authority root cannot be resolved: $root" >&2
        return 1
    fi
    keyset="${resolved_root%/}/$keyset_id"
    _validation_check_authority_keyset "$keyset" "$output" || return 1
    printf '%s\n' "$keyset"
}

# 内部: lock の state が存在するか（形は問わない）。
_validation_keyset_lock_state_exists() {
    declare -p _VALIDATION_KEYSET_LOCK >/dev/null 2>&1
}

# 内部: state が lock の作った形か（非 export の配列、5 要素、fd は数字）。環境から来た変数は
# 配列にならず export 属性を持つので、ここで拒否される。
_validation_keyset_lock_state_is_well_formed() {
    local declaration
    declaration="$(declare -p _VALIDATION_KEYSET_LOCK 2>/dev/null)" || return 1
    [[ "$declaration" == "declare -a _VALIDATION_KEYSET_LOCK="* ]] || return 1
    (( ${#_VALIDATION_KEYSET_LOCK[@]} == 5 )) \
        && [[ "${_VALIDATION_KEYSET_LOCK[0]}" =~ ^[0-9]+$ && "${_VALIDATION_KEYSET_LOCK[1]}" =~ ^[0-9]+$ ]]
}

# 内部: fd の open file description が所有する排他 flock の dev:ino を stdout に出す（無ければ偽）。
_validation_fd_exclusive_flock_identity() {
    local fd="$1" line
    [[ "$fd" =~ ^[0-9]+$ && -r "/proc/self/fdinfo/$fd" ]] || return 1
    while IFS= read -r line; do
        if [[ "$line" =~ ^lock:[[:space:]]+[0-9]+:[[:space:]]+FLOCK[[:space:]]+ADVISORY[[:space:]]+WRITE[[:space:]]+[0-9-]+[[:space:]]+([0-9a-f]+:[0-9a-f]+:[0-9]+)[[:space:]] ]]; then
            printf '%s\n' "${BASH_REMATCH[1]}"
            return 0
        fi
    done < "/proc/self/fdinfo/$fd"
    return 1
}

# 内部: 所有の証明（冒頭の comment）。
_validation_keyset_lock_is_owned() {
    local primary="$1" shadow="$2" identity="$3" held
    [[ -n "$identity" && "$primary" != "$shadow" ]] || return 1
    held="$(_validation_fd_exclusive_flock_identity "$primary")" && [[ "$held" == "$identity" ]] || return 1
    held="$(_validation_fd_exclusive_flock_identity "$shadow")" && [[ "$held" == "$identity" ]]
}

# 内部: 所有の証明に加えて、keyset が今も lock した inode を指し、identity の判定を満たすか。
_validation_keyset_lock_is_valid_for() {
    local primary="$1" shadow="$2" identity="$3" keyset="$4" output="$5"
    _validation_keyset_lock_is_owned "$primary" "$shadow" "$identity" || return 1
    [[ ! -L "$keyset" && -d "$keyset" && "$keyset" -ef "/dev/fd/$primary" ]] || return 1
    _validation_check_authority_keyset "$keyset" "$output" 2>/dev/null
}

# keyset の inode を lock する。keyset は validation_resolve_authority_keyset の出力（同じ判定に
# かけ直す）。
# - 存在しなければ `mkdir -p -m 700` で作る。
# - 上限付きで待つ（`VALIDATION_KEYSET_LOCK_WAIT_SECONDS`、既定 120 秒）。超えたら
#   「held by another run for too long」で 1 を返し、keyset には何も書かない。
# - 取得後に所有・inode・identity を確かめる（待っている間の差し替えを拒否する）。
# - `chmod 700` は lock を取った後に、lock した inode に対して行う。
# - state が既にあれば（保持中・stale・偽造・環境由来のどれでも）2 を返す。
validation_lock_authority_keyset() {
    local keyset="$1" output="$2"
    local wait_seconds="${VALIDATION_KEYSET_LOCK_WAIT_SECONDS:-120}"
    local primary shadow identity resolved_output flock_status
    if _validation_keyset_lock_state_exists; then
        echo "Error: an authority keyset lock state already exists (held, stale, forged or from the environment); refusing to lock $keyset" >&2
        return 2
    fi
    if [[ ! "$wait_seconds" =~ ^[0-9]+([.][0-9]+)?$ ]]; then
        echo "Error: VALIDATION_KEYSET_LOCK_WAIT_SECONDS must be a non-negative number of seconds" >&2
        return 1
    fi
    _validation_check_authority_keyset "$keyset" "$output" || return 1
    resolved_output="$(realpath -m -- "$output")" || return 1
    if ! mkdir -p -m 700 -- "$keyset" 2>/dev/null || [[ -L "$keyset" || ! -d "$keyset" ]]; then
        echo "Error: authority keyset is not a directory and cannot be created as one: $keyset" >&2
        return 1
    fi
    if ! exec {primary}<"$keyset"; then
        echo "Error: authority keyset cannot be opened for locking: $keyset" >&2
        return 1
    fi
    flock_status=0
    flock -E 75 -w "$wait_seconds" "$primary" || flock_status=$?
    if (( flock_status != 0 )); then
        exec {primary}<&-
        if (( flock_status == 75 )); then
            echo "Error: authority keyset is held by another run for too long (${wait_seconds}s): $keyset" >&2
        else
            echo "Error: authority keyset cannot be locked (flock exit $flock_status): $keyset" >&2
        fi
        return 1
    fi
    if ! exec {shadow}<&"$primary"; then
        exec {primary}<&-
        echo "Error: authority keyset lock descriptor cannot be duplicated: $keyset" >&2
        return 1
    fi
    identity="$(_validation_fd_exclusive_flock_identity "$primary")" || identity=""
    if ! _validation_keyset_lock_is_valid_for "$primary" "$shadow" "$identity" "$keyset" "$resolved_output"; then
        exec {primary}<&- {shadow}<&-
        echo "Error: authority keyset was replaced while waiting for its lock, or its lock cannot be proven: $keyset" >&2
        return 1
    fi
    if ! chmod 700 -- "/dev/fd/$primary"; then
        exec {primary}<&- {shadow}<&-
        echo "Error: authority keyset permissions cannot be restricted: $keyset" >&2
        return 1
    fi
    _VALIDATION_KEYSET_LOCK=("$primary" "$shadow" "$identity" "$keyset" "$resolved_output")
}

# keyset lock を解放する（primary と shadow を閉じる）。state が無ければ何もしない。
# 所有の証明が成り立たなければ、どの fd も閉じずに 2 を返す（自分が取得した lock 以外を閉じない）。
# keyset の path が差し替えられていても、所有していれば閉じる（自分の lock の解放なので）。
validation_unlock_authority_keyset() {
    local primary shadow
    _validation_keyset_lock_state_exists || return 0
    if ! _validation_keyset_lock_state_is_well_formed \
        || ! _validation_keyset_lock_is_owned \
            "${_VALIDATION_KEYSET_LOCK[0]}" "${_VALIDATION_KEYSET_LOCK[1]}" "${_VALIDATION_KEYSET_LOCK[2]}"; then
        echo "Error: the authority keyset lock state does not match a lock this process holds; not closing any descriptor" >&2
        return 2
    fi
    primary="${_VALIDATION_KEYSET_LOCK[0]}"
    shadow="${_VALIDATION_KEYSET_LOCK[1]}"
    exec {primary}<&- {shadow}<&-
    unset _VALIDATION_KEYSET_LOCK
}

# 内部: 鍵を書く helper の共通の前提。key_file が「いま保持している keyset lock の keyset の直下の
# file」であることを確かめ、書き込み先（lock した inode の中の path）を stdout に出す。
_validation_keyset_member_target() {
    local key_file="$1" name
    if ! _validation_keyset_lock_state_exists; then
        echo "Error: no authority keyset lock is held for $key_file" >&2
        return 2
    fi
    if ! _validation_keyset_lock_state_is_well_formed; then
        echo "Error: the authority keyset lock state was not created by validation_lock_authority_keyset: $key_file" >&2
        return 2
    fi
    local primary="${_VALIDATION_KEYSET_LOCK[0]}" shadow="${_VALIDATION_KEYSET_LOCK[1]}"
    local identity="${_VALIDATION_KEYSET_LOCK[2]}" keyset="${_VALIDATION_KEYSET_LOCK[3]}"
    local output="${_VALIDATION_KEYSET_LOCK[4]}"
    if ! _validation_keyset_lock_is_owned "$primary" "$shadow" "$identity"; then
        echo "Error: the recorded authority keyset lock (fd $primary) is not held by this process: $key_file" >&2
        return 2
    fi
    name="${key_file##*/}"
    if [[ "${key_file%/*}" != "$keyset" ]] || ! _validation_path_component_is_valid "$name"; then
        echo "Error: authority key must be a file directly under the locked keyset $keyset: $key_file" >&2
        return 2
    fi
    if [[ -L "$keyset" || ! -d "$keyset" || ! "$keyset" -ef "/dev/fd/$primary" ]]; then
        echo "Error: authority keyset no longer names the locked directory: $keyset" >&2
        return 2
    fi
    _validation_check_authority_keyset "$keyset" "$output" || return 1
    if [[ -L "/dev/fd/$primary/$name" ]]; then
        echo "Error: authority key must not be a symlink: $key_file" >&2
        return 1
    fi
    printf '%s\n' "/dev/fd/$primary/$name"
}

# supervisor / worker の HMAC 鍵（32 byte）を具体化する。空または無ければ subshell の
# `umask 077` の中で一時 file に書き、32 byte を確かめてから atomic に置く（途中で止まっても
# 短い鍵を残さない）。既にあれば regular file であることだけ確かめて書き換えない（鍵の長さの
# 妥当性は読む側の supervisor_command が所有する）。
validation_materialize_process_key() {
    local key_file="$1" target temporary
    target="$(_validation_keyset_member_target "$key_file")" || return
    if [[ -e "$target" && ! -f "$target" ]]; then
        echo "Error: process authority key is not a regular file: $key_file" >&2
        return 1
    fi
    [[ -s "$target" ]] && return 0
    if ! temporary="$(umask 077; mktemp -- "$target.tmp.XXXXXX")"; then
        echo "Error: process authority key cannot be written: $key_file" >&2
        return 1
    fi
    if ! (umask 077; head -c 32 /dev/urandom > "$temporary") \
        || [[ "$(stat -c %s -- "$temporary" 2>/dev/null)" != 32 ]] \
        || ! mv -f -T -- "$temporary" "$target"; then
        rm -f -- "$temporary"
        echo "Error: process authority key cannot be written: $key_file" >&2
        return 1
    fi
}

# 内部: pair-status 鍵 CLI を 1 回呼ぶ。repo root で実行する（呼び出し側の cwd に依存しない。
# 相対の python_bin は呼び出し側の cwd で先に解決する）。失敗したら traceback を出さず、その
# stderr の最後の行（無ければ exit status）を理由にする。
_validation_pair_status_key_cli() {
    local python_bin="$1" failure="$2" error_output status=0 reason
    shift 2
    [[ "$python_bin" != */* || "$python_bin" == /* ]] || python_bin="$PWD/$python_bin"
    error_output="$(cd "$_VALIDATION_KEY_AUTHORITY_REPO_ROOT" \
        && "$python_bin" -m "$_VALIDATION_PAIR_STATUS_KEY_MODULE" "$@" 2>&1 >/dev/null)" || status=$?
    (( status == 0 )) && return 0
    reason="$(printf '%s\n' "$error_output" | tail -n 1)"
    echo "Error: $failure: ${reason:-exit $status}" >&2
    return 1
}

# pair-status 署名鍵の具体化規則（唯一の owner）。
# - 秘密鍵が空（無い）: 生成し、公開鍵も書く。
# - 秘密鍵だけある（出力 dir を消して取り直した等）: 秘密鍵から公開鍵を書き直す。
# - どの場合も最後に対を validate する。秘密鍵を書くのは空と判定したときだけで、
#   validate の後は書き換えない。
# 秘密鍵は保持している keyset の直下、公開鍵は lock で記録した OUTPUT の中でなければならない。
validation_materialize_pair_status_keypair() {
    local python_bin="$1" private_key="$2" public_key="$3" target public_target
    target="$(_validation_keyset_member_target "$private_key")" || return
    if ! public_target="$(realpath -m -- "$public_key" 2>/dev/null)" \
        || [[ "$public_target" != "${_VALIDATION_KEYSET_LOCK[4]}/"* ]]; then
        echo "Error: pair-status public key must be inside OUTPUT_BASE_DIR (${_VALIDATION_KEYSET_LOCK[4]}): $public_key" >&2
        return 1
    fi
    if [[ ! -s "$target" ]]; then
        _validation_pair_status_key_cli "$python_bin" "pair-status keypair cannot be generated" \
            --generate-private-key "$target" --write-public-key "$public_target" || return 1
    elif [[ ! -s "$public_target" ]]; then
        _validation_pair_status_key_cli "$python_bin" \
            "pair-status public key cannot be exported from the retained private key" \
            --export-public-from-private "$target" --write-public-key "$public_target" || return 1
    fi
    if ! _validation_pair_status_key_cli "$python_bin" \
        "pair-status private key and public key are not a valid pair" \
        --validate-private-key "$target" --public-key "$public_target"; then
        echo "Private key: $private_key" >&2
        echo "Public key: $public_target" >&2
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
