# TIMEOUT / 長時間 pair のプロファイリングと診断（Issue #124）

「どの処理で時間を使ったか」「kill された瞬間に何をしていたか」を、結果 JSON が
出ない pair でも調べるための手順。**ここに出てくる値はすべて診断で、判定
（canonical outcome / UNKNOWN reason / proof gate）には一切関与しない。**

- PR-124-A: `diagnostics.timings` の region 階層・恒等式・solver counter
- PR-124-B: kill されても残る stage journal と faulthandler の登録契約
- PR-124-C: deadline 手前の stack dump 要求、dump の永続化、`timeout_kind`、hotspot

---

## 1. 1 pair が残す file

| file | 書き手 | cleanup 後 |
|---|---|---|
| `<pair>.log` | child（CLI） | 残る |
| `<pair>.pair-status.json` | runner（署名済み） | 残る |
| `<pair>.stage.jsonl` | child（`StageJournal`） | 残る |
| `.runtime-metrics/<pair>.stack-dump.txt` | supervisor が退避 | 残る |
| `.runtime-metrics/<pair>.stack-dump.status.json` | supervisor | 残る |
| `.runtime-metrics/<pair>.runtime.json` | runner | 残る |
| `<checkpoint>/<nonce>/stack-dump.txt` | child の faulthandler | **消える** |
| `<checkpoint>/<nonce>/canonical-result-envelope.json` | child | **消える** |

`process_authority_cleanup` は pair の直後に checkpoint を消し、run 終了時に
`EQBENCH_RUN_TMPDIR` ごと消える。したがって **checkpoint 配下の file は正本に
しない**。dump の正本は `.runtime-metrics/<pair>.stack-dump.txt`。

## 2. stage journal（`<pair>.stage.jsonl`）の読み方

schema `pair-stage-journal-v1`、append-only JSONL、1 行 = 1 event。
key は `schema` / `seq` / `event` / `stage` / `seconds` / `t_monotonic` /
`t_epoch` / `pid` / `payload`。`event` は `handler_registered` / `stage_start` /
`stage_end` / `counter` / `note` の 5 種類。

```bash
# 最後の 20 行（kill 直前に何をしていたか）
tail -n 20 logs/EqBench/<run>/eq/<sample>/<fn>/<pair>.stage.jsonl |
  python3 -c 'import json,sys
for line in sys.stdin:
    row = json.loads(line)
    print(row["seq"], row["event"], row["stage"], row["seconds"])'
```

読むときの注意:

- **最後に完了した stage は kill 後の teardown になり得る。** SIGTERM を受けた
  child は `close_programs` などの後始末を走らせてから終わるので、`stage_end` の
  最後の行がそこになることがある。時間の所在は
  `longest_completed_stage`（完了区間のうち最長）と各行の `seconds` で見る。
- **進行中の stage は推定で、どの瞬間の推定かで変わる。** `stage_start` があって
  対応する `stage_end` が無い区間のうち一番内側のもの。journal の末尾まで読むと、
  teardown まで走った pair では全部閉じていて空になる。そこで集計側は
  sidecar の `signal_sent_epoch`（stack dump を撮った瞬間）で journal を切り、
  **候補 frame と同じ瞬間**に開いていた region を `in_progress_stage` にする。
  どちらから取ったかは `in_progress_stage_basis`（`at_stack_dump` /
  `journal_end` / `none_open` / `(unknown)`）に残る。
- 末尾 1 行が途中で切れていることがある（SIGKILL）。`partial_final_line` として
  数え、壊れた行（`malformed_lines`）とは分けて扱う。

### multi-execution journal

journal path は pair 固定（`${log%.log}.stage.jsonl`）で、runner は新規実行が
確定した pair についてのみ child 起動前に journal を捨てる（PR-124-B）。
**supervisor recovery が child を再起動する経路**では、同じ file に 2 つ目の
execution が追記され得る。混在の検出条件は

1. `seq` の巻き戻り（直前の行の `seq` 以下）
2. `pair_journal_opened` note が 2 本以上
3. `handler_registered` の `pid` / `start_token` が current child と不一致

の 3 つ。`core/stage_journal_reader.py` は行を execution segment に切り、
**current child に一意に結び付く segment だけ**を使う。一意に選べない場合は
`unavailable:ambiguous_multi_execution` として、stage も dump も推測しない。
前の execution の readiness を current の送信可否に使うこともしない。

「検出できるからそのまま全行を読んでよい」ではない。混在を見つけたら
**合算せず unknown に落とす**のが正しい扱い。

## 3. handler readiness と SIGUSR1

child は JVM 起動より前に
`faulthandler.register(SIGUSR1, file=<checkpoint>/stack-dump.txt, all_threads=True, chain=False)`
を呼び、**例外なく返った場合だけ** `handler_registered` を journal に書く。

- `/proc/<pid>/status` の `SigCgt` は `payload.sigcgt_probe` に補助情報として
  併記するだけで、readiness の根拠にしない（JVM は多数の handler を登録する）。
- 登録に失敗したら `note: handler_registration_failed:<例外型>` だけを書く。
- `chain=False` は「登録時点の previous handler へ連鎖しない」設定であって、
  あとから別の handler に上書きされないことを保証するものではない。JVM 起動後も
  Python の faulthandler が効くことの根拠は実 JVM 子プロセス test。

supervisor は deadline の `PAIR_STACK_DUMP_LEAD`（既定 2s）前に **1 回だけ**
診断を要求する。送信条件は次の全部:

- current execution segment に register 成功由来の `handler_registered` がある
- その行の `pid` / `start_token` が current child と一致する
- `signal_number` が SIGUSR1、`all_threads` が true、`dump_path_tmp` /
  `dump_artifact_path` が今の pair の設定と一致する
- 送信直前の cancel 確認と identity 再確認を通る
- 同一プロセスへ束縛された pidfd から送れる（`os.pidfd_open` +
  `signal.pidfd_send_signal`）。束縛できない環境では送らず
  `unavailable:identity_binding_unavailable`

**process group へは送らない**（`killpg` は使わない）。送信も dump の観測も
daemon worker thread の中だけで行い、監視ループは join しない。診断が遅くても
失敗してもハングしても、**worker thread を作れなくても**、kill 開始は deadline
から 0.5 秒以内。

**cancel と「送信開始」には linearization point があり、監視ループは何も待たない。**

「送信の直前に cancel を見る」だけでは check-then-act のままで、確認後・送信前に
cancel が完了する interleaving が残る。かといって cancel が送信用の lock を
**待つ**設計にすると、今度は診断 worker が syscall で止まっているあいだ監視ループの
kill 開始が遅れてしまう（deadline を診断に引きずられる）。

そこで **「送信開始の順序づけ」と「syscall の完了」を分ける**。
一度きりの送信権 `_send_permit` を置き、worker も cancel も
`acquire(blocking=False)` でしか触らない:

| 先に権利を取った側 | 結果 |
|---|---|
| cancel | worker は以後 `acquire` に失敗し、**送信を開始しない**（`refused_cancelled`） |
| worker | 送信は「開始済み」。cancel は取得に失敗して**即座に戻り**、syscall の完了は待たない |

どちらも待たないので、監視ループが診断の lock や I/O で止まることはない。
送信が先に linearize した場合、あとから来た cancel でその事実を取り消さない
（`signal_sent` は true のまま、`unavailable_reason` に `cancelled` は入らない）。
どちらが先だったかは `send_claimed_offset_seconds` と
`cancel_linearized_offset_seconds` の順序で読める。

journal 読取・`pidfd_open`・identity 確認・dump polling は権利取得より**前**
（= 権利を持たない状態）で行うので、そこで時間がかかっても cancel は待たされない。

`signal_start_state` は `signal_sent` の bool では潰れる区別を持つ:

| 値 | 意味 |
|---|---|
| `sent` | 送信の syscall が戻り、**送信成功を確認した** |
| `claimed_not_sent` | **送信権は取ったが、送信成功をまだ確認できていない。** syscall が失敗した場合だけでなく、まだ実行中（in-flight）・ハングしている・worker がその途中で失敗した場合も含む |
| `refused_cancelled` | cancel が先に権利を取ったので、送信を開始しなかった |
| `not_requested` | 診断そのものを要求していない（deadline 前に終了した pair） |
| `not_claimed` | 要求はしたが readiness などで権利取得まで進まなかった |

`claimed_not_sent` を「失敗」と読まないこと。**明示的な失敗は
`unavailable_reason`** が `signal_failed:<例外型>` / `process_exited` として持つので、
区別はそちらで行う。

`send_claimed` は送信権の所有そのものから導く（acquire の直後に別 flag を立てる
形だと、その 2 命令のあいだに status を snapshot されたときに「権利は持っているのに
`false`」と見える window が残る）。cancel 側にも同様の window はあるが、
`cancel_future_requests()` も `status_payload()` も監視スレッドが呼ぶので、
その thread が自分の中間状態を観測することはない。

deadline の起点は barrier 解放の直後で 1 回だけ固定し、診断 object の生成は
そのあと。診断を足したぶん child の実効予算が伸びることはない。

## 4. 診断状態（`<pair>.stack-dump.status.json`）

schema `pair-stack-dump-status-v1`。4 つの状態を**別々に**持つ。

| key | 意味 |
|---|---|
| `handler_registered` | child が faulthandler を登録できたか |
| `signal_sent` | supervisor が SIGUSR1 を送ったか |
| `dump_observed` | 送ったあと dump file の増加を観測できたか |
| `sent_but_unobserved` | 送ったが観測できなかった（**dump が無い、ではない**） |
| `unavailable_reason` | 送らなかった / 送れなかった理由 |
| `artifact_status` | `copied` / `partial` / `missing` / `copy_failed:<errno>` / `unset` |
| `deadline_finalization_offset_seconds` | deadline 到達 → termination path へ入るまで（**まだ signal は送っていない**） |
| `kill_signal` / `kill_start_offset_seconds` | **実際に**最初の termination signal（SIGTERM）を送れた時刻と、deadline からの実測秒。送る前に child が終了した pair は `null`（kill を開始したと記録しない） |
| `signal_sent_epoch` | dump を撮った瞬間（journal を切って `active` を出すのに使う） |
| `send_claimed` / `send_claimed_offset_seconds` | 送信権を取った（送信開始が linearize した）時刻。syscall の成否とは別 |
| `signal_start_state` | 下表の 5 値。`signal_sent=false` の中身を潰さない |
| `cancel_linearized_offset_seconds` | cancel が送信権を取った時刻。取れなかった（worker が先だった）場合は `null` |
| `child_timeout_evidence` | cleanup 前に検証した子の terminal timeout 証拠 |

「送った」と「取れた」を同一視しない。`sent_but_unobserved` の pair でも、
supervisor は終了処理のあとに改めて退避を試すので `artifact_status` が
`copied` になることがある。`missing` を名乗るのは、退避時に dump が存在しない
（または 0 byte）ことを確認したときだけ。

**取得できた dump は最終 outcome によらず保存する。** deadline 前に正常終了した
pair の dump も `.runtime-metrics` に残る。

## 5. `timeout_kind`

`reporting/timeout_hotspot_summary.py` が、**独立した 2 本の必須証拠**から分類する。
payload の有無・log の文字列・returncode 単独からは推定しない。

- **P（supervisor process deadline）**: `canonical_outcome=TIMEOUT` /
  `supervisor_status=TIMEOUT` / `supervisor_authority_kind=DurableTimeoutFinalizationBundle` /
  `child_exit_disposition` が deadline 経路の disposition
  （`SIGTERM_AFTER_DEADLINE` / `SIGKILL_AFTER_DEADLINE` /
  `EXITED_<n>[_BEFORE|_AFTER_SIGTERM|SIGKILL]`）に**完全一致** /
  `child_returncode` が既存 validator と一致 / `classification_valid`。
- **S（子の solver timeout）**: 子の canonical bundle を**検証**し、identity が
  この pair・この execution に束縛され、outcome が TIMEOUT で、terminal timeout が
  solver（`terminal_timeout_candidate_selection_receipt.solver_invocation_id`）で
  識別できること。`RESOLVED + returncode=3` だけでは S にしない。

  **どこまで検証したかを混ぜない。** S の経路は 2 つあって強さが違う:

  | 経路 | `verification` | 確定 S になるか |
  |---|---|---|
  | supervisor が cleanup 前に signing key で検証し sidecar に残した証拠 | `supervisor_key_verified` | なる（**優先**） |
  | pair log の bundle を key 無しで読んだもの（封あり） | `replay_only_unsigned` | **ならない**（`supervisor_key_verification` が欠落） |
  | pair log の bundle に key を渡して読んだもの | `supervisor_key_verified` | なる |
  | 封の無い bundle（`bundle_seal_key_id` が null。開発・test 用） | `unsealed_bundle` | なる |

  key 無しの `validate_canonical_result_finalization_bundle` は digest と event
  stream の replay しか見ず、`bundle_signature` を検査しない。body を書き換えて
  digest を計算し直した bundle は digest 検査を通ってしまうので、封のある bundle
  を key 無しで「検証済み」と呼ばない。集計 CLI は key を渡さない（run 中と
  offline 再集計で同じ結果にするため）ので、実運用の S は sidecar 経由になる。

| `timeout_kind` | 条件 |
|---|---|
| `process_wall_clock` | P のみ |
| `child_solver_timeout` | S のみ |
| `both_signals` | P と S が独立に成立 |
| `unknown` | TIMEOUT だが根拠不足 / 検証失敗 / 矛盾 |
| `not_applicable` | 検証済みの最終 outcome が TIMEOUT 以外 |

#129（異常終了の分類）と #106（analysis budget）はこの taxonomy に混ぜない。

## 6. hotspot と候補 frame

stack dump は **全 thread**（`Thread 0x…` と `Current thread 0x…` の両方）を
解析する。各 block の最内 frame（`most recent call first` の先頭）を
`candidate_frames` として並べ、関数名に `wait` / `acquire` / `select` / `poll` を
含む frame には `waiting` 印を付ける。

**候補 frame は root cause ではない。** kill された瞬間にその thread がいた
観測点でしかなく、待機中の frame は「待たせている側」ではない。

表の軸は `last_completed_stage × in_progress_stage × candidate_frame`。
`last_completed_stage` は journal 末尾のもの（kill 後の `close_programs` に
なり得る）、`in_progress_stage` は dump を撮った瞬間のもの、`candidate_frames` も
同じ瞬間のもの。時間の所在は `longest_completed_stage` で見る。
どの次元も、値が観測できなかった pair は `(unknown)` bucket に入る。
**`(unknown)` と 0 件（`(none)`）を潰さない。**

## 7. offline 再集計

run 中に runner が gate の直後で実行するのと同じコマンドを、run 終了後に
そのまま流せる。読むのは run dir に残る file だけなので、checkpoint cleanup 後も
同じ表が出る。

```bash
python3 -B -m scripts.function_tracer_pcode.reporting.timeout_hotspot_summary \
  logs/EqBench/<run>/eq logs/EqBench/<run>/neq \
  --json /tmp/timeout_hotspot_summary.json \
  --health-summary-json logs/EqBench/<run>/eq/run_health_summary.json \
  --health-summary-text logs/EqBench/<run>/eq/run_health_summary.txt
```

`run_health_summary.{json,txt}` には `timeout_diagnostics` 節として
`timeout_kind` / `timeout_hotspots` などが入る。**この節が無い run は
「TIMEOUT が 0 件」ではなく「集計していない」**（PR-124-C 以前の run も同じ）。

## 8. `PAIR_PROCESS_TIMEOUT=60s` の診断 run

わざと短い deadline で走らせ、TIMEOUT pair を多く作って診断経路
（registration → 送信 → 観測 → 退避 → 分類 → hotspot）を確かめるための run。

```bash
ANALYSIS_TIMEOUT=0 PAIR_PROCESS_TIMEOUT=60s OUTPUT_BASE_DIR=logs/EqBench/subset_issue124_t60 \
  bash eqbench_run_subset.sh
```

`ANALYSIS_TIMEOUT=0` が要る（Issue #106 PR-106-B 以降）。固定 subset の既定の解析の期限
（115 s）と余裕は 60 s の process timeout に収まらないので、指定しないと runner は pair を
始めずに exit 1 する。また期限があると pair は process TIMEOUT の前に理由付き UNKNOWN で
終わり、この run が作りたい TIMEOUT 経路を通らない。

**これは評価ではない。** 60s は本番の予算（既定 600s、固定 subset は 240s）より
ずっと短いので、ここで出た TIMEOUT 件数・outcome 分布・reason 集合を
通常 run の遷移比較に使ってはいけない。目的は診断経路の確認だけ。
**FULL_EQBENCH / FULL_NEQ の代わりにもならない。**

## 9. cProfile で 1 pair を掘る

runner を通さず 1 pair を直接プロファイルする（専用の env var は無い。
`cProfile` を CLI の前に噛ませるだけ）:

```bash
python3 -B -m cProfile -o /tmp/pair.prof \
  -m scripts.function_tracer_pcode.cli.main \
  --equiv <left> <right> -f <fn> --emit-result-json
python3 -c "import pstats; pstats.Stats('/tmp/pair.prof').sort_stats('cumulative').print_stats(40)"
```

authority の finalize 区間（`_profiled_finish`）だけを見たいときは、既存の
`UNKNOWN_TAXONOMY_V2_PROFILE_FINISH_DIR` に出力先ディレクトリを渡す
（`authority/lifecycle/production_boundary.py`）。区間ごとの秒数は結果 JSON の
`diagnostics.timings`（`stages` / `regions` / `phases` / `boundary_seconds`）にも
入っているので、まずそちらを見てから profile を取ると当たりが早い。

## 10. 解析の期限（`ANALYSIS_TIMEOUT`）と margin の実測（Issue #106 PR-106-B）

runner は pair に解析の期限（`--analysis-timeout`）を渡し、`ANALYSIS_TIMEOUT +
ANALYSIS_TIMEOUT_MARGIN <= PAIR_PROCESS_TIMEOUT` を run の開始前に確かめる
（規則は `reporting/runner_timeout_policy.py`、使い方は README の
"Analysis deadline (Issue #106)"）。margin は「期限で打ち切った pair が、process の期限
（と supervisor の stack dump の先行時間）より前に終わる」ための余裕で、その根拠は次の
道具で run の出力から測る:

```bash
python3 -B -m scripts.function_tracer_pcode.reporting.deadline_margin_summary \
  logs/EqBench/<run>/eq logs/EqBench/<run>/neq --json /tmp/margin.json
```

期限で打ち切った pair 1 件を、重ならない連続した区間に分ける（二重計上しない。
`needed = wall − 期限 = pre + overrun + post_trip + tail` が恒等式で成り立つ）:

| 区間 | 内容 | 端点 |
|---|---|---|
| `pre` | 解析の外の固定費（supervisor・CLI の起動、JVM、project open、import、auto analyze） | supervisor の開始 → 期限の起点 |
| `overrun` | checkpoint の無い区間・止まるまで戻らない処理（協調的な solver の停止と join を含む）。負の値は「期限まで sub-operation の余裕 0.5 s を切ったので始めなかった」 | 期限 → trip |
| `post_trip` | 限界の帰属・結果の組み立て・出力の準備（`unwind`）、`connector.finish`・receipt（`authority_finalize`）、conditional lane、`close_programs`、結果 JSON（`result_emit`） | trip → 最後の journal event |
| `tail` | JVM の停止・process の終了・supervisor の pair status の durable write・回収 | 最後の journal event → runner が終わりを観測 |

Neq の runner は per-pair の runtime receipt を書かない（#160）ので、Neq の pair は
`overrun` / `post_trip` / `pre_child`（child の journal の開始から）だけを持ち、`pre` /
`tail` / `needed` には入らない。

### 採用値の根拠（PR-106-B、commit `aa06b462`、2026-10-02）

条件: 固定 subset（`PAIR_PROCESS_TIMEOUT=240s`、P=20、identical fast path 1）を期限 30 s
（診断）と 120 s、P-ell（ell `B12_B16`、600 s、P=6）を期限 480 s で 1 本ずつ。他 session の
run と一部重なった（host の load average は最大 41.7）。

| 区間 | 30 s subset（trip 43、うち receipt あり 23） | 120 s subset（trip 5 / 2） | 480 s P-ell（trip 6 / 6） | 最大 |
|---|---|---|---|---|
| `pre` | median 19.6 / p90 24.7 / max 30.4 | max 29.5 | median 7.7 / max 9.6 | **30.4** |
| `overrun` | median 0.18 / p90 2.1 / max 5.1 | max 1.1 | max 6.9 | **6.9** |
| `post_trip` | median 0.47 / p90 1.8 / max 11.8 | max 18.9 | max 56.5（CheckCond: `authority_finalize` 38.9 + `result_emit` 17.5） | **56.5** |
| `tail` | median 1.5 / p90 2.5 / max 2.8 | max 5.5 | max 27.8 | **27.8** |
| `needed`（実際の合計） | max 32.9 | max 53.9 | max 85.1 | 85.1 |

margin = 区間ごとの最大の和 121.6 s + stack dump の先行時間 2 s = 123.6 s を 5 s 単位に
切り上げた **125 s**。既定の期限はそこから決まる: full は 600 − 125 = **475 s**、固定 subset は
240 − 125 = **115 s**（計画の暫定値 480 / 120 s はこの和を収められなかった）。

- 区間の最大は別の pair・別の run の値を足している（同時に起きた値ではない）ので、1 pair の
  実際の合計の最大（85.1 s）より大きい。full run は高負荷（固定費が大きい）と長い期限
  （確定処理が重い）が同時に起き得るので、和を採った。
- 協調的な worker の停止・join は `overrun` に含まれる（PR-106-A の実測で z3 の
  interrupt 後の戻りは最大 0.12 s）。足し直していない。止められない worker（能力を宣言
  しない backend）の join は有限の上限が無いので margin に入れない: その pair は
  supervisor の TIMEOUT（fallback）になり、保証の対象外（Class B）。
- PR-106-A の候補値との照合: 固定費 ~50 s（高負荷）→ 今回 30.4 s、`connector.finish`
  最大 25 s → 今回 38.9 s（大きくなった）、出力最大 12 s → 17.5 s、checkpoint の無い区間の越え
  28.8 s（`61a51f5`、高負荷）→ 今回の最大 6.9 s（再現せず。margin には入れていない）。
- **観測した最大は保証ではない。** 件数が少なく（p99 は n ≥ 100 の区間だけ）、full run と
  高負荷（load > 50）の profile は測っていない。margin を越えた pair は process TIMEOUT
  （`Outcome.TIMEOUT`、exit 3）として記録され、別の結果に化けない。`PAIR_STACK_DUMP_LEAD` を
  大きくしたとき、または上の区間が増えたときは、この表を取り直して margin を見直す。
