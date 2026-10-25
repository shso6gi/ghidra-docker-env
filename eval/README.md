# 全件評価の wrapper（`eval/`）

FULL_NEQ / FULL_EQBENCH の全件評価を、固定の条件（`profile.env`）で、中断と再開を含めて 1 つの
評価として実行する。`eval/` は analysis source digest の外にあり、ここを変えても評価の identity は
変わらない。

**完了の判定は 1 つだけ。** `summarize.py` の `completion` が、次の owner の判定を並べて決める。
`summary` の VERDICT と、`start` の「完了済み（何もしない）」は同じ結果を使う。

| 条件 | owner |
|---|---|
| 実行の連鎖が CLOSED | `reporting/execution_chain.verify_execution_chain` |
| 正式な full verdict | `verification_ledger.build_row` + `full_scope_evidence` |
| HEAD の一致 | `verification_ledger.head_match` |
| すべての execution がこの評価の条件 | `meta.json` の fingerprint と各開始の記録 |
| wrapper の記録が終端し、壊れていない | `records.py`（launch の状態機械、execution との対応） |
| 評価の container が無い | host での観測（観測できなければ判定しない） |

runner の exit code は記録するが、完了の根拠にしない。gate（soundness / benchmark）は別の欄に出し、
完了に混ぜない。

## 使い方

評価用の worktree（freeze の commit、clean）から実行する。Neq を先に、Eq を後に、それぞれ手動で。

```bash
eval/neq.sh start --freeze <40 桁の commit>   # preflight の後、背景で実行（同じ command で再開）
eval/neq.sh status [--verify]                 # 読み取り専用（--verify で検証器も呼ぶ）
eval/neq.sh stop                              # 停止（docker stop、猶予は profile）と、未完了の launch の回収
eval/neq.sh summary [--json]                  # 読み取り専用。完了の判定と集計
```

`status` / `stop` / `summary` の `--freeze` の既定は worktree の HEAD。`eval/eq.sh` も同じ。

`summary` の exit code: 0 = 完了、1 = 未完了（理由と分類を列挙）、2 = 判定できない（記録の破損、
読み取りの失敗、container の状態を観測できない、集計の欄を作れなかった）。

## 置き場所と記録

| 何 | どこ |
|---|---|
| 出力先（runner の証跡だけ） | `logs/EqBench/eval_<commit 12 桁>_<neq\|eq>/` |
| wrapper の記録 | 同じ場所の `.wrapper/`（`meta.json`、`events.jsonl`、`launches/<n>/`、`tmp/`、`authority/`） |
| slot の lock | `~/.cache/ghidra-eval/eval.lock`（`flock`。背景の supervisor と `docker run` の CLI が保持する） |

launch（`start` 1 回）の記録は、次の順に 1 つずつ確定し、上書きしない（`records.py`）。

1. `launch.json` — 起動の要求（staging dir に書き、rename 1 回で `launches/<n>` になる）
2. `container.json` — `docker run` が返した container（作られていたのに記録の前に止まった場合は、
   回収が名前と label で見つけて記録する）
3. `runner.log` → `exit.json` — 終了の観測（exit code・`OOMKilled`・この launch の execution・
   `runner.log` の sha256）。`docker logs` が失敗したら何も保存しない
4. `evidence.json` — 未終端の pair の写しと検証器の判定（次の再開が pair の診断を消す前に取る）
5. `released.json` — `docker rm` の後、container が「存在しない」と観測できたとき

`exit.json` の種類: `ran`（終了を観測した）／`not_started`（container は作られなかった）／
`exit_unobserved`（wrapper の外で container が消され、終了を観測できなかった。permanent）。

`watch.jsonl` には cgroup の観測を **毎回**（既定 10 秒ごと）1 行で残す。読めなかった観測も
`observed: false` で残す。

## 状態と、次にすること

| 状態 | 見え方 | 次にすること |
|---|---|---|
| 実行中 | `status`: container running、lock 保持 | 待つ。止めるなら `stop` |
| 停止・kill・異常終了の後 | container absent、launch は終端 | 同じ条件で `start`（確定済みの pair は再利用、未終端だけ再実行） |
| launch が未完了（supervisor が消えた、記録・削除・docker の操作が失敗した、起動の前に止まった） | `status`: `launch n is unfinished (...)`。`start` は拒否 | `stop`（container を止め、記録の続きから終端まで進める）→ `start` |
| 記録が壊れている（確定した記録の欠損・不整合、launch の欠番、journal との食い違い、出力先の execution との対応の不一致） | `status`: `DAMAGED: ...`、`summary` は判定できない | 自動では直さない。原因を調べる |
| 最初の execution が開始の記録の前に止まった | 出力先に manifest も開始の記録も pair も無い | `start` が出力先を `.wrapper/aborted-outputs/` へ移して新規に始める（削除しない） |
| 完了 | `summary` が `VERDICT: COMPLETE`（exit 0） | 何もしない。`start` は何も書かない |
| chain は CLOSED だが ledger が正式性を拒否 | `summary`: `no_full_verdict` | `start` は再開する（完了とは言わない） |
| 正式な完了に到達できない（permanent） | `summary`: `[permanent] ...` | この評価の記録を残し、別の `--tag` で新しい評価を始める |

**理由の分類と `start` の決定**（`protocol.py` の登録表が唯一の owner。`summary` も同じ分類を出す）

| 分類 | 意味 | 例 |
|---|---|---|
| resumable | 同じ条件で runner を再び動かせば進む | 出力先が無い、連鎖が OPEN、full verdict が無い、最新の execution の commit が HEAD と照合できない |
| blocking | この評価への運用の操作（`stop`）が先に要る。操作の後は続けられる | 未完了の launch、評価の container が残っている |
| permanent | この評価は正式な完了に到達できない | wrapper の外で container が消され終了を観測できなかった launch、別の条件で動いた execution |
| unverifiable | 判定できない | 記録の破損、読み取りの失敗、container の状態を観測できない |

`start` は、COMPLETE なら何もしない。permanent・blocking・unverifiable（または未知の分類）が
**1 つでもあれば**、他の理由が何であっても何も書かずに拒否する。permanent のときは、この評価の記録を
残したまま、別の評価（別の `--tag`）として始め直す。resumable だけのときだけ再開する。

**reader の応答の受理**: 読み取り専用の container の応答（完了の判定・launch の証拠・検証器・summary）は、
要求ごとの終了コードと応答の形の **両方** を満たすときだけ受理する。非 0 終了の正しい JSON も、0 終了の
別の形の JSON も、途中で切れた出力も受理しない。受理しなかった応答からは何も記録せず、container を
残す（`stop` が正常な応答で再試行する）。`summary` の終了コードも受理した結果から決める。

確定した ERROR / TIMEOUT は再開で再実行しない（一次結果として残る）。外部から kill されて終端
しなかった pair は未完了として再試行される。

**中断の集計**: launch の証拠（`evidence.json`）は、その時点の出力先にある未終端の receipt の写しで、
前の execution が残したものも含む。集計は、receipt の execution（run_id）を記録した launch に帰属させて
から行う。同じ `(run_id, nonce, pair)` を複数の launch の写しで見たものは 1 件（重複観測）で、同じ pair
でも別の execution・nonce で再び止まったものは別の件（実際の再試行）。どの launch も記録していない
execution の receipt は「帰属不明」として別に出し、どの launch の現象にもしない。

`summary` は、外部 kill の OOM の可能性を、**その件の launch の** 観測と `OOMKilled` から
`yes`（実行中に、直前の有効な観測からの区間で `oom_kill` が増えた、または container が OOMKilled）／
`no`（実行区間を観測が覆い、増分が 0）／`unobserved`（それ以外）で示す。SIGKILL だけからは OOM と書かない。

## 所要時間の目安（全件規模）

Eq の全件（49,320 pair、3 execution の合成 tree、本番の writer と署名）で、検証器 1 回が約 20 秒、
`summary` 全体が約 140 秒。`start` の preflight は `completion` を 1 回呼ぶ（検証器と ledger を含む）。
