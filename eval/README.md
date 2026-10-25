# 全件評価の wrapper（`eval/`）

FULL_NEQ / FULL_EQBENCH の全件評価を、固定の条件（`profile.env`）で、中断と再開を含めて 1 つの
評価として実行する。`eval/` は analysis source digest の外にあり、ここを変えても評価の identity は
変わらない。

**wrapper は完了や正式性を判定しない。** 完了は `execution_chain verify`（実行の連鎖の検証器）と
verification ledger の full verdict だけが決める。runner の exit code は記録するが、完了の根拠に
しない。

## 使い方

評価用の worktree（freeze の commit、clean）から実行する。Neq を先に、Eq を後に、それぞれ手動で
起動する。

```bash
eval/neq.sh start --freeze <40 桁の commit>   # preflight の後、背景で実行（同じ command で再開）
eval/neq.sh status [--verify]                 # 読み取り専用。--verify で検証器も呼ぶ
eval/neq.sh stop                              # 正規の停止（docker stop、猶予は profile）
eval/neq.sh summary [--json]                  # 読み取り専用。完了の判定と集計
```

`status` / `stop` / `summary` の `--freeze` の既定は worktree の HEAD。`eval/eq.sh` も同じ。

## 置き場所

| 何 | どこ |
|---|---|
| 出力先（runner の証跡だけ） | `logs/EqBench/eval_<commit 12 桁>_<neq\|eq>/` |
| wrapper の記録 | 同じ場所の `.wrapper/`（`meta.json`、`events.jsonl`、`launches/<n>/`、`tmp/`、`authority/`） |
| slot の lock | `~/.cache/ghidra-eval/eval.lock`（`flock`。背景の supervisor が保持する） |

`launches/<n>/` には launch ごとに、`launch.json`（起動時の記録）、`container.json`、`watch.jsonl`
（cgroup の `oom_kill` / `memory.peak`）、`exit.json`（exit code・`OOMKilled`・この launch の
execution）、`runner.log`、`evidence.json`（終了直後の未終端の pair と検証器の判定）が残る。

## start の流れ

1. lock を `flock -n` で取る（取れなければ拒否）。
2. preflight（何も書かない）: profile、image、slot の container（状態を問わない）が無いこと、
   worktree が clean で HEAD が `--freeze`、disk の空き、条件の照合、出力先の検証。
3. 出力先が検証器で `CLOSED_SAME_IDENTITY` なら、**何も書かずに終了する**（評価は完了済み）。
4. それ以外: 初回は `meta.json` に条件を記録し、前回までの run tmpdir の残骸を消してから、
   背景の supervisor が container（`--init --network none --memory --memory-swap`）を起動する。
   supervisor は lock を受け継ぎ、container の終了・記録・削除の確認まで保持する。

条件（image の id、container の上限、profile の sha256、mount の path、container 内の path、
tool の version と cgroup の上限）の要約を `EQBENCH_ENVIRONMENT_FINGERPRINT` として runner に渡す。
runner は開始の記録に残し、検証器は execution 間の一致を要求する。**条件が違えば start は何も
書かずに拒否する。条件を変えるときは別の評価（別の `--tag` か commit）として始める。**

## 状態と、次にすること

| 状態 | 見え方 | 次にすること |
|---|---|---|
| 実行中 | `status`: container running、lock 保持 | 待つ。止めるなら `stop` |
| 停止・kill・異常終了の後 | container absent、lock free、verify OPEN | 同じ条件で `start`（確定済みの pair は再利用、未終端だけ再実行） |
| supervisor だけが消えた | container running か exited、lock free | `stop`（container を止め、終了を記録して消す）→ `start` |
| 終了の記録を書けなかった | slot の container が残る | 原因（disk など）を直して `stop` → `start` |
| 最初の execution が開始の記録の前に止まった | 出力先に manifest も開始の記録も pair も無い | `start` が出力先を `.wrapper/aborted-outputs/` へ移して新規に始める（削除しない） |
| 完了 | `summary` が `VERDICT: COMPLETE`（exit 0） | 何もしない。`start` は何も書かない |

`summary` の exit code: 0 = 完了、1 = 未完了（理由を列挙）、2 = 判定できない（検証器が動かない、
wrapper の記録が読めないなど）。完了には次のすべてが要る: 検証器が CLOSED、すべての execution が
この評価の fingerprint、ledger の full verdict、HEAD の一致、wrapper の記録に欠損なし、評価の
container が無いこと。gate（soundness / benchmark）の結果は別の欄に出し、完了の判定に混ぜない。

確定した ERROR / TIMEOUT は再開で再実行しない（一次結果として残る）。外部から kill されて終端
しなかった pair は未完了として再試行される。`summary` は、そのような pair を「外部 kill」と列挙し、
cgroup の `oom_kill` がその pair の実行中に増えていたとき（または container 自体が OOMKilled の
とき）だけ「OOM の可能性」と書く。

## 所要時間の目安（全件規模）

Eq の全件（49,320 pair、3 execution の合成 tree、本番の writer と署名）で、検証器 1 回が約 20 秒、
`summary` 全体が約 140 秒。`start` の preflight は検証器を 1 回、`status --verify` も 1 回呼ぶ。
