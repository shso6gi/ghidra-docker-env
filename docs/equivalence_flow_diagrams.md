# Equivalence Flow Diagrams

リファクタリング後の実装に合わせて、等価性判定まわりの主要フローを mermaid で整理したものです。
対象コードは主に [checker.py](/mnt/c/Users/saito/Git/ghidra-docker-env/scripts/function_tracer_pcode/checker/checker.py), [workflow.py](/mnt/c/Users/saito/Git/ghidra-docker-env/scripts/function_tracer_pcode/checker/workflow.py), [handler.py](/mnt/c/Users/saito/Git/ghidra-docker-env/scripts/function_tracer_pcode/checker/phases/handler.py), [pairwise.py](/mnt/c/Users/saito/Git/ghidra-docker-env/scripts/function_tracer_pcode/proof/strategies/pairwise.py), [analyzer.py](/mnt/c/Users/saito/Git/ghidra-docker-env/scripts/function_tracer_pcode/analysis/returns/analyzer.py) です。

## 1. 全体フロー図（エンドツーエンド）

```mermaid
flowchart TD
    A["check_from_binaries() 開始"] --> B["PhaseContext / DebugTrace / TypeFixResult を初期化"]
    B --> C{"retry_with_type_fix ?"}
    C -->|Yes| D["TypeFixer を両バイナリ分生成"]
    C -->|No| E["Phase plan を先頭から実行"]
    D --> E

    E --> F["Phase P0_BASE"]
    F --> G["初回のみ: 2関数を解析"]
    G --> H["stage plan 実行"]

    H --> I{"strategy = pairwise ?"}
    I -->|Yes| J["Stage S_PAIRWISE"]
    J --> K{"結果は UNKNOWN/TIMEOUT ?"}
    K -->|Yes| L["Stage S_MONOLITHIC_FALLBACK"]
    K -->|No| M["stage plan 終了"]
    I -->|No| N["Stage S_MONOLITHIC_FALLBACK のみ実行"]
    L --> M
    N --> M

    M --> O{"結果は EQUIVALENT ?"}
    O -->|Yes| P["終了: EQUIVALENT"]
    O -->|No| Q{"critical error ?"}
    Q -->|Yes| R["終了: ERROR/UNKNOWN"]
    Q -->|No| S{"結果は SAT<br/>(is_equivalent == False) ?"}

    S -->|Yes| T{"retry_with_type_fix かつ<br/>Phase 4-B 候補あり ?"}
    T -->|Yes| U["Phase 4-B: MIPS64 偽反例判定"]
    U --> V{"ABI 制約あり ?"}
    V -->|Yes| W["ABI 制約付きで再solve"]
    W --> X{"再結果は EQUIVALENT ?"}
    X -->|Yes| P
    X -->|No| Y["終了: NOT EQUIVALENT"]
    V -->|No| Y
    T -->|No| Y

    S -->|No| Z{"通常 retry 可 ?<br/>(UNKNOWN/TIMEOUT のみ)"}
    Z -->|No| R
    Z -->|Yes| AA["次の Phase へ"]

    AA --> AB["Phase P1_SIGNEDNESS"]
    AB --> AC["戻り値 signedness fix<br/>+ 引数 signedness fix"]
    AC --> AD{"変更が入った ?"}
    AD -->|No| AE["attempt 記録のみして次へ"]
    AD -->|Yes| AF["仮説 overlay 済み analysis view を再利用"]
    AF --> AG["再デコンパイルせず stage plan 再実行"]
    AG --> O
    AE --> AH["Phase P2_PATTERN_INT"]

    AH --> AI["戻り値 pattern fix<br/>+ 引数 type fix"]
    AI --> AJ{"変更が入った ?"}
    AJ -->|No| AK["P4-A tail 判定へ"]
    AJ -->|Yes| AL["仮説 overlay 済み analysis view を再利用"]
    AL --> AM["再デコンパイルせず stage plan 再実行"]
    AM --> O

    AK --> AN{"P4-A MIPS64 ABI fix を<br/>保守的に適用できる ?"}
    AN -->|No| AO["最後の結果で終了"]
    AN -->|Yes| AP["Phase 4-A 実行"]
    AP --> AQ{"変更が入った ?"}
    AQ -->|No| AO
    AQ -->|Yes| AR["analysis overlay reuse + stage plan 再実行"]
    AR --> AS{"結果は SAT かつ<br/>Phase 4-B 候補あり ?"}
    AS -->|Yes| U
    AS -->|No| AT{"結果は EQUIVALENT ?"}
    AT -->|Yes| P
    AT -->|No| AO
```

## 2. pairwise 戦略の内部フロー（1つの判定サイクル内）

補足:
P1/P2/P4-A の型修正 phase は Ghidra `Program` を更新しません。
各 phase は `FunctionReturnAnalysis` / `FunctionSignature` に仮説 overlay を重ね、
その effective analysis view を使って次の stage plan を再実行します。
そのため、retry 後に見ているのは「仮説を注入して永続変更した Program」ではなく、
「元 Program から得た解析結果に仮説コンテキストを重ねた view」です。

```mermaid
flowchart TD
    A["PairwiseStrategy.check()"] --> B["returns から ReturnCase 群を抽出"]
    B --> C["total_pairs = len(cases1) * len(cases2)"]
    C --> D{"total_pairs == 0 ?"}
    D -->|Yes| E["空結果を返す"]
    D -->|No| F["base_ctx を構築<br/>パラメータ置換関数を準備"]

    F --> G["全ペア (i, j) を順に走査"]
    G --> H["Stage 1: conds-only query を生成"]
    H --> I["SMT 実行<br/>(C1_i ∧ C2_j)"]
    I --> J{"UNSAT ?"}
    J -->|Yes| K["この条件組み合わせは到達不能<br/>pair = EQUIVALENT 扱い"]
    K --> L["次のペアへ"]

    J -->|No| M["Stage 2: with-ineq query を生成"]
    M --> N["SMT 実行<br/>(C1_i ∧ C2_j ∧ V1_i != V2_j)"]
    N --> O{"SAT ?"}
    O -->|Yes| P["決定的な反例を取得<br/>NOT EQUIVALENT で即終了"]
    O -->|No| Q{"UNSAT ?"}
    Q -->|Yes| R["値まで一致<br/>pair = EQUIVALENT"]
    R --> L
    Q -->|No| S["Normalization fallback へ"]

    S --> T["符号情報 / MIN 除外 / 条件事実を収集"]
    T --> U["式を正規化<br/>必要なら UDIV guard 付き正規化"]
    U --> V{"正規化で式が変化した ?"}
    V -->|No| W["pair = UNKNOWN"]
    W --> L
    V -->|Yes| X["norm-ineq query を生成"]
    X --> Y["SMT 実行<br/>(C1_i ∧ C2_j ∧ V1_norm != V2_norm)"]
    Y --> Z{"UNSAT ?"}
    Z -->|Yes| AA["正規化後に等価と確認<br/>pair = EQUIVALENT"]
    AA --> L
    Z -->|No| AB{"SAT ?"}
    AB -->|Yes| AC["正規化後でも反例あり<br/>NOT EQUIVALENT で即終了"]
    AB -->|No| AD["pair = UNKNOWN"]
    AD --> L

    L --> AE{"まだ未処理ペアがある ?"}
    AE -->|Yes| G
    AE -->|No| AF{"SAT pair があった ?"}
    AF -->|Yes| AG["最終結果: NOT EQUIVALENT"]
    AF -->|No| AH{"UNKNOWN pair があった ?"}
    AH -->|Yes| AI["最終結果: UNKNOWN"]
    AH -->|No| AJ{"全 pair が UNSAT ?"}
    AJ -->|Yes| AK["最終結果: EQUIVALENT"]
    AJ -->|No| AL["最終結果: UNKNOWN<br/>(想定外エラー混在)"]
```

## 3. 「1回の関数解析」で何をしているか（判定前処理）

```mermaid
flowchart TD
    A["ReturnAnalyzer.analyze_function_by_name()"] --> B["関数名から Function を取得"]
    B --> C{"関数が見つかった ?"}
    C -->|No| D["None を返す"]
    C -->|Yes| E["analyze_function() へ"]

    E --> F["Decompiler で decompileFunction()"]
    F --> G{"decompile 成功かつ HighFunction あり ?"}
    G -->|No| D
    G -->|Yes| H["PcodeTracer を生成"]
    H --> I["ConditionTracker を生成"]
    I --> J["PhiHandler を生成して tracer に注入"]
    J --> K["ConditionTracker.build() で<br/>ブロック情報と条件追跡を準備"]

    K --> L["パラメータ情報を収集<br/>(name, type, signed, storage, index)"]
    L --> M["戻り値型を取得"]
    M --> N["SignednessDetector で<br/>戻り値まわりの符号性を推定"]
    N --> O["RETURN P-code を列挙"]

    O --> P["各 RETURN を順に解析"]
    P --> Q["RETURN までの path conditions を取得"]
    Q --> R{"戻り値入力がある ?"}
    R -->|No| S["void return として<br/>unknown('void') を記録"]
    R -->|Yes| T["return varnode を解析"]

    T --> U{"値チェーンに MULTIEQUAL がある ?"}
    U -->|Yes| V["PHI ベース展開<br/>expand_from_varnode(..., [])"]
    U -->|No| W["path conditions 付き展開<br/>expand_from_varnode(..., path_conditions)"]
    V --> X["候補 value + conditions 群を得る"]
    W --> X

    X --> Y["各候補について矛盾条件を除外"]
    Y --> Z{"有効候補がある ?"}
    Z -->|Yes| AA["conditions を簡約して<br/>ReturnInfo として追加"]
    Z -->|No| AB["simple trace にフォールバック<br/>trace_varnode() の結果を使う"]
    AB --> AC["path conditions を簡約して<br/>ReturnInfo を1件追加"]
    AA --> AD{"まだ RETURN が残っている ?"}
    AC --> AD
    S --> AD
    AD -->|Yes| P
    AD -->|No| AE["FunctionReturnAnalysis を構築"]
    AE --> AF["debug 時は dump / coverage / unknown summary を出力"]
    AF --> AG["解析結果を返す"]
```
