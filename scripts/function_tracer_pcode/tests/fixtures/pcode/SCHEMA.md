# `recorded-pcode-fixture-v1`

実 Ghidra が返した P-code / API surface の記録形式。**Ghidra 無しで、production
connector 付きの `check_from_binaries` を同じ経路で再生する**ためだけに存在する
（Issue #109 PR-A）。

- 記録器: `scripts/function_tracer_pcode/tests/tools/record_pcode_fixture.py`（PyGhidra 必須）
- 再生器: `scripts/function_tracer_pcode/tests/fixtures/pcode/recorded_program.py`
- surface 定義（key の綴り・値の符号化・検証）: `schema.py`（記録器と再生器の**唯一の**正本）
- 比較面: `snapshot.py`（記録器と再生 test が同じ関数を使う）

## 設計の前提

1. **fixture は記録であって model ではない。** 「この object のこの member を
   こう呼んだらこれが返った」という観測しか持たない。Ghidra の object graph を
   別表現へ組み直さないので、再生器は値を引くだけで、推論・既定値・
   Ghidra API の再実装を持たない。
2. **未記録は None でも空でも既定値でもない。** 記録された値は envelope
   `{"v": ...}` に入り、`{"v": {"kind": "none"}}` は「None が返った」、
   `{"v": {"kind": "list", "items": []}}` は「空列が返った」。key 自体が無ければ
   未記録で、再生器は `RecordedProgram.missing_accesses` に積んでから
   `RecordedSurfaceMissing` を送出する。
3. **例外だけでは検出保証にならない。** production には Ghidra の例外を捕捉して
   不完全解析に落とす経路が多数ある（`except Exception` baseline 950 件）。
   再生 test は左右の `missing_accesses == []` を必ず assert する。
4. **記録と再生で surface 定義を分けない。** key の作り方も値の符号化も
   `schema.py` の 1 箇所。`RecordingDecompiler.dispose()` と
   `RecordedDecompiler.dispose()` のように片側だけに必要な宣言は、両側へ明示的に
   同じものを置く。

## 構造

```
{
  "header": {...},                 # 出自（下記）
  "roots": {"program": "o0", "decompiler": "o1"},
  "objects": {
    "o0": {
      "kind": "ghidra.program.database.ProgramDB",   # 記録時の Java class
      "eq_group": 0,                                  # Java の equals 同値類
      "members": {
        "attr:getMemory":  {"v": {"kind": "method"}},
        "call:getMemory()": {"v": {"kind": "ref", "id": "o12"}},
        "call:getByte(ref:eq88)": {"v": {"kind": "int", "value": 12}}
      }
    }
  }
}
```

### member key

| key | 意味 |
|---|---|
| `attr:<name>` | `getattr(object, name)` の結果の**種別**。`{"kind": "absent"}` = 実 object に member が無かった（= `AttributeError`、**未記録ではない**）、`{"kind": "method"}` = callable、`{"kind": "value", "value": <tagged>}` = 非 callable の属性値 |
| `call:<name>(<args>)` | その member を `args` で呼んだ結果 |

`__str__` / `__bool__` / `__len__` / `__iter__` / `__getitem__` も `call:` に載る。
JPype の Java object はこれらを持たないことがあるので、記録器は member を引き当て
るのではなく **Python 組み込みの意味論を実 object に当てた結果**を記録する
（`str(real)` / `bool(real)` / `len(real)` / `list(iter(real))` / `real[i]`）。

### 引数の綴り

`none` / `bool:true` / `int:5` / `float:1.5` / `str:"x"` / `bytes:<hex>` /
`list:[...]` / `ref:eq<同値類>`。

object 引数が**同一性ではなく Java 同値類**なのは、`Memory.getByte(Address)` の
ような API が呼ぶたびに新しい `Address` instance を受け取るため。同一性で key を
作ると同じ番地の読み取りが別 key に散る。同値類で引くのは Java 側の `equals` の
意味そのもの。

### 値の tag

`none` / `bool` / `int` / `float`(repr 文字列) / `str` / `bytes`(hex) /
`list`(`items`) / `ref`(`id`)。

### 観測列（状態を持つ API）

同じ key の観測がすべて同一なら 1 件に畳む。**同一でなければ**
`{"seq": [<envelope>, ...]}` として呼び出し順に並べる。Ghidra には
`Iterator.hasNext` / `next` のように状態を持つ API と、`getBody()` /
`getImageBase()` / `getIterator()` のように**呼ぶたびに新しい instance を返す**
getter がある。1 key = 1 値に畳むと再生が実体と食い違う。
`seq` を使い切った後の呼び出しは**未記録**（欠落履歴 + 例外）になる。

畳めるかどうかは object 参照の**同一性**で見る。`equals` で畳むと、
「どの instance に何を要求したか」が instance をまたいで散っているのに、
再生では 1 つの代表へ集まってしまう。

### 例外

実 API が例外を送出したことも `{"raises": {"type": ..., "message": ...}}` として
記録し、再生では `RecordedCallFailure` として送出する。記録しないと、再生側で
「未記録」と区別できない。

## header

`schema` / `fixture_id` / `side` / `recorded_at_utc` / `recording_commit` /
`recording_dirty` / `analysis_source_digest` / `recorder_version` /
`ghidra_version` / `pyghidra_version` / `binary{binary_id, eqbench_relative_path,
sha256, size, kind}` / `eqbench{upstream_url, commit}` /
`target{function_name, entry}` / `recording_mode{identical_fast_path, connector}`。

`analysis_source_digest` は記録時の `execution_identity.source_tree_digest`
（出自の記録であって、再生時に一致を要求する値ではない。fixture 自身を commit
すれば digest は変わる）。

## 記録される範囲

- **HighFunction 系**（`IR_SATURATION_KINDS`）は、production が実際に要求した
  member 名をその kind の全 object へ**飽和**させる。index accessor
  （`getInput` / `getIn` / `getOut`）は、production が要求した件数 API
  （`getNumInputs` / `getInSize` / `getOutSize`）で回す。API 名を先回りで
  並べることはしない。
- **同値類の飽和**: Java の `equals` で等しい object のどれか 1 つに出た要求は
  全員へ出す。
- **Program / Memory / Listing / SymbolTable / FunctionManager /
  DataTypeManager など**は要求駆動のまま。

fixture のサイズ上限は設けない（再生に必要な callee / P-code / memory /
observation を削らない）。

## 記録と再生

```bash
docker compose run --rm ghidra-dev python3 -B -m scripts.function_tracer_pcode.tests.tools.record_pcode_fixture \
  --left  targets/EqBench/benchmarks/bess/bessj0/Eq/source/newV-arm64-clang-O0 \
  --right targets/EqBench/benchmarks/bess/bessj0/Eq/source/newV-arm64-clang-O1 \
  --function snippet --binary-ids B1 B2 \
  --fixture-id bessj0_snippet_B1_B2 \
  --output-dir scripts/function_tracer_pcode/tests/fixtures/pcode/bessj0_snippet_B1_B2 \
  --work-dir tmp/record-pcode
```

記録も再生も **production connector 付きの `check_from_binaries`** を通る。
`ReturnAnalyzer` を単独で回すことはしない。DI は 2 点だけ:

- `ReturnAnalyzer(program, decompiler=...)`
- `EquivalenceChecker(analyzer_factory=...)`

記録時は実 `Program` を recording proxy で包み、実 `DecompInterface` を
`openProgram(real_program)` してから `RecordingDecompiler` として注入する
（`DecompInterface.openProgram()` は JPype の型検査で proxy を受け取らない）。
実 decompiler の破棄は記録器の `finally`。

## 決定性

同じ入力で 2 回記録し、`header` の `recorded_at_utc` / `recording_dirty` /
`analysis_source_digest` / `recording_commit` を除いて比較する:

```bash
python3 -B -m scripts.function_tracer_pcode.tests.tools.record_pcode_fixture --compare <dir-a> <dir-b>
```

`bessj0_snippet_B1_B2` の実測（Ghidra 12.0.1 / PyGhidra 3.0.2）:
`analysis_snapshot.json` と `check_snapshot.json` は byte 一致。fixture 本体は
**8 member を除いて** byte 一致で、差分は

- `ProgramDB.getUniqueProgramID()`（Ghidra が import ごとに振る一意 ID）
- `PcodeBlockBasic.hashCode()` 7 件（JVM の identity hash）

のみ。どちらも **Ghidra 自身が import をまたいで再現しない値**で、production は
どちらも実際に使う（`ConditionTracker` の block index、runtime ref の owner）。
記録から外すと再生が未記録になるので、値をすり替えたり除いたりはしない。
解析結果と判定結果に効いていないことは 2 つの snapshot の byte 一致が示す。

## 既知の制約

- recording proxy は Java object ではないので、production の
  `isinstance(obj, <Ghidra class>)` / Java static API（`core/signature.py` の
  型判定 probe）は記録時にも成立しない。これらの site はすべて
  `try/except Exception` で object API の fallback を持っており、Ghidra の無い
  再生環境（import 自体が失敗する）と**同じ分岐**へ落ちる。つまり record と
  replay は一致するが、**proxy を挟まない実 CLI 実行とは一致しない可能性がある**。
  fixture test は real-binary 検証の代替ではない。
- fixture は判定意味論を持たない。schema は文字列 1 本の完全一致で検査し、
  migration 機構は持たない。
