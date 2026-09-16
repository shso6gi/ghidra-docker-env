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
   Ghidra API の再実装を持たない。唯一の例外は identity 由来の 2 面で、
   **観測した raw 値の equality / collision relation を保存したまま**、具体値
   だけを決定的な surrogate に置換する（下記）。
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
`list`(`items`) / `ref`(`id`) / `identity_surrogate`(`value` + `member`)。

### identity surrogate（唯一、raw 値を記録しない面）

`Object.hashCode()` と `Program.getUniqueProgramID()` は Ghidra / JVM が
**import ごとに違う値**を返す。具体値そのものに意味は無い — Java の契約は
`a.equals(b) => a.hashCode() == b.hashCode()` **だけ**（異なる object の hash
collision は合法）で、program ID は不透明な handle — production はどちらも
「等しいか」だけに使う（`condition/tracker.py` の block 索引、runtime ref /
parameter の owner 識別）。

そこで記録器は、**実際に観測した raw 値どうしの equality / collision relation を
保存し、具体値だけを決定的な surrogate に置換する**。

- 同じ `(member, raw 値)` → 同じ surrogate
- 違う raw 値 → 違う surrogate
- **unequal な receiver 間の hash collision も、観測されたとおり保存される**
  （production は `hashCode()` を索引 key に使うので、collision の有無自体が
  意味論。受け手の同値類で採番すると、実観測の collision を壊してしまう）
- raw 値そのものは fixture に残さない

採番は「その `(member, raw 値)` を初めて観測した順」の通し番号 `group` で、
raw 値の大小にも Python の randomized hash にも依存しない。surrogate は
`(side, member, group)` から一意に決まる:

```
canonical_identity_surrogate(side, member, group) =
      (side_ordinal  + 1) * IDENTITY_SURROGATE_SIDE_STRIDE
    + (member_ordinal + 1) * IDENTITY_SURROGATE_MEMBER_STRIDE
    + group
```

side と member で帯が分かれるので、左右でも member 間でも衝突しない。記録器は
surrogate を **production にもそのまま返す**ので、記録時と再生時に production が
見る値は同一になる。

正規化するのは `schema.IDENTITY_DERIVED_METHODS` に宣言した member だけ。
**fail-closed**:

- `hashCode` で Java-equal（同じ同値類）の receiver が違う raw 値を返したら
  `IdentityContractViolation` → 記録を止める（どちらかへ勝手に寄せない）
- 宣言外の member、引数付きの呼び出し、整数以外の戻り値も記録を止める

validator は fixture 側で次を検査する:

- `member` が宣言済みで、key の member 名と一致する
- `group` が exact int で帯域内
- `value == canonical_identity_surrogate(side, member, group)`
  （任意の in-band 値を受理しない）
- fixture 全体で `(member, group)` と `value` が **1 対 1**
  （同じ group が 2 つの値を持たない / 同じ値が 2 つの group に使い回されない）

**削除で production surface を欠落させることはしない**（production はどちらの
値も実際に読む）。

### 例外

実 API が例外を送出したことも `{"raises": {"type": ..., "message": ...}}` として
記録し、再生では `RecordedCallFailure` として送出する。記録しないと、再生側で
「未記録」と区別できない。

### schema 検証は fail-closed

`validate_fixture` は**完全一致**で検査する（migration 機構は持たない）:

- top-level / header / `binary` / `eqbench` / `target` / `recording_mode` /
  `roots` / object entry / member envelope / tagged value / 例外 payload の
  **許可 key 集合を明示**し、余剰 field を黙って受理しない
- scalar は変換で救済せず exact 型（exact bool / bool を受けない exact int /
  exact str）
- SHA-256 と `analysis_source_digest` は 64 桁の小文字 hex、
  `recording_commit` / `eqbench.commit` は 40 桁
- `side` は `left` / `right`、`recording_mode.connector` は `production`
- identity surrogate は `value == canonical_identity_surrogate(side, member, group)`
  で、fixture 全体で `(member, group)` と `value` が 1 対 1
- `eqbench_relative_path` は working root からの canonical relative path
  （絶対 path や `..` を含まない）
- `ref` の参照先 object id が実在する
- 不正な fixture は**再生前に**落ちる。再生時に意味のある値へ coercion しない

## header

`schema` / `fixture_id` / `side` / `recorded_at_utc` / `recording_commit` /
`recording_dirty` / `analysis_source_digest` / `recorder_version` /
`ghidra_version` / `pyghidra_version` / `binary{binary_id,
eqbench_relative_path, sha256, size, kind}` / `eqbench{upstream_url, commit}` /
`target{function_name, entry}` / `recording_mode{identical_fast_path,
connector}`。

### working root と upstream provenance は別の事実

- **`binary.eqbench_relative_path`**: binary を実際に読んだ **writable working
  root**（runner の `EQBENCH_ROOT` と同じ `benchmarks` 直下）からの relative
  path。root の外の file を basename へ縮退させると出自が消えるので、記録器は
  **fail-closed** にする（`--eqbench-root` 必須）。
- **`binary.sha256` / `size`**: その working-root file から計算する。
- **`eqbench.upstream_url` / `eqbench.commit`**: canonical な **read-only**
  checkout（既定 `targets/EqBench`、`--eqbench-canonical-checkout`）から読む
  upstream の出自。取れなければ記録しない。
- 記録器は working root が canonical checkout の中にある場合も拒否する
  （canonical checkout を runner の workspace として使わない、という運用を
  記録側でも守る）。

`analysis_source_digest` は**記録が走った時点の解析 source** の
`execution_identity.source_tree_digest`。再生時に一致を要求する値ではない。

digest の対象（`SOURCE_ROOTS`）には `tests/` も入るので、書き出した fixture 自身は
その digest に含まれない（含めようとすると自己参照で固定点が無い）。したがって:

- **同じ tree の状態から続けて記録すれば**、`recording_commit` も
  `analysis_source_digest` も含めて byte 一致する（これが決定性の性質）。
- 生成した fixture を tree に入れると tree が変わるので、その後の記録は別の
  digest を持つ。これは非決定ではなく、出自が正しく変わったということ。

## 記録される範囲

- **HighFunction 系**（`IR_SATURATION_KINDS`）は、production が実際に要求した
  member 名をその kind の全 object へ**飽和**させる。index accessor
  （`getInput` / `getIn` / `getOut`）は、production が要求した件数 API
  （`getNumInputs` / `getInSize` / `getOutSize`）で回す。API 名を先回りで
  並べることはしない。
- **同値類の飽和**: Java の `equals` で等しい object のどれか 1 つに出た要求は
  全員へ出す。飽和が **production の観測列を乱さない**こと: 既に記録のある key は
  呼び直さない（件数 API も記録済みの値を読む）。dunder は飽和しない。
- **Program / Memory / Listing / SymbolTable / FunctionManager /
  DataTypeManager など**は要求駆動のまま。

fixture のサイズ上限は設けない（再生に必要な callee / P-code / memory /
observation を削らない）。

## 記録と再生

binary は canonical な `targets/EqBench` ではなく **fresh writable working
root** から読む（runner は入力 root の `Eq/source/` に書き込むので、canonical
checkout は read-only に保つ）。

```bash
W=tmp/eqbench-work/3724fce5
[[ ! -e "$W" ]] || { echo "working root exists: $W (rm -rf it first)" >&2; exit 1; }
mkdir -p "$W/benchmarks" && cp -a targets/EqBench/benchmarks/. "$W/benchmarks/"

docker compose run --rm ghidra-dev python3 -B -m scripts.function_tracer_pcode.tests.tools.record_pcode_fixture \
  --eqbench-root /workspace/$W/benchmarks \
  --left  /workspace/$W/benchmarks/bess/bessj0/Eq/source/newV-arm64-clang-O0 \
  --right /workspace/$W/benchmarks/bess/bessj0/Eq/source/newV-arm64-clang-O1 \
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

同じ入力で 2 回以上記録し、比較する:

```bash
python3 -B -m scripts.function_tracer_pcode.tests.tools.record_pcode_fixture --compare <dir-a> <dir-b>
```

比較から外すのは **volatile な header field だけ**
（`recorded_at_utc` / `recording_dirty`）。`recording_commit` と
`analysis_source_digest` は同じ source からの再記録なら一致すべき出自なので
隠さない。

`bessj0_snippet_B1_B2` の実測（Ghidra 12.0.1 / PyGhidra 3.0.2、source tree を
凍結して 4 回記録し 6 通りすべて比較）: `left.json` / `right.json` /
`analysis_snapshot.json` / `check_snapshot.json` の 4 file とも **byte 一致**
（差分 0）。identity 由来の 2 面（`getUniqueProgramID` / `hashCode`）は上記の
surrogate で正規化されている。

## 既知の制約

- recording proxy は Java object ではないので、production の
  `isinstance(obj, <Ghidra class>)` / Java static API（`core/signature.py` の
  型判定 probe）は記録時にも成立しない。これらの site はすべて
  `try/except Exception` で object API の fallback を持っており、Ghidra の無い
  再生環境（import 自体が失敗する）と**同じ分岐**へ落ちる。つまり record と
  replay は一致するが、**proxy を挟まない実 CLI 実行とは一致しない可能性がある**。
  fixture test は real-binary 検証の代替ではない。
- 記録された例外は型名と文字列で再生する（`RecordedCallFailure`）。production が
  Ghidra の例外クラスで分岐する経路があれば、そこは再生できない。
- fixture は判定意味論を持たない。schema は文字列 1 本の完全一致で検査し、
  migration 機構は持たない。

## なぜ計画書 (v5 §3.3) の構造化 schema ではないのか

計画 v5 は `high_functions{blocks, ops, varnodes, high_variables, ...}` という
**Ghidra の object graph を写した構造化 schema** を書いていた。実 Ghidra での
end-to-end 記録で次が分かり、観測の一様記録へ設計を更新した（計画の目的 —
Ghidra 無し再生・soundness・決定性・provenance・fail-closed — はそのまま）。

1. **状態を持つ API がある。** `Iterator.hasNext` / `next` は呼ぶたびに違う値を
   返す。構造化 schema は「1 つの構造」を書く形なので、この時間的な列を持てない。
2. **同じ getter が毎回新しい instance を返す。** `getBody()` / `getImageBase()`
   / `getIterator()` は fresh object を返す。構造で写すと「どの instance に何を
   要求したか」が失われ、再生で取り違える（実測でこの取り違えが起きた）。
3. **Java の equality と identity の使い分けが要る。** lookup の引数（`Address`）は
   `equals` で引くのが正しく、戻り値の畳み込みは identity で見るのが正しい。
   構造化 schema にはこの 2 つを別々に表す場所が無い。
4. **構造化すると再生側が Ghidra の object graph を組み直す。** `getDef()` /
   `getInput(i)` / `getHigh()` を id 参照から復元するのは Ghidra API の再実装で、
   「recorded object に意味論を実装しない」という PR-109-A の前提に反する。

観測の一様記録は、記録器が「呼ばれたことを書く」だけ、再生器が「書いてあることを
返す」だけで済み、上の 4 点をそのまま表せる。構造化 schema が持つはずだった面
（block / op / varnode / high variable / prototype / local symbol map）は、
HighFunction 系の飽和記録によってすべて fixture に載る。
