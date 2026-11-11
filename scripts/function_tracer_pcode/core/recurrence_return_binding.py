"""Recurrence summary の return binding の証拠（Issue #297）。

promotion が受理する recurrence summary は、遷移の正しさ（``transition_termination``）とは別に、
「その summary の値が関数の RETURN の値そのものである」ことを示さなければならない。ここはその
証拠の **型と identity** だけを持つ（P-code を読むのは analysis、規則を判定するのは proof）。

- :class:`PcodeDataflowSnapshot` は、関数の P-code の事実（op・def-use・幅・block の辺）を 1 回で
  読み取った写しである。RETURN の chain、ループの guard・帰納変数の step などは、proof がこの写しから
  自分で導く（同じ事実を別の場所で独立に解釈しない）。
- :class:`CountedLoopReturnBindingEvidence` は、counted scalar loop の summary 1 つに対する証拠である。
  digest は proposal の digest に入る。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple

from scripts.function_tracer_pcode.core.recurrence_contracts import (
    RETURN_BINDING_PROPOSITION,
    RETURN_BINDING_RULES,
    RecurrenceDigestCodec,
)
from scripts.function_tracer_pcode.core.runtime_refs.pcode import (
    PCODE_MNEMONIC_BY_OPCODE,
    PCODE_OPCODE_BY_MNEMONIC,
)

PCODE_DATAFLOW_SNAPSHOT_SCHEMA = "pcode_dataflow_snapshot_v3"
COUNTED_LOOP_RETURN_BINDING_SCHEMA = "counted_loop_return_binding_evidence_v3"

#: 入力の種類。``op`` は P-code op の出力（``producer_key`` がその op の key）、``constant`` は定数、
#: ``free`` はどの op も定義しない入力（関数の入力・分岐先の address など。置き場所で識別する）。
PCODE_FACT_INPUT_KINDS = frozenset({"op", "constant", "free"})
#: 置き場所が値を識別しない空間（一時変数）。この空間の ``free`` な入力は写しに入れられない。
UNIDENTIFIED_STORAGE_SPACES = frozenset({"unique", "const"})


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def is_frozen_value(value: Any) -> bool:
    """値が作った後に変わらない形（``None``・bool・int・str・その tuple）だけでできていること。

    証拠の identity（digest）は作ったときに計算する。中身が変えられる値（list・dict・式の object）を
    含むと、digest と中身が食い違い得るので、証拠には入れない。
    """

    stack = [value]
    while stack:
        current = stack.pop()
        if current is None or isinstance(current, (bool, int, str)):
            continue
        if type(current) is tuple:
            stack.extend(current)
            continue
        return False
    return True


def pcode_opcode_is_consistent(mnemonic: Any, opcode: Any) -> bool:
    """mnemonic と opcode が core の表と双方向に矛盾しないこと（どちらかが表にあれば、もう片方と対で一致）。

    表に無い組（両方とも未登録）は矛盾ではないが、どの規則もその op を登録済みの種類として扱わない。
    """

    if type(mnemonic) is not str or not mnemonic or type(opcode) is not int:
        return False
    known_number = PCODE_OPCODE_BY_MNEMONIC.get(mnemonic)
    known_mnemonic = PCODE_MNEMONIC_BY_OPCODE.get(opcode)
    if known_number is None and known_mnemonic is None:
        return True
    return known_number == opcode and known_mnemonic == mnemonic


def is_full_pcode_op_key(key: Any) -> bool:
    """``PcodeOpRef.stable_key()`` の full context の形（binary・関数・seq を含む 8 要素）か。

    fallback の key（binary と関数を含まない）は別の関数の op と衝突し得るので、証拠に使わない。
    """

    return (
        isinstance(key, tuple) and len(key) == 8 and key[0] == "pcode_op"
        and key[1] is not None and isinstance(key[2], tuple) and isinstance(key[3], tuple)
        and isinstance(key[6], int) and not isinstance(key[6], bool)
    )


@dataclass(frozen=True)
class PcodeFactInput:
    """op の入力 1 つ。``free`` の入力は、どの op も定義しない値の **置き場所**（``storage``）で識別する。

    同じ op の key・同じ CFG でも、入力の置き場所・幅・引数の番号が違えば別の値なので、写しの digest に
    入れる（入れないと、入力だけが違う解析の証拠を取り違える）。置き場所の無い入力（``unique`` 空間の
    未定義値など）は識別できないので、producer は写しを作らない。
    """

    kind: str
    size: int
    producer_key: Optional[Tuple[Any, ...]] = None
    constant: Optional[int] = None
    #: ``free`` の入力の置き場所 ``(空間の名前, offset)``。
    storage: Optional[Tuple[str, int]] = None
    #: ``free`` の入力が関数の引数のとき、その番号（Ghidra の parameter の category index）。
    parameter_index: Optional[int] = None

    def __post_init__(self) -> None:
        if self.kind not in PCODE_FACT_INPUT_KINDS:
            raise ValueError(f"unknown P-code input kind: {self.kind!r}")
        if not _is_int(self.size) or self.size <= 0:
            raise ValueError("P-code input size must be a positive int")
        if (self.kind == "op") != (self.producer_key is not None):
            raise ValueError("only an op input carries a producer key")
        if self.kind == "op" and not is_full_pcode_op_key(self.producer_key):
            raise ValueError("P-code input producer key is not a full op key")
        if (self.kind == "constant") != (self.constant is not None):
            raise ValueError("only a constant input carries a value")
        if self.constant is not None and (not _is_int(self.constant) or self.constant < 0):
            raise ValueError("P-code constant must be a non-negative int")
        if (self.kind == "free") != (self.storage is not None):
            raise ValueError("only a free input carries a storage identity")
        if self.storage is not None and not (
            isinstance(self.storage, tuple) and len(self.storage) == 2
            and isinstance(self.storage[0], str) and self.storage[0]
            and self.storage[0] not in UNIDENTIFIED_STORAGE_SPACES
            and _is_int(self.storage[1]) and self.storage[1] >= 0
        ):
            raise ValueError("P-code free input storage is not identified")
        if self.parameter_index is not None and (
            self.kind != "free" or not _is_int(self.parameter_index) or self.parameter_index < 0
        ):
            raise ValueError("only a free input is a parameter, with a non-negative index")

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "pcode_fact_input_v2", self.kind, self.size, self.producer_key, self.constant,
            self.storage, self.parameter_index,
        )


@dataclass(frozen=True)
class PcodeFactOp:
    key: Tuple[Any, ...]
    opcode: int
    mnemonic: str
    block_index: int
    output_size: Optional[int]
    inputs: Tuple[PcodeFactInput, ...]

    def __post_init__(self) -> None:
        if not is_full_pcode_op_key(self.key) or not is_frozen_value(self.key):
            raise ValueError("P-code op key is not a full op key")
        if type(self.inputs) is not tuple or not all(type(item) is PcodeFactInput for item in self.inputs):
            raise ValueError("P-code op inputs must be a tuple of input facts")
        if not _is_int(self.block_index):
            raise ValueError("P-code op block index must be an int")
        if self.key[6] != self.opcode:
            raise ValueError("P-code op key and opcode disagree")
        if not pcode_opcode_is_consistent(self.mnemonic, self.opcode):
            raise ValueError(f"P-code mnemonic/opcode are inconsistent: {self.mnemonic}/{self.opcode}")
        if self.output_size is not None and (
            not isinstance(self.output_size, int) or isinstance(self.output_size, bool) or self.output_size <= 0
        ):
            raise ValueError("P-code output size must be a positive int or None")

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "pcode_fact_op_v1", self.key, self.opcode, self.mnemonic, self.block_index,
            self.output_size, tuple(item.stable_key() for item in self.inputs),
        )


@dataclass(frozen=True)
class PcodeFactBlock:
    index: int
    key: Tuple[Any, ...]
    predecessors: Tuple[int, ...]
    successors: Tuple[int, ...]
    true_successor: Optional[int]
    false_successor: Optional[int]
    op_keys: Tuple[Tuple[Any, ...], ...]

    def __post_init__(self) -> None:
        if not (
            _is_int(self.index) and is_frozen_value(self.key)
            and is_frozen_value((self.predecessors, self.successors, self.op_keys))
            and all(_is_int(item) for item in self.predecessors + self.successors)
            and all(item is None or _is_int(item) for item in (self.true_successor, self.false_successor))
        ):
            raise ValueError("P-code block fact is not frozen")

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "pcode_fact_block_v1", self.index, self.key, self.predecessors, self.successors,
            self.true_successor, self.false_successor, self.op_keys,
        )


@dataclass(frozen=True)
class PcodeParameterFact:
    """関数の引数 1 つの、Ghidra の prototype の置き場所（HighFunction の parameter の storage）。

    ``pieces`` は storage の varnode ``(空間, offset, 幅)`` の列（Ghidra の ``VariableStorage`` の順）。
    写しの ``free`` な入力は、この表の置き場所と照合できたときだけ引数の値として読む（番号だけで
    同じ値と見なさない）。
    """

    index: int
    size: int
    pieces: Tuple[Tuple[str, int, int], ...]

    def __post_init__(self) -> None:
        if not _is_int(self.index) or self.index < 0 or not _is_int(self.size) or self.size <= 0:
            raise ValueError("P-code parameter fact needs a non-negative index and a positive size")
        if type(self.pieces) is not tuple or not self.pieces or not all(
            isinstance(piece, tuple) and len(piece) == 3
            and isinstance(piece[0], str) and piece[0] and piece[0] not in UNIDENTIFIED_STORAGE_SPACES
            and _is_int(piece[1]) and piece[1] >= 0 and _is_int(piece[2]) and piece[2] > 0
            for piece in self.pieces
        ):
            raise ValueError("P-code parameter storage pieces are not identified")
        if sum(piece[2] for piece in self.pieces) != self.size:
            raise ValueError("P-code parameter storage pieces do not cover its size")

    def stable_key(self) -> Tuple[Any, ...]:
        return ("pcode_parameter_fact_v1", self.index, self.size, self.pieces)

    def value_slice(self, storage: Tuple[str, int], size: int, *, big_endian: bool) -> Optional[int]:
        """置き場所 ``storage``・幅 ``size`` の入力が、この引数の値のどの byte からの切り出しか。

        引数の storage が 1 つの varnode で、入力がその範囲に収まるときだけ、値の最下位からの byte の
        位置を返す（little endian は低い address が下位、big endian は高い address が下位）。
        storage が複数の varnode の引数は、各 piece と値の位置の対応を示せないので ``None``。
        """

        if len(self.pieces) != 1:
            return None
        space, offset, width = self.pieces[0]
        if storage[0] != space or storage[1] < offset or storage[1] + size > offset + width:
            return None
        return (offset + width) - (storage[1] + size) if big_endian else storage[1] - offset


@dataclass(frozen=True)
class PcodeDataflowSnapshot:
    """1 つの HighFunction の P-code の事実の写し。作ったときに形を検査する（不整合なら ValueError）。"""

    function_identity: Tuple[Any, ...]
    blocks: Tuple[PcodeFactBlock, ...]
    ops: Tuple[PcodeFactOp, ...]
    #: 関数の引数の置き場所（Ghidra の prototype）と、program の byte order。
    parameters: Tuple[PcodeParameterFact, ...] = ()
    big_endian: bool = False
    schema_version: str = PCODE_DATAFLOW_SNAPSHOT_SCHEMA
    # 索引（``_ops_by_key`` / ``_blocks_by_index``）と digest は dataclass の field にしない。解析の
    # successor は dataclass を ``replace`` で field ごとに写す（``core.analysis._semantic_copy``）ので、
    # ``init=False`` の field があると写せない。写しは ``__post_init__`` で索引を作り直す。

    def __post_init__(self) -> None:
        if self.schema_version != PCODE_DATAFLOW_SNAPSHOT_SCHEMA:
            raise ValueError("P-code dataflow snapshot schema is not allowed")
        if not self.function_identity or not is_frozen_value(self.function_identity):
            raise ValueError("P-code dataflow snapshot needs a frozen function identity")
        if type(self.blocks) is not tuple or type(self.ops) is not tuple:
            raise ValueError("P-code dataflow snapshot facts must be tuples")
        if not all(type(item) is PcodeFactBlock for item in self.blocks) or not all(
            type(item) is PcodeFactOp for item in self.ops
        ):
            raise ValueError("P-code dataflow snapshot facts must be fact records")
        if type(self.parameters) is not tuple or not all(
            type(item) is PcodeParameterFact for item in self.parameters
        ) or type(self.big_endian) is not bool:
            raise ValueError("P-code dataflow snapshot parameters must be parameter facts")
        parameters_by_index = {item.index: item for item in self.parameters}
        if len(parameters_by_index) != len(self.parameters):
            raise ValueError("P-code dataflow snapshot has a duplicate parameter index")
        ops_by_key: Dict[Tuple[Any, ...], PcodeFactOp] = {}
        for op in self.ops:
            if op.key in ops_by_key:
                raise ValueError("P-code dataflow snapshot has a duplicate op key")
            ops_by_key[op.key] = op
        blocks_by_index: Dict[int, PcodeFactBlock] = {}
        for block in self.blocks:
            if block.index in blocks_by_index:
                raise ValueError("P-code dataflow snapshot has a duplicate block index")
            blocks_by_index[block.index] = block
        listed = []
        for block in self.blocks:
            for neighbour in block.predecessors + block.successors:
                if neighbour not in blocks_by_index:
                    raise ValueError("P-code dataflow snapshot edge leaves the function")
            for branch in (block.true_successor, block.false_successor):
                if branch is not None and branch not in block.successors:
                    raise ValueError("P-code dataflow snapshot branch is not a successor")
            for key in block.op_keys:
                op = ops_by_key.get(key)
                if op is None or op.block_index != block.index:
                    raise ValueError("P-code dataflow snapshot block lists a foreign op")
                listed.append(key)
        if len(listed) != len(ops_by_key) or set(listed) != set(ops_by_key):
            raise ValueError("P-code dataflow snapshot ops are not partitioned by blocks")
        for op in self.ops:
            for item in op.inputs:
                if item.kind == "op" and item.producer_key not in ops_by_key:
                    raise ValueError("P-code dataflow snapshot input refers to an unknown op")
        object.__setattr__(self, "_parameters_by_index", parameters_by_index)
        object.__setattr__(self, "_ops_by_key", ops_by_key)
        object.__setattr__(self, "_blocks_by_index", blocks_by_index)
        object.__setattr__(
            self, "_digest", RecurrenceDigestCodec.digest(self.schema_version, self.stable_key()),
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            self.schema_version, self.function_identity,
            tuple(item.stable_key() for item in self.blocks),
            tuple(item.stable_key() for item in self.ops),
            tuple(item.stable_key() for item in self.parameters), self.big_endian,
        )

    @property
    def digest(self) -> str:
        return self._digest

    def rebuilt(self) -> "PcodeDataflowSnapshot":
        """field（作った後に変わらない fact の tuple）だけから作り直した写し。

        索引と digest は ``__post_init__`` が field から計算する。proof はこの写しだけを読むので、
        索引・digest が field と食い違うことはない（作り直した digest を元の digest と照合する）。
        """

        return PcodeDataflowSnapshot(
            function_identity=self.function_identity, blocks=self.blocks, ops=self.ops,
            parameters=self.parameters, big_endian=self.big_endian, schema_version=self.schema_version,
        )

    def parameter(self, index: int) -> Optional[PcodeParameterFact]:
        return self._parameters_by_index.get(index)

    def op(self, key: Tuple[Any, ...]) -> Optional[PcodeFactOp]:
        return self._ops_by_key.get(key)

    def block(self, index: int) -> Optional[PcodeFactBlock]:
        return self._blocks_by_index.get(index)

    def ops_with_opcode(self, opcode: int) -> Tuple[PcodeFactOp, ...]:
        return tuple(op for op in self.ops if op.opcode == opcode)


@dataclass(frozen=True)
class CountedLoopReturnBindingEvidence:
    """counted scalar loop の summary 1 つに対する return binding の証拠。

    P-code の **事実だけ** を持つ: 関数の P-code の写し（``snapshot``）と、ループの accumulator・帰納変数の
    PHI の key。start / limit / 初期値・1 回分の更新・条件の意味は、proof が写しから自分で導く
    （producer が作った式を信じない）。中身はすべて作った後に変わらない値なので、digest は中身と食い違わない。
    ``producer_failures`` は producer が写しを揃えられなかった理由で、1 つでもあれば proof は拒否する。
    """

    function_identity: Tuple[Any, ...]
    snapshot: Optional[PcodeDataflowSnapshot]
    accumulator_phi_key: Optional[Tuple[Any, ...]]
    induction_phi_key: Optional[Tuple[Any, ...]]
    producer_failures: Tuple[str, ...] = ()
    schema_version: str = COUNTED_LOOP_RETURN_BINDING_SCHEMA

    def __post_init__(self) -> None:
        if self.schema_version != COUNTED_LOOP_RETURN_BINDING_SCHEMA:
            raise ValueError("counted-loop return binding evidence schema is not allowed")
        if self.snapshot is not None and type(self.snapshot) is not PcodeDataflowSnapshot:
            raise ValueError("counted-loop return binding snapshot must be a P-code dataflow snapshot")
        if not is_frozen_value((
            self.function_identity, self.accumulator_phi_key, self.induction_phi_key,
        )) or type(self.function_identity) is not tuple:
            raise ValueError("counted-loop return binding identity must be frozen")
        if type(self.producer_failures) is not tuple or not all(
            isinstance(item, str) and item for item in self.producer_failures
        ):
            raise ValueError("counted-loop return binding producer failures must be strings")
        object.__setattr__(self, "_digest", self.recomputed_digest())

    def stable_key(self, snapshot_digest: Optional[str] = None) -> Tuple[Any, ...]:
        if snapshot_digest is None and self.snapshot is not None:
            snapshot_digest = self.snapshot.digest
        return (
            self.schema_version, self.function_identity, snapshot_digest,
            self.accumulator_phi_key, self.induction_phi_key, tuple(self.producer_failures),
        )

    @property
    def digest(self) -> str:
        return self._digest

    def recomputed_digest(self) -> str:
        """写しを field から作り直して計算した digest（proof・artifact の検査はこれを使う）。"""

        snapshot_digest = None if self.snapshot is None else self.snapshot.rebuilt().digest
        return RecurrenceDigestCodec.digest(self.schema_version, self.stable_key(snapshot_digest))


def parameter_leaf_mismatch(snapshot: PcodeDataflowSnapshot, expr: Any) -> Optional[str]:
    """候補の式の引数 ``expr``（番号 0 以上の ``PARAMETER``）が、写しの引数の表のその番号の値そのものか。

    SMT の symbol は引数の番号で決まる。番号が同じでも置き場所・幅が違う値を同じ symbol にしないよう、
    候補の引数の ``storage_info``（空間・offset・幅）と幅が、表の 1 つの piece と全幅で一致することを
    要求する。一致すれば ``None``、しなければ理由。複数の piece の引数は対応を示せないので受け付けない。
    """

    index = getattr(expr, "value", None)
    if not _is_int(index) or index < 0:
        return "synthetic_parameter"
    fact = snapshot.parameter(index)
    if fact is None:
        return f"parameter_{index}_not_in_prototype"
    if len(fact.pieces) != 1:
        return f"parameter_{index}_multi_storage"
    storage = getattr(expr, "storage_info", None)
    observed = (
        getattr(storage, "space_name", None), getattr(storage, "offset", None), getattr(storage, "size", None),
    )
    if observed != fact.pieces[0] or int(getattr(expr, "size", 0) or 0) != fact.size:
        return f"parameter_{index}_storage"
    return None


def return_binding_proposition(proposal: Any) -> Tuple[Any, ...]:
    """proposal に対する return binding の subproof の命題（proof・発行・再利用が同じ形を作る）。

    ``(命題の名前, proposal の digest, 中身から作り直した証拠の digest, 候補の id, 規則の全部)``。
    証拠の無い proposal には命題が無い（``ValueError``）。
    """

    evidence = getattr(proposal, "return_binding_evidence", None)
    if type(evidence) is not CountedLoopReturnBindingEvidence:
        raise ValueError("recurrence proposal has no return binding evidence")
    return (
        RETURN_BINDING_PROPOSITION,
        proposal.digest,
        evidence.recomputed_digest(),
        tuple(sorted(
            (item.candidate_id for item in proposal.new_returns),
            key=lambda value: repr(value),
        )),
        RETURN_BINDING_RULES,
    )


def validate_return_binding_subproof(subproofs: Any, proposal: Any) -> None:
    """artifact の return binding の subproof が、**この** proposal とその証拠・候補を束ねていること。

    artifact を発行・保存・再利用するたびに検査する。証拠の無い proposal・別の proposal / 証拠 /
    候補の命題・規則の一部だけの命題は ``ValueError``。
    """

    expected = return_binding_proposition(proposal)
    if proposal.return_binding_evidence.digest != expected[2]:
        raise ValueError("recurrence return binding evidence changed after the proposal was made")
    items = [item for item in tuple(subproofs or ()) if getattr(item, "proof_kind", None) == "return_binding"]
    if len(items) != 1:
        raise ValueError("recurrence artifact needs exactly one return binding subproof")
    if tuple(items[0].proposition_key) != expected:
        raise ValueError("recurrence return binding subproof is not bound to the proposal evidence")


# ---------------------------------------------------------------------------
# snapshot から導くループの事実（producer と proof が同じ関数を使う: 解釈を 1 か所に置く）
# ---------------------------------------------------------------------------



def _opcode(mnemonic: str) -> int:
    return PCODE_OPCODE_BY_MNEMONIC[mnemonic]


#: RETURN から accumulator PHI までの chain で値を変えずに通す op（初回は COPY だけ。CAST は bit を保つが
#: 戻り値の型の解釈を変えるので、RETURN の値として扱う根拠と正例が揃うまで通さない）。
RETURN_CHAIN_PASSTHROUGH_MNEMONICS = ("COPY",)
#: 比較・帰納変数の更新・limit の operand で通す op。比較の signedness は比較の opcode が決め、同幅の
#: COPY / CAST は bit を変えないので、counter の同一性を保つ（cast した counter は幅が違うので通らない）。
OPERAND_PASSTHROUGH_MNEMONICS = ("COPY", "CAST")
#: chain の段数の上限（P-code の COPY の連鎖は短い。上限を超えたら結び付かないと扱う）。
RETURN_CHAIN_MAX_STEPS = 16


def loop_region(snapshot: PcodeDataflowSnapshot, header_index: int) -> frozenset:
    """header を含む強連結成分（header から到達でき、header へ戻れる block の集合）。"""

    if snapshot.block(header_index) is None:
        return frozenset()

    def reach(start: int, forward: bool) -> set:
        seen, stack = set(), [start]
        while stack:
            index = stack.pop()
            if index in seen:
                continue
            seen.add(index)
            block = snapshot.block(index)
            stack.extend(block.successors if forward else block.predecessors)
        return seen

    return frozenset(reach(header_index, True) & reach(header_index, False))


def region_exit_edges(snapshot: PcodeDataflowSnapshot, region: frozenset) -> Tuple[Tuple[int, int], ...]:
    return tuple(sorted(
        (index, successor)
        for index in region
        for successor in snapshot.block(index).successors
        if successor not in region
    ))


def region_is_acyclic_without_header(
    snapshot: PcodeDataflowSnapshot, region: frozenset, header_index: int,
) -> bool:
    """header を除いた region に循環が無いこと（ループの内側の循環を禁止する）。"""

    nodes = set(region) - {header_index}
    state: Dict[int, int] = {}
    for root in sorted(nodes):
        if root in state:
            continue
        stack = [(root, iter(snapshot.block(root).successors))]
        state[root] = 1
        while stack:
            index, successors = stack[-1]
            advanced = False
            for successor in successors:
                if successor not in nodes:
                    continue
                if state.get(successor) == 1:
                    return False
                if successor not in state:
                    state[successor] = 1
                    stack.append((successor, iter(snapshot.block(successor).successors)))
                    advanced = True
                    break
            if not advanced:
                state[index] = 2
                stack.pop()
    return True


def split_phi_inputs(
    snapshot: PcodeDataflowSnapshot, phi: PcodeFactOp, header_index: int, region: frozenset,
) -> Optional[Tuple[Tuple[int, ...], Tuple[int, ...]]]:
    """header の MULTIEQUAL の入力を、入辺が region の外（entry）か中（backedge）かで分ける。"""

    block = snapshot.block(header_index)
    if (
        block is None or phi.opcode != _opcode("MULTIEQUAL") or phi.block_index != header_index
        or len(phi.inputs) != len(block.predecessors)
    ):
        return None
    entry = tuple(i for i, pred in enumerate(block.predecessors) if pred not in region)
    back = tuple(i for i, pred in enumerate(block.predecessors) if pred in region)
    return entry, back


def follow_passthrough(
    snapshot: PcodeDataflowSnapshot, item: PcodeFactInput,
    mnemonics: Tuple[str, ...] = OPERAND_PASSTHROUGH_MNEMONICS,
) -> Tuple[PcodeFactInput, Tuple[Tuple[Any, ...], ...]]:
    """値の bit を変えない op（``mnemonics``、同幅・入力 1 つ）を辿った先の入力と、通った op の key。"""

    passthrough = {_opcode(name) for name in mnemonics}
    links = []
    current = item
    for _ in range(RETURN_CHAIN_MAX_STEPS):
        if current.kind != "op":
            break
        producer = snapshot.op(current.producer_key)
        if (
            producer is None or producer.opcode not in passthrough or len(producer.inputs) != 1
            or producer.output_size != current.size or producer.inputs[0].size != current.size
        ):
            break
        links.append(producer.key)
        current = producer.inputs[0]
    return current, tuple(links)


@dataclass(frozen=True)
class ReturnChainFact:
    return_key: Tuple[Any, ...]
    status: str
    links: Tuple[Tuple[Any, ...], ...]
    input_size: Optional[int]


def return_chains(
    snapshot: PcodeDataflowSnapshot, accumulator_phi_key: Tuple[Any, ...],
) -> Tuple[ReturnChainFact, ...]:
    """関数の全 RETURN について、値の入力が COPY だけを通って accumulator PHI の出力に着くか。"""

    out = []
    phi = snapshot.op(accumulator_phi_key)
    for ret in snapshot.ops_with_opcode(_opcode("RETURN")):
        if len(ret.inputs) < 2:
            out.append(ReturnChainFact(ret.key, "no_value_input", (), None))
            continue
        value = ret.inputs[1]
        final, links = follow_passthrough(snapshot, value, RETURN_CHAIN_PASSTHROUGH_MNEMONICS)
        if final.kind != "op":
            status = f"blocked_by:{final.kind}"
        elif phi is not None and final.producer_key == phi.key and phi.output_size == value.size:
            status = "bound"
        else:
            producer = snapshot.op(final.producer_key)
            status = f"blocked_by:{producer.mnemonic}/{producer.output_size}"
        out.append(ReturnChainFact(ret.key, status, links, value.size))
    return tuple(out)


@dataclass(frozen=True)
class HeaderGuardFact:
    cbranch_key: Tuple[Any, ...]
    compare_key: Tuple[Any, ...]
    compare_mnemonic: str
    counter_operand: int
    limit_operand: int
    continue_relation: str
    widths: Tuple[int, ...]


def header_guard(
    snapshot: PcodeDataflowSnapshot, header_index: int, induction_phi_key: Tuple[Any, ...],
    region: frozenset,
) -> Tuple[Optional[HeaderGuardFact], Optional[str]]:
    """header の CBRANCH の条件を、帰納変数 PHI に直接かかる大小比較として読む。

    ``continue_relation`` は「ループを続ける条件」を、帰納変数 ``iv`` と limit ``L`` で表した形
    （``iv<L`` / ``L<iv`` / ``iv<=L`` / ``L<=iv``）。counter が cast・mask を通る、両辺が counter、
    比較が大小でない（``!=`` など）場合は ``None`` と理由を返す。
    """

    block = snapshot.block(header_index)
    cbranch_ops = [snapshot.op(key) for key in block.op_keys if snapshot.op(key).opcode == _opcode("CBRANCH")]
    if len(cbranch_ops) != 1:
        return None, "header_cbranch_count"
    cbranch = cbranch_ops[0]
    true_in = block.true_successor in region if block.true_successor is not None else None
    false_in = block.false_successor in region if block.false_successor is not None else None
    if true_in is None or false_in is None or true_in == false_in:
        return None, "header_cbranch_sides"
    if len(cbranch.inputs) < 2:
        return None, "header_cbranch_inputs"
    negated = False
    current = cbranch.inputs[1]
    compare = None
    for _ in range(RETURN_CHAIN_MAX_STEPS):
        current, _links = follow_passthrough(snapshot, current)
        if current.kind != "op":
            return None, "guard_not_computed"
        producer = snapshot.op(current.producer_key)
        if producer.opcode == _opcode("BOOL_NEGATE") and len(producer.inputs) == 1:
            negated = not negated
            current = producer.inputs[0]
            continue
        compare = producer
        break
    comparisons = {"INT_LESS": True, "INT_SLESS": True, "INT_LESSEQUAL": False, "INT_SLESSEQUAL": False}
    if compare is None or compare.mnemonic not in comparisons or len(compare.inputs) != 2:
        return None, f"guard_op:{getattr(compare, 'mnemonic', None)}"
    counter = []
    for index, item in enumerate(compare.inputs):
        final, _links = follow_passthrough(snapshot, item)
        counter.append(final.kind == "op" and final.producer_key == induction_phi_key)
    if counter[0] == counter[1]:
        return None, "guard_counter_operand_not_unique_or_cast"
    counter_operand = 0 if counter[0] else 1
    strict = comparisons[compare.mnemonic]
    continue_on_compare_true = (not negated) if true_in else negated
    # compare(a, b) = a < b（strict）または a <= b。続ける条件は compare か、その否定（b <= a / b < a）。
    if continue_on_compare_true:
        relation = ("iv<L" if counter_operand == 0 else "L<iv") if strict else (
            "iv<=L" if counter_operand == 0 else "L<=iv")
    else:
        relation = ("L<=iv" if counter_operand == 0 else "iv<=L") if strict else (
            "L<iv" if counter_operand == 0 else "iv<L")
    return HeaderGuardFact(
        cbranch_key=cbranch.key,
        compare_key=compare.key,
        compare_mnemonic=compare.mnemonic,
        counter_operand=counter_operand,
        limit_operand=1 - counter_operand,
        continue_relation=relation,
        widths=tuple(item.size for item in compare.inputs),
    ), None


def induction_steps(
    snapshot: PcodeDataflowSnapshot, induction_phi: PcodeFactOp, header_index: int, region: frozenset,
) -> Tuple[Optional[Tuple[Optional[int], ...]], Optional[str]]:
    """帰納変数 PHI の backedge の入力が、それぞれ ``phi ± 定数`` であるときの定数（符号付き）の列。"""

    split = split_phi_inputs(snapshot, induction_phi, header_index, region)
    if split is None:
        return None, "induction_phi_shape"
    entry, back = split
    if len(entry) != 1 or not back:
        return None, "induction_phi_edges"
    steps = []
    for index in back:
        final, _links = follow_passthrough(snapshot, induction_phi.inputs[index])
        step = None
        producer = snapshot.op(final.producer_key) if final.kind == "op" else None
        if (
            producer is not None and producer.mnemonic in {"INT_ADD", "INT_SUB"}
            and len(producer.inputs) == 2 and producer.output_size == induction_phi.output_size
        ):
            left, right = producer.inputs
            if producer.mnemonic == "INT_ADD" and left.kind == "constant":
                left, right = right, left
            left_final, _ = follow_passthrough(snapshot, left)
            if (
                right.kind == "constant" and left_final.kind == "op"
                and left_final.producer_key == induction_phi.key
            ):
                bits = right.size * 8
                raw = int(right.constant) & ((1 << bits) - 1)
                signed = raw - (1 << bits) if raw >> (bits - 1) else raw
                step = signed if producer.mnemonic == "INT_ADD" else -signed
        steps.append(step)
    return tuple(steps), None


#: ループの中で計算されても、入力がすべてループ不変なら値もループ不変な op（純粋な整数演算・bit の写し）。
#: MULTIEQUAL（ループの値を運ぶ）・LOAD / CALL（memory・副作用）・除算（trap）は入れない。
LOOP_INVARIANT_PURE_MNEMONICS = frozenset({
    "COPY", "CAST", "INT_ZEXT", "INT_SEXT", "SUBPIECE", "PIECE", "INT_ADD", "INT_SUB", "INT_MULT",
    "INT_2COMP", "INT_NEGATE", "INT_XOR", "INT_AND", "INT_OR", "INT_LEFT", "INT_RIGHT", "INT_SRIGHT",
})
#: ループ不変の判定で辿る op の数の上限（超えたら不変とは言わない）。
LOOP_INVARIANT_MAX_OPS = 64


def input_is_loop_invariant(
    snapshot: PcodeDataflowSnapshot, item: PcodeFactInput, region: frozenset,
) -> bool:
    """入力の値がループ不変であること（T-inv）。

    定数・関数の入力・region の外の op の出力は不変。region の中の op は、純粋な整数演算
    （``LOOP_INVARIANT_PURE_MNEMONICS``）で、入力がすべて不変なときだけ不変（例: ``while (i < n + n)`` の
    ``INT_MULT(n, 2)`` は header で毎回計算されるが不変）。MULTIEQUAL・memory・call を通るなら不変と言わない。
    """

    pure = {_opcode(name) for name in LOOP_INVARIANT_PURE_MNEMONICS}
    stack = [item]
    seen = set()
    while stack:
        current = stack.pop()
        if current.kind != "op":
            continue
        op = snapshot.op(current.producer_key)
        if op.block_index not in region or op.key in seen:
            continue
        seen.add(op.key)
        if op.opcode not in pure or len(seen) > LOOP_INVARIANT_MAX_OPS:
            return False
        stack.extend(op.inputs)
    return True
