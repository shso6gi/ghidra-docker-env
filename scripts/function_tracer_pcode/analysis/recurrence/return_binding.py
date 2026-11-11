"""Issue #297: counted scalar loop の summary が RETURN の値を表すことの証拠を作る（producer）。

ここが P-code を読む唯一の場所である。

- :func:`_impl__capture_pcode_dataflow_snapshot` は関数の P-code の事実を 1 回だけ読み、
  ``PcodeDataflowSnapshot`` にする。走査は解析の census（control profile の block 数・op 数）を上限にし、
  上限を超えたら写しを作らない（記録の足りない iterator で回り続けない）。
- :func:`_impl__counted_loop_return_binding_evidence` は、写しと、builder が見つけたループの
  accumulator・帰納変数の PHI の key を束ねる。式は作らない（値の意味は proof が写しから作る）。

どの規則が成り立つかは判定しない（``proof.recurrence_return_binding`` が判定する）。
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Tuple

from scripts.function_tracer_pcode.core.recurrence_return_binding import (
    UNIDENTIFIED_STORAGE_SPACES,
    CountedLoopReturnBindingEvidence,
    PcodeDataflowSnapshot,
    PcodeFactBlock,
    PcodeFactInput,
    PcodeFactOp,
    PcodeParameterFact,
)
from scripts.function_tracer_pcode.core.runtime_refs.pcode import PcodeBlockRef, PcodeOpRef

#: Ghidra / 記録 object の読み取りで起こり得る失敗（broad except は使わない）。
_READ_FAILURES = (AttributeError, TypeError, ValueError, IndexError, RuntimeError)


class _SnapshotBoundExceeded(Exception):
    """走査が census の上限を超えた（記録の足りない iterator・壊れた CFG）。"""


class _FreeInputUnidentified(Exception):
    """どの op も定義しない入力の置き場所を識別できない（写しの digest で入力を区別できない）。"""


_U64 = (1 << 64) - 1
#: prototype の引数の数の上限（関数の引数は少ない。超えたら表を作らない）。
_MAX_PARAMETERS = 64


class _ParameterStorageUnavailable(Exception):
    """Ghidra の prototype の引数の置き場所を読めない。"""


def _parameter_facts(high_function) -> Tuple[Tuple[PcodeParameterFact, ...], bool]:
    """HighFunction の引数（local symbol map の parameter）の番号・幅・storage と、program の byte order。"""

    symbols = high_function.getLocalSymbolMap()
    count = int(symbols.getNumParams())
    if count < 0 or count > _MAX_PARAMETERS:
        raise _ParameterStorageUnavailable()
    facts = []
    for position in range(count):
        symbol = symbols.getParamSymbol(position)
        if symbol is None:
            raise _ParameterStorageUnavailable()
        storage = symbol.getStorage()
        varnodes = list(storage.getVarnodes()) if storage is not None else []
        if not varnodes:
            raise _ParameterStorageUnavailable()
        pieces = []
        for varnode in varnodes:
            space = varnode.getAddress().getAddressSpace()
            pieces.append((str(space.getName()), int(varnode.getOffset()) & _U64, int(varnode.getSize())))
        try:
            facts.append(PcodeParameterFact(
                index=int(symbol.getCategoryIndex()), size=int(symbol.getSize()), pieces=tuple(pieces),
            ))
        except ValueError as exc:
            raise _ParameterStorageUnavailable() from exc
    language = high_function.getFunction().getProgram().getLanguage()
    return tuple(facts), bool(language.isBigEndian())


def _parameter_slice(parameters, item: PcodeFactInput, big_endian: bool) -> Optional[int]:
    for fact in parameters:
        if fact.index == item.parameter_index:
            return fact.value_slice(item.storage, item.size, big_endian=big_endian)
    return None


def _free_input(varnode, size: int) -> PcodeFactInput:
    """定義の無い入力を、置き場所（空間・offset）と、関数の引数ならその番号で表す。"""

    address = varnode.getAddress()
    space = address.getAddressSpace() if address is not None else None
    name = str(space.getName()) if space is not None else ""
    if not name or name in UNIDENTIFIED_STORAGE_SPACES:
        raise _FreeInputUnidentified()
    parameter_index = None
    high = varnode.getHigh() if bool(varnode.isInput()) else None
    symbol = high.getSymbol() if high is not None else None
    if symbol is not None and bool(symbol.isParameter()):
        index = int(symbol.getCategoryIndex())
        parameter_index = index if index >= 0 else None
    return PcodeFactInput(
        "free", size, storage=(name, int(varnode.getOffset()) & _U64), parameter_index=parameter_index,
    )



def _bounded(iterator_factory, budget: List[int]):
    """Java の ``hasNext``/``next`` の iterator（または Python の iterable）を、共有の残り予算
    ``budget[0]`` の範囲で回す。予算を超えたら :class:`_SnapshotBoundExceeded`。"""

    iterator = iterator_factory()
    if iterator is None:
        return
    if hasattr(iterator, "hasNext"):
        while iterator.hasNext():
            if budget[0] <= 0:
                raise _SnapshotBoundExceeded()
            budget[0] -= 1
            yield iterator.next()
        return
    for item in iterator:
        if budget[0] <= 0:
            raise _SnapshotBoundExceeded()
        budget[0] -= 1
        yield item


def _java_iterator(collection):
    """Java の collection は ``iterator()``、Python の値はそのまま返す（上限は呼び出し側の ``_bounded``）。"""

    factory = getattr(collection, "iterator", None)
    return factory() if callable(factory) else collection


def _seq_identity(op) -> Optional[Tuple[Any, ...]]:
    seq = op.getSeqnum()
    if seq is None:
        return None
    target = seq.getTarget()
    return (
        str(target.getAddressSpace().getName()), int(target.getOffset()),
        int(seq.getTime()), int(seq.getOrder()),
    )


def _impl__capture_pcode_dataflow_snapshot(
    self, high_function, analysis,
) -> Tuple[Optional[PcodeDataflowSnapshot], Dict[Tuple[Any, ...], Any], Optional[str]]:
    """HighFunction の P-code の事実を 1 回で読む。``(写し, key → live op, 失敗の理由)`` を返す。

    上限は ``FunctionControlEffectProfile`` の ``block_count`` / ``pcode_op_count``（同じ HighFunction を
    別に数えた census）。上限を超える・識別が full でない・形が壊れているときは写しを作らない。
    """

    profile = getattr(getattr(analysis, "effect_summary", None), "function_control_effect_profile", None)
    block_budget = [int(getattr(profile, "block_count", 0) or 0)]
    op_budget = [int(getattr(profile, "pcode_op_count", 0) or 0)]
    if profile is None or block_budget[0] <= 0 or op_budget[0] <= 0:
        return None, {}, "census_unavailable"
    try:
        function_identity = analysis.outcome_function_identity()
    except _READ_FAILURES:
        return None, {}, "function_identity_unavailable"
    tracer = self.tracer
    identity = dict(
        binary_id=getattr(tracer, "_function_binary_id", None),
        program_uid=getattr(tracer, "_function_program_id", None),
        function_entry_space=getattr(tracer, "_function_entry_space", None),
        function_entry_offset=getattr(tracer, "_function_entry_offset", None),
    )
    try:
        raw_blocks = list(_bounded(lambda: _java_iterator(high_function.getBasicBlocks()), block_budget))
        live_ops: Dict[Tuple[Any, ...], Any] = {}
        key_by_seq: Dict[Tuple[Any, ...], Tuple[Any, ...]] = {}
        ops_by_block: List[Tuple[Any, List[Tuple[Tuple[Any, ...], Any]]]] = []
        for block in raw_blocks:
            listed = []
            for ordinal, op in enumerate(_bounded(block.getIterator, op_budget)):
                ref = PcodeOpRef.from_pcode_op(op, local_op_ordinal=ordinal, **identity)
                if ref is None or not ref._has_full_identity_context():
                    return None, {}, "op_identity_incomplete"
                key = ref.stable_key()
                seq = _seq_identity(op)
                if key in live_ops or seq is None or seq in key_by_seq:
                    return None, {}, "op_identity_duplicate"
                live_ops[key] = op
                key_by_seq[seq] = key
                listed.append((key, op))
            ops_by_block.append((block, listed))
        fact_ops = []
        fact_blocks = []
        for block, listed in ops_by_block:
            index = int(block.getIndex())
            for key, op in listed:
                inputs = []
                for position in range(int(op.getNumInputs())):
                    varnode = op.getInput(position)
                    size = int(varnode.getSize())
                    if bool(varnode.isConstant()):
                        # Java の long は符号付き。値は幅の bit だけを持つ（P-code の定数の意味）
                        inputs.append(PcodeFactInput(
                            "constant", size, constant=int(varnode.getOffset()) & ((1 << (8 * size)) - 1),
                        ))
                        continue
                    definition = varnode.getDef()
                    if definition is None:
                        inputs.append(_free_input(varnode, size))
                        continue
                    producer = key_by_seq.get(_seq_identity(definition))
                    if producer is None:
                        return None, {}, "def_outside_function"
                    inputs.append(PcodeFactInput("op", size, producer_key=producer))
                output = op.getOutput()
                fact_ops.append(PcodeFactOp(
                    key=key,
                    opcode=int(op.getOpcode()),
                    mnemonic=str(op.getMnemonic()),
                    block_index=index,
                    output_size=None if output is None else int(output.getSize()),
                    inputs=tuple(inputs),
                ))
            block_ref = PcodeBlockRef(
                block_index=index,
                start_address_offset=int(block.getStart().getOffset()),
                binary_id=identity["binary_id"] or identity["program_uid"],
                function_entry_space=identity["function_entry_space"],
                function_entry_offset=identity["function_entry_offset"],
            )
            successors = tuple(int(block.getOut(i).getIndex()) for i in range(int(block.getOutSize())))
            true_out = block.getTrueOut() if len(successors) == 2 else None
            false_out = block.getFalseOut() if len(successors) == 2 else None
            fact_blocks.append(PcodeFactBlock(
                index=index,
                key=block_ref.stable_key(),
                predecessors=tuple(int(block.getIn(i).getIndex()) for i in range(int(block.getInSize()))),
                successors=successors,
                true_successor=None if true_out is None else int(true_out.getIndex()),
                false_successor=None if false_out is None else int(false_out.getIndex()),
                op_keys=tuple(key for key, _op in listed),
            ))
        parameters, big_endian = _parameter_facts(high_function)
        for op in fact_ops:
            for item in op.inputs:
                if item.parameter_index is not None and _parameter_slice(parameters, item, big_endian) is None:
                    # HighSymbol は引数と言うが、prototype の置き場所に収まらない入力
                    return None, {}, "parameter_input_outside_prototype_storage"
        snapshot = PcodeDataflowSnapshot(
            function_identity=tuple(function_identity),
            blocks=tuple(fact_blocks),
            ops=tuple(fact_ops),
            parameters=parameters,
            big_endian=big_endian,
        )
    except _SnapshotBoundExceeded:
        return None, {}, "scan_bound_exceeded"
    except _FreeInputUnidentified:
        return None, {}, "free_input_identity_unavailable"
    except _ParameterStorageUnavailable:
        return None, {}, "parameter_storage_unavailable"
    except _READ_FAILURES as exc:
        return None, {}, f"snapshot_read_failed:{type(exc).__name__}"
    return snapshot, live_ops, None


def _impl__counted_loop_return_binding_evidence(
    self,
    *,
    high_function,
    analysis,
    induction,
    accumulator,
) -> CountedLoopReturnBindingEvidence:
    """counted scalar loop の summary 1 つの証拠を作る。揃わないものは ``producer_failures`` に書く。"""

    failures: List[str] = []
    try:
        function_identity = tuple(analysis.outcome_function_identity())
    except _READ_FAILURES:
        function_identity = ("function_identity_unavailable",)
        failures.append("function_identity_unavailable")
    snapshot, live_ops, failure = self._capture_pcode_dataflow_snapshot(high_function, analysis)
    if failure:
        failures.append(failure)
    acc_key = iv_key = None
    if snapshot is not None:
        acc_key = _live_key(live_ops, accumulator.phi_op)
        iv_key = _live_key(live_ops, induction.phi_op)
        if acc_key is None or iv_key is None:
            failures.append("loop_phi_not_in_snapshot")
        if analysis.pcode_dataflow_digest is None:
            analysis.pcode_dataflow_digest = snapshot.digest
        elif analysis.pcode_dataflow_digest != snapshot.digest:
            failures.append("pcode_dataflow_digest_conflict")
    return CountedLoopReturnBindingEvidence(
        function_identity=function_identity,
        snapshot=snapshot,
        accumulator_phi_key=acc_key,
        induction_phi_key=iv_key,
        producer_failures=tuple(failures),
    )


def _live_key(live_ops: Dict[Tuple[Any, ...], Any], op) -> Optional[Tuple[Any, ...]]:
    """live op の key（SeqNum で照合する。Python の object の同一性は使わない）。"""

    if op is None:
        return None
    target = _seq_identity(op)
    for key, candidate in live_ops.items():
        if _seq_identity(candidate) == target:
            return key
    return None
