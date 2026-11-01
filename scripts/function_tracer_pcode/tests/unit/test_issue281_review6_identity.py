# -*- coding: utf-8 -*-
"""Issue #281 review 6: 関数をまたぐ値の同一性（memo の寿命、parameter の所有者・時点・値、stack の部分的な書き込み）。

1. `CalleeImporter` の memo は id(node) を鍵にしていて、元の node を生かしていなかった。解放された node の id を
   別の node が再利用すると、以前の結果を返した（bounded refinement で 111, 222 が 111, 111 になり得た）。
2. parameter の照合は、node の identity key（所有者の無い index・記憶域・caller の descriptor の key）の
   どれか 1 つが当たれば置き換えていた。所有者の違う同じ index の parameter、同じ register にある別の値・
   post-state の確定値が引数に化け得た。
3. stack の書き込みは範囲の完全一致だけを見ていた。8 byte の値の 4 byte を上書きした後の読み出しを、元の値と
   読み得た（引数の選択・live-in の判定・stack の load の回復）。

ここの例は production の関数を合成入力で実行したもの（実 binary の判定まで届くかは未確認）。
"""

from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.analysis.effects import call_argument
from scripts.function_tracer_pcode.analysis.effects.call_boundary import (
    REFUSED_CALLEE_FOREIGN_PARAMETER,
    REFUSED_CALLEE_PARAMETER_IDENTITY,
    REFUSED_CALLEE_PARAMETER_UNBOUND,
    REFUSED_CALLEE_REGISTER_VALUE,
    CallBoundaryRefused,
    CalleeBinding,
    CalleeImporter,
    CallSite,
    CalleeTimeline,
    import_callee_expression,
)
from scripts.function_tracer_pcode.core import (
    CanonicalLocation,
    Expression,
    ExpressionType,
    LocationBaseRef,
    PostStateValueRef,
)
from scripts.function_tracer_pcode.core.program_order import ProgramOrder
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.tests.unit._program_order_fakes import FakeOp, fake_cfg

PROGRAM = 7
CALLEE_ENTRY = 0x2000
OTHER_ENTRY = 0x3000
A0 = StorageInfo(is_register=True, register_name="a0", size=8, size_bits=64, base_register_name="a0", base_register_size_bits=64)
A1 = StorageInfo(is_register=True, register_name="a1", size=8, size_bits=64, base_register_name="a1", base_register_size_bits=64)
CALLEE_PARAMETERS = [
    {
        "name": "param_1",
        "index": 0,
        "data_type": "long",
        "size": 8,
        "storage": A0,
        "owner_program_id": PROGRAM,
        "owner_entry_offset": CALLEE_ENTRY,
    }
]


def _q() -> Expression:
    return Expression.parameter("q", index=1, data_type="long", size=8)


def _callee_parameter(owner_entry=CALLEE_ENTRY, *, index=0, storage=A0) -> Expression:
    return Expression.parameter(
        "param_1",
        index=index,
        data_type="long",
        size=8,
        storage_info=storage,
        runtime_ref=LocationBaseRef.parameter(
            "param_1", index=index, owner_program_id=PROGRAM, owner_entry_offset=owner_entry
        ),
    )


def _binding() -> CalleeBinding:
    return CalleeBinding.for_arguments(CALLEE_PARAMETERS, [_q()])


def _import(expr: Expression) -> Expression:
    return import_callee_expression(expr, CallSite(None), CalleeTimeline.unknown(), binding=_binding())


def _show(expr: Expression) -> str:
    if expr.expr_type is ExpressionType.CONSTANT:
        return str(expr.value)
    if expr.expr_type in (ExpressionType.PARAMETER, ExpressionType.VARIABLE):
        return str(expr.name)
    return f"{expr.operator}({', '.join(_show(operand) for operand in expr.operands)})"


# ---------------------------------------------------------------------------
# 1. memo の寿命・可変性
# ---------------------------------------------------------------------------


def test_a_freed_node_id_reused_by_another_node_does_not_return_the_old_result():
    """CPython は解放した object の場所を次の確保に再利用する（同じ大きさの object は後入れ先出し）。

    修正前: 1 つ目の式（と子）が解放された後、2 つ目の式の子が同じ id を得て、memo の古い結果を返した
    （`INT_ADD(q, 222)` のはずが `INT_ADD(INT_ADD(q, 111), q)`）。
    """

    importer = CalleeImporter(CallSite(None), CalleeTimeline.unknown(), binding=_binding())
    first = Expression.binary_op("INT_ADD", _callee_parameter(), Expression.constant(111, size=8))
    assert _show(importer.expression(first)) == "INT_ADD(q, 111)"
    del first
    parameter = _callee_parameter()
    constant = Expression.constant(222, size=8)
    second = Expression.binary_op("INT_ADD", parameter, constant)
    assert _show(importer.expression(second)) == "INT_ADD(q, 222)"


def test_a_node_changed_after_an_import_is_imported_again():
    """組み立て中（凍結前）の node は呼び出し側が後で書き換え得る。呼び出しをまたいで memo の結果を返さない。"""

    importer = CalleeImporter(CallSite(None), CalleeTimeline.unknown(), binding=_binding())
    node = Expression.binary_op("INT_ADD", _callee_parameter(), Expression.constant(1, size=8))
    node.size = 8
    assert importer.expression(node).size == 8
    node.size = 4
    assert importer.expression(node).size == 4


def test_a_frozen_node_shares_its_import_across_calls():
    """凍結済みの node（意味の field が変わらない）は、呼び出しをまたいで 1 回だけ変換する。"""

    importer = CalleeImporter(CallSite(None), CalleeTimeline.unknown(), binding=_binding())
    node = Expression.binary_op("INT_ADD", _callee_parameter(), Expression.constant(1, size=8)).freeze()
    assert importer.expression(node) is importer.expression(node)


def test_bounded_refinement_keeps_each_return_of_a_nested_expansion():
    """caller は f(p) を返し、f は k ごとに g(param_1) + 111·k を返し、g は自分の parameter を返す。

    f の文脈で入れ子の g を展開した式は、return ごとに作られて捨てられる。修正前は捨てられた式の id を次の
    return の式（の部分木）が再利用し、memo の古い結果を返した（観測: 6 return × 20 回で 12 回、
    `INT_ADD(p, 222)` の重複や、定数が `p` に化けた return）。
    """

    from scripts.function_tracer_pcode.analysis.bounded_refinement import BoundedCallRefiner
    from scripts.function_tracer_pcode.core import CallTargetRef, Condition, DeferredCallInfo, DeferredCallRef, PcodeOpRef, ReturnInfo
    from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis

    def deferred(name, caller_entry, argument):
        target = CallTargetRef.from_name(name)
        return DeferredCallInfo(
            placeholder_name=f"call:{name}#0",
            target_ref=target,
            arguments=[argument],
            deferred_call_ref=DeferredCallRef(
                caller_entry_offset=caller_entry,
                pcode_op_ref=PcodeOpRef(seq_order=1, mnemonic="CALL"),
                target_ref=target,
                sequence=0,
            ),
            sequence=0,
        )

    def placeholder(info):
        return Expression.unknown(info.placeholder_name, runtime_ref=info.unknown_ref)

    int_param = lambda name, index: {"name": name, "index": index, "data_type": "int", "size": 4}
    returns = 6
    expected = sorted(f"INT_ADD(p, {111 * (k + 1)})" for k in range(returns))
    for _trial in range(10):
        call_f = deferred("f", 0x1000, Expression.parameter("p", index=0, size=4))
        caller = create_mock_analysis(
            "caller",
            parameters=[int_param("p", 0)],
            returns=[ReturnInfo(address="0x1000", value=placeholder(call_f), conditions=[])],
        )
        caller.entry_point = "0x00001000"
        caller.deferred_calls = {call_f.deferred_call_ref.stable_key(): call_f}
        call_g = deferred("g", 0x2000, Expression.parameter("param_1", index=0, size=4))
        f_returns = []
        for k in range(returns):
            selector = Expression.binary_op(
                "INT_EQUAL", Expression.parameter("param_1", index=0, size=4), Expression.constant(k, size=4)
            )
            f_returns.append(
                ReturnInfo(
                    address=hex(0x2000 + 4 * k),
                    value=Expression.binary_op("INT_ADD", placeholder(call_g), Expression.constant(111 * (k + 1), size=4)),
                    conditions=[Condition(selector)],
                )
            )
        f = create_mock_analysis("f", parameters=[int_param("param_1", 0)], returns=f_returns)
        f.entry_point = "0x00002000"
        f.deferred_calls = {call_g.deferred_call_ref.stable_key(): call_g}
        g = create_mock_analysis(
            "g",
            parameters=[int_param("x", 0)],
            returns=[ReturnInfo(address="0x3000", value=Expression.parameter("x", index=0, size=4), conditions=[])],
        )
        analyses = {"f": f, "g": g}
        refiner = BoundedCallRefiner(
            lambda target_ref, args=None: analyses.get(target_ref.function_name),
            max_unroll=2,
            max_cases=64,
            debug=False,
        )

        refiner.refine_analysis(caller)

        assert sorted(_show(ret.value) for ret in caller.returns) == expected


# ---------------------------------------------------------------------------
# 2. parameter の所有者・時点・値
# ---------------------------------------------------------------------------


def test_the_callee_own_parameter_is_replaced():
    assert _show(_import(_callee_parameter())) == "q"


def test_an_ownerless_parameter_node_is_replaced_by_its_index():
    """所有者を持たない `PARAMETER`（callee の解析が作ったもの）は index で callee の parameter に対応する。"""

    assert _show(_import(Expression.parameter("param_1", index=0, size=8))) == "q"


def test_a_parameter_of_another_function_with_the_same_index_is_refused():
    """修正前: 所有者の無い key `("parameter", 0)` が当たり、別の関数の parameter が引数 q になった。"""

    with pytest.raises(CallBoundaryRefused) as raised:
        _import(_callee_parameter(owner_entry=OTHER_ENTRY))
    assert raised.value.reason == REFUSED_CALLEE_FOREIGN_PARAMETER


def test_another_value_in_the_parameter_register_is_not_the_argument():
    """修正前: 記憶域の key（a0）が当たり、callee のある時点で a0 にある別の値が引数 q になった。"""

    later_value = Expression.variable("uVar1", size=8, storage_info=A0)
    with pytest.raises(CallBoundaryRefused) as raised:
        _import(Expression.binary_op("INT_ADD", later_value, Expression.constant(1, size=8)))
    assert raised.value.reason == REFUSED_CALLEE_REGISTER_VALUE


def test_a_post_state_value_in_the_parameter_register_is_not_the_argument():
    """修正前: post-state の主張を落とした後、記憶域の key（a0）で引数 q に置き換えた。"""

    location = CanonicalLocation(base_ref=LocationBaseRef.parameter("param_1", index=0), offset=0, size=8)
    settled = Expression.variable("uVar1", size=8, storage_info=A0, runtime_ref=PostStateValueRef(location=location))
    with pytest.raises(CallBoundaryRefused) as raised:
        _import(settled)
    assert raised.value.reason == REFUSED_CALLEE_REGISTER_VALUE


def test_a_parameter_with_a_post_state_claim_keeps_its_value_and_drops_the_claim():
    """`PARAMETER` の値そのものは入口の値。「callee の出口の状態と等しい」主張だけを落として置き換える。"""

    location = CanonicalLocation(base_ref=LocationBaseRef.parameter("param_1", index=0), offset=0, size=8)
    node = Expression.parameter("param_1", index=0, size=8, runtime_ref=PostStateValueRef(location=location))
    assert _show(_import(node)) == "q"


def test_a_parameter_whose_storage_disagrees_with_its_index_is_refused():
    """index 0 の parameter は a0。a1 に居ると主張する index 0 の node は、どちらの値か決められない。"""

    with pytest.raises(CallBoundaryRefused) as raised:
        _import(_callee_parameter(storage=A1))
    assert raised.value.reason == REFUSED_CALLEE_PARAMETER_IDENTITY


def test_a_parameter_node_that_is_no_callee_parameter_is_refused():
    """callee の parameter のどれでもない `PARAMETER`（loop の placeholder など）は caller へ渡さない。"""

    with pytest.raises(CallBoundaryRefused) as raised:
        _import(Expression.parameter("__loop_iv", index=-10_000, size=4))
    assert raised.value.reason == REFUSED_CALLEE_PARAMETER_UNBOUND


def test_the_caller_descriptors_do_not_decide_the_callee_parameter():
    """effect の境界は簡約に caller の descriptor を渡す。修正前はそれで callee の node を引き、caller の
    parameter と同じ記憶域（a1）にある callee の値が、callee の index 1 の引数に化け得た。"""

    caller_parameters = [
        {"name": "p", "index": 0, "size": 8, "storage": A0},
        {"name": "r", "index": 1, "size": 8, "storage": A1},
    ]
    two_callee = [
        LocationBaseRef.parameter("a", index=0, owner_program_id=PROGRAM, owner_entry_offset=CALLEE_ENTRY),
        LocationBaseRef.parameter("b", index=1, owner_program_id=PROGRAM, owner_entry_offset=CALLEE_ENTRY),
    ]
    binding = CalleeBinding.for_arguments(two_callee, [_q(), Expression.constant(9, size=8)], simplify_parameters=caller_parameters)
    with pytest.raises(CallBoundaryRefused) as raised:
        import_callee_expression(
            Expression.variable("local", size=8, storage_info=A1), CallSite(None), CalleeTimeline.unknown(), binding=binding
        )
    assert raised.value.reason == REFUSED_CALLEE_REGISTER_VALUE


# ---------------------------------------------------------------------------
# 3. stack の部分的な書き込み
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "left, right, relation",
    [
        ((-16, 8), (-16, 8), 3),
        ((-16, 4), (-16, 8), 1),
        ((-12, 4), (-16, 8), 1),
        ((-20, 8), (-16, 8), 1),
        ((-8, 4), (-16, 8), 0),
        ((-24, 8), (-16, 8), 0),
        ((-16, 0), (-16, 8), 1),
    ],
)
def test_memory_range_relation(left, right, relation):
    assert call_argument._impl__memory_range_relation(left[0], left[1], right[0], right[1]) == relation


STACK_SPACE_ID = 0x1B


class _Space:
    def getSpaceID(self):
        return STACK_SPACE_ID

    def getName(self):
        return "stack"


class _StackVarnode:
    def __init__(self, offset, size, label=None):
        self.offset = offset
        self.size = size
        self.label = label

    def getAddress(self):
        return SimpleNamespace(getAddressSpace=lambda: _Space())

    def getOffset(self):
        return self.offset

    def getSize(self):
        return self.size



class _ValueVarnode:
    def __init__(self, size, label):
        self.size = size
        self.label = label

    def getSize(self):
        return self.size

    def getAddress(self):
        return SimpleNamespace(getAddressSpace=lambda: None)


class _Op:
    def __init__(self, mnemonic, inputs=(), output=None):
        self.mnemonic = mnemonic
        self.inputs = list(inputs)
        self.output = output

    def getMnemonic(self):
        return self.mnemonic

    def getNumInputs(self):
        return len(self.inputs)

    def getInput(self, index):
        return self.inputs[index]

    def getOutput(self):
        return self.output


SLOT = StorageInfo(is_register=False, space_name="stack", space_id=STACK_SPACE_ID, offset=-16, size=8, size_bits=64)


def _stack_tracer():
    def storage_of(varnode):
        if isinstance(varnode, _StackVarnode):
            return StorageInfo(
                is_register=False,
                space_name="stack",
                space_id=STACK_SPACE_ID,
                offset=varnode.offset,
                size=varnode.size,
                size_bits=varnode.size * 8,
            )
        return None

    return SimpleNamespace(_get_storage_info_from_varnode=storage_of)


def _value_of_varnode(monkeypatch):
    monkeypatch.setattr(
        call_argument,
        "_resolve_call_argument_expression",
        lambda varnode, *a, **k: Expression.variable(varnode.label, size=varnode.size),
    )


def test_an_argument_slot_partly_overwritten_after_its_write_is_unknown(monkeypatch):
    """8 byte の stack の引数を書いた後、その 4 byte を別の値で上書きする。呼び出しで渡る値は元の値ではない。

    修正前: 4 byte の書き込みは範囲が完全一致しないので「触れていない」とされ、元の 8 byte の値を引数にした。
    """

    _value_of_varnode(monkeypatch)
    full = _Op("COPY", [_ValueVarnode(8, "whole")], output=_StackVarnode(-16, 8, "whole"))
    half = _Op("COPY", [_ValueVarnode(4, "half")], output=_StackVarnode(-16, 4, "half"))
    selected = call_argument._impl__select_best_storage_candidate([full, half], SLOT, _stack_tracer(), [], {})
    assert selected is None


def test_an_argument_slot_written_whole_is_its_last_write(monkeypatch):
    _value_of_varnode(monkeypatch)
    full = _Op("COPY", [_ValueVarnode(8, "whole")], output=_StackVarnode(-16, 8, "whole"))
    elsewhere = _Op("COPY", [_ValueVarnode(4, "other")], output=_StackVarnode(-8, 4, "other"))
    selected = call_argument._impl__select_best_storage_candidate([full, elsewhere], SLOT, _stack_tracer(), [], {})
    assert selected is not None and selected.name == "whole"


def test_a_partial_write_is_a_write_for_the_live_in_check():
    """修正前: 4 byte の上書きを書き込みと数えず、記憶域を入口の値（live-in）のままと読み得た。"""

    half = _Op("COPY", [_ValueVarnode(4, "half")], output=_StackVarnode(-12, 4))
    assert call_argument._impl__path_writes_storage([half], SLOT, _stack_tracer())


X1 = StorageInfo(is_register=True, register_name="x1", size=8, size_bits=64, base_register_name="x1", base_register_size_bits=64)
X0 = StorageInfo(is_register=True, register_name="x0", size=8, size_bits=64, base_register_name="x0", base_register_size_bits=64)


class _RegisterVarnode:
    def __init__(self, storage, label):
        self.storage = storage
        self.label = label
        self.size = storage.size

    def getSize(self):
        return self.size


def _register_tracer():
    return SimpleNamespace(_get_storage_info_from_varnode=lambda varnode: getattr(varnode, "storage", None))


def test_an_argument_register_written_before_an_earlier_call_is_unknown(monkeypatch):
    """x1 に値を入れた後に別の呼び出しがあり、その後の呼び出しで x1 が引数になる。x1 は caller-saved。

    修正前: 前の呼び出しは出力（x0）しか書き込みと数えず、呼び出しの前の x1 の値を引数にした。
    """

    _value_of_varnode(monkeypatch)
    write_x1 = _Op("COPY", [_ValueVarnode(8, "early")], output=_RegisterVarnode(X1, "early"))
    earlier_call = _Op("CALL", [_ValueVarnode(8, "target")], output=_RegisterVarnode(X0, "ret"))
    assert call_argument._impl__select_best_storage_candidate([write_x1, earlier_call], X1, _register_tracer(), [], {}) is None
    assert call_argument._impl__path_writes_storage([earlier_call], X1, _register_tracer())


def test_the_return_register_of_an_earlier_call_is_its_result(monkeypatch):
    """呼び出しの出力が記憶域を丸ごと書けば、その値（呼び出しの結果）が引数。"""

    _value_of_varnode(monkeypatch)
    earlier_call = _Op("CALL", [_ValueVarnode(8, "target")], output=_RegisterVarnode(X0, "ret"))
    selected = call_argument._impl__select_best_storage_candidate([earlier_call], X0, _register_tracer(), [], {})
    assert selected is not None and selected.name == "ret"


def test_an_argument_register_written_after_an_earlier_call_is_that_write(monkeypatch):
    _value_of_varnode(monkeypatch)
    earlier_call = _Op("CALL", [_ValueVarnode(8, "target")], output=_RegisterVarnode(X0, "ret"))
    write_x1 = _Op("COPY", [_ValueVarnode(8, "late")], output=_RegisterVarnode(X1, "late"))
    selected = call_argument._impl__select_best_storage_candidate([earlier_call, write_x1], X1, _register_tracer(), [], {})
    assert selected is not None and selected.name == "late"


# stack の load の回復（`_recover_parameter_from_stack_load`）。順序は偽の CFG から作る


class _Store(FakeOp):
    def __init__(self, block, position, slot, size):
        super().__init__(block, position, mnemonic="STORE")
        self._slot = slot
        self._value = _ValueVarnode(size, f"stored{size}")

    def getOutput(self):
        return None

    def getNumInputs(self):
        return 3

    def getInput(self, index):
        return [None, self._slot, self._value][index]


class _Load(FakeOp):
    def __init__(self, block, position, slot, size):
        super().__init__(block, position, mnemonic="LOAD")
        self._slot = slot
        self._out = _ValueVarnode(size, "loaded")

    def getOutput(self):
        return self._out

    def getInput(self, index):
        return [None, self._slot][index]


class _Writer(FakeOp):
    def __init__(self, block, position, mnemonic, output=None, inputs=()):
        super().__init__(block, position, mnemonic=mnemonic)
        self._output = output
        self._inputs = list(inputs)

    def getOutput(self):
        return self._output

    def getNumInputs(self):
        return len(self._inputs)

    def getInput(self, index):
        return self._inputs[index]


SLOT_ADDRESS = object()


def _load_value(monkeypatch, ops_builder, successors=None):
    successors = successors or {0: [1], 1: []}
    _high, blocks = fake_cfg(successors)
    ops, load = ops_builder(blocks)
    order = ProgramOrder(successors)
    tracer = SimpleNamespace(program_order=lambda: order, get_all_pcode_ops=lambda: list(ops) + [load])

    def stack_key(varnode, size=0):
        if isinstance(varnode, tuple) and varnode and varnode[0] is SLOT_ADDRESS:
            return ("stack", varnode[1], size)
        if isinstance(varnode, _StackVarnode):
            return ("stack", varnode.offset, size or varnode.size)
        return None

    monkeypatch.setattr(call_argument, "_stack_location_key", stack_key)
    monkeypatch.setattr(
        call_argument,
        "_recover_parameter_expression_from_varnode",
        lambda varnode, *a, **k: Expression.parameter("p", index=0, size=varnode.getSize()),
    )
    return call_argument._impl__recover_parameter_from_stack_load(load, tracer, [], 0, set())


def test_a_load_of_a_spilled_value_is_the_spilled_value(monkeypatch):
    def build(blocks):
        return [_Store(blocks[0], 0, (SLOT_ADDRESS, -16), 8)], _Load(blocks[1], 0, (SLOT_ADDRESS, -16), 8)

    recovered = _load_value(monkeypatch, build)
    assert recovered is not None and recovered.name == "p"


def test_a_load_after_part_of_the_spill_is_overwritten_is_unknown(monkeypatch):
    """修正前: 4 byte の store は範囲の key が一致しないので見えず、8 byte の spill の値を load の値にした。"""

    def build(blocks):
        return (
            [_Store(blocks[0], 0, (SLOT_ADDRESS, -16), 8), _Store(blocks[0], 1, (SLOT_ADDRESS, -12), 4)],
            _Load(blocks[1], 0, (SLOT_ADDRESS, -16), 8),
        )

    assert _load_value(monkeypatch, build) is None


def test_a_load_after_a_call_that_may_write_the_slot_is_unknown(monkeypatch):
    """spill と load の間の呼び出しは、stack の番地が渡っていればその範囲を書き得る。"""

    def build(blocks):
        return (
            [_Store(blocks[0], 0, (SLOT_ADDRESS, -16), 8), _Writer(blocks[0], 1, "CALL")],
            _Load(blocks[1], 0, (SLOT_ADDRESS, -16), 8),
        )

    assert _load_value(monkeypatch, build) is None


def test_a_call_before_the_spill_does_not_hide_the_spill(monkeypatch):
    def build(blocks):
        return (
            [_Writer(blocks[0], 0, "CALL"), _Store(blocks[0], 1, (SLOT_ADDRESS, -16), 8)],
            _Load(blocks[1], 0, (SLOT_ADDRESS, -16), 8),
        )

    recovered = _load_value(monkeypatch, build)
    assert recovered is not None and recovered.name == "p"


def test_a_store_through_an_unknown_pointer_between_spill_and_load_makes_it_unknown(monkeypatch):
    def build(blocks):
        unknown_pointer = _ValueVarnode(8, "ptr")
        return (
            [
                _Store(blocks[0], 0, (SLOT_ADDRESS, -16), 8),
                _Writer(blocks[0], 1, "STORE", inputs=[None, unknown_pointer, _ValueVarnode(8, "v")]),
            ],
            _Load(blocks[1], 0, (SLOT_ADDRESS, -16), 8),
        )

    assert _load_value(monkeypatch, build) is None


def test_a_slot_defined_by_arithmetic_is_not_its_first_input(monkeypatch):
    """修正前: 出力が stack の範囲の op の入力 0 を値にしていた（`slot = p + 1` を p と読んだ）。"""

    def build(blocks):
        add = _Writer(
            blocks[0],
            0,
            "INT_ADD",
            output=_StackVarnode(-16, 8),
            inputs=[_ValueVarnode(8, "p"), _ValueVarnode(8, "one")],
        )
        return [add], _Load(blocks[1], 0, _StackVarnode(-16, 8), 8)

    assert _load_value(monkeypatch, build) is None


# 値を保つ形だけを辿る（`_recover_parameter_expression_from_varnode`）


class _Defined:
    def __init__(self, op, size):
        self._op = op
        self.size = size

    def getDef(self):
        return self._op

    def getSize(self):
        return self.size


def _live_in_parameter(monkeypatch):
    marker = _ValueVarnode(4, "live_in")
    monkeypatch.setattr(
        call_argument,
        "_parameter_expression_from_varnode",
        lambda varnode, tracer, parameters: Expression.parameter("p", index=0, size=4) if varnode is marker else None,
    )
    return marker


def test_a_zero_extended_parameter_keeps_its_extension(monkeypatch):
    """修正前: ZEXT の入力の parameter（4 byte）を 8 byte の varnode の値として返し、後で符号拡張され得た。"""

    marker = _live_in_parameter(monkeypatch)
    extended = _Defined(_Op("INT_ZEXT", [marker], output=_ValueVarnode(8, "wide")), 8)
    recovered = call_argument._impl__recover_parameter_expression_from_varnode(extended, SimpleNamespace(), [])
    assert recovered is not None
    assert recovered.expr_type is ExpressionType.UNARY_OP and recovered.operator == "INT_ZEXT"
    assert recovered.size == 8 and recovered.operands[0].name == "p"


def test_a_piece_is_not_one_of_its_inputs(monkeypatch):
    """修正前: PIECE(p, x) の値を p と読んだ（もう一方の入力が値から落ちる）。"""

    marker = _live_in_parameter(monkeypatch)
    piece = _Defined(_Op("PIECE", [marker, _ValueVarnode(4, "other")], output=_ValueVarnode(8, "wide")), 8)
    assert call_argument._impl__recover_parameter_expression_from_varnode(piece, SimpleNamespace(), []) is None
