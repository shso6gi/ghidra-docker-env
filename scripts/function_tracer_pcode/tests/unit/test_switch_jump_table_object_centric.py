# -*- coding: utf-8 -*-

from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.switch import build_switch_dispatch_summaries
from scripts.function_tracer_pcode.core import (
    AddressValueRef,
    Condition,
    Expression,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.core.structural import expression_key_safe
from scripts.function_tracer_pcode.semantics.transform.expander import ExpandedValue


def _resolve_concrete_address_offset(expr):
    if expr is None:
        return None
    runtime_ref = getattr(expr, "runtime_ref", None)
    if runtime_ref is not None and getattr(runtime_ref, "address_offset", None) is not None:
        return int(runtime_ref.address_offset)
    expr_type = getattr(expr, "expr_type", None)
    if expr_type is not None and expr_type.name == "CONSTANT":
        return int(expr.value)
    if expr_type is not None and expr_type.name == "BINARY_OP" and expr.operator == "INT_ADD":
        left = _resolve_concrete_address_offset(expr.operands[0])
        right = _resolve_concrete_address_offset(expr.operands[1])
        if left is None or right is None:
            return None
        return left + right
    if expr_type is not None and expr_type.name == "BINARY_OP" and expr.operator == "INT_MULT":
        left = _resolve_concrete_address_offset(expr.operands[0])
        right = _resolve_concrete_address_offset(expr.operands[1])
        if left is None or right is None:
            return None
        return left * right
    if expr_type is not None and expr_type.name == "INTRINSIC" and expr.name == "PTRSUB":
        base = _resolve_concrete_address_offset(expr.operands[0])
        offset = _resolve_concrete_address_offset(expr.operands[1])
        if base is None or offset is None:
            return None
        return base + offset
    if expr_type is not None and expr_type.name == "INTRINSIC" and expr.name == "PTRADD":
        base = _resolve_concrete_address_offset(expr.operands[0])
        index = _resolve_concrete_address_offset(expr.operands[1])
        elem = _resolve_concrete_address_offset(expr.operands[2])
        if base is None or index is None or elem is None:
            return None
        return base + index * elem
    return None


def _addr_var(name: str, address_offset: int, size: int = 8) -> Expression:
    return Expression.variable(
        name,
        size=size,
        runtime_ref=AddressValueRef(
            address_offset=address_offset,
            display_hint=name,
            symbol_name=name,
            is_initialized=True,
            can_read=True,
            can_write=False,
            is_volatile=False,
        ),
    )


class _FakeSeq:
    def __init__(self, target, time, order=0):
        self._target = target
        self._time = time
        self._order = order

    def getTarget(self):
        return self._target

    def getTime(self):
        return self._time

    def getOrder(self):
        return self._order


class _FakeAddress:
    def __init__(self, offset: int, text: str):
        self._offset = offset
        self._text = text

    def getOffset(self):
        return self._offset

    def getAddressSpace(self):
        return None

    def __str__(self):
        return self._text


class _FakeLoadTable:
    def __init__(self, address: int, size: int, num: int):
        self._address = _FakeAddress(address, f"0x{address:x}")
        self._size = size
        self._num = num

    def getAddress(self):
        return self._address

    def getSize(self):
        return self._size

    def getNum(self):
        return self._num


class _FakeJumpTable:
    def __init__(self, switch_offset: int, labels, targets, load_tables):
        self._switch_address = _FakeAddress(switch_offset, f"0x{switch_offset:x}")
        self._labels = list(labels)
        self._targets = [_FakeAddress(target, f"0x{target:x}") for target in targets]
        self._load_tables = list(load_tables)

    def getSwitchAddress(self):
        return self._switch_address

    def getLabelValues(self):
        return list(self._labels)

    def getCases(self):
        return list(self._targets)

    def getLoadTables(self):
        return list(self._load_tables)


class _FakeIndirectOp:
    def __init__(self, mnemonic: str, target_offset: int, input_varnode):
        self._mnemonic = mnemonic
        self._seq = _FakeSeq(_FakeAddress(target_offset, f"0x{target_offset:x}"), 17, 3)
        self._input = input_varnode

    def getMnemonic(self):
        return self._mnemonic

    def getNumInputs(self):
        return 1

    def getInput(self, index):
        assert index == 0
        return self._input

    def getSeqnum(self):
        return self._seq


class _FakeReturn:
    def __init__(self, target: str = "0x1000"):
        self._seq = _FakeSeq(target, 5, 1)

    def getSeqnum(self):
        return self._seq


class _FakeReturnWithValue(_FakeReturn):
    def __init__(self, value_varnode, target: str = "0x1000"):
        super().__init__(target=target)
        self._value_varnode = value_varnode

    def getNumInputs(self):
        return 2

    def getInput(self, index):
        if index == 1:
            return self._value_varnode
        raise AssertionError(index)


class _FakeImplicitReturn:
    def getNumInputs(self):
        return 1


class _FakeBlockAddress(_FakeAddress):
    pass


class _FakeBlock:
    def __init__(self, start_offset: int, stop_offset: int):
        self._start = _FakeBlockAddress(start_offset, f"0x{start_offset:x}")
        self._stop = _FakeBlockAddress(stop_offset, f"0x{stop_offset:x}")

    def getStart(self):
        return self._start

    def getStop(self):
        return self._stop


def _build_callind_target_expression() -> Expression:
    param = Expression.parameter("param_1", 0, size=8)
    subpiece = Expression.binary_op("SUBPIECE", param, Expression.constant(0, 4))
    subpiece.size = 4
    index_expr = Expression.unary_op("INT_ZEXT", subpiece)
    index_expr.size = 8

    load_address = Expression.intrinsic(
        "PTRADD",
        [
            _addr_var("PTR_00114000", 0x00114000, size=8),
            Expression.binary_op(
                "INT_ADD",
                Expression.binary_op("INT_MULT", index_expr, Expression.constant(8, 8)),
                Expression.constant(0x3670, 8),
            ),
            Expression.constant(1, 8),
        ],
        size=8,
    )
    table_value = Expression.memory(load_address, size=8)

    return Expression.intrinsic(
        "PTRADD",
        [
            Expression.intrinsic(
                "PTRSUB",
                [
                    Expression.constant(0, 8),
                    Expression.constant(0x11C050, 8),
                ],
                size=8,
            ),
            table_value,
            Expression.constant(1, 8),
        ],
        size=8,
    )


def test_build_switch_dispatch_summaries_recovers_direct_branchind_selector():
    input_varnode = Mock()
    branchind_op = _FakeIndirectOp("BRANCHIND", 0x401080, input_varnode)
    switch_block = Mock(index=7, pcode_ops=[branchind_op])
    switch_block.index = 7

    tracer = Mock()
    tracer.high_function.getJumpTables.return_value = [
        _FakeJumpTable(
            0x401080,
            labels=[0, 1, 2, 3],
            targets=[0x401000, 0x401010, 0x401020, 0x401030, 0x401040],
            load_tables=[],
        )
    ]
    tracer.trace_varnode.return_value = Expression.parameter("param_1", 0, size=4)
    tracer._resolve_concrete_address_offset.side_effect = _resolve_concrete_address_offset

    condition_tracker = Mock()
    condition_tracker.block_by_index = {7: switch_block}
    condition_tracker.get_all_valid_block_paths_to_block.return_value = [([switch_block], [])]

    summaries = build_switch_dispatch_summaries(
        tracer=tracer,
        condition_tracker=condition_tracker,
        parameters=[{"name": "param_1", "index": 0, "size": 4}],
        concretize_readonly_loads=lambda expr, _conds, _params: expr,
    )

    assert len(summaries) == 1
    summary = summaries[0]
    assert summary.paths[0].selector.to_string() == "param_1"
    assert len(summary.paths[0].cases) == 5
    assert summary.paths[0].cases[-1].is_default is True
    assert [
        case.target_address
        for case in summary.paths[0].cases
    ] == [0x401000, 0x401010, 0x401020, 0x401030, 0x401040]


def test_build_switch_dispatch_summaries_recovers_selector_from_callind_jump_table():
    input_varnode = Mock()
    callind_op = _FakeIndirectOp("CALLIND", 0x401080, input_varnode)
    switch_block = Mock(index=7, pcode_ops=[callind_op])
    switch_block.index = 7

    tracer = Mock()
    tracer.high_function.getJumpTables.return_value = [
        _FakeJumpTable(
            0x401080,
            labels=[0, 1, 2, 3],
            targets=[0x401000, 0x401010, 0x401020, 0x401030],
            load_tables=[_FakeLoadTable(0x00114000 + 0x3670, 8, 4)],
        )
    ]
    tracer.trace_varnode.return_value = _build_callind_target_expression()
    tracer._resolve_concrete_address_offset.side_effect = _resolve_concrete_address_offset

    condition_tracker = Mock()
    condition_tracker.block_by_index = {7: switch_block}
    range_cond = Condition(
        Expression.binary_op(
            "INT_LESS",
            Expression.parameter("param_1", 0, size=8),
            Expression.constant(4, 8),
        ),
        False,
    )
    condition_tracker.get_all_valid_block_paths_to_block.return_value = [([switch_block], [range_cond])]

    summaries = build_switch_dispatch_summaries(
        tracer=tracer,
        condition_tracker=condition_tracker,
        parameters=[{"name": "param_1", "index": 0, "size": 8}],
        concretize_readonly_loads=lambda expr, _conds, _params: expr,
    )

    assert len(summaries) == 1
    summary = summaries[0]
    assert summary.dispatch_mnemonic == "CALLIND"
    assert summary.target_addresses == (0x401000, 0x401010, 0x401020, 0x401030)
    assert len(summary.paths) == 1
    selector_text = summary.paths[0].selector.to_string()
    assert "param_1" in selector_text
    assert len(summary.paths[0].cases) == 4
    guard_exprs = [
        next(cond.expression for cond in case.conditions if cond.expression.operator == "INT_EQUAL")
        for case in summary.paths[0].cases
    ]
    assert [
        guard.operands[1].value
        for guard in guard_exprs
    ] == [0, 1, 2, 3]
    assert len({expression_key_safe(guard.operands[0]) for guard in guard_exprs}) == 1


def test_build_switch_dispatch_summaries_synthesizes_callind_cases_without_jump_table():
    input_varnode = Mock()
    callind_op = _FakeIndirectOp("CALLIND", 0x401080, input_varnode)
    switch_block = Mock(index=7, pcode_ops=[callind_op])
    switch_block.index = 7

    tracer = Mock()
    tracer.high_function.getJumpTables.return_value = []
    tracer.trace_varnode.return_value = _build_callind_target_expression()
    tracer._resolve_concrete_address_offset.side_effect = _resolve_concrete_address_offset

    condition_tracker = Mock()
    condition_tracker.block_by_index = {7: switch_block}
    selector_subpiece = Expression.binary_op("SUBPIECE", Expression.parameter("param_1", 0, size=8), Expression.constant(0, 4))
    selector_subpiece.size = 4
    selector_expr = Expression.unary_op("INT_ZEXT", selector_subpiece)
    selector_expr.size = 8
    range_cond = Condition(
        Expression.binary_op(
            "INT_LESS",
            selector_expr,
            Expression.constant(4, 8),
        ),
        False,
    )
    condition_tracker.get_all_valid_block_paths_to_block.return_value = [([switch_block], [range_cond])]

    table = {
        0x00114000 + 0x3670 + 0x0: 0x00001000,
        0x00114000 + 0x3670 + 0x8: 0x00001010,
        0x00114000 + 0x3670 + 0x10: 0x00001020,
        0x00114000 + 0x3670 + 0x18: 0x00001030,
    }

    summaries = build_switch_dispatch_summaries(
        tracer=tracer,
        condition_tracker=condition_tracker,
        parameters=[{"name": "param_1", "index": 0, "size": 8}],
        concretize_readonly_loads=lambda expr, _conds, _params: expr,
        read_memory_value=lambda addr, _size: table.get(addr),
    )

    assert len(summaries) == 1
    summary = summaries[0]
    assert summary.dispatch_mnemonic == "CALLIND"
    assert summary.target_addresses == (0x11d050, 0x11d060, 0x11d070, 0x11d080)
    assert len(summary.paths[0].cases) == 4


def test_resolve_local_return_expression_uses_implicit_return_storage_fallback():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    tracer = Mock()

    return_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="v0",
        base_register_name="v0",
        size=8,
        size_bits=64,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    local_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="v0",
        base_register_name="v0",
        size=8,
        size_bits=64,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    local_values = {("register", 0x10, 8): Expression.constant(1000, 8)}
    local_storages = {("register", 0x10, 8): local_storage}

    with patch.object(analyzer, "_get_function_return_varnodes", return_value=[]), patch.object(
        analyzer,
        "_get_implicit_return_target_storages",
        return_value=[return_storage],
    ):
        resolved = analyzer._resolve_local_return_expression(
            _FakeImplicitReturn(),
            tracer,
            local_values,
            local_storages,
            {},
            current_function=Mock(),
        )

    assert resolved is not None
    assert resolved.expr_type.name == "CONSTANT"
    assert int(resolved.value) == 1000


def test_return_analyzer_recovers_switch_like_returns_from_jump_table_callind_targets():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analyzer._current_parameters = [
        {"name": "param_1", "index": 0, "size": 8, "data_type": "ulong", "is_signed": False}
    ]
    analyzer.program.getImageBase.return_value.getOffset.return_value = 0

    input_varnode = Mock()
    callind_op = _FakeIndirectOp("CALLIND", 0x401080, input_varnode)
    switch_block = Mock(index=7, pcode_ops=[callind_op])
    switch_block.index = 7
    return_op = _FakeReturn()
    return_site = analyzer._describe_pcode_site(return_op, "0x1000")

    analysis = FunctionReturnAnalysis(
        function_name="branch_switch_dense",
        entry_point="0x1000",
        parameters=list(analyzer._current_parameters),
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.unknown("callind_out_of_scope:UNKNOWN_FUNC"),
                conditions=[],
                branch_index=0,
                pcode_identity=return_site["pcode_identity"],
                pcode_order=return_site["pcode_order"],
                pcode_time=return_site["pcode_time"],
            )
        ],
        return_type="int",
        unknown_event_reasons=["callind_out_of_scope"],
        unknown_event_count=1,
    )

    tracer = Mock()
    tracer.high_function.getJumpTables.return_value = [
        _FakeJumpTable(
            0x401080,
            labels=[0, 1, 2, 3],
            targets=[0x401000, 0x401010, 0x401020, 0x401030],
            load_tables=[_FakeLoadTable(0x00114000 + 0x3670, 8, 4)],
        )
    ]
    tracer.trace_varnode.return_value = _build_callind_target_expression()
    tracer._resolve_concrete_address_offset.side_effect = _resolve_concrete_address_offset

    range_cond = Condition(
        Expression.binary_op(
            "INT_LESS",
            Expression.parameter("param_1", 0, size=8),
            Expression.constant(4, 8),
        ),
        False,
    )
    condition_tracker = Mock()
    condition_tracker.block_by_index = {7: switch_block}
    condition_tracker.get_all_valid_block_paths_to_block.return_value = [([switch_block], [range_cond])]
    condition_tracker.get_all_valid_block_paths_to_return.return_value = [([switch_block], [range_cond])]

    target_returns = {
        0x401000: [ExpandedValue(Expression.constant(1000, 4), [])],
        0x401010: [ExpandedValue(Expression.constant(1001, 4), [])],
        0x401020: [ExpandedValue(Expression.constant(1002, 4), [])],
        0x401030: [ExpandedValue(Expression.constant(1003, 4), [])],
    }

    with patch.object(
        analyzer,
        "_resolve_local_code_target_expansions",
        side_effect=lambda addr, _active_functions, current_function=None, args=None: target_returns.get(addr),
    ):
        recovered = analyzer._recover_switch_like_returns_from_pcode(
            analysis,
            tracer,
            condition_tracker,
            return_ops=[return_op],
            current_function=Mock(),
            active_functions=set(),
        )

    assert recovered is not None
    assert [ret.value.value for ret in recovered] == [1000, 1001, 1002, 1003]
    assert all(ret.pcode_identity == "0x401080:t17" for ret in recovered)
    assert all(any(cond.to_string() == "(param_1 < 4)" for cond in ret.conditions) for ret in recovered)
    recovered_guard_exprs = [
        next(cond.expression for cond in ret.conditions if cond.expression.operator == "INT_EQUAL")
        for ret in recovered
    ]
    assert [
        guard.operands[1].value
        for guard in recovered_guard_exprs
    ] == [0, 1, 2, 3]
    assert len({expression_key_safe(guard.operands[0]) for guard in recovered_guard_exprs}) == 1


def test_return_analyzer_falls_back_to_legacy_switch_recovery_without_jump_tables():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analyzer._current_parameters = [
        {"name": "param_1", "index": 0, "size": 8, "data_type": "ulong", "is_signed": False}
    ]
    analyzer.program.getImageBase.return_value.getOffset.return_value = 0

    input_varnode = Mock()
    branchind_op = _FakeIndirectOp("BRANCHIND", 0x401080, input_varnode)
    return_op = _FakeReturn()
    return_site = analyzer._describe_pcode_site(return_op, "0x1000")
    switch_block = Mock(index=7, pcode_ops=[branchind_op])
    switch_block.index = 7

    analysis = FunctionReturnAnalysis(
        function_name="branch_switch_dense",
        entry_point="0x1000",
        parameters=list(analyzer._current_parameters),
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.unknown("callind_out_of_scope:BRANCHIND"),
                conditions=[],
                branch_index=0,
                pcode_identity=return_site["pcode_identity"],
                pcode_order=return_site["pcode_order"],
                pcode_time=return_site["pcode_time"],
            )
        ],
        return_type="int",
        unknown_event_reasons=["callind_out_of_scope"],
        unknown_event_count=1,
    )

    cond = Condition(
        Expression.binary_op("INT_LESS", Expression.parameter("param_1", 0, size=8), Expression.constant(2, 8)),
        False,
    )

    condition_tracker = Mock()
    condition_tracker.block_by_index = {7: switch_block}
    condition_tracker.get_all_valid_block_paths_to_block.return_value = [([switch_block], [cond])]
    condition_tracker.get_all_valid_block_paths_to_return.return_value = [([switch_block], [cond])]

    target_expr = Expression.memory(
        Expression.binary_op(
            "INT_ADD",
            _addr_var("PTR_00002000", 0x00002000, size=8),
            Expression.binary_op(
                "INT_ADD",
                Expression.binary_op(
                    "INT_MULT",
                    Expression.parameter("param_1", 0, size=8),
                    Expression.constant(8, 8),
                ),
                Expression.constant(0x100, 8),
            ),
        ),
        size=8,
    )
    tracer = Mock()
    tracer.high_function.getJumpTables.return_value = []
    tracer.trace_varnode.return_value = target_expr

    table = {
        0x2000 + 0x100 + 0x0: 0x401000,
        0x2000 + 0x100 + 0x8: 0x401010,
    }

    with patch.object(analyzer, "_read_memory_value", side_effect=lambda addr, size: table.get(addr)):
        with patch.object(
            analyzer,
            "_resolve_local_code_target_expansions",
            side_effect=lambda addr, _active_functions, current_function=None, args=None: (
                [ExpandedValue(Expression.constant(1000, 4), [])]
                if addr == 0x401000
                else [ExpandedValue(Expression.constant(1001, 4), [])]
            ),
        ):
            recovered = analyzer._recover_switch_like_returns_from_pcode(
                analysis,
                tracer,
                condition_tracker,
                return_ops=[return_op],
                current_function=Mock(),
                active_functions=set(),
            )

    assert recovered is not None
    assert [ret.value.value for ret in recovered] == [1000, 1001]


def test_return_analyzer_resolves_switch_case_targets_via_path_aware_local_blocks():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analyzer._current_parameters = [
        {"name": "param_1", "index": 0, "size": 4, "data_type": "uint", "is_signed": False}
    ]
    analyzer.program.getImageBase.return_value.getOffset.return_value = 0

    selector_varnode = Mock()
    branchind_op = _FakeIndirectOp("BRANCHIND", 0x401080, selector_varnode)
    switch_block = Mock(index=7, pcode_ops=[branchind_op], block=_FakeBlock(0x401080, 0x401087))
    switch_block.index = 7
    switch_block.block = _FakeBlock(0x401080, 0x401087)

    target_blocks = {}
    target_addresses = [0x401000, 0x401010, 0x401020, 0x401030, 0x401040]
    for idx, address in enumerate(target_addresses, start=10):
        block_info = Mock(index=idx, pcode_ops=[], block=_FakeBlock(address, address + 7))
        block_info.index = idx
        block_info.block = _FakeBlock(address, address + 7)
        target_blocks[address] = block_info

    value_varnode = Mock()
    return_op = _FakeReturnWithValue(value_varnode)
    return_site = analyzer._describe_pcode_site(return_op, "0x1000")
    return_block = Mock(index=30, pcode_ops=[return_op], block=_FakeBlock(0x402000, 0x402007))
    return_block.index = 30
    return_block.block = _FakeBlock(0x402000, 0x402007)

    analysis = FunctionReturnAnalysis(
        function_name="branch_switch_dense",
        entry_point="0x1000",
        parameters=list(analyzer._current_parameters),
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.unknown("callind_out_of_scope:BRANCHIND"),
                conditions=[],
                branch_index=0,
                pcode_identity=return_site["pcode_identity"],
                pcode_order=return_site["pcode_order"],
                pcode_time=return_site["pcode_time"],
            )
        ],
        return_type="int",
        unknown_event_reasons=["callind_out_of_scope"],
        unknown_event_count=1,
    )

    tracer = Mock()
    tracer.high_function.getJumpTables.return_value = [
        _FakeJumpTable(
            0x401080,
            labels=[0, 1, 2, 3],
            targets=target_addresses,
            load_tables=[],
        )
    ]
    tracer.trace_varnode.return_value = Expression.parameter("param_1", 0, size=4)
    tracer._resolve_concrete_address_offset.side_effect = _resolve_concrete_address_offset

    block_by_index = {7: switch_block, 30: return_block}
    for block_info in target_blocks.values():
        block_by_index[block_info.index] = block_info

    condition_tracker = Mock()
    condition_tracker.block_by_index = block_by_index
    condition_tracker.get_all_valid_block_paths_to_block.return_value = [([switch_block], [])]

    path_entries = [
        ([switch_block, target_blocks[0x401000], return_block], []),
        ([switch_block, target_blocks[0x401010], return_block], []),
        ([switch_block, target_blocks[0x401020], return_block], []),
        ([switch_block, target_blocks[0x401030], return_block], []),
        ([switch_block, target_blocks[0x401040], return_block], []),
    ]
    condition_tracker.get_all_valid_block_paths_to_return.return_value = path_entries

    def _path_aware_recovery(_tracked_sources, _address, _tracer, _tracker, path_conditions, return_index_base, **_kwargs):
        cond_strings = sorted(cond.to_string() for cond in path_conditions)
        if "(param_1 == 0)" in cond_strings:
            return [ReturnInfo(address="0x1000", value=Expression.constant(1000, 4), conditions=list(path_conditions), branch_index=return_index_base)]
        if "(param_1 == 1)" in cond_strings:
            return [ReturnInfo(address="0x1000", value=Expression.constant(1001, 4), conditions=list(path_conditions), branch_index=return_index_base)]
        if "(param_1 == 2)" in cond_strings:
            return [ReturnInfo(address="0x1000", value=Expression.constant(1002, 4), conditions=list(path_conditions), branch_index=return_index_base)]
        if "(param_1 == 3)" in cond_strings:
            return [ReturnInfo(address="0x1000", value=Expression.constant(1003, 4), conditions=list(path_conditions), branch_index=return_index_base)]
        return [ReturnInfo(address="0x1000", value=Expression.constant(-1000 & 0xFFFFFFFF, 4), conditions=list(path_conditions), branch_index=return_index_base)]

    dispatch_conditions = [Condition(Expression.binary_op("INT_EQUAL", Expression.parameter("param_1", 0, size=4), Expression.constant(0, 4)), False)]
    with patch.object(analyzer, "_build_return_tracking_targets", return_value=[Mock()]):
        with patch.object(analyzer, "_rewrite_tracked_return_values_for_op", side_effect=lambda tracked_values, *_args, **_kwargs: tracked_values):
            with patch.object(analyzer, "_recover_return_infos_from_tracked_sources", side_effect=_path_aware_recovery):
                expanded = analyzer._resolve_switch_case_target_expansions(
                    0x401000,
                    dispatch_conditions,
                    tracer,
                    condition_tracker,
                    [return_op],
                    active_functions=set(),
                    current_function=Mock(),
                )

    assert expanded is not None
    assert [entry.value.value for entry in expanded] == [1000]
