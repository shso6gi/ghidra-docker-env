# -*- coding: utf-8 -*-
"""non-PHI return の複数経路展開に関する回帰テスト"""

from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.condition import ConditionTracker
from scripts.function_tracer_pcode.model import (
    AddressValueRef,
    CanonicalLocation,
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
    ReturnInfo,
    StorageInfo,
)
from scripts.function_tracer_pcode.transform.expander import ExpandedValue, ExpressionExpander


def _param(name: str, size: int = 4) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=size)


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


def _cond(operator: str, left: Expression, right: Expression, negated: bool = False) -> Condition:
    return Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator=operator,
            operands=[left, right],
            size=1,
        ),
        negated=negated,
    )


def test_condition_tracker_collects_all_valid_paths_to_return():
    tracer = Mock()
    tracer.high_function = Mock()
    tracer.debug = False

    tracker = ConditionTracker(tracer)

    return_parent = object()
    return_op = Mock()
    return_op.getParent.return_value = return_parent

    block_info = Mock()
    block_info.index = 3
    all_paths = [[Mock()], [Mock(), Mock()]]

    tracker.get_block_by_hash = Mock(return_value=block_info)
    tracker.get_all_valid_paths_to_block = Mock(return_value=all_paths)

    result = tracker.get_all_valid_paths_to_return(return_op)

    assert result == all_paths
    tracker.get_block_by_hash.assert_called_once_with(return_parent)
    tracker.get_all_valid_paths_to_block.assert_called_once_with(
        block_info,
        limit_paths=None,
    )


def test_condition_tracker_collects_all_valid_block_paths_to_return():
    class _FakeBlock:
        def __init__(self, index):
            self._index = index

        def getIndex(self):
            return self._index

    tracer = Mock()
    tracer.high_function = Mock()
    tracer.debug = False

    tracker = ConditionTracker(tracer)

    entry_block = _FakeBlock(0)
    true_block = _FakeBlock(1)
    false_block = _FakeBlock(2)
    return_block = _FakeBlock(3)

    selector = _param("param_1")
    zero = Expression.constant(0, 4)
    branch_condition = Expression.binary_op("INT_NOTEQUAL", selector, zero)

    entry_info = Mock(
        index=0,
        out_edges=[true_block, false_block],
        branch_condition=branch_condition,
        true_out_index=1,
        false_out_index=2,
    )
    entry_info.has_conditional_branch.return_value = True
    true_info = Mock(index=1, out_edges=[return_block])
    true_info.has_conditional_branch.return_value = False
    false_info = Mock(index=2, out_edges=[return_block])
    false_info.has_conditional_branch.return_value = False
    return_info = Mock(index=3, out_edges=[])
    return_info.has_conditional_branch.return_value = False

    mapping = {
        true_block: true_info,
        false_block: false_info,
        return_block: return_info,
    }

    tracker.entry_block = entry_info
    tracker.get_block_by_hash = Mock(side_effect=lambda block: mapping.get(block))

    return_op = Mock()
    return_op.getParent.return_value = return_block

    path_entries = tracker.get_all_valid_block_paths_to_return(return_op)

    assert len(path_entries) == 2
    assert [[block.index for block in blocks] for blocks, _conds in path_entries] == [
        [0, 1, 3],
        [0, 2, 3],
    ]
    condition_strings = [[cond.to_string() for cond in conds] for _blocks, conds in path_entries]
    assert condition_strings[0] == ["(param_1 != 0)"]
    assert condition_strings[1] in (["(param_1 == 0)"], ["(not (param_1 != 0))"])


def test_condition_tracker_caches_valid_block_paths():
    class _FakeBlock:
        def __init__(self, index):
            self._index = index

        def getIndex(self):
            return self._index

    tracer = Mock()
    tracer.high_function = Mock()
    tracer.debug = False

    tracker = ConditionTracker(tracer)
    entry_block = _FakeBlock(0)
    target_block = _FakeBlock(1)

    entry_info = Mock(index=0)
    target_info = Mock(index=1)
    tracker.entry_block = entry_info

    calls = {"count": 0}

    def _fake_find(**kwargs):
        calls["count"] += 1
        kwargs["all_paths"].append(([entry_info, target_info], []))

    tracker._find_block_paths_with_conditions = _fake_find  # type: ignore[method-assign]

    first = tracker.get_all_valid_block_paths_to_block(target_info)
    second = tracker.get_all_valid_block_paths_to_block(target_info)

    assert len(first) == 1
    assert len(second) == 1
    assert calls["count"] == 1


def test_condition_tracker_caches_single_best_path_conditions():
    tracer = Mock()
    tracer.high_function = Mock()
    tracer.debug = False

    tracker = ConditionTracker(tracer)
    tracker.entry_block = Mock(index=0)
    target_info = Mock(index=3)

    cond = _cond("INT_NOTEQUAL", _param("param_1"), Expression.constant(0, 4))
    calls = {"count": 0}

    def _fake_find(**kwargs):
        calls["count"] += 1
        kwargs["all_paths"].append([cond])

    tracker._find_paths_with_conditions = _fake_find  # type: ignore[method-assign]

    first = tracker.get_path_conditions_to_block(target_info)
    second = tracker.get_path_conditions_to_block(target_info)

    assert [c.to_string() for c in first] == ["(param_1 != 0)"]
    assert [c.to_string() for c in second] == ["(param_1 != 0)"]
    assert calls["count"] == 1


def test_condition_tracker_refined_branch_dedup_does_not_require_to_string(monkeypatch):
    tracer = Mock()
    tracer.high_function = Mock()
    tracer.debug = False
    tracker = ConditionTracker(tracer)

    shared = Expression.parameter("param_1", index=0, size=1)
    duplicate_a = ExpandedValue(shared, [])
    duplicate_b = ExpandedValue(shared, [])

    def _boom_expr(_self, simplify=True):
        raise AssertionError("branch dedup should not depend on Expression.to_string")

    def _boom_cond(_self):
        raise AssertionError("branch dedup should not depend on Condition.to_string")

    monkeypatch.setattr(Expression, "to_string", _boom_expr)
    monkeypatch.setattr(Condition, "to_string", _boom_cond)

    class _Simplifier:
        @staticmethod
        def simplify_conditions(conditions):
            return list(conditions)

        @staticmethod
        def is_contradiction(_conditions):
            return False

    refined = tracker._build_refined_branch_condition(
        [duplicate_a, duplicate_b],
        output_size=1,
        expression_returns_bool=lambda expr: expr.size == 1,
        condition_simplifier=_Simplifier(),
    )

    assert refined is shared


def test_return_analyzer_expands_non_multiequal_return_for_each_valid_path():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    tracer = Mock()
    tracer.clear_cache = Mock()

    path_a = [
        _cond("INT_SLESS", _param("param_1"), _param("param_2")),
    ]
    path_b = [
        _cond("INT_SLESSEQUAL", _param("param_2"), _param("param_1")),
        _cond("INT_SLESS", _param("param_1"), _param("param_3"), negated=True),
    ]
    all_paths = [path_a, path_b]

    class FakeExpander:
        calls = []

        def __init__(self, tracer_obj, tracker_obj, debug=False, call_resolver=None, **kwargs):
            self.tracer = tracer_obj
            self.tracker = tracker_obj
            self.debug = debug
            self.call_resolver = call_resolver

        def expand_from_varnode(self, return_varnode, base_conditions, depth=0):
            FakeExpander.calls.append([cond.to_string() for cond in base_conditions])
            return [
                ExpandedValue(
                    Expression(ExpressionType.CONSTANT, value=0xFFFFFFF6, size=4),
                    list(base_conditions),
                )
            ]

    with patch.object(ReturnAnalyzer, "_contains_multiequal", return_value=False):
        with patch("scripts.function_tracer_pcode.transform.ExpressionExpander", FakeExpander):
            results = analyzer._analyze_return_value(
                return_varnode=Mock(),
                address="0x1000",
                tracer=tracer,
                condition_tracker=Mock(),
                path_conditions=path_a,
                return_index=7,
                all_path_conditions=all_paths,
    )

    assert len(results) == 2
    assert [ret.branch_index for ret in results] == [700, 701]
    assert [cond.to_string() for cond in results[0].conditions] == [
        cond.to_string() for cond in path_a
    ]
    assert [cond.to_string() for cond in results[1].conditions] == [
        cond.to_string() for cond in path_b
    ]
    assert FakeExpander.calls == [
        [cond.to_string() for cond in path_a],
        [cond.to_string() for cond in path_b],
    ]
    tracer.clear_cache.assert_called_once()


def test_return_analyzer_multiequal_return_does_not_bypass_phi_expansion_for_loop_candidates():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analyzer.program.getImageBase.return_value.getOffset.return_value = 0

    tracer = Mock()
    tracer.clear_cache = Mock()

    class FakeExpander:
        calls = 0

        def __init__(self, tracer_obj, tracker_obj, debug=False, call_resolver=None, **kwargs):
            self.tracer = tracer_obj
            self.tracker = tracker_obj
            self.debug = debug
            self.call_resolver = call_resolver

        def expand_from_varnode(self, return_varnode, base_conditions, depth=0):
            FakeExpander.calls += 1
            return [
                ExpandedValue(
                    Expression(ExpressionType.CONSTANT, value=7, size=4),
                    list(base_conditions),
                )
            ]

    with patch.object(ReturnAnalyzer, "_contains_multiequal", return_value=True):
        with patch("scripts.function_tracer_pcode.transform.ExpressionExpander", FakeExpander):
            with patch(
                "scripts.function_tracer_pcode.analysis.analyzer.StructuralRecurrenceSummarizer._extract_counted_scalar_loop_model",
                side_effect=AssertionError("MULTIEQUAL returns must be expanded directly"),
            ):
                results = analyzer._analyze_return_value(
                    return_varnode=Mock(),
                    address="0x1000",
                    tracer=tracer,
                    condition_tracker=Mock(),
                    path_conditions=[],
                    return_index=3,
                )

    assert len(results) == 1
    assert results[0].value.value == 7
    assert FakeExpander.calls == 1
    tracer.clear_cache.assert_called_once()


def test_expression_expander_prunes_multiequal_paths_that_become_contradictory_after_merge():
    selector_eq_zero = _cond("INT_EQUAL", _param("param_1"), Expression.constant(0, 4))
    selector_nonzero = _cond("INT_NOTEQUAL", _param("param_1"), Expression.constant(0, 4))

    class _InputVarnode:
        def getDef(self):
            return None

        def getSize(self):
            return 4

    class _ParentBlock:
        def getInSize(self):
            return 1

        def getIn(self, index):
            return pred_block if index == 0 else None

    class _MultiequalOp:
        def getParent(self):
            return parent_block

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            return input_varnode if index == 0 else None

    class _BlockInfo:
        def __init__(self, index):
            self.index = index

    class _Tracker:
        def get_block_by_hash(self, block):
            return _BlockInfo(1) if block is pred_block else None

        def get_all_valid_paths_to_block(self, target_block):
            assert target_block.index == 1
            return [[], [selector_nonzero]]

    class _Tracer:
        debug = False

        def trace_varnode(self, _varnode, depth=0, use_cache=False):
            return Expression.constant(7, 4)

    pred_block = object()
    parent_block = _ParentBlock()
    input_varnode = _InputVarnode()
    expander = ExpressionExpander(_Tracer(), condition_tracker=_Tracker(), debug=False)
    expander._get_edge_condition = lambda from_block_info, to_block: None

    expanded = expander._expand_multiequal_internal(
        _MultiequalOp(),
        [selector_eq_zero],
        depth=0,
    )

    assert len(expanded) == 1
    assert expanded[0].value.to_smt() == "(_ bv7 32)"
    assert [cond.to_string() for cond in expanded[0].conditions] == ["(param_1 == 0)"]


def test_return_analyzer_collapses_same_value_under_complementary_conditions():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    selector = _param("param_1")
    zero = Expression.constant(0, 4)
    cond_true = _cond("INT_NOTEQUAL", selector, zero)
    cond_false = _cond("INT_NOTEQUAL", selector, zero, negated=True)
    same_value = Expression.constant(7, 4)

    expanded_values = [
        ExpandedValue(same_value, [cond_true]),
        ExpandedValue(same_value, [cond_false]),
    ]

    results = analyzer._build_return_infos_from_expansions(
        address="0x1000",
        expanded_values=expanded_values,
        return_index=3,
    )

    assert len(results) == 1
    assert results[0].value.to_string() == "7"
    assert results[0].conditions == []


def test_return_analyzer_collapses_same_value_under_stack_guard_like_conditions():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    guard_ptr = _addr_var("PTR___stack_chk_guard_120013160", 0x120013160, size=8)
    left = Expression.memory(
        Expression.binary_op(
            "INDIRECT",
            Expression.memory(guard_ptr, size=8),
            Expression.constant(74, 4),
        ),
        size=8,
    )
    right = Expression.memory(
        Expression.binary_op("INDIRECT", guard_ptr, Expression.constant(74, 4)),
        size=8,
    )
    guard_expr = Expression.binary_op("INT_NOTEQUAL", left, right)
    value = Expression.constant(0, 4)

    expanded_values = [
        ExpandedValue(value, [Condition(guard_expr, True)]),
        ExpandedValue(value, [Condition(guard_expr, False)]),
    ]

    results = analyzer._build_return_infos_from_expansions(
        address="0x2000",
        expanded_values=expanded_values,
        return_index=4,
    )

    assert len(results) == 1
    assert results[0].conditions == []


def test_return_analyzer_drops_budget_fallback_when_precise_case_has_same_conditions():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    selector = _param("param_1")
    zero = Expression.constant(0, 4)
    cond = _cond("INT_NOTEQUAL", selector, zero)

    precise = Expression.constant(7, 4)
    noisy = Expression.binary_op(
        "INT_ADD",
        Expression.constant(1, 4),
        Expression.unknown("INT_ADD_budget_exceeded"),
    )

    expanded_values = [
        ExpandedValue(noisy, [cond]),
        ExpandedValue(precise, [cond]),
    ]

    results = analyzer._build_return_infos_from_expansions(
        address="0x2400",
        expanded_values=expanded_values,
        return_index=5,
    )

    assert len(results) == 1
    assert results[0].value.to_string() == "7"
    assert [c.to_string() for c in results[0].conditions] == [cond.to_string()]


def test_return_analyzer_drops_unresolved_case_when_precise_case_has_same_conditions():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    selector = _param("param_1")
    zero = Expression.constant(0, 4)
    cond = _cond("INT_NOTEQUAL", selector, zero)

    expanded_values = [
        ExpandedValue(Expression.unknown("phi_no_valid_branch"), [cond]),
        ExpandedValue(Expression.constant(0, 4), [cond]),
    ]

    results = analyzer._build_return_infos_from_expansions(
        address="0x2800",
        expanded_values=expanded_values,
        return_index=6,
    )

    assert len(results) == 1
    assert results[0].value.to_string() == "0"
    assert [c.to_string() for c in results[0].conditions] == [cond.to_string()]


def test_return_analyzer_drops_stack_protector_condition_from_sole_return_case():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    guard_ptr = _addr_var("PTR___stack_chk_guard_00111fe8", 0x00111FE8, size=8)
    guard_expr = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op(
            "INT_SUB",
            Expression.memory(
                Expression.binary_op(
                    "INDIRECT",
                    Expression.memory(guard_ptr, size=8),
                    Expression.constant(48, 4),
                ),
                size=8,
            ),
            Expression.memory(
                Expression.binary_op("INDIRECT", guard_ptr, Expression.constant(48, 4)),
                size=8,
            ),
        ),
        Expression.constant(0, 8),
    )

    stripped = analyzer._strip_stack_protector_only_conditions(
        [
            ReturnInfo(
                address="0x4000",
                value=Expression.constant(7, 4),
                conditions=[Condition(guard_expr, True)],
                branch_index=0,
            )
        ]
    )

    assert len(stripped) == 1
    assert stripped[0].conditions == []


def test_return_analyzer_drops_stack_protector_conditions_from_all_equivalent_cases():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    guard_ptr = _addr_var("PTR___stack_chk_guard_120013160", 0x120013160, size=8)
    guard_expr = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.memory(
            Expression.binary_op(
                "INDIRECT",
                Expression.memory(guard_ptr, size=8),
                Expression.constant(74, 4),
            ),
            size=8,
        ),
        Expression.memory(
            Expression.binary_op("INDIRECT", guard_ptr, Expression.constant(74, 4)),
            size=8,
        ),
    )
    value = Expression.variable(
        "guard_after_call",
        size=4,
        runtime_ref=CanonicalLocation(
            base_ref=LocationBaseRef.stack_frame(),
            offset=-48,
            size=4,
        ),
    )

    stripped = analyzer._strip_stack_protector_only_conditions(
        [
            ReturnInfo(address="0x2000", value=value, conditions=[Condition(guard_expr, False)], branch_index=0),
            ReturnInfo(address="0x2000", value=value, conditions=[Condition(guard_expr, True)], branch_index=1),
        ]
    )

    assert len(stripped) == 2
    assert all(info.conditions == [] for info in stripped)

    merged = analyzer._merge_equivalent_return_infos(stripped)

    assert len(merged) == 1
    assert merged[0].conditions == []


def test_return_analyzer_detects_stack_protector_guard_by_structure_without_name_hint():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    base_ptr = Expression.variable("tmp_guard_base", size=8)
    guard_expr = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op(
            "INT_SUB",
            Expression.memory(
                Expression.binary_op(
                    "INDIRECT",
                    Expression.memory(base_ptr, size=8),
                    Expression.constant(48, 4),
                ),
                size=8,
            ),
            Expression.memory(
                Expression.binary_op("INDIRECT", base_ptr, Expression.constant(48, 4)),
                size=8,
            ),
        ),
        Expression.constant(0, 8),
    )

    assert analyzer._condition_looks_like_stack_protector_guard(Condition(guard_expr, False)) is True


def test_return_analyzer_detects_stack_protector_guard_through_bool_negate_wrapper():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    base_ptr = Expression.variable("tmp_guard_base", size=8)
    guard_compare = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op(
            "INT_SUB",
            Expression.memory(
                Expression.binary_op(
                    "INDIRECT",
                    Expression.memory(base_ptr, size=8),
                    Expression.constant(48, 4),
                ),
                size=8,
            ),
            Expression.memory(
                Expression.binary_op("INDIRECT", base_ptr, Expression.constant(48, 4)),
                size=8,
            ),
        ),
        Expression.constant(0, 8),
    )
    wrapped = Condition(Expression.unary_op("BOOL_NEGATE", guard_compare), False)

    assert analyzer._condition_looks_like_stack_protector_guard(wrapped) is True


def test_return_analyzer_detects_stack_protector_guard_with_direct_indirect_probe_shape():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    guard_addr = Expression.constant(0x111FE8, size=8)
    displacement = Expression.constant(48, 4)
    guard_compare = Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op(
            "INT_SUB",
            Expression.binary_op(
                "INDIRECT",
                Expression.memory(guard_addr, size=8),
                displacement,
            ),
            Expression.memory(
                Expression.binary_op("INDIRECT", guard_addr, displacement),
                size=8,
            ),
        ),
        Expression.constant(0, 8),
    )

    assert analyzer._condition_looks_like_stack_protector_guard(Condition(guard_compare, False)) is True


def test_return_analyzer_local_memory_key_does_not_require_string_render(monkeypatch):
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    addr_expr = Expression.binary_op(
        "INT_ADD",
        _param("param_1", size=8),
        Expression.constant(16, 4),
    )

    def _boom(_self, simplify=True):
        raise AssertionError("local memory key generation should not require to_string")

    monkeypatch.setattr(Expression, "to_string", _boom)

    key = analyzer._local_memory_key(addr_expr, 8)

    assert key[1] == 8
    assert key[0] == addr_expr.structural_key(
        normalize_commutative=True,
        strip_width_adapters=True,
        collapse_full_masks=True,
    )


def test_return_analyzer_local_memory_key_ignores_read_order_for_same_address():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    base = Expression.parameter("param_1", index=0, size=8)
    key_a = analyzer._local_memory_key(Expression.memory(base, size=4, read_order_key=11), 8)
    key_b = analyzer._local_memory_key(Expression.memory(base, size=4, read_order_key=22), 8)

    assert key_a == key_b


def test_implicit_return_path_recovery_prefers_terminal_call_producer_over_older_output_varnode():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    class _FakeSpace:
        def getName(self):
            return "register"

    class _FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getAddressSpace(self):
            return _FakeSpace()

        def getOffset(self):
            return self._offset

    class _FakeVarnode:
        def __init__(self, offset, size=8):
            self._offset = offset
            self._size = size

        def getAddress(self):
            return _FakeAddress(self._offset)

        def getOffset(self):
            return self._offset

        def getSize(self):
            return self._size

    class _FakeOp:
        def __init__(self, mnemonic, output=None):
            self._mnemonic = mnemonic
            self._output = output

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return self._output

    return_storage = StorageInfo(
        is_register=True,
        space_name="register",
        offset=0x4000,
        size=8,
        size_bits=64,
        register_name="x0",
        base_register_name="x0",
        base_register_offset=0x4000,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    leaf_output = _FakeVarnode(0x4000, 8)
    leaf_call = _FakeOp("CALL", output=leaf_output)
    terminal_call = _FakeOp("CALL", output=None)
    return_op = _FakeOp("RETURN", output=None)
    block_info = Mock()
    block_info.pcode_ops = [leaf_call, terminal_call, return_op]

    tracer = Mock()
    tracer._get_storage_info_from_varnode.side_effect = (
        lambda varnode: return_storage if varnode is leaf_output else None
    )
    condition_tracker = Mock()

    analyzer._get_implicit_return_target_storages = Mock(return_value=[return_storage])
    analyzer._analyze_return_value = Mock(
        side_effect=AssertionError("older output varnode should not be selected")
    )
    expected = [
        ReturnInfo(
            address="0x1000",
            value=Expression.constant(11, 4),
            conditions=[],
            branch_index=0,
        )
    ]
    analyzer._recover_implicit_return_from_terminal_call = Mock(return_value=expected)

    recovered = analyzer._recover_implicit_return_from_block_paths(
        return_op=return_op,
        address="0x1000",
        tracer=tracer,
        condition_tracker=condition_tracker,
        return_index=0,
        path_entries=[([block_info], [])],
        active_functions=set(),
        current_function=Mock(),
        site_metadata=None,
    )

    assert recovered == expected
    analyzer._recover_implicit_return_from_terminal_call.assert_called_once()
    assert (
        analyzer._recover_implicit_return_from_terminal_call.call_args.args[0]
        is terminal_call
    )


def test_implicit_return_path_recovery_materializes_non_call_terminal_output_varnode():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    class _FakeSpace:
        def getName(self):
            return "register"

    class _FakeAddress:
        def __init__(self, offset):
            self._offset = offset

        def getAddressSpace(self):
            return _FakeSpace()

        def getOffset(self):
            return self._offset

    class _FakeVarnode:
        def __init__(self, offset, size=8):
            self._offset = offset
            self._size = size

        def getAddress(self):
            return _FakeAddress(self._offset)

        def getOffset(self):
            return self._offset

        def getSize(self):
            return self._size

    class _FakeOp:
        def __init__(self, mnemonic, output=None):
            self._mnemonic = mnemonic
            self._output = output

        def getMnemonic(self):
            return self._mnemonic

        def getOutput(self):
            return self._output

    return_storage = StorageInfo(
        is_register=True,
        space_name="register",
        offset=0x4000,
        size=8,
        size_bits=64,
        register_name="x0",
        base_register_name="x0",
        base_register_offset=0x4000,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    arithmetic_output = _FakeVarnode(0x4000, 8)
    prep_call = _FakeOp("CALL", output=None)
    arithmetic_op = _FakeOp("INT_ADD", output=arithmetic_output)
    return_op = _FakeOp("RETURN", output=None)
    block_info = Mock()
    block_info.pcode_ops = [prep_call, arithmetic_op, return_op]

    tracer = Mock()
    tracer._get_storage_info_from_varnode.side_effect = (
        lambda varnode: return_storage if varnode is arithmetic_output else None
    )
    condition_tracker = Mock()

    analyzer._get_implicit_return_target_storages = Mock(return_value=[return_storage])
    expected = [
        ReturnInfo(
            address="0x2000",
            value=Expression.constant(23, 4),
            conditions=[],
            branch_index=1,
        )
    ]
    analyzer._analyze_return_value = Mock(return_value=expected)
    analyzer._recover_implicit_return_from_terminal_call = Mock(
        side_effect=AssertionError("non-call producer should stay on varnode analysis")
    )

    recovered = analyzer._recover_implicit_return_from_block_paths(
        return_op=return_op,
        address="0x2000",
        tracer=tracer,
        condition_tracker=condition_tracker,
        return_index=1,
        path_entries=[([block_info], [])],
        active_functions=set(),
        current_function=Mock(),
        site_metadata=None,
    )

    assert recovered == expected
    analyzer._analyze_return_value.assert_called_once()
    assert analyzer._analyze_return_value.call_args.args[0] is arithmetic_output
