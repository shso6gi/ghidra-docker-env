# -*- coding: utf-8 -*-
"""Test support: ``ReturnAnalyzer`` の公開前の段を、Ghidra の面だけ差し替えて本物のまま走らせる（Issue #211）。

``analyze_through_pipeline(template)`` は本物の ``ReturnAnalyzer.analyze_function_by_name`` を呼ぶ。
差し替えるのは Ghidra の面（関数の検索・decompile・tracer・parameter の収集・戻り値の型・ABI の封印）と、
return を得る段（``_recover_control_region_returns_early`` が template の return をそのまま返す）と、
template が材料を持たない段（構造的な再帰の要約・bounded call refinement・CFG から作る outcome partition
の要約）だけ。return を得た後の解析の段（parameter の同期・return partition の正規化・incomplete
control flow の印・observable effect）と公開境界（``publish_raw_function_analysis``: 意味値の公開と
入力領域の封印）は本物。

``outcome_seed=True`` のときは outcome partition の段（``_apply_outcome_partition_summaries``: termination の
証拠と outcome seed の構築）も本物で通し、CFG を要る要約（``_try_apply_*``）だけを「適用しない」にする。
本番の解析器は解析ごとに seed を作り、seed のある解析は比較の前に outcome partition の段の cause を出す
（plan v4 PR-C §7.3 の 3）。合成の CFG は無いので、seed のある解析は CFG の到達性を証明できず、比較は
EQ にならない（``outcome_cfg_reachability_unproven``）。EQ の対照は既定（seed なし）で作る。

``run_production_check(..., analyze=analyze_through_pipeline)`` と組み合わせると、左右の解析がこの段を
通った後に本物の checker・authority・cutover で判定される。
"""

from __future__ import annotations

import copy
from contextlib import ExitStack
from typing import Any
from unittest.mock import Mock, patch


class _Address:
    def __init__(self, offset: int) -> None:
        self._offset = offset

    def getOffset(self) -> int:  # noqa: N802 - Ghidra API
        return self._offset

    def __str__(self) -> str:
        return hex(self._offset)


class _Program:
    def __init__(self, program_id: int) -> None:
        self._program_id = program_id

    def getUniqueProgramID(self) -> int:  # noqa: N802 - Ghidra API
        return self._program_id


class _Function:
    """``CallTargetRef.from_function`` が読む面だけを持つ Ghidra の関数（Mock の属性を ref に入れない）。"""

    def __init__(self, name: str) -> None:
        self._name = name
        self._program = _Program(sum(map(ord, name)))

    def getName(self) -> str:  # noqa: N802 - Ghidra API
        return self._name

    def getEntryPoint(self) -> _Address:  # noqa: N802 - Ghidra API
        return _Address(0x401000)

    def getProgram(self) -> _Program:  # noqa: N802 - Ghidra API
        return self._program

    def isExternal(self) -> bool:  # noqa: N802 - Ghidra API
        return False

    def isThunk(self) -> bool:  # noqa: N802 - Ghidra API
        return False


class _Tracer:
    def __init__(self, *_args: Any, **_kwargs: Any) -> None:
        self.high_function = Mock()
        self.debug = False
        self.unknown_tracker = Mock(events=[])
        self.record_deferred_call = None

    def find_return_ops(self) -> list:
        return [Mock()]

    def clear_cache(self) -> None:
        return None


class _ConditionTracker:
    def __init__(self, _tracer: Any) -> None:
        self.block_by_index = {}

    def build(self) -> None:
        return None

    def refine_branch_conditions(self, **_kwargs: Any) -> None:
        return None


def _cfg_outcome_summaries() -> tuple:
    """outcome partition の段が呼ぶ、CFG を要る要約（``self._try_apply_*``）の名前。

    一覧を手で持たず、段の本体（``_impl__apply_outcome_partition_summaries``）が呼ぶ名前を読む: 要約が
    増えても「適用しない」に差し替え漏れが出ない。
    """

    import ast
    import inspect
    import textwrap

    from scripts.function_tracer_pcode.analysis.returns import return_extraction

    tree = ast.parse(textwrap.dedent(inspect.getsource(return_extraction._impl__apply_outcome_partition_summaries)))
    names = sorted({
        node.func.attr
        for node in ast.walk(tree)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and isinstance(node.func.value, ast.Name)
        and node.func.value.id == "self"
        and node.func.attr.startswith("_try_apply_")
    })
    if not names:
        raise AssertionError("the outcome partition stage calls no CFG summary; the harness premise changed")
    return tuple(names)


def analyze_through_pipeline(template: Any, *, outcome_seed: bool = False) -> Any:
    """``template``（公開前の解析）の return から始めて、本物の解析の段と公開境界を通した解析。

    呼ぶたびに新しい解析器・新しい return の複製を使う（本番の再解析と同じく、毎回新しい解析を作る）。
    """

    from scripts.function_tracer_pcode.analysis.returns import analyze_function as analyze_function_module
    from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer

    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analyzer.program.getImageBase.return_value.getOffset.return_value = 0
    decompile_results = Mock()
    decompile_results.decompileCompleted.return_value = True
    decompile_results.getHighFunction.return_value = Mock(getFunctionPrototype=Mock(return_value=None))

    function = _Function(template.function_name)
    parameters = copy.deepcopy(list(template.parameters or []))
    returns = copy.deepcopy(list(template.returns or []))
    abi_facts = copy.deepcopy(template.return_abi_facts)

    with ExitStack() as stack:
        stack.enter_context(patch("scripts.function_tracer_pcode.analysis.returns.analyzer.PcodeTracer", _Tracer))
        stack.enter_context(
            patch("scripts.function_tracer_pcode.analysis.returns.analyzer.ConditionTracker", _ConditionTracker)
        )
        stack.enter_context(patch("scripts.function_tracer_pcode.analysis.phi_resolver.PhiHandler", Mock))
        # decompile の production の入口（broker）は program の binary content authority を要るので、入口ごと差し替える。
        stack.enter_context(
            patch(
                "scripts.function_tracer_pcode.ghidra.decompilation_broker.decompile_within_deadline",
                lambda *_args, **_kwargs: decompile_results,
            )
        )
        stack.enter_context(
            patch.object(analyze_function_module, "_sealed_return_abi_facts", lambda *_args: copy.deepcopy(abi_facts))
        )
        stack.enter_context(
            patch.object(analyzer._program_access, "find_function_by_name", return_value=function)
        )
        stack.enter_context(patch.object(analyzer, "_collect_parameters", return_value=parameters))
        stack.enter_context(
            patch.object(
                analyzer,
                "_augment_parameters_with_implicit_passthrough",
                side_effect=lambda params, *_args, **_kwargs: params,
            )
        )
        stack.enter_context(
            patch.object(
                analyzer,
                "_get_return_type_info",
                return_value=(template.return_type_obj, template.return_type),
            )
        )
        stack.enter_context(patch.object(analyzer, "_detect_signedness", return_value=None))
        stack.enter_context(
            patch.object(analyzer, "_recover_control_region_returns_early", return_value=(returns, []))
        )
        stack.enter_context(patch.object(analyzer, "_apply_structural_recurrence_summary", return_value=None))
        stack.enter_context(patch.object(analyzer, "_apply_bounded_call_refinement", return_value=None))
        if outcome_seed:
            for name in _cfg_outcome_summaries():
                stack.enter_context(patch.object(analyzer, name, return_value=False))
        else:
            stack.enter_context(patch.object(analyzer, "_apply_outcome_partition_summaries", return_value=None))
        return analyzer.analyze_function_by_name(template.function_name)
