# -*- coding: utf-8 -*-
"""``debug`` という名前だが guard ではない、**この repository の現状**の一覧。

`test_no_eager_debug_rendering.py` の棚卸しが「宣言し忘れ」と「意図的に guard で
はない」を区別するための baseline。static test 側の所有物で、production の
contract ではない — 変更軸が違う:

* production owner (`analysis/debug/render.py`) が持つのは「**何を** debug guard と
  認めるか」「**どの対象で**呼んだ描画を有界と認めるか」。設計判断であり、
  repository に何が書いてあるかとは独立。
* 本 module が持つのは「**いま** repository に、debug という名前だが guard では
  ない構文がどれだけあるか」。観測結果であり、無関係なコードを消せば減り、
  足せば増える。

そのため production code には置かない（診断 helper が test の都合で太らない）。

内容は棚卸しと同じ canonical descriptor:

* ``("attr", <受け手の path>, <属性名>)`` — 抑止状態や診断 payload の読み出し
* ``("unsupported", <ast.dump(..., include_attributes=False)>)`` — canonical
  descriptor 文法の外にある式（比較・引数付き呼び出しなど）。``ast.dump`` は
  行番号などの非意味情報を含まないので、同値な構文は同じ文字列、意味の違う
  ``x is True`` / ``x is False`` / ``x == y`` / ``x != y`` は別の文字列になる。

棚卸し test は observed と（owner の guard 宣言 ∪ 本 baseline）の**完全一致**を
見るので、未知形を足しても、消えた形が残っていても FAIL する。
"""

from __future__ import annotations

from typing import Any, FrozenSet, Tuple

GuardShape = Tuple[Any, ...]

#: 抑止状態 / 診断 payload の有無を読んでいるだけの属性。
_NON_GUARD_ATTRIBUTES: FrozenSet[GuardShape] = frozenset({
    # cls._debug_suppressed  (analysis/condition/simplifier_debug.py:36)
    ('attr', ('cls',), '_debug_suppressed'),
    # self._debug_suppressed  (analysis/phi_resolver.py:112)
    ('attr', ('self',), '_debug_suppressed'),
    # self.pairwise_debug_stats  (checker/result.py:401)
    ('attr', ('self',), 'pairwise_debug_stats'),
})

#: canonical descriptor 文法の外にある式（比較・引数付き呼び出しなど）。
#: message 数の上限、``debug_trace`` の型検査、``block_debug_key`` によるグラフ
#: 比較、CLI 引数の有無など。いずれも「ここへ入ったら debug が有効」ではない。
_NON_GUARD_UNSUPPORTED: FrozenSet[GuardShape] = frozenset(
    ("unsupported", dump)
    for dump in {
        # 'debug' in params  (smt/parallel.py:237)
        "Compare(left=Constant(value='debug'), ops=[In()], comparators=[Name(id='params', ctx=Load())])",
        # (aggregate.get('evidence_present') or {}).get('debug_trace')  (reporting/root_blocker_summary.py:360)
        "Call(func=Attribute(value=BoolOp(op=Or(), values=[Call(func=Attribute(value=Name(id='aggregate', ctx=Load()), attr='get', ctx=Load()), args=[Constant(value='evidence_present')], keywords=[]), Dict(keys=[], values=[])]), attr='get', ctx=Load()), args=[Constant(value='debug_trace')], keywords=[])",
        # cls._debug_message_count >= cls._DEBUG_MESSAGE_LIMIT  (analysis/condition/simplifier_debug.py:35)
        "Compare(left=Attribute(value=Name(id='cls', ctx=Load()), attr='_debug_message_count', ctx=Load()), ops=[GtE()], comparators=[Attribute(value=Name(id='cls', ctx=Load()), attr='_DEBUG_MESSAGE_LIMIT', ctx=Load())])",
        # complete_recurrence_promotion_signals(promotion.attempt, debug_print=self._debug_print)  (checker/checker.py:759)
        "Call(func=Name(id='complete_recurrence_promotion_signals', ctx=Load()), args=[Attribute(value=Name(id='promotion', ctx=Load()), attr='attempt', ctx=Load())], keywords=[keyword(arg='debug_print', value=Attribute(value=Name(id='self', ctx=Load()), attr='_debug_print', ctx=Load()))])",
        # count <= cls._DEBUG_REPEAT_LIMIT  (analysis/condition/simplifier_debug.py:111)
        "Compare(left=Name(id='count', ctx=Load()), ops=[LtE()], comparators=[Attribute(value=Name(id='cls', ctx=Load()), attr='_DEBUG_REPEAT_LIMIT', ctx=Load())])",
        # count == cls._DEBUG_REPEAT_LIMIT + 1  (analysis/condition/simplifier_debug.py:113)
        "Compare(left=Name(id='count', ctx=Load()), ops=[Eq()], comparators=[BinOp(left=Attribute(value=Name(id='cls', ctx=Load()), attr='_DEBUG_REPEAT_LIMIT', ctx=Load()), op=Add(), right=Constant(value=1))])",
        # debug_key in current  (proof/obligations/stage_runner.py:89)
        "Compare(left=Name(id='debug_key', ctx=Load()), ops=[In()], comparators=[Name(id='current', ctx=Load())])",
        # extracted_for_debug is not None  (analysis/recurrence/readonly_reduction.py:2158)
        "Compare(left=Name(id='extracted_for_debug', ctx=Load()), ops=[IsNot()], comparators=[Constant(value=None)])",
        # hasattr(args, 'debug')  (ghidra/ghidra_runtime.py:64)
        "Call(func=Name(id='hasattr', ctx=Load()), args=[Name(id='args', ctx=Load()), Constant(value='debug')], keywords=[])",
        # isinstance(debug_trace, Mapping)  (reporting/unknown_reason_summary.py:986)
        "Call(func=Name(id='isinstance', ctx=Load()), args=[Name(id='debug_trace', ctx=Load()), Name(id='Mapping', ctx=Load())], keywords=[])",
        # isinstance(payload.get('debug_trace'), Mapping)  (reporting/root_blocker_summary.py:395)
        "Call(func=Name(id='isinstance', ctx=Load()), args=[Call(func=Attribute(value=Name(id='payload', ctx=Load()), attr='get', ctx=Load()), args=[Constant(value='debug_trace')], keywords=[]), Name(id='Mapping', ctx=Load())], keywords=[])",
        # key in _FINAL_DISPOSITION_DEBUG_KEYS  (proof/obligations/stage_runner.py:77)
        "Compare(left=Name(id='key', ctx=Load()), ops=[In()], comparators=[Name(id='_FINAL_DISPOSITION_DEBUG_KEYS', ctx=Load())])",
        # len(cls._debug_repeat_counts) > 4096  (analysis/condition/simplifier_debug.py:107)
        "Compare(left=Call(func=Name(id='len', ctx=Load()), args=[Attribute(value=Name(id='cls', ctx=Load()), attr='_debug_repeat_counts', ctx=Load())], keywords=[]), ops=[Gt()], comparators=[Constant(value=4096)])",
        # note.startswith(('debug:', 'diagnostic:'))  (proof/obligations/snapshot.py:82)
        "Call(func=Attribute(value=Name(id='note', ctx=Load()), attr='startswith', ctx=Load()), args=[Tuple(elts=[Constant(value='debug:'), Constant(value='diagnostic:')], ctx=Load())], keywords=[])",
        # result.debug_trace is not None  (checker/workflow.py:461)
        "Compare(left=Attribute(value=Name(id='result', ctx=Load()), attr='debug_trace', ctx=Load()), ops=[IsNot()], comparators=[Constant(value=None)])",
        # self._block_debug_key(predecessor) != self._block_debug_key(acc_parent)  (analysis/returns/return_extraction.py:1165)
        "Compare(left=Call(func=Attribute(value=Name(id='self', ctx=Load()), attr='_block_debug_key', ctx=Load()), args=[Name(id='predecessor', ctx=Load())], keywords=[]), ops=[NotEq()], comparators=[Call(func=Attribute(value=Name(id='self', ctx=Load()), attr='_block_debug_key', ctx=Load()), args=[Name(id='acc_parent', ctx=Load())], keywords=[])])",
        # self._debug_message_count >= self._debug_message_limit  (analysis/phi_resolver.py:111)
        "Compare(left=Attribute(value=Name(id='self', ctx=Load()), attr='_debug_message_count', ctx=Load()), ops=[GtE()], comparators=[Attribute(value=Name(id='self', ctx=Load()), attr='_debug_message_limit', ctx=Load())])",
        # self.block_graph.block_debug_key(acc_parent) != self.block_graph.block_debug_key(state_parent)  (analysis/returns/control_recovery.py:408)
        "Compare(left=Call(func=Attribute(value=Attribute(value=Name(id='self', ctx=Load()), attr='block_graph', ctx=Load()), attr='block_debug_key', ctx=Load()), args=[Name(id='acc_parent', ctx=Load())], keywords=[]), ops=[NotEq()], comparators=[Call(func=Attribute(value=Attribute(value=Name(id='self', ctx=Load()), attr='block_graph', ctx=Load()), attr='block_debug_key', ctx=Load()), args=[Name(id='state_parent', ctx=Load())], keywords=[])])",
        # self.block_graph.block_debug_key(block) in scc_keys  (analysis/returns/divergence_proofs.py:261)
        "Compare(left=Call(func=Attribute(value=Attribute(value=Name(id='self', ctx=Load()), attr='block_graph', ctx=Load()), attr='block_debug_key', ctx=Load()), args=[Name(id='block', ctx=Load())], keywords=[]), ops=[In()], comparators=[Name(id='scc_keys', ctx=Load())])",
        # self.block_graph.block_debug_key(succ) not in block_keys  (analysis/returns/divergence_proofs.py:809)
        "Compare(left=Call(func=Attribute(value=Attribute(value=Name(id='self', ctx=Load()), attr='block_graph', ctx=Load()), attr='block_debug_key', ctx=Load()), args=[Name(id='succ', ctx=Load())], keywords=[]), ops=[NotIn()], comparators=[Name(id='block_keys', ctx=Load())])",
        # self.block_graph.block_debug_key(successor) in scc_keys  (analysis/returns/divergence_proofs.py:229)
        "Compare(left=Call(func=Attribute(value=Attribute(value=Name(id='self', ctx=Load()), attr='block_graph', ctx=Load()), attr='block_debug_key', ctx=Load()), args=[Name(id='successor', ctx=Load())], keywords=[]), ops=[In()], comparators=[Name(id='scc_keys', ctx=Load())])",
        # self.block_graph.block_debug_key(successor) not in scc_keys  (analysis/returns/divergence_proofs.py:264)
        "Compare(left=Call(func=Attribute(value=Attribute(value=Name(id='self', ctx=Load()), attr='block_graph', ctx=Load()), attr='block_debug_key', ctx=Load()), args=[Name(id='successor', ctx=Load())], keywords=[]), ops=[NotIn()], comparators=[Name(id='scc_keys', ctx=Load())])",
        # type(debug) is not bool  (proof/conditional_view.py:563)
        "Compare(left=Call(func=Name(id='type', ctx=Load()), args=[Name(id='debug', ctx=Load())], keywords=[]), ops=[IsNot()], comparators=[Name(id='bool', ctx=Load())])",
    }
)

#: 棚卸しが「guard ではない」と認める形の全体。
DEBUG_SHAPED_NON_GUARDS: FrozenSet[GuardShape] = _NON_GUARD_ATTRIBUTES | _NON_GUARD_UNSUPPORTED
