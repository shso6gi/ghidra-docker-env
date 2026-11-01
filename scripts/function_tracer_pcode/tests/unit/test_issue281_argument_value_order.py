# -*- coding: utf-8 -*-
"""Issue #281 review 5 / #285: 呼び出しの引数の値（caller → callee へ渡る値）を決める書き込みの順序。

呼び出しの時点の記憶域の値は、経路の上で呼び出しより前の **最後の** 書き込みで決まる。修正前は:

* 経路の op を番地の順で比べていた（番地が後ろの block が先に実行される配置で、呼び出しより前の op を落とす）。
* 「引数らしさ」の高い候補を、後の書き込みより優先していた（上書きされた値を引数にする）。
* stack の load の値を、関数全体の番地の順で「前の最後の書き込み」から選んでいた（分岐の別の腕の書き込みを選ぶ）。
"""

from types import SimpleNamespace

from scripts.function_tracer_pcode.analysis.effects import call_argument
from scripts.function_tracer_pcode.analysis.effects.call_paths import _impl__path_ops_before_call
from scripts.function_tracer_pcode.core import Expression
from scripts.function_tracer_pcode.core.program_order import ProgramOrder
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.tests.unit._program_order_fakes import FakeOp, fake_cfg


def _block(*ops):
    return SimpleNamespace(pcode_ops=list(ops))


def test_path_ops_follow_the_path_not_the_addresses():
    """経路 0 → 2 → 1（block 2 の番地が後ろ）。呼び出しは block 1。block 2 の op も呼び出しより前。"""

    _high, blocks = fake_cfg({0: [2], 2: [1], 1: []})
    early = FakeOp(blocks[0], 0, address=0x1000)
    laid_out_late = FakeOp(blocks[2], 0, address=0x9000)
    call = FakeOp(blocks[1], 1, mnemonic="CALL", address=0x2000)
    after_call = FakeOp(blocks[1], 2, address=0x2004)
    ops = _impl__path_ops_before_call(
        [_block(early), _block(laid_out_late), _block(FakeOp(blocks[1], 0, address=0x1ffc), call, after_call)],
        call,
    )
    assert laid_out_late in ops and early in ops
    assert after_call not in ops
    assert ops.index(early) < ops.index(laid_out_late)


def test_a_path_that_does_not_reach_the_call_is_unknown():
    _high, blocks = fake_cfg({0: []})
    call = FakeOp(blocks[0], 5, mnemonic="CALL")
    assert _impl__path_ops_before_call([_block(FakeOp(blocks[0], 0))], call) is None


def _candidates(monkeypatch, table):
    """op → (値, rank, 引数らしさ) を返すように候補の作り方を差し替える。"""

    monkeypatch.setattr(
        call_argument,
        "_recover_call_argument_candidate_from_op",
        lambda op, *a, **k: table.get(id(op)),
    )


def _select(ops):
    return call_argument._impl__select_best_storage_candidate(
        ops, StorageInfo(is_register=True, register_name="x0", size=8), None, [], {}
    )


def test_the_last_write_before_the_call_is_the_argument(monkeypatch):
    """前の書き込みの方が「引数らしい」（rank が高い）でも、後の書き込みが値を決める。"""

    first, last = object(), object()
    plausible = Expression.parameter("p", index=0, size=8)
    overwritten_by = Expression.constant(0, size=8)
    _candidates(monkeypatch, {id(first): (plausible, 3, 9), id(last): (overwritten_by, 3, 0)})
    assert _select([first, last]) is overwritten_by


def test_a_last_write_to_part_of_the_storage_makes_the_argument_unknown(monkeypatch):
    first, last = object(), object()
    _candidates(
        monkeypatch,
        {id(first): (Expression.constant(1, size=8), 3, 0), id(last): (Expression.constant(2, size=4), 1, 0)},
    )
    assert _select([first, last]) is None


# ---------------------------------------------------------------------------
# stack の load の値
# ---------------------------------------------------------------------------


class _Varnode:
    def __init__(self, offset, size=4):
        self.offset = offset
        self.size = size

    def getSize(self):
        return self.size


class _StoreOp(FakeOp):
    def __init__(self, block, position, slot):
        super().__init__(block, position, mnemonic="STORE")
        self._slot = slot

    def getOutput(self):
        return None

    def getNumInputs(self):
        return 3

    def getInput(self, index):
        return [None, self._slot, _Varnode(0, 4)][index]


class _LoadOp(FakeOp):
    def __init__(self, block, position, slot):
        super().__init__(block, position, mnemonic="LOAD")
        self._slot = slot

    def getOutput(self):
        return _Varnode(99, 4)

    def getInput(self, index):
        return [None, self._slot][index]


def _recover(monkeypatch, successors, stores, load):
    high, blocks = fake_cfg(successors)
    slot = _Varnode(-8)
    store_ops = [_StoreOp(blocks[block], position, slot) for block, position in stores]
    load_op = _LoadOp(blocks[load[0]], load[1], slot)
    order = ProgramOrder(successors)
    tracer = SimpleNamespace(program_order=lambda: order, get_all_pcode_ops=lambda: store_ops + [load_op])
    monkeypatch.setattr(
        call_argument,
        "_stack_location_key",
        lambda varnode, size=0: ("stack", varnode.offset, size or varnode.size) if varnode is slot else None,
    )
    recovered = []
    monkeypatch.setattr(
        call_argument,
        "_recover_parameter_expression_from_varnode",
        lambda varnode, *a, **k: recovered.append(varnode) or Expression.parameter("p", index=0, size=4),
    )
    return call_argument._impl__recover_parameter_from_stack_load(load_op, tracer, [], 0, set()), recovered


def test_a_spill_in_the_entry_block_is_the_value_of_the_load(monkeypatch):
    result, recovered = _recover(monkeypatch, {0: [1], 1: []}, [(0, 0)], (1, 0))
    assert result is not None and len(recovered) == 1


def test_stores_on_two_branch_arms_leave_the_load_unknown(monkeypatch):
    """0 → {1, 2} → 3。どちらの腕の store も load より前にあり得る: 値は経路で変わる。"""

    result, _recovered = _recover(monkeypatch, {0: [1, 2], 1: [3], 2: [3], 3: []}, [(1, 0), (2, 0)], (3, 0))
    assert result is None


def test_a_single_store_on_one_arm_does_not_dominate_the_load(monkeypatch):
    result, _recovered = _recover(monkeypatch, {0: [1, 2], 1: [3], 2: [3], 3: []}, [(1, 0)], (3, 0))
    assert result is None


def test_a_store_laid_out_after_the_load_but_executed_before_it_is_used(monkeypatch):
    """0 → 2 → 1 で store は block 2（番地は後ろ）、load は block 1。修正前の番地の順では見えなかった。"""

    result, recovered = _recover(monkeypatch, {0: [2], 2: [1], 1: []}, [(2, 0)], (1, 0))
    assert result is not None and len(recovered) == 1
