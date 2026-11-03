"""Issue #282 AC 9（PR #289 review）: frame への access と frame の外への access の alias の証拠。

入口の pointer・global は entry SP より下を指し得る（一律の前提を置かない）。stack 変数・prologue の退避・spill・
callee の frame への書き込みは high P-code に現れないので、機械語の P-code（命令ごとの raw P-code）で、番地が SP
だけから作られた access（frame）と SP を含まない access（frame の外）を分ける。両方がある関数・SP と他の値の両方
から作った番地・呼び出しのある関数は証拠なし（`effect_store_location_unmodeled` で EQ と NOT_EQ を止める）。
frame だけ・frame の外だけの関数は判定を変えない。

命令は Ghidra の API の形をした小さな fake で組む（`analysis/effects/frame_alias.py` が読む method だけ）。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.analysis.effects.frame_alias import frame_alias_unproven, mark_frame_alias_unproven
from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary

SP, X0, X1, X8, X29, X30 = 0x8, 0x4000, 0x4008, 0x4040, 0x40E8, 0x40F0


class _Space:
    def __init__(self, name):
        self._name = name

    def getName(self):  # noqa: N802 - Ghidra API
        return self._name


class _Address:
    def __init__(self, offset, space="ram"):
        self._offset = offset
        self._space = _Space(space)

    def getOffset(self):  # noqa: N802
        return self._offset

    def getAddressSpace(self):  # noqa: N802
        return self._space


class _Varnode:
    def __init__(self, kind, offset, size=8):
        self.kind, self.offset, self.size = kind, offset, size

    def isConstant(self):  # noqa: N802
        return self.kind == "const"

    def isRegister(self):  # noqa: N802
        return self.kind == "register"

    def isUnique(self):  # noqa: N802
        return self.kind == "unique"

    def getOffset(self):  # noqa: N802
        return self.offset

    def getSize(self):  # noqa: N802
        return self.size

    def getAddress(self):  # noqa: N802
        return _Address(self.offset, self.kind)


def reg(offset):
    return _Varnode("register", offset)


def const(value):
    return _Varnode("const", value)


def uniq(offset):
    return _Varnode("unique", offset)


def ram(offset):
    return _Varnode("ram", offset)


class _Op:
    def __init__(self, mnemonic, inputs, output=None):
        self._mnemonic, self._inputs, self._output = mnemonic, list(inputs), output

    def getMnemonic(self):  # noqa: N802
        return self._mnemonic

    def getNumInputs(self):  # noqa: N802
        return len(self._inputs)

    def getInput(self, index):  # noqa: N802
        return self._inputs[index]

    def getOutput(self):  # noqa: N802
        return self._output


def add(out, base, offset):
    return _Op("INT_ADD", [base, const(offset)], out)


def copy(out, source):
    return _Op("COPY", [source], out)


def store(address, value):
    return _Op("STORE", [const(0x1B1), address, value])


def load(out, address):
    return _Op("LOAD", [const(0x1B1), address], out)


class _Instruction:
    def __init__(self, address, ops, *, fall_through=True, flows=(), delay_slot=False):
        self.address, self.ops = address, ops
        self.fall_through, self.flows, self.delay_slot = fall_through, list(flows), delay_slot

    def getAddress(self):  # noqa: N802
        return _Address(self.address)

    def getPcode(self):  # noqa: N802
        return list(self.ops)

    def getFallThrough(self):  # noqa: N802
        return _Address(self.address + 4) if self.fall_through else None

    def getFlows(self):  # noqa: N802
        return [_Address(target) for target in self.flows]

    def isInDelaySlot(self):  # noqa: N802
        return self.delay_slot


class _Listing:
    def __init__(self, instructions):
        self.instructions = instructions

    def getInstructions(self, _body, _forward):  # noqa: N802
        return list(self.instructions)


class _Register:
    def getAddress(self):  # noqa: N802
        return _Address(SP, "register")


class _Spec:
    def getStackPointer(self):  # noqa: N802
        return _Register()


class _Program:
    def __init__(self, instructions):
        self._listing = _Listing(instructions)

    def getListing(self):  # noqa: N802
        return self._listing

    def getCompilerSpec(self):  # noqa: N802
        return _Spec()


class _Function:
    def getBody(self):  # noqa: N802
        return object()

    def getEntryPoint(self):  # noqa: N802
        return _Address(0x1000)


def _code(*bodies):
    """1 命令 1 要素の op の列。最後の命令は戻る（fall-through 無し）。"""

    instructions = []
    for index, ops in enumerate(bodies):
        last = index == len(bodies) - 1
        ops = list(ops) + ([_Op("RETURN", [reg(X30)])] if last else [])
        instructions.append(_Instruction(0x1000 + 4 * index, ops, fall_through=not last))
    return _Program(instructions)


def _verdict(program):
    return frame_alias_unproven(program, _Function())


# 退避（prologue）: sp - 16 へ x29 / x30 を書く
PROLOGUE = [add(uniq(0x100), reg(SP), -16), store(uniq(0x100), reg(X29))]


# ---------------------------------------------------------------------------
# 負例: frame と frame の外の access が組み合わさる（修正前は high P-code に現れず、どの gate も見ていなかった）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "program",
    [
        # (a) 退避（high P-code に現れない frame への書き込み）の後に `*p` を読む: p == sp - 16 なら退避した値
        pytest.param(_code(PROLOGUE, [load(reg(X8), reg(X0))]), id="frame-write-then-pointer-read"),
        # (b) `*p` へ書いた後に退避した register を復元する（frame の読み出し）: p が退避の slot なら戻り先が変わる
        pytest.param(
            _code([store(reg(X0), reg(X1))], [add(uniq(0x100), reg(SP), -16), load(reg(X29), uniq(0x100))]),
            id="pointer-write-then-frame-read",
        ),
        # (c) `*p` へ書いた後に frame（stack 変数）へ書く: 観測する `*p` の最終値が変わり得る
        pytest.param(
            _code([store(reg(X0), reg(X1))], [add(uniq(0x100), reg(SP), -8), store(uniq(0x100), const(0))]),
            id="pointer-write-then-frame-write",
        ),
        # (d) frame pointer（x29 = sp）経由の stack 変数と `*p`。x29 の出自は命令を跨いで追う
        pytest.param(
            _code([copy(reg(X29), reg(SP))], [add(uniq(0x100), reg(X29), -4), store(uniq(0x100), reg(X1))],
                  [load(reg(X8), reg(X0))]),
            id="frame-pointer-slot-then-pointer-read",
        ),
        # (e) 大きな負の offset の frame への store と global（定数番地）の読み出し: 外の領域に届き得る
        pytest.param(
            _code([add(uniq(0x100), reg(SP), -0x100000), store(uniq(0x100), reg(X1))],
                  [copy(reg(X8), ram(0x11000))]),
            id="large-negative-offset-and-global",
        ),
        # (f) `sp + x1`（SP と他の値の両方から作った番地）: frame の外にも届き得る
        pytest.param(
            _code([_Op("INT_ADD", [reg(SP), reg(X1)], uniq(0x100)), store(uniq(0x100), const(0))]),
            id="sp-plus-variable-index",
        ),
        # (g) 呼び出し: callee の frame への書き込みは entry SP より下へ届く（命令からは分からない）
        pytest.param(_code([_Op("CALL", [ram(0x2000)])], [load(reg(X8), reg(X0))]), id="call"),
        # (h) loop の back edge で register が SP 由来になる（前向きの解析の合流）
        pytest.param(
            _Program([
                _Instruction(0x1000, [copy(reg(X8), reg(X0))]),
                _Instruction(0x1004, [store(reg(X8), const(1))]),
                _Instruction(0x1008, [copy(reg(X8), reg(SP)), _Op("BRANCH", [_Varnode("ram", 0x1004)])],
                             fall_through=False, flows=[0x1004]),
            ]),
            id="register-becomes-frame-on-a-back-edge",
        ),
    ],
)
def test_frame_and_outside_accesses_together_have_no_evidence(program):
    assert _verdict(program) is not None


@pytest.mark.parametrize(
    "program",
    [
        pytest.param(_Program([]), id="no-instructions"),
        # 本体の外への分岐（tail call）
        pytest.param(
            _Program([_Instruction(0x1000, [_Op("BRANCH", [_Varnode("ram", 0x9000)])], fall_through=False,
                                   flows=[0x9000])]),
            id="branch-out-of-the-body",
        ),
        # 行き先の分からない間接分岐
        pytest.param(
            _Program([_Instruction(0x1000, [_Op("BRANCHIND", [reg(X8)])], fall_through=False)]),
            id="unresolved-indirect-branch",
        ),
    ],
)
def test_unreadable_or_unbounded_code_has_no_evidence(program):
    assert _verdict(program) is not None


def test_a_program_without_the_listing_api_has_no_evidence():
    assert frame_alias_unproven(object(), _Function()) is not None


# ---------------------------------------------------------------------------
# 正例: 組み合わさらない関数は判定を変えない（stack 変数を持つ関数を一律に止めない）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "program",
    [
        # O0 の spill / reload だけ（frame だけを使う）
        pytest.param(
            _code(PROLOGUE, [copy(reg(X29), reg(SP))], [add(uniq(0x100), reg(X29), -4), store(uniq(0x100), reg(X0))],
                  [add(uniq(0x100), reg(X29), -4), load(reg(X8), uniq(0x100))]),
            id="frame-only",
        ),
        # frame を持たない leaf の pointer の読み書きだけ
        pytest.param(_code([load(reg(X8), reg(X0))], [store(reg(X1), reg(X8))]), id="pointer-only"),
        # register だけ
        pytest.param(_code([_Op("INT_ADD", [reg(X0), reg(X1)], reg(X0))]), id="registers-only"),
        # 分岐を持つ frame だけの関数（合流しても SP 由来のまま）
        pytest.param(
            _Program([
                _Instruction(0x1000, [copy(reg(X8), reg(SP)), _Op("CBRANCH", [_Varnode("ram", 0x1008), reg(X0)])],
                             flows=[0x1008]),
                _Instruction(0x1004, [add(reg(X8), reg(SP), -8)]),
                _Instruction(0x1008, [store(reg(X8), const(0)), _Op("RETURN", [reg(X30)])], fall_through=False),
            ]),
            id="frame-only-with-a-join",
        ),
    ],
)
def test_functions_whose_accesses_do_not_combine_keep_their_evidence(program):
    assert _verdict(program) is None


def test_the_reason_is_added_once_to_an_effect_summary():
    summary = EffectSummary(parameter_names=[], effects=[])
    assert mark_frame_alias_unproven(summary)
    assert not mark_frame_alias_unproven(summary)
    assert summary.incomplete_reasons == ("effect_store_location_unmodeled",)


# ---------------------------------------------------------------------------
# 最終判定: 証拠なしは EQ と NOT_EQ の両方を止め、証拠ありは判定を保つ（本物の解析の段・production の check）
# ---------------------------------------------------------------------------


def _template(name):
    from scripts.function_tracer_pcode.core import Expression, FunctionReturnAnalysis, ReturnInfo

    from scripts.function_tracer_pcode.tests.unit._memory_model_fixtures import _param

    value = Expression.binary_op("INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(1, 4))
    return FunctionReturnAnalysis(
        function_name=name,
        entry_point="0x1000",
        parameters=[_param("a", size=4, index=0)],
        returns=[ReturnInfo(address="0x1", conditions=[], value=value)],
        return_type="int",
    )


@pytest.mark.parametrize("frame_alias, blocked", [(None, False), ("frame and non-frame memory accesses", True)])
def test_missing_evidence_blocks_both_verdicts_and_present_evidence_keeps_them(frame_alias, blocked):
    from scripts.function_tracer_pcode.tests.unit._analyzer_pipeline_harness import analyze_through_pipeline

    analysis = analyze_through_pipeline(_template("f"), frame_alias=frame_alias)
    reason = "effect_store_location_unmodeled"
    assert (reason in analysis.get_equivalence_blocking_unsafety_reasons()) is blocked
    assert (reason in analysis.get_decisive_sat_unsafety_reasons()) is blocked
