"""ProgramAccessService collaborator（lifecycle 分割 2/3）の回帰テスト。"""

import ast
import inspect

import pytest
from contextlib import AbstractContextManager
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns import lifecycle
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.lifecycle import ProgramAccessService

NAMES = {
    "program_is_big_endian", "program_identity", "program_transaction", "program_userop_name",
    "get_function_manager", "resolve_function_from_address", "find_function_by_name",
    "resolve_function_from_program_offset", "get_instruction_with_fallback", "attempt_disassemble_at",
    "get_decompiler", "dispose", "decompile_function", "make_tracer", "find_block_info_for_program_offset",
}
FACADE_CALLBACKS = ("address_offset_for_block_endpoint", "decompile_with_broker")
SUPPLIERS = ("program_value", "binary_id_value", "debug_flag", "decompiler_value")


def _analyzer(program=None):
    return ReturnAnalyzer(program=Mock() if program is None else program, debug=False)


def test_collaborator_holds_only_its_dependencies():
    analyzer = _analyzer()
    service = analyzer._program_access
    assert set(vars(service)) == {"debug_reporter"} | set(FACADE_CALLBACKS) | set(SUPPLIERS) | {"set_decompiler"}
    assert service.debug_reporter is analyzer._debug_reporter


def test_every_delegator_forwards_to_the_collaborator():
    analyzer = _analyzer()
    names = {n for n, _ in inspect.getmembers(ProgramAccessService, predicate=inspect.isfunction)} - {"__init__"}
    assert names == NAMES
    for name in sorted(names):
        facade_name = name if name == "dispose" else "_" + name
        sentinel = object()
        assert not isinstance(inspect.getattr_static(ReturnAnalyzer, facade_name), (staticmethod, classmethod)), name
        with patch.object(analyzer._program_access, name, return_value=sentinel) as mocked:
            params = list(inspect.signature(getattr(ReturnAnalyzer, facade_name)).parameters.values())[1:]
            args, kwargs = [], {}
            for param in params:
                if param.kind is inspect.Parameter.KEYWORD_ONLY:
                    kwargs[param.name] = Mock()
                else:
                    args.append(Mock())
            assert getattr(analyzer, facade_name)(*args, **kwargs) is sentinel
            mocked.assert_called_once_with(*args, **kwargs)


def test_decompiler_ownership_stays_on_the_facade():
    """_decompiler は ReturnAnalyzer が所有し、collaborator は supplier + setter で扱う（既存 seam 保存）。"""
    analyzer = _analyzer()
    assert analyzer._decompiler is None
    fake = Mock()
    with patch.dict("sys.modules", {"ghidra": Mock(), "ghidra.app": Mock(), "ghidra.app.decompiler": Mock(DecompInterface=Mock(return_value=fake))}):
        assert analyzer._get_decompiler() is fake
    assert analyzer._decompiler is fake                 # setter 経由で facade 属性に書かれる
    fake.openProgram.assert_called_once_with(analyzer.program)
    assert analyzer._get_decompiler() is fake           # 2 回目は生成しない
    analyzer.dispose()
    fake.dispose.assert_called_once()
    assert analyzer._decompiler is None                 # dispose は setter で None に戻す
    analyzer._decompiler = Mock()                       # 既存テストの直接代入 seam
    assert analyzer._program_access.decompiler_value() is analyzer._decompiler


def test_get_decompiler_stores_the_instance_before_open_program_like_the_old_implementation():
    """#77 レビュー指摘: 旧実装は DecompInterface 生成直後（openProgram より前）に _decompiler へ保存していた。
    openProgram が例外を投げても instance が facade に残り、dispose() で回収できる順序を固定する。"""
    analyzer = _analyzer()
    fake = Mock()
    fake.openProgram.side_effect = RuntimeError("open failed")
    with patch.dict("sys.modules", {"ghidra": Mock(), "ghidra.app": Mock(), "ghidra.app.decompiler": Mock(DecompInterface=Mock(return_value=fake))}):
        with pytest.raises(RuntimeError):
            analyzer._get_decompiler()
    assert analyzer._decompiler is fake
    analyzer.dispose()
    fake.dispose.assert_called_once()
    assert analyzer._decompiler is None


def test_dispose_tolerates_dead_jvm_but_reraises_other_errors():
    analyzer = _analyzer()
    analyzer._decompiler = Mock()
    analyzer._decompiler.dispose.side_effect = Exception("Java Virtual Machine is not running")
    analyzer.dispose()
    assert analyzer._decompiler is None
    analyzer._decompiler = Mock()
    analyzer._decompiler.dispose.side_effect = RuntimeError("boom")
    try:
        analyzer.dispose()
    except RuntimeError:
        pass
    else:
        raise AssertionError("non-JVM errors must propagate")
    assert analyzer._decompiler is None


def test_program_transaction_is_still_a_context_manager():
    program = Mock()
    program.startTransaction.return_value = 7
    analyzer = _analyzer(program)
    cm = analyzer._program_transaction("desc")
    assert isinstance(cm, AbstractContextManager)
    with cm:
        pass
    program.startTransaction.assert_called_once_with("desc")
    program.endTransaction.assert_called_once_with(7, True)


def test_decompile_function_goes_through_the_facade_broker_callback():
    analyzer = _analyzer()
    results = Mock()
    results.decompileCompleted.return_value = True
    with patch("scripts.function_tracer_pcode.ghidra.decompilation_broker.decompile_function", return_value=results) as broker:
        assert analyzer._decompile_function("fn", 30) is results
        assert broker.call_args.args[0] is analyzer       # broker には facade を渡す
    tree = ast.parse(inspect.getsource(lifecycle))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "ProgramAccessService")
    assert not [n for n in ast.walk(cls) if isinstance(n, ast.Call)
                and any(isinstance(a, ast.Name) and a.id == "self" for a in list(n.args) + [k.value for k in n.keywords])]


def test_suppliers_read_analyzer_state_at_call_time():
    analyzer = _analyzer()
    service = analyzer._program_access
    assert service.program_value() is analyzer.program
    analyzer._binary_id = "B-late"
    assert service.binary_id_value() == "B-late"
    analyzer.debug = True
    assert service.debug_flag() is True


def test_unextracted_helpers_dispatch_through_the_facade_at_call_time():
    analyzer = _analyzer()
    for attr in FACADE_CALLBACKS:
        sentinel = object()
        with patch.object(ReturnAnalyzer, "_" + attr, return_value=sentinel) as mocked:
            assert getattr(analyzer._program_access, attr)(Mock(), key=1) is sentinel
            mocked.assert_called_once()


def test_make_tracer_and_program_identity_are_direct_dependencies_elsewhere():
    analyzer = _analyzer()
    holders = [v for v in vars(analyzer).values()
               if type(v).__module__.startswith("scripts.function_tracer_pcode.analysis.returns.") and "program_access" in vars(v)]
    assert holders and all(h.program_access is analyzer._program_access for h in holders)
    assert not any("make_tracer" in vars(h) or "program_identity" in vars(h) for h in holders)
