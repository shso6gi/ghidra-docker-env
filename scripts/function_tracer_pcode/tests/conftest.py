# -*- coding: utf-8 -*-
"""pytest共通設定・フィクスチャ"""

import sys
import importlib
from pathlib import Path
from typing import Any, Dict, List, Optional, cast

# ★ [P3] sys.path操作を一元化：conftest.pyで一度だけ設定
workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

pytest = cast(Any, importlib.import_module("pytest"))

# Issue #22 PR-22-D: bounded path が呼んでよい code は package の code だけ（`core/live_values`）。
# test の module が定義する record・converter・reducer も呼ばせるため、test の harness だけが
# `tests/unit` を信頼する（fixture の記録した Ghidra の値の代わりは信頼しない: production と同じ）
from scripts.function_tracer_pcode.core import live_values as _live_values  # noqa: E402

_live_values.trust_code_directory(str(Path(__file__).parent / "unit"))

# Issue #109: 1 replay の検証は test module ではなく
# `tests/fixtures/pcode/replay_validation.py` が持つ（fast / full が共有する
# 唯一の実装）。assertion rewriting の対象へ明示的に入れておかないと、そこだけ
# 素の `assert` になって失敗時に値が出なくなる。import より前に登録する。
pytest.register_assert_rewrite(
    "scripts.function_tracer_pcode.tests.fixtures.pcode.replay_validation"
)
pytest.register_assert_rewrite(
    "scripts.function_tracer_pcode.tests.fixtures.pcode.corpus"
)


def pytest_addoption(parser):
    """記録済み corpus の選択肢（Issue #109）。

    どれを走らせるかを test 名の文字列一致（`-k`）ではなく manifest と明示の
    id で決めるための入口。CI の job 名と workflow が安定して参照できる。
    """

    group = parser.getgroup("recorded corpus")
    group.addoption(
        "--recorded-tier", action="store", default="pr_gate",
        choices=("pr_gate", "full"),
        help=(
            "which recorded replays to run: pr_gate (cases.json pr_gate=true, "
            "the per-PR gate) or full (all of them)"
        ),
    )
    group.addoption(
        "--recorded-replay", action="append", default=[], metavar="VARIANT_ID",
        help=(
            "run only this recorded replay (repeatable); overrides "
            "--recorded-tier. Used by one shard of the recorded-full matrix"
        ),
    )
    group.addoption(
        "--recorded-report-dir", action="store", default=None, metavar="DIR",
        help=(
            "write one machine-readable record per replay that passed every "
            "check, for the recorded-full aggregate job"
        ),
    )


#: 結果が壁時計に左右される test の印（Issue #239）: module の外の時計（production の時計・別の test module の
#: helper）で測る上限、実の時計で動く短い期限。module の中で時計を読む test は印が無くても
#: `_wall_clock_functions` が見つける。付け忘れは `tests/unit/test_issue239_gc_isolation.py` の静的な検査が見つける
WALL_CLOCK_MARKER = "wall_clock"


def pytest_configure(config):
    config.addinivalue_line(
        "markers",
        "recorded_replay: runs a recorded P-code replay (Issue #109). The "
        "per-PR unit-fast job deselects these; recorded-fast and "
        "recorded-full run them.",
    )
    config.addinivalue_line(
        "markers",
        f"{UNSCOPED_CONDITION_CACHE}: run the test outside any condition-cache scope "
        "(Issue #224). Only for tests that check the out-of-scope or nesting behaviour "
        "of the scope itself.",
    )
    config.addinivalue_line(
        "markers",
        f"{WALL_CLOCK_MARKER}: the test's result depends on the wall clock through a clock read "
        "outside its module (a production clock, a helper of another test module) or a deadline "
        "on the real clock. Its call runs with the older heap frozen (Issue #239, "
        "`pytest_runtest_call`).",
    )


#: 条件 cache の scope の外で走らせる test の印（Issue #224。`_pair_condition_cache_scope`）
UNSCOPED_CONDITION_CACHE = "unscoped_condition_cache"


@pytest.fixture(scope="session", autouse=True)
def _shared_source_trees_stay_unchanged():
    """静的な guard が共有した AST を、どの test も書き換えていないこと（Issue #224）。

    `tests/unit/_package_sources.parse_source` は同じ text の AST を test 間で共有する。session の
    終わりに、覚えた AST を覚えたときの text の parse と比べ、違えば session を失敗させる
    （共有の値の書き換えは、別の test の結果を test の順序に依存させる）。
    """

    yield
    from scripts.function_tracer_pcode.tests.unit._package_sources import changed_trees

    changed = changed_trees()
    assert changed == [], "a test mutated a shared AST (tests/unit/_package_sources): " + ", ".join(changed)


@pytest.fixture(autouse=True)
def _pair_condition_cache_scope(request):
    """test 1 つを、pair 1 つと同じ寿命の条件 cache の scope で包む（Issue #224）。

    production では pair 境界（`authority/lifecycle/production_boundary.py`）が pair ごとに
    `condition_cache_scope()` を開き、scope の外では cache は何も覚えない
    （`analysis/condition/condition_cache.py`）。unit test は部品を pair 境界の外で直接呼ぶ
    ので、scope が無いと条件 oracle の問い合わせが毎回 solver まで行き、production には無い
    費用を払う（1 test で Z3 context を 1,763 回作る例がある）。ここで test ごとに空の scope
    を開き、抜けたら捨てる: production の pair と同じく、test をまたいで意味の状態を持ち
    越さない。test の中で pair 境界を通る経路は、その中で自分の scope を入れ子に開く
    （production と同じ）。

    scope の外の挙動・scope の入れ子そのものを確かめる test は
    `@pytest.mark.unscoped_condition_cache` で外す。
    """

    if request.node.get_closest_marker(UNSCOPED_CONDITION_CACHE) is not None:
        yield
        return
    from scripts.function_tracer_pcode.analysis.condition.condition_cache import condition_cache_scope

    with condition_cache_scope():
        yield


@pytest.fixture(autouse=True)
def _pair_certificate_session():
    """test 1 つを、pair の比較の実行 1 回と同じ寿命の、左右の同一視の証明書の session で包む（plan v4 PR-P）。

    production では比較の実行（workflow・stage runner・strategy の branch）が session を開き、抜けると
    全ての証明書が失効する。unit test は部品をその外で直接呼ぶので、test ごとに session を開いて捨てる。
    session の外・寿命そのものを確かめる test は ``entered_certificate_session(None)`` で外へ出る。
    """

    from scripts.function_tracer_pcode.proof.formula.input_correspondence.certificates import certificate_session

    with certificate_session() as session:
        yield session


#: 壁時計を読む関数の名前（module の path ごとに 1 回だけ求める）
_WALL_CLOCK_FUNCTIONS: Dict[str, frozenset] = {}
_WALL_CLOCK_NAMES = frozenset({"perf_counter", "perf_counter_ns", "monotonic", "monotonic_ns"})


def _wall_clock_functions(path: str) -> frozenset:
    """module の中で壁時計を読む関数の名前（直接読む関数と、それを module の中で呼ぶ関数の閉包）。

    呼び出しは名前だけで照合する（束縛を解決しない）: module の中の時計を読む関数と同じ名前の別の呼び出し
    （`subprocess.run` と module の `run` など）も読むと見なす。外れても freeze が増えるだけ（memory の費用で、
    測定は正しいまま）。module の外で読む時計は見えないので、その test は `wall_clock` の印を付ける
    （付け忘れは `test_issue239_gc_isolation.py` の静的な検査が見つける）。
    """

    known = _WALL_CLOCK_FUNCTIONS.get(path)
    if known is not None:
        return known
    import ast

    try:
        tree = ast.parse(Path(path).read_text(encoding="utf-8"))
    except (OSError, SyntaxError):
        tree = None
    calls: Dict[str, set] = {}
    reading = set()
    for node in ast.walk(tree) if tree is not None else ():
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        names = set()
        for inner in ast.walk(node):
            if isinstance(inner, ast.Call):
                func = inner.func
                name = func.attr if isinstance(func, ast.Attribute) else getattr(func, "id", None)
                if name is not None:
                    names.add(name)
        calls.setdefault(node.name, set()).update(names)
        if names & _WALL_CLOCK_NAMES:
            reading.add(node.name)
    changed = True
    while changed:
        changed = False
        for name, called in calls.items():
            if name not in reading and called & reading:
                reading.add(name)
                changed = True
    known = _WALL_CLOCK_FUNCTIONS[path] = frozenset(reading)
    return known


def _measures_wall_clock(item) -> bool:
    """`item` の test 関数が壁時計を読むか（`wall_clock` の印、または module の中の関数の閉包）。"""

    if item.get_closest_marker(WALL_CLOCK_MARKER) is not None:
        return True
    name = getattr(item, "originalname", None) or getattr(item, "name", "")
    path = getattr(item, "path", None)
    return path is not None and name in _wall_clock_functions(str(path))


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_call(item):
    """壁時計で時間を測る test の本体（call）の間だけ、それより前から在る object を GC の世代から外す（Issue #239）。

    wall-clock の上限を持つ test は、被測定 code の仕事だけで時間が決まるべきで、先に走った test が
    残した session の値（共有の AST の台帳など、数百万 object）の full collection が測定の区間に入ると
    落ちる。call の前に `gc.freeze()` で既存の object を永続の世代へ移し、call の後に `gc.unfreeze()` で
    最も古い世代へ戻す（世代の list のつなぎ替えだけで、費用は object の数に依らない）。

    * call の中で作った object は今と同じく GC される（被測定 code が作る値の GC の時間は測定に入る）
    * call より前（fixture の setup・前の test）から在る循環は call の間は集められず、call の後で集められる
    * call より前から在る object の弱参照は call の間は消えない（call の中で、前から在る object が集められる
      ことを確かめる test は、その object を call の中で作る）
    * 対象は壁時計を読む test 関数だけ（`wall_clock` の印か、直接読むか、module の中の読む関数を呼ぶ:
      `_measures_wall_clock`）。
      それ以外の test の間は今と同じ GC で、古い循環の回収（full collection）を先送りし続けない（session の
      memory を増やさない）
    * GC の有効 / 無効・閾値は変えない。外で既に freeze されていれば何もしない（他の freeze を解かない）
    """

    import gc

    if gc.get_freeze_count() or not _measures_wall_clock(item):
        yield
        return
    gc.freeze()
    try:
        yield
    finally:
        gc.unfreeze()


yaml = cast(Any, importlib.import_module("yaml"))
from dataclasses import dataclass, field
from unittest.mock import Mock

# 完全なパッケージパスでインポート
from scripts.function_tracer_pcode.core.analysis import publish_raw_function_analysis
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixResult
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.core import (
    CallTargetRef,
    FunctionReturnAnalysis,
    ReturnInfo,
    Expression,
    ExpressionType,
)
from scripts.function_tracer_pcode.core.analysis import SignednessResult


# ============================================================================
# ★ [P3] Helper Functions (not fixtures) - IDE安全・再利用性向上
# ============================================================================

def load_golden_cases() -> List[Dict[str, Any]]:
    """ゴールデンケースをYAMLから読み込み（通常の関数）"""
    yaml_path = Path(__file__).parent / "fixtures" / "cases.yml"
    with open(yaml_path, 'r', encoding='utf-8') as f:
        data = yaml.safe_load(f)
    return data['test_cases']


class MockDataOrganization:
    # 外の runtime object（Ghidra の object）の代わり: 意味値の到達走査では葉（Issue #227）
    __semantic_opaque__ = True

    def __init__(self, *, int_size=4, long_size=8, long_long_size=8, short_size=2, char_size=1, pointer_size=8):
        self._int_size = int_size
        self._long_size = long_size
        self._long_long_size = long_long_size
        self._short_size = short_size
        self._char_size = char_size
        self._pointer_size = pointer_size

    def getIntegerSize(self):
        return self._int_size

    def getLongSize(self):
        return self._long_size

    def getLongLongSize(self):
        return self._long_long_size

    def getShortSize(self):
        return self._short_size

    def getCharSize(self):
        return self._char_size

    def getPointerSize(self):
        return self._pointer_size


class MockDataType:
    # 外の runtime object（Ghidra の object）の代わり: 意味値の到達走査では葉（Issue #227）
    __semantic_opaque__ = True

    def __init__(self, name: str, length: int, is_signed: bool, path: Optional[str] = None):
        self._name = name
        self._length = length
        self._is_signed = is_signed
        self._path = path or f"/builtin/{name}"
        self._data_type_manager = None
        self._opposite = None

    def getName(self):
        return self._name

    def getLength(self):
        return self._length

    def isSigned(self):
        return self._is_signed

    def getDataTypePath(self):
        return self._path

    def getDataTypeManager(self):
        return self._data_type_manager

    def setDataTypeManager(self, data_type_manager):
        self._data_type_manager = data_type_manager

    def getOppositeSignednessDataType(self):
        return self._opposite

    def setOppositeSignednessDataType(self, opposite):
        self._opposite = opposite

    def isEquivalent(self, other):
        return str(self.getDataTypePath()) == str(other.getDataTypePath())

    def isUndefined(self):
        return self._name.startswith("undefined")

    def __str__(self):
        return self._name


class MockVoidDataType(MockDataType):
    def __init__(self):
        super().__init__("void", 0, False, "/builtin/void")


class MockPointerDataType(MockDataType):
    def __init__(self, name: str, length: int, referenced_data_type=None, path: Optional[str] = None):
        super().__init__(name, length, False, path or f"/builtin/{name}")
        self._referenced_data_type = referenced_data_type

    def getDataType(self):
        return self._referenced_data_type

    def isPointer(self):
        return True


class MockFloatDataType(MockDataType):
    pass


class MockDataTypeManager:
    # 外の runtime object（Ghidra の object）の代わり: 意味値の到達走査では葉（Issue #227）
    __semantic_opaque__ = True

    def __init__(self, architecture: str = "x86:LE:64:default"):
        pointer_size = 8 if ":64:" in architecture else 4
        self._data_organization = MockDataOrganization(pointer_size=pointer_size)
        self._data_types = {}
        self._register_builtins()

    def _add(self, data_type: MockDataType):
        data_type.setDataTypeManager(self)
        self._data_types[data_type.getName()] = data_type
        self._data_types[f"/{data_type.getName()}"] = data_type
        self._data_types[data_type.getDataTypePath()] = data_type
        return data_type

    def _add_signed_pair(self, signed_name: str, unsigned_name: str, size: int):
        signed_dt = self._add(MockDataType(signed_name, size, True))
        unsigned_dt = self._add(MockDataType(unsigned_name, size, False))
        signed_dt.setOppositeSignednessDataType(unsigned_dt)
        unsigned_dt.setOppositeSignednessDataType(signed_dt)

    def _register_builtins(self):
        self._add(MockVoidDataType())
        self._add_signed_pair("char", "unsigned char", 1)
        self._add_signed_pair("short", "unsigned short", 2)
        self._add_signed_pair("int", "unsigned int", 4)
        self._add_signed_pair("long", "unsigned long", 8)
        self._add_signed_pair("long long", "unsigned long long", 8)
        self._add_signed_pair("int8_t", "uint8_t", 1)
        self._add_signed_pair("int16_t", "uint16_t", 2)
        self._add_signed_pair("int32_t", "uint32_t", 4)
        self._add_signed_pair("int64_t", "uint64_t", 8)
        self._add(MockFloatDataType("float", 4, True, "/builtin/float"))
        self._add(MockFloatDataType("double", 8, True, "/builtin/double"))
        self._add(MockDataType("undefined1", 1, False, "/builtin/undefined1"))
        self._add(MockDataType("undefined2", 2, False, "/builtin/undefined2"))
        self._add(MockDataType("undefined4", 4, False, "/builtin/undefined4"))
        self._add(MockDataType("undefined8", 8, False, "/builtin/undefined8"))
        self._alias("uchar", "unsigned char")
        self._alias("ushort", "unsigned short")
        self._alias("uint", "unsigned int")
        self._alias("ulong", "unsigned long")
        self._alias("ulonglong", "unsigned long long")
        self._alias("longlong", "long long")
        self._alias("bool", "unsigned char")

    def _alias(self, alias_name: str, canonical_name: str):
        target = self._data_types.get(canonical_name)
        if target is None:
            return
        self._data_types[alias_name] = target
        self._data_types[f"/{alias_name}"] = target

    def _pointer_name(self, base_name: str) -> str:
        return f"{base_name.strip()} *"

    def _get_or_create_pointer(self, base_name: str):
        pointer_name = self._pointer_name(base_name)
        existing = self._data_types.get(pointer_name) or self._data_types.get(f"/{pointer_name}")
        if existing is not None:
            return existing
        referenced = self._data_types.get(base_name) or self._data_types.get(f"/{base_name}")
        pointer_dt = MockPointerDataType(
            pointer_name,
            self._data_organization.getPointerSize(),
            referenced_data_type=referenced,
            path=f"/builtin/{pointer_name}",
        )
        return self._add(pointer_dt)

    def getDataType(self, name):
        data_type = self._data_types.get(name)
        if data_type is not None:
            return data_type
        normalized = (name or "").strip()
        if normalized.endswith("*"):
            base_name = normalized[:-1].strip()
            if base_name:
                return self._get_or_create_pointer(base_name)
        return None

    def findDataType(self, name):
        return self.getDataType(name)

    def getDataOrganization(self):
        return self._data_organization

    def getPointer(self, datatype):
        if datatype is None:
            return None
        base_name = datatype.getName() if hasattr(datatype, "getName") else str(datatype)
        return self._get_or_create_pointer(base_name)

    def getFloatDataTypes(self):
        return tuple(
            data_type
            for data_type in set(self._data_types.values())
            if isinstance(data_type, MockFloatDataType)
        )


def create_mock_data_type_manager(architecture: str = "x86:LE:64:default") -> MockDataTypeManager:
    return MockDataTypeManager(architecture=architecture)


def resolve_mock_data_type(type_name: Optional[str], data_type_manager: Optional[MockDataTypeManager] = None):
    if not type_name:
        return None
    dtm = data_type_manager or create_mock_data_type_manager()
    return dtm.getDataType(type_name) or dtm.findDataType(type_name) or dtm.getDataType(f"/{type_name}")


@dataclass
class MockProgram:
    """モックバイナリプログラム（ArchitectureDetectorと整合性を保つ）"""
    # 外の runtime object（Ghidra の object）の代わり: 意味値の到達走査では葉（Issue #227）
    __semantic_opaque__ = True

    name: str
    architecture: str = "x86:LE:64:default"
    data_type_manager: Optional[MockDataTypeManager] = None

    def __post_init__(self):
        self.data_type_manager = self.data_type_manager or create_mock_data_type_manager(self.architecture)
    
    def getName(self):
        return self.name

    def getDataTypeManager(self):
        return self.data_type_manager
    
    def getLanguage(self):
        """★ [P1] ArchitectureDetectorが参照する形式に完全一致"""
        arch = self.architecture
        
        class MockLanguageID:
            def getIdAsString(self):
                return arch
            
            def __str__(self):
                return arch
        
        class MockProcessor:
            def toString(self):
                # "MIPS:BE:64:64-32addr" -> "MIPS"
                return arch.split(':')[0]
            
            def __str__(self):
                return arch.split(':')[0]
        
        class MockLanguage:
            def getProcessor(self):
                return MockProcessor()
            
            def getLanguageID(self):
                return MockLanguageID()
        
        return MockLanguage()


def create_mock_analysis(
    function_name: str,
    return_type: str = "int",
    parameters: Optional[List[Dict[str, Any]]] = None,
    returns: Optional[List[ReturnInfo]] = None,
    signedness: Optional[str] = None
) -> FunctionReturnAnalysis:
    """モック解析結果を作成
    
    ★ [P1] 修正: パラメータ情報を正しく設定してP4B検証を可能にする
    """
    if parameters is None:
        parameters = []
    dtm = create_mock_data_type_manager()
    
    if returns is None:
        returns = [
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.PARAMETER, name="param_1")
            )
        ]
    
    normalized_parameters: List[Dict[str, Any]] = []
    for index, param in enumerate(parameters):
        normalized = dict(param)
        data_type_name = normalized.get("data_type")
        data_type_obj = normalized.get("data_type_obj") or resolve_mock_data_type(data_type_name, dtm)
        normalized["data_type_obj"] = data_type_obj
        normalized.setdefault("index", index)
        if data_type_obj is not None:
            normalized.setdefault("size", int(data_type_obj.getLength()))
            normalized.setdefault("is_signed", bool(data_type_obj.isSigned()))
        normalized_parameters.append(normalized)

    synthetic_program_id = sum(ord(ch) for ch in function_name) & 0xFFFFFFFF
    analysis = FunctionReturnAnalysis(
        function_name=function_name,
        entry_point="0x00401000",
        parameters=normalized_parameters,
        returns=returns,
        function_ref=CallTargetRef.from_name(
            function_name,
            program_id=synthetic_program_id,
            entry_offset=0x00401000,
        ),
    )
    
    analysis.return_type = return_type
    analysis.return_type_obj = resolve_mock_data_type(return_type, dtm)
    
    if signedness:
        analysis.signedness_result = SignednessResult(signedness=signedness)
    
    # 本番の公開境界（`analyze_function_by_name`）と同じ扱いにする: test も
    # 解析結果の producer なので、返す前に抱えている意味値を公開し、parameter 表を
    # 入力領域の正本として封印する（Issue #185）。
    return publish_raw_function_analysis(analysis)


def create_mock_result(
    is_equivalent: Optional[bool],
    solver_status: Optional[SolverStatus] = None,
    elapsed_time: float = 0.1,
    counterexample: Optional[Dict] = None,
    error_message: Optional[str] = None
) -> EquivalenceResult:
    """モック判定結果を作成"""
    if solver_status is None:
        if is_equivalent is True:
            solver_status = SolverStatus.UNSAT
        elif is_equivalent is False:
            solver_status = SolverStatus.SAT
        else:
            solver_status = SolverStatus.UNKNOWN
    
    solver_result = SolverResult(
        solver_name="mock_solver",
        status=solver_status,
        elapsed_time=elapsed_time,
        model=counterexample
    )
    
    parallel_result = ParallelResult(results=[solver_result])
    
    result = EquivalenceResult(
        is_equivalent=is_equivalent,
        function1_name="func1",
        function2_name="func2",
        binary1_name="binary1",
        binary2_name="binary2",
        solver_results=parallel_result,
        type_fix_result=TypeFixResult()
    )
    
    if error_message:
        result.error_message = error_message
    
    # ★ [P1] 追加: counterexampleがあればFormattedCounterexampleも設定
    if counterexample:
        from scripts.function_tracer_pcode.checker.counterexample import FormattedCounterexample
        result.counterexample = FormattedCounterexample(
            parameters={k: hex(v) if isinstance(v, int) else str(v) for k, v in counterexample.items()},
            return_value1=None,
            return_value2=None,
            raw_model=counterexample
        )
    
    return result


# ============================================================================
# ★ Pytest Fixtures
# ============================================================================

@pytest.fixture(scope="session")
def golden_cases():
    """ゴールデンケースをYAMLから読み込み（セッション全体で1回のみ）"""
    return load_golden_cases()


@pytest.fixture(scope="session")
def golden_cases_by_id(golden_cases):
    """★ [P3] ID検索用の辞書を提供（高速化）"""
    return {case['id']: case for case in golden_cases}


@pytest.fixture
def mock_program_x86():
    """x86バイナリのモック"""
    return MockProgram(name="test_x86.exe", architecture="x86:LE:64:default")


@pytest.fixture
def mock_program_mips64():
    """★ [P1] MIPS64バイナリのモック（ArchitectureDetectorで確実に検出される）"""
    return MockProgram(name="test_mips64.elf", architecture="MIPS:BE:64:64-32addr")


@pytest.fixture
def solver_status_map():
    """★ YAML用のステータスマッピング"""
    return {
        "SAT": SolverStatus.SAT,
        "UNSAT": SolverStatus.UNSAT,
        "UNKNOWN": SolverStatus.UNKNOWN,
        "TIMEOUT": SolverStatus.TIMEOUT,
    }


@pytest.fixture
def is_equiv_map():
    """★ YAML用の等価性マッピング"""
    return {
        "SAT": False,
        "UNSAT": True,
        "UNKNOWN": None,
        "TIMEOUT": None,
    }
