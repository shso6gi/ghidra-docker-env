# -*- coding: utf-8 -*-
"""包括捕捉（broad except）の静的 baseline（Issue #125 PR-125-B）。

#108 が既存の `except Exception` を型付き例外へ置き換えるまでの間、**新しい
包括捕捉が増えないこと**だけを固定する guard。既存の件数は凍結 baseline
（`broad_except_baseline.json`）として持ち、**delete-only** で運用する:

* 新しい `(module, qualname)` が出る → FAIL
* 既存 key の `logged` / `unlogged` が増える → FAIL
* 実測が baseline より減ったのに baseline が残っている（stale）→ FAIL
* 行が動いただけ → PASS（key に行番号を含めない）
* handler を消して baseline を同じだけ縮める → PASS

baseline は例外の意味分類を持たない。目的は「新規・増加の防止」と「削減を
stale 検出で強制的に反映させること」の 2 つだけで、どの handler が正しいかの
判断は #108 / 各 producer の責務。

`logged` / `unlogged` の意味:

* `logged`   = handler 本体で `log_swallowed(...)` を呼ぶ（握り潰しを
  `core.errors` の台帳に残す）handler。
* `unlogged` = それ以外の handler。

判定は AST の `Call` node で行う（コメントや変数名からは推定しない）。handler
本体に入れ子で置かれた別の `except` 節・関数定義・lambda の中の呼び出しは、
その handler の記録ではないので数えない。
"""

from __future__ import annotations

import ast
import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterator, List, Mapping, Tuple


#: 包括捕捉とみなす例外名（tuple の要素に 1 つでもあれば包括捕捉）。
BROAD_EXCEPTION_NAMES = frozenset({"Exception", "BaseException"})

#: 握り潰しを台帳に残す関数名（`core.errors.log_swallowed`）。
SWALLOWED_LEDGER_FUNCTION = "log_swallowed"

#: package 直下の走査しないディレクトリ（テスト自身は対象外）。
#: ここに無い場所へ test を置くと新しい key として FAIL するので、見落としでは
#: なく「置き場所が違う」ことが分かる。
EXCLUDED_TOP_LEVEL_DIRS = frozenset({"tests"})

PACKAGE_ROOT = Path(__file__).resolve().parents[2]
BASELINE_PATH = Path(__file__).resolve().parent / "broad_except_baseline.json"
BASELINE_SCHEMA = "broad-except-baseline-v1"

#: 関数本体の中で定義された名前を表す Python 標準の qualname 区切り。
LOCALS_MARKER = "<locals>"

#: 関数にもクラスにも属さない module 直下の handler の qualname。
MODULE_QUALNAME = "<module>"


@dataclass
class BroadExceptViolations:
    """baseline と実測の差。空なら PASS。"""

    added: List[Tuple[str, str, Dict[str, int]]] = field(default_factory=list)
    increased: List[Tuple[str, str, Dict[str, int], Dict[str, int]]] = field(
        default_factory=list
    )
    stale: List[Tuple[str, str, Dict[str, int], Dict[str, int]]] = field(
        default_factory=list
    )

    def __bool__(self) -> bool:
        return bool(self.added or self.increased or self.stale)

    def describe(self) -> str:
        lines: List[str] = []
        for module, qualname, actual in self.added:
            lines.append(
                f"new broad-except site {module}:{qualname} -> {actual}; "
                "raise a typed failure (core.errors) instead of catching Exception"
            )
        for module, qualname, expected, actual in self.increased:
            lines.append(
                f"broad-except count grew at {module}:{qualname}: "
                f"baseline {expected} -> actual {actual}"
            )
        for module, qualname, expected, actual in self.stale:
            lines.append(
                f"stale baseline entry {module}:{qualname}: "
                f"baseline {expected} -> actual {actual}; "
                "the baseline is delete-only, so shrink it to the measured value"
            )
        return "\n".join(lines)


def _iter_source_files(root: Path) -> Iterator[Path]:
    for path in sorted(root.rglob("*.py")):
        relative = path.relative_to(root)
        if relative.parts[0] in EXCLUDED_TOP_LEVEL_DIRS:
            continue
        yield path


def _module_name(root: Path, path: Path) -> str:
    relative = path.relative_to(root)
    parts = list(relative.parts)
    if parts[-1] == "__init__.py":
        parts.pop()
    else:
        parts[-1] = parts[-1][: -len(".py")]
    return ".".join(parts) if parts else relative.stem


def _is_broad(handler: ast.ExceptHandler) -> bool:
    """bare `except:` / `except Exception` / `except BaseException` / それらを含む tuple。"""

    if handler.type is None:
        return True
    elements = handler.type.elts if isinstance(handler.type, ast.Tuple) else [handler.type]
    for element in elements:
        if isinstance(element, ast.Name) and element.id in BROAD_EXCEPTION_NAMES:
            return True
        if isinstance(element, ast.Attribute) and element.attr in BROAD_EXCEPTION_NAMES:
            return True
    return False


def _handler_owned_nodes(handler: ast.ExceptHandler) -> Iterator[ast.AST]:
    """handler 本体のうち、**この handler が実行する** node だけを辿る。

    入れ子の `except` 節・関数定義・lambda の中身はその handler の記録では
    ないので降りない（外側 handler を誤って `logged` にしない）。
    """

    def _owned(node: ast.AST) -> bool:
        return not isinstance(
            node,
            (ast.ExceptHandler, ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda),
        )

    stack: List[ast.AST] = [node for node in handler.body if _owned(node)]
    while stack:
        node = stack.pop()
        yield node
        stack.extend(child for child in ast.iter_child_nodes(node) if _owned(child))


def _logs_swallowed(handler: ast.ExceptHandler) -> bool:
    for node in _handler_owned_nodes(handler):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        if isinstance(func, ast.Name) and func.id == SWALLOWED_LEDGER_FUNCTION:
            return True
        if isinstance(func, ast.Attribute) and func.attr == SWALLOWED_LEDGER_FUNCTION:
            return True
    return False


def _walk_qualnames(node: ast.AST, prefix: str) -> Iterator[Tuple[ast.ExceptHandler, str]]:
    """`node` の子を辿り、各 `ExceptHandler` を囲む qualname とともに返す。"""

    for child in ast.iter_child_nodes(node):
        if isinstance(child, ast.ClassDef):
            inner = f"{prefix}.{child.name}" if prefix else child.name
            yield from _walk_qualnames(child, inner)
            continue
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
            inner = f"{prefix}.{child.name}" if prefix else child.name
            yield from _walk_qualnames(child, f"{inner}.{LOCALS_MARKER}")
            continue
        if isinstance(child, ast.ExceptHandler):
            owner = prefix
            if owner.endswith(f".{LOCALS_MARKER}"):
                owner = owner[: -len(f".{LOCALS_MARKER}")]
            yield child, owner or MODULE_QUALNAME
        yield from _walk_qualnames(child, prefix)


def scan_broad_except_handlers(root: Path) -> Dict[str, Dict[str, Dict[str, int]]]:
    """`root` 以下の package 本体を走査し、`(module, qualname)` ごとの件数を返す。

    戻り値は baseline JSON の `entries` と同じ形（module -> qualname ->
    `{"logged": n, "unlogged": m}`）。件数 0 の key は含めない。
    """

    entries: Dict[str, Dict[str, Dict[str, int]]] = {}
    for path in _iter_source_files(Path(root)):
        module = _module_name(Path(root), path)
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        per_qualname: Dict[str, Dict[str, int]] = {}
        for handler, qualname in _walk_qualnames(tree, ""):
            if not _is_broad(handler):
                continue
            counts = per_qualname.setdefault(qualname, {"logged": 0, "unlogged": 0})
            counts["logged" if _logs_swallowed(handler) else "unlogged"] += 1
        if per_qualname:
            entries[module] = dict(sorted(per_qualname.items()))
    return dict(sorted(entries.items()))


def compare_to_baseline(
    actual: Mapping[str, Mapping[str, Mapping[str, int]]],
    baseline: Mapping[str, Mapping[str, Mapping[str, int]]],
) -> BroadExceptViolations:
    """実測と baseline の差を 3 種類に分けて返す（delete-only 運用）。"""

    violations = BroadExceptViolations()
    zero = {"logged": 0, "unlogged": 0}
    keys = {
        (module, qualname)
        for source in (actual, baseline)
        for module, qualnames in source.items()
        for qualname in qualnames
    }
    for module, qualname in sorted(keys):
        measured = dict(zero)
        measured.update(actual.get(module, {}).get(qualname, {}))
        expected = baseline.get(module, {}).get(qualname)
        if expected is None:
            violations.added.append((module, qualname, measured))
            continue
        expected = {**zero, **expected}
        if any(measured[kind] > expected[kind] for kind in zero):
            violations.increased.append((module, qualname, expected, measured))
        if any(measured[kind] < expected[kind] for kind in zero):
            violations.stale.append((module, qualname, expected, measured))
    return violations


def load_baseline(path: Path = BASELINE_PATH) -> Dict[str, Dict[str, Dict[str, int]]]:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    assert payload["schema"] == BASELINE_SCHEMA
    return payload["entries"]


def render_baseline_document(
    entries: Mapping[str, Mapping[str, Mapping[str, int]]],
) -> str:
    """baseline ファイルの正準テキスト（1 key = 1 行）。

    `json.dumps(indent=...)` は件数まで改行するので、削減 diff が読みにくい。
    key ごとに 1 行へ畳んだこの形を正とし、`test_baseline_file_is_canonical`
    が固定する。#108 で handler を消したときは、その行を消すだけでよい。
    """

    lines = ['{', f'  "schema": "{BASELINE_SCHEMA}",', '  "entries": {']
    modules = sorted(entries)
    for module_index, module in enumerate(modules):
        qualnames = entries[module]
        lines.append(f"    {json.dumps(module)}: {{")
        names = sorted(qualnames)
        for name_index, qualname in enumerate(names):
            counts = qualnames[qualname]
            row = (
                f"      {json.dumps(qualname)}: "
                f'{{"logged": {int(counts["logged"])}, '
                f'"unlogged": {int(counts["unlogged"])}}}'
            )
            lines.append(row + ("," if name_index + 1 < len(names) else ""))
        lines.append("    }" + ("," if module_index + 1 < len(modules) else ""))
    lines.extend(["  }", "}"])
    return "\n".join(lines) + "\n"


def baseline_totals(
    entries: Mapping[str, Mapping[str, Mapping[str, int]]],
) -> Dict[str, int]:
    totals = {"keys": 0, "logged": 0, "unlogged": 0}
    for qualnames in entries.values():
        for counts in qualnames.values():
            totals["keys"] += 1
            totals["logged"] += int(counts.get("logged", 0))
            totals["unlogged"] += int(counts.get("unlogged", 0))
    totals["handlers"] = totals["logged"] + totals["unlogged"]
    return totals


# ---------------------------------------------------------------------------
# fixture tree helpers（scanner API の入力を変えて挙動を確認する）
# ---------------------------------------------------------------------------


def _write_tree(root: Path, files: Mapping[str, str]) -> Path:
    for name, source in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
    return root


# ---------------------------------------------------------------------------
# 1. 現 HEAD の baseline
# ---------------------------------------------------------------------------


def test_broad_except_baseline_matches_the_current_package():
    violations = compare_to_baseline(
        scan_broad_except_handlers(PACKAGE_ROOT), load_baseline()
    )
    assert not violations, violations.describe()


def test_baseline_is_a_frozen_snapshot_with_stable_totals():
    """凍結値そのもの（#108 で減らすときだけ動かす）。"""

    entries = load_baseline()
    assert baseline_totals(entries) == {
        "keys": 596,
        "logged": 0,
        "unlogged": 923,
        "handlers": 923,
    }


#: `module.path` / `Host.method.<locals>.inner` / `<module>` だけを許す形。
_MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$")
_QUALNAME_SEGMENT_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*|<locals>)$")


def test_baseline_keys_carry_no_line_numbers():
    """key に位置情報（`path:line` の類）が一切入っていないこと。"""

    for module, qualnames in load_baseline().items():
        assert _MODULE_RE.fullmatch(module), module
        for qualname, counts in qualnames.items():
            if qualname != MODULE_QUALNAME:
                for segment in qualname.split("."):
                    assert _QUALNAME_SEGMENT_RE.fullmatch(segment), qualname
            assert set(counts) == {"logged", "unlogged"}
            assert counts["logged"] >= 0 and counts["unlogged"] >= 0
    # 位置が変わっても key は動かない、を fixture で直接確かめる。
    assert MODULE_QUALNAME == "<module>"


# ---------------------------------------------------------------------------
# 2. fail 条件（新規 / 増加 / stale）
# ---------------------------------------------------------------------------


_FIXTURE_MODULE = '''
def handler():
    try:
        pass
    except Exception:
        pass
'''


def test_new_module_qualname_fails(tmp_path):
    root = _write_tree(tmp_path, {"pkg/mod.py": _FIXTURE_MODULE})
    violations = compare_to_baseline(scan_broad_except_handlers(root), {})
    assert violations
    assert violations.added == [("pkg.mod", "handler", {"logged": 0, "unlogged": 1})]
    assert "new broad-except site pkg.mod:handler" in violations.describe()


def test_existing_count_increase_fails(tmp_path):
    source = _FIXTURE_MODULE + '''
def handler_again():
    try:
        pass
    except Exception:
        pass
'''
    root = _write_tree(tmp_path, {"pkg/mod.py": source.replace("handler_again", "handler")})
    baseline = {"pkg": {}, "pkg.mod": {"handler": {"logged": 0, "unlogged": 1}}}
    violations = compare_to_baseline(scan_broad_except_handlers(root), baseline)
    assert violations
    assert violations.increased == [
        ("pkg.mod", "handler", {"logged": 0, "unlogged": 1}, {"logged": 0, "unlogged": 2})
    ]
    assert not violations.added and not violations.stale


def test_stale_baseline_fails_when_a_count_shrinks(tmp_path):
    root = _write_tree(tmp_path, {"pkg/mod.py": _FIXTURE_MODULE})
    baseline = {"pkg.mod": {"handler": {"logged": 0, "unlogged": 3}}}
    violations = compare_to_baseline(scan_broad_except_handlers(root), baseline)
    assert violations
    assert violations.stale == [
        ("pkg.mod", "handler", {"logged": 0, "unlogged": 3}, {"logged": 0, "unlogged": 1})
    ]
    assert "delete-only" in violations.describe()


def test_stale_baseline_fails_when_the_whole_key_is_gone(tmp_path):
    root = _write_tree(tmp_path, {"pkg/mod.py": "def handler():\n    return 1\n"})
    baseline = {"pkg.mod": {"handler": {"logged": 1, "unlogged": 2}}}
    violations = compare_to_baseline(scan_broad_except_handlers(root), baseline)
    assert violations.stale == [
        ("pkg.mod", "handler", {"logged": 1, "unlogged": 2}, {"logged": 0, "unlogged": 0})
    ]


def test_shrinking_the_baseline_with_the_handler_passes(tmp_path):
    root = _write_tree(tmp_path, {"pkg/mod.py": "def handler():\n    return 1\n"})
    assert not compare_to_baseline(scan_broad_except_handlers(root), {})


def test_moving_lines_does_not_change_the_measurement(tmp_path):
    moved = '''
# Issue #125: この上下にコメントと空行を足しても baseline は動かない。


def unrelated():
    return 0


def handler():
    # 途中にもコメントを足す
    try:

        pass

    except Exception:

        pass
'''
    first = scan_broad_except_handlers(
        _write_tree(tmp_path / "a", {"pkg/mod.py": _FIXTURE_MODULE})
    )
    second = scan_broad_except_handlers(
        _write_tree(tmp_path / "b", {"pkg/mod.py": moved})
    )
    assert first == second == {"pkg.mod": {"handler": {"logged": 0, "unlogged": 1}}}
    assert not compare_to_baseline(second, first)


# ---------------------------------------------------------------------------
# 3. 検出対象と logged / unlogged の区別
# ---------------------------------------------------------------------------


def test_detects_bare_exception_baseexception_and_tuple_forms(tmp_path):
    source = '''
import builtins


def bare():
    try:
        pass
    except:
        pass


def broad():
    try:
        pass
    except Exception:
        pass


def base():
    try:
        pass
    except BaseException:
        pass


def tuple_form():
    try:
        pass
    except (ValueError, Exception):
        pass


def dotted_tuple_form():
    try:
        pass
    except (KeyError, builtins.BaseException):
        pass


def narrow():
    try:
        pass
    except (ValueError, KeyError):
        pass


def narrow_dotted():
    try:
        pass
    except builtins.ValueError:
        pass
'''
    entries = scan_broad_except_handlers(_write_tree(tmp_path, {"pkg/mod.py": source}))
    assert set(entries["pkg.mod"]) == {
        "bare", "broad", "base", "tuple_form", "dotted_tuple_form"
    }
    assert all(
        counts == {"logged": 0, "unlogged": 1} for counts in entries["pkg.mod"].values()
    )


def test_logged_and_unlogged_are_distinguished(tmp_path):
    source = '''
from scripts.function_tracer_pcode.core import errors
from scripts.function_tracer_pcode.core.errors import log_swallowed


def logged_plain():
    try:
        pass
    except Exception as exc:
        log_swallowed(None, exc, site="pkg.mod.logged_plain")


def logged_attribute():
    try:
        pass
    except Exception as exc:
        errors.log_swallowed("r", exc, site="pkg.mod.logged_attribute")


def unlogged_named_like_it():
    log_swallowed_later = 1
    try:
        pass
    except Exception:
        # log_swallowed(...) はコメントなので記録ではない
        return log_swallowed_later


def both_kinds():
    try:
        pass
    except Exception as exc:
        log_swallowed(None, exc, site="pkg.mod.both_kinds")
    try:
        pass
    except Exception:
        pass
'''
    entries = scan_broad_except_handlers(_write_tree(tmp_path, {"pkg/mod.py": source}))
    assert entries["pkg.mod"] == {
        "both_kinds": {"logged": 1, "unlogged": 1},
        "logged_attribute": {"logged": 1, "unlogged": 0},
        "logged_plain": {"logged": 1, "unlogged": 0},
        "unlogged_named_like_it": {"logged": 0, "unlogged": 1},
    }


def test_a_nested_handler_does_not_mark_the_outer_handler_logged(tmp_path):
    source = '''
from scripts.function_tracer_pcode.core.errors import log_swallowed


def outer():
    try:
        pass
    except Exception:
        try:
            pass
        except Exception as inner:
            log_swallowed(None, inner, site="pkg.mod.outer")


def deferred():
    try:
        pass
    except Exception as exc:
        def later():
            log_swallowed(None, exc, site="pkg.mod.deferred")

        return later
'''
    entries = scan_broad_except_handlers(_write_tree(tmp_path, {"pkg/mod.py": source}))
    assert entries["pkg.mod"]["outer"] == {"logged": 1, "unlogged": 1}
    assert entries["pkg.mod"]["deferred"] == {"logged": 0, "unlogged": 1}


# ---------------------------------------------------------------------------
# 4. 走査範囲と qualname の安定性
# ---------------------------------------------------------------------------


def test_tests_directory_is_not_scanned(tmp_path):
    root = _write_tree(
        tmp_path,
        {
            "pkg/mod.py": _FIXTURE_MODULE,
            "tests/unit/test_thing.py": _FIXTURE_MODULE,
            "tests/conftest.py": _FIXTURE_MODULE,
        },
    )
    entries = scan_broad_except_handlers(root)
    assert set(entries) == {"pkg.mod"}


def test_the_real_package_scan_excludes_tests():
    entries = scan_broad_except_handlers(PACKAGE_ROOT)
    assert entries
    assert not any(module.split(".")[0] == "tests" for module in entries)


def test_qualnames_are_stable_for_methods_nested_defs_and_module_level(tmp_path):
    source = '''
try:
    pass
except Exception:
    pass


class Host:
    try:
        pass
    except Exception:
        pass

    def method(self):
        try:
            pass
        except Exception:
            pass

        def inner():
            try:
                pass
            except Exception:
                pass

        return inner

    class Nested:
        async def amethod(self):
            try:
                pass
            except Exception:
                pass


def factory():
    class Local:
        def method(self):
            try:
                pass
            except Exception:
                pass

    return Local
'''
    entries = scan_broad_except_handlers(_write_tree(tmp_path, {"pkg/mod.py": source}))
    assert set(entries["pkg.mod"]) == {
        "<module>",
        "Host",
        "Host.method",
        "Host.method.<locals>.inner",
        "Host.Nested.amethod",
        "factory.<locals>.Local.method",
    }


def test_package_init_modules_keep_the_package_name(tmp_path):
    root = _write_tree(
        tmp_path, {"pkg/__init__.py": _FIXTURE_MODULE, "pkg/mod.py": _FIXTURE_MODULE}
    )
    assert set(scan_broad_except_handlers(root)) == {"pkg", "pkg.mod"}


# ---------------------------------------------------------------------------
# 5. baseline 自体の健全性
# ---------------------------------------------------------------------------


def test_baseline_file_is_canonical():
    """on-disk のテキストが正準形そのもの（再生成が決定的になる）。"""

    assert BASELINE_PATH.read_text(encoding="utf-8") == render_baseline_document(
        load_baseline()
    )


def test_baseline_file_is_sorted_and_has_no_empty_entries():
    payload = json.loads(BASELINE_PATH.read_text(encoding="utf-8"))
    entries = payload["entries"]
    assert list(entries) == sorted(entries)
    for module, qualnames in entries.items():
        assert qualnames, f"empty module entry: {module}"
        assert list(qualnames) == sorted(qualnames)
        for qualname, counts in qualnames.items():
            assert counts["logged"] or counts["unlogged"], (
                f"zero entry must be deleted, not kept: {module}:{qualname}"
            )


def test_baseline_schema_is_pinned():
    payload = json.loads(BASELINE_PATH.read_text(encoding="utf-8"))
    assert set(payload) == {"schema", "entries"}
    assert payload["schema"] == BASELINE_SCHEMA
