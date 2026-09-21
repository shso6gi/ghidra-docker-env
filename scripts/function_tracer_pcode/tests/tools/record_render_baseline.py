# -*- coding: utf-8 -*-
"""PR-22-C **変更前**の SMT 描画を固定 fixture として録る。

old / new の意味一致を確かめるには old の出力が要るが、旧 renderer を production
に残したくはない。そこで変更前の commit でこの生成器を回し、出力を fixture に
固定する。比較する式は `tests/fixtures/render/corpus.py` が両方の commit で同じ
ものを組む（描画側に依存しない module にしてある）。

録り直し方（fixture の header にも書いてある）:

```bash
git worktree add /tmp/render-baseline <base commit>
cp -r scripts/function_tracer_pcode/tests/fixtures/render /tmp/render-baseline/scripts/function_tracer_pcode/tests/fixtures/
cp scripts/function_tracer_pcode/tests/tools/record_render_baseline.py /tmp/render-baseline/scripts/function_tracer_pcode/tests/tools/
cd /tmp/render-baseline && python3 -B -m scripts.function_tracer_pcode.tests.tools.record_render_baseline --output <repo>/scripts/function_tracer_pcode/tests/fixtures/render/baseline_smt.json
```
"""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
from typing import Any, Dict

from scripts.function_tracer_pcode.core.render_smt import (
    _to_smt_internal,
    collect_unknown_smt_declarations,
    expression_returns_bool,
    expression_smt_bit_width,
)
from scripts.function_tracer_pcode.core.expression import ExpressionType
from scripts.function_tracer_pcode.tests.fixtures.render.corpus import build_corpus


def _iter_nodes(expression):
    nodes = []
    pending = [expression]
    seen = set()
    while pending:
        node = pending.pop()
        if node is None or id(node) in seen:
            continue
        seen.add(id(node))
        nodes.append(node)
        expr_type = getattr(node, "expr_type", None)
        if expr_type is not None and expr_type == ExpressionType.PHI and node.value:
            for condition, value in reversed(node.value):
                if value is not None:
                    pending.append(value)
                inner = getattr(condition, "expression", None)
                if inner is not None:
                    pending.append(inner)
                elif condition is not None and getattr(condition, "expr_type", None) is not None:
                    pending.append(condition)
            continue
        pending.extend(reversed(list(getattr(node, "operands", None) or [])))
    return nodes


def declaration_lines(expression, *, float_mode: str, address_context: bool):
    """式に現れる自由 symbol の宣言。old / new どちらでも同じ規則で作れる。"""

    lines = []
    declared = set()

    def declare(name: str, sort: str) -> None:
        if name in declared:
            return
        declared.add(name)
        lines.append(f"(declare-const {name} {sort})")

    for name, bits in collect_unknown_smt_declarations(expression):
        declare(name, f"(_ BitVec {int(bits)})")

    for node in _iter_nodes(expression):
        expr_type = getattr(node, "expr_type", None)
        if expr_type is None:
            continue
        bits = max(1, int(expression_smt_bit_width(node) or 1))
        if expr_type == ExpressionType.PARAMETER:
            declare(node.name or f"param_{node.value}", f"(_ BitVec {bits})")
        elif expr_type == ExpressionType.VARIABLE:
            rendered = _to_smt_internal(node)
            if rendered == (node.name or "var"):
                declare(rendered, f"(_ BitVec {bits})")
        elif expr_type == ExpressionType.MEMORY:
            mem_bits = bits if bits in (8, 16, 32, 64) else 32
            declare(f"mem{mem_bits}", f"(Array (_ BitVec 64) (_ BitVec {mem_bits}))")
        elif expr_type == ExpressionType.INTRINSIC:
            pass
    return sorted(lines)


def render_case(spec: Dict[str, Any]) -> str:
    return _to_smt_internal(
        spec["expression"],
        bool(spec.get("prefer_signed_arithmetic", False)),
        None,
        bool(spec.get("address_context", False)),
        spec.get("float_mode", "uf"),
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True)
    arguments = parser.parse_args()

    try:
        commit = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip()
    except (subprocess.SubprocessError, OSError):
        commit = "unknown"

    cases: Dict[str, Any] = {}
    skipped: Dict[str, str] = {}
    for name, spec in sorted(build_corpus().items()):
        expression = spec["expression"]
        try:
            smt = render_case(spec)
            declarations = declaration_lines(
                expression,
                float_mode=spec.get("float_mode", "uf"),
                address_context=bool(spec.get("address_context", False)),
            )
            sort = "bool" if expression_returns_bool(expression) else "bitvec"
        except Exception as exc:  # noqa: BLE001 - 生成器なので理由を残して落とす
            skipped[name] = f"{type(exc).__name__}: {exc}"
            continue
        cases[name] = {
            "smt": smt,
            "declarations": declarations,
            "sort": sort,
            "float_mode": spec.get("float_mode", "uf"),
            "prefer_signed_arithmetic": bool(spec.get("prefer_signed_arithmetic", False)),
            "address_context": bool(spec.get("address_context", False)),
        }

    payload = {
        "schema": "render-baseline-smt-v1",
        "recorded_at_commit": commit,
        "generator": "scripts.function_tracer_pcode.tests.tools.record_render_baseline",
        "corpus": "scripts.function_tracer_pcode.tests.fixtures.render.corpus.build_corpus",
        "note": (
            "SMT rendered by the renderer as it was before PR-22-C. The differential "
            "test renders the same corpus with the current renderer and asks a solver "
            "whether the two can differ."
        ),
        "skipped": skipped,
        "cases": cases,
    }
    path = pathlib.Path(arguments.output)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    print(f"{path}: {len(cases)} cases, {len(skipped)} skipped")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
