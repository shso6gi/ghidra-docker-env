#!/usr/bin/env python3
"""Select changed Neq functions and their source-level caller closure.

The Neq runner compiles the complete source pair, but it does not need to
compare every unchanged helper as a top-level function for the primary
NOT_EQ evaluation.  This utility keeps all changed function definitions and
all callers reachable by reverse traversal of the direct call graph in both
source variants.
"""

from __future__ import annotations

import argparse
import re
from collections import defaultdict, deque
from pathlib import Path
from typing import Iterable

from list_c_functions import (
    FunctionDefinition,
    _mask_comments_and_literals,
    iter_function_definitions,
)


_CALL_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(")


def _remove_comments(text: str) -> str:
    """Remove C comments while preserving literals and line structure."""

    chars = list(text)
    i = 0
    n = len(chars)
    while i < n:
        ch = chars[i]
        nxt = chars[i + 1] if i + 1 < n else ""
        if ch == "/" and nxt == "/":
            chars[i] = chars[i + 1] = " "
            i += 2
            while i < n and chars[i] != "\n":
                chars[i] = " "
                i += 1
            continue
        if ch == "/" and nxt == "*":
            chars[i] = chars[i + 1] = " "
            i += 2
            while i + 1 < n:
                if chars[i] == "*" and chars[i + 1] == "/":
                    chars[i] = chars[i + 1] = " "
                    i += 2
                    break
                if chars[i] != "\n":
                    chars[i] = " "
                i += 1
            continue
        if ch in {"\"", "'"}:
            quote = ch
            i += 1
            escaped = False
            while i < n:
                current = chars[i]
                if escaped:
                    escaped = False
                elif current == "\\":
                    escaped = True
                elif current == quote:
                    i += 1
                    break
                i += 1
            continue
        i += 1
    return "".join(chars)


def _normalized_definition(source: str, definition: FunctionDefinition) -> str:
    text = source[definition.declaration_start : definition.body_end + 1]
    return " ".join(_remove_comments(text).split())


def _definitions(source_path: Path) -> tuple[str, list[FunctionDefinition]]:
    source = source_path.read_text(encoding="utf-8", errors="ignore")
    definitions = list(iter_function_definitions(source))
    if not definitions:
        raise ValueError(f"no non-main function definitions found: {source_path}")
    names = [definition.name for definition in definitions]
    if len(names) != len(set(names)):
        raise ValueError(f"duplicate function definitions found: {source_path}")
    return source, definitions


def _calls_by_function(
    source: str,
    definitions: Iterable[FunctionDefinition],
) -> dict[str, set[str]]:
    definitions = list(definitions)
    known_names = {definition.name for definition in definitions}
    calls: dict[str, set[str]] = {}
    for definition in definitions:
        body = source[definition.body_start : definition.body_end + 1]
        calls[definition.name] = {
            match.group(1)
            for match in _CALL_RE.finditer(_mask_comments_and_literals(body))
            if match.group(1) in known_names and match.group(1) != definition.name
        }
    return calls


def select_functions(new_source: Path, old_source: Path) -> tuple[list[str], list[str], list[str], list[str]]:
    new_text, new_definitions = _definitions(new_source)
    old_text, old_definitions = _definitions(old_source)
    new_by_name = {definition.name: definition for definition in new_definitions}
    old_by_name = {definition.name: definition for definition in old_definitions}
    if set(new_by_name) != set(old_by_name):
        raise ValueError(
            "function census differs: "
            f"new_only={sorted(set(new_by_name) - set(old_by_name))} "
            f"old_only={sorted(set(old_by_name) - set(new_by_name))}"
        )

    all_names = [definition.name for definition in new_definitions]
    changed = [
        name
        for name in all_names
        if _normalized_definition(new_text, new_by_name[name])
        != _normalized_definition(old_text, old_by_name[name])
    ]
    if not changed:
        raise ValueError("no changed function definition found")

    new_calls = _calls_by_function(new_text, new_definitions)
    old_calls = _calls_by_function(old_text, old_definitions)
    callers: dict[str, set[str]] = defaultdict(set)
    for call_graph in (new_calls, old_calls):
        for caller, callees in call_graph.items():
            for callee in callees:
                callers[callee].add(caller)

    closure = set(changed)
    pending = deque(changed)
    while pending:
        callee = pending.popleft()
        for caller in callers[callee]:
            if caller not in closure:
                closure.add(caller)
                pending.append(caller)

    caller_closure = [name for name in all_names if name in closure and name not in set(changed)]
    selected = [name for name in all_names if name in closure]
    return all_names, changed, caller_closure, selected


def _write_lines(path: Path, names: Iterable[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(f"{name}\n" for name in names), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--new-source", type=Path, required=True)
    parser.add_argument("--old-source", type=Path, required=True)
    parser.add_argument("--all-output", type=Path, required=True)
    parser.add_argument("--changed-output", type=Path, required=True)
    parser.add_argument("--caller-output", type=Path, required=True)
    parser.add_argument("--selected-output", type=Path, required=True)
    args = parser.parse_args()

    all_names, changed, caller_closure, selected = select_functions(
        args.new_source, args.old_source
    )
    _write_lines(args.all_output, all_names)
    _write_lines(args.changed_output, changed)
    _write_lines(args.caller_output, caller_closure)
    _write_lines(args.selected_output, selected)
    print(
        f"all={len(all_names)} changed={len(changed)} "
        f"caller_closure={len(caller_closure)} selected={len(selected)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
