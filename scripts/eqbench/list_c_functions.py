#!/usr/bin/env python3
"""List top-level C function definitions in an EqBench source file.

This intentionally uses a small conservative parser instead of a broad regex:
it strips comments and string/character literals, walks top-level text, and
reports definitions whose parameter list is followed by a function body.
"""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, Optional


_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*$")
_CONTROL_WORDS = {
    "if",
    "for",
    "while",
    "switch",
    "return",
    "sizeof",
}
_DECLARATION_PREFIXES = {
    "typedef",
}


def _mask_comments_and_literals(text: str) -> str:
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

        if ch in {'"', "'"}:
            quote = ch
            chars[i] = " "
            i += 1
            escaped = False
            while i < n:
                current = chars[i]
                if current != "\n":
                    chars[i] = " "
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


def _matching_paren(text: str, open_index: int) -> Optional[int]:
    depth = 0
    for index in range(open_index, len(text)):
        if text[index] == "(":
            depth += 1
        elif text[index] == ")":
            depth -= 1
            if depth == 0:
                return index
    return None


def _skip_ws_and_attributes(text: str, index: int) -> int:
    n = len(text)
    while index < n:
        while index < n and text[index].isspace():
            index += 1
        if text.startswith("__attribute__", index):
            attr_open = text.find("(", index)
            if attr_open < 0:
                return index
            attr_close = _matching_paren(text, attr_open)
            if attr_close is None:
                return index
            index = attr_close + 1
            continue
        return index
    return index


def _top_level_depths(text: str) -> list[int]:
    depths: list[int] = []
    depth = 0
    for ch in text:
        depths.append(depth)
        if ch == "{":
            depth += 1
        elif ch == "}" and depth > 0:
            depth -= 1
    return depths


@dataclass(frozen=True)
class FunctionDefinition:
    """A top-level function definition span in the original source text."""

    name: str
    declaration_start: int
    body_start: int
    body_end: int


def _candidate_name(text: str, paren_index: int) -> Optional[str]:
    prefix = text[:paren_index].rstrip()
    match = _IDENT_RE.search(prefix)
    if not match:
        return None
    name = match.group(0)
    if name in _CONTROL_WORDS:
        return None

    declaration_prefix = prefix[: match.start()]
    separator_index = max(
        declaration_prefix.rfind(";"),
        declaration_prefix.rfind("{"),
        declaration_prefix.rfind("}"),
    )
    declaration = declaration_prefix[separator_index + 1 :].strip()
    if not declaration:
        return None
    first_word = declaration.split(None, 1)[0] if declaration.split(None, 1) else ""
    if first_word in _DECLARATION_PREFIXES:
        return None
    if "=" in declaration:
        return None
    return name


def _matching_brace(text: str, open_index: int) -> Optional[int]:
    depth = 0
    for index in range(open_index, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return index
    return None


def iter_function_definitions(source_text: str) -> Iterator[FunctionDefinition]:
    text = _mask_comments_and_literals(source_text)
    depths = _top_level_depths(text)
    seen: set[str] = set()
    index = 0
    while index < len(text):
        if text[index] != "(" or depths[index] != 0:
            index += 1
            continue

        close_index = _matching_paren(text, index)
        if close_index is None:
            break

        body_index = _skip_ws_and_attributes(text, close_index + 1)
        if body_index >= len(text) or text[body_index] != "{":
            index = close_index + 1
            continue

        name = _candidate_name(text, index)
        if name and name != "main" and name not in seen:
            body_end = _matching_brace(text, body_index)
            if body_end is None:
                index = body_index + 1
                continue
            prefix = text[:index].rstrip()
            name_start = prefix.rfind(name)
            if name_start < 0:
                index = body_end + 1
                continue
            declaration_prefix = prefix[:name_start]
            separator_index = max(
                declaration_prefix.rfind(";"),
                declaration_prefix.rfind("{"),
                declaration_prefix.rfind("}"),
            )
            seen.add(name)
            yield FunctionDefinition(
                name=name,
                declaration_start=separator_index + 1,
                body_start=body_index,
                body_end=body_end,
            )
        index = body_index + 1


def iter_function_names(source_text: str) -> Iterator[str]:
    for definition in iter_function_definitions(source_text):
        yield definition.name


def list_function_names(path: Path) -> Iterable[str]:
    text = path.read_text(encoding="utf-8", errors="ignore")
    return iter_function_names(text)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    args = parser.parse_args()

    for function_name in list_function_names(args.source):
        print(function_name)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
