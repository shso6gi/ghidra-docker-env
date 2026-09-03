# -*- coding: utf-8 -*-
"""Source-adjacent declaration evidence for benchmark binaries."""

from __future__ import annotations

import re
from pathlib import Path
from typing import Optional


_COMMENT_RE = re.compile(r"/\*.*?\*/|//[^\n]*", re.DOTALL)
_IGNORED_SPECIFIERS = {
    "static",
    "extern",
    "inline",
    "__inline",
    "__inline__",
}


def infer_adjacent_c_return_type(binary_path: object, function_name: str) -> Optional[str]:
    """Infer ``function_name`` return type from a C file adjacent to ``binary_path``.

    The EqBench layout keeps ``newV.c`` next to compiled ``newV-arch-compiler-opt``
    binaries. This helper is deliberately conservative: if the exact stem-matched
    adjacent source file is absent, or the declaration shape is ambiguous, it
    returns ``None`` and the binary-only path remains unchanged.
    """

    source_path = find_adjacent_c_source(binary_path)
    if source_path is None:
        return None
    try:
        source_text = source_path.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return None
    return extract_c_return_type(source_text, function_name)


def find_adjacent_c_source(binary_path: object) -> Optional[Path]:
    try:
        path = Path(str(binary_path))
    except Exception:
        return None
    parent = path.parent
    if not parent:
        return None

    stem = path.name.split("-", 1)[0]
    if stem:
        candidate = parent / f"{stem}.c"
        if candidate.is_file():
            return candidate

    return None


def extract_c_return_type(source_text: str, function_name: str) -> Optional[str]:
    if not source_text or not function_name:
        return None

    stripped = _COMMENT_RE.sub("", source_text)
    pattern = re.compile(
        r"(?:^|[;\n}])\s*([A-Za-z_][\w\s\*]*?)\s+"
        + re.escape(function_name)
        + r"\s*\(",
        re.MULTILINE,
    )
    matches = []
    for match in pattern.finditer(stripped):
        return_type = _normalize_return_type(match.group(1))
        if return_type:
            matches.append(return_type)

    unique = sorted(set(matches))
    if len(unique) != 1:
        return None
    return unique[0]


def _normalize_return_type(raw_return_type: str) -> Optional[str]:
    tokens = str(raw_return_type or "").replace("\n", " ").split()
    tokens = [token for token in tokens if token not in _IGNORED_SPECIFIERS]
    if not tokens:
        return None
    normalized = " ".join(tokens)
    normalized = re.sub(r"\s*\*\s*", " *", normalized)
    normalized = re.sub(r"\s+", " ", normalized).strip()
    if not normalized:
        return None
    return normalized
