#!/usr/bin/env python3
"""Check that main.tex keeps the non-content format of tech-sample-css.tex."""

from __future__ import annotations

import difflib
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parent.parent
SAMPLE = ROOT / "tech-sample-css.tex"
MAIN = ROOT / "main.tex"


def preamble(path: Path) -> list[str]:
    lines: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines(keepends=True):
        lines.append(line)
        if line.strip() == r"\begin{document}":
            return lines
    raise ValueError(f"{path.name}: \\begin{{document}} not found")


def require_order(text: str, tokens: list[str]) -> None:
    offset = 0
    for token in tokens:
        position = text.find(token, offset)
        if position < 0:
            raise ValueError(f"main.tex: required template element missing: {token}")
        offset = position + len(token)


def main() -> int:
    sample_preamble = preamble(SAMPLE)
    main_preamble = preamble(MAIN)
    if sample_preamble != main_preamble:
        diff = "".join(
            difflib.unified_diff(
                sample_preamble,
                main_preamble,
                fromfile=SAMPLE.name,
                tofile=MAIN.name,
            )
        )
        print("main.tex preamble differs from the CSS template:", file=sys.stderr)
        print(diff, file=sys.stderr)
        return 1

    text = MAIN.read_text(encoding="utf-8")
    require_order(
        text,
        [
            r"\title{",
            r"\etitle{",
            r"\affiliate{",
            r"\author{",
            r"\begin{abstract}",
            r"\end{abstract}",
            r"\begin{jkeyword}",
            r"\end{jkeyword}",
            r"\begin{eabstract}",
            r"\end{eabstract}",
            r"\begin{ekeyword}",
            r"\end{ekeyword}",
            r"\maketitle",
        ],
    )
    print("Template format check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
