"""Phase 2: the rewrite settings are dead.  They are accepted only as a
deprecated compatibility shim and never reach the checker's behaviour."""
import warnings

import pytest

from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.cli.args import build_parser


def test_checker_ignores_rewrite_kwargs_with_a_deprecation_warning():
    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always")
        checker = EquivalenceChecker(strategy="pairwise", timeout=5, enable_rewrite=False)
    assert any(issubclass(w.category, DeprecationWarning) for w in caught)
    # compatibility surface: the attributes keep their former defaults / the
    # passed values, but nothing in the checker reads them any more
    assert checker.enable_rewrite is False
    assert checker.rewrite_direction == "to_modulo"
    assert not hasattr(checker, "_apply_rewrite")

    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always")
        default = EquivalenceChecker(strategy="pairwise", timeout=5)
    assert not [w for w in caught if issubclass(w.category, DeprecationWarning)]
    assert default.enable_rewrite is True
    assert default.rewrite_direction == "to_modulo"


def test_checker_internals_do_not_read_the_compatibility_attributes():
    """The attributes exist only as a compatibility surface: every mention in
    the checker package must be the assignment in __init__."""
    import re
    from pathlib import Path

    root = Path(__file__).resolve().parents[2] / "checker"
    reads = []
    for path in root.rglob("*.py"):
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            code = line.split("#", 1)[0]
            for match in re.finditer(r"self\.(enable_rewrite|rewrite_direction)\b", code):
                if not re.match(r"\s*=(?!=)", code[match.end():]):
                    reads.append(f"{path.name}:{lineno}")
    assert reads == [], f"internal reads of the deprecated attributes: {reads}"


def test_cli_still_parses_the_deprecated_flags():
    parser = build_parser()
    args = parser.parse_args(["--equiv", "a", "b", "-f", "f", "--no-rewrite", "--rewrite-direction", "to_expansion"])
    assert args.no_rewrite is True and args.rewrite_direction == "to_expansion"
    assert "非推奨" in parser.format_help()
