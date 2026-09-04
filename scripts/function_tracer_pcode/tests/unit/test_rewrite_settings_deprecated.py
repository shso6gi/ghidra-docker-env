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
    assert not hasattr(checker, "enable_rewrite")
    assert not hasattr(checker, "rewrite_direction")
    assert not hasattr(checker, "_apply_rewrite")

    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always")
        EquivalenceChecker(strategy="pairwise", timeout=5)
    assert not [w for w in caught if issubclass(w.category, DeprecationWarning)]


def test_cli_still_parses_the_deprecated_flags():
    parser = build_parser()
    args = parser.parse_args(["--equiv", "a", "b", "-f", "f", "--no-rewrite", "--rewrite-direction", "to_expansion"])
    assert args.no_rewrite is True and args.rewrite_direction == "to_expansion"
    assert "非推奨" in parser.format_help()
