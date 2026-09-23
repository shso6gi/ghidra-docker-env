"""最終 ``InputCorrespondence``（parameter 入力の対応関係）の唯一の owner（Issue #167）。

比較する 2 関数の parameter をどう結び付けるか（premise）、どの入力 extension
仮定が成り立つか（entailed assumptions）、それを使う書き換えの許可
（``RewriteAuthorization``）、SAT / UNSAT を最終判定に使ってよいか
（``decisive_sufficient``）は、全部ここで決める 1 つの relation から導出する。

authority flow（v5 §4.3、一方向）::

    raw analysis ──┬─ raw ProjectionClosure（semantics/projection_closure）
                   └─ validated IEE（evidence.py、出所は checker/arch/input_extension）
        → relation.build_input_correspondence_set（pairing.py → R0〜R5）
        → model.InputCorrespondenceSet
            → premise_lines / entailed assumption / authorization(side)
            → normalizer → query → decisive gate

変更軸ごとに module を分けてある:

* ``evidence.py``: IEE の contract と validator（新しい出所は provider 側に足す）。
* ``pairing.py``: どの parameter とどの parameter を結ぶか。
* ``relation.py``: 1 pair にどの relation（R0〜R5）を与えるか。raw だけを受け付ける。
* ``model.py``: relation の値と、そこから導出される全ての値（consumer はここだけ読む）。

Names are resolved lazily on first access so importing a submodule never
pulls in the whole layer (and cannot create import cycles).
"""

from importlib import import_module

_PACKAGE = "scripts.function_tracer_pcode.proof.formula.input_correspondence"
_LAZY = {
    **{
        name: (f"{_PACKAGE}.evidence", name)
        for name in (
            "AbiExtensionRule",
            "InputExtensionEvidence",
            "InputExtensionRefusal",
            "ParameterBinding",
            "StorageObservation",
            "TrustedParameterClassification",
            "analysis_parameter_binding",
            "validate_input_extension_evidence",
        )
    },
    **{
        name: (f"{_PACKAGE}.model", name)
        for name in (
            "LEFT",
            "RIGHT",
            "InputCorrespondence",
            "InputCorrespondenceSet",
            "InputCorrespondenceStatus",
            "InputRelationKind",
            "SideParameter",
            "extension_assumption_line",
            "extension_premise_lines",
        )
    },
    **{
        name: (f"{_PACKAGE}.relation", name)
        for name in (
            "PROJECTION_CANDIDATE_BITS",
            "RawAnalysisRequiredError",
            "build_input_correspondence_set",
            "build_tie_only_correspondence_set",
        )
    },
    "build_parameter_pairs": (f"{_PACKAGE}.pairing", "build_parameter_pairs"),
}

__all__ = sorted(_LAZY)


def __getattr__(name):
    try:
        module_name, attribute = _LAZY[name]
    except KeyError:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}") from None
    value = getattr(import_module(module_name), attribute)
    globals()[name] = value
    return value


def __dir__():
    return sorted(set(globals()) | set(_LAZY))
