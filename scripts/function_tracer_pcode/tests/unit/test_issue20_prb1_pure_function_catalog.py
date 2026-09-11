# -*- coding: utf-8 -*-
"""C99 math catalog + decision-neutral call-model candidate metadata (Issue #20 PR-B1).

catalog は「仮定を置けば model 化し得る callsite」の分類にしか使わない。ここで
固定するのは主に **成立しないこと**: 名前一致だけ、user-defined 同名、provenance
不明、alias の証拠不足、signature 不一致、errno / fenv 観測中 — いずれも candidate
不成立でなければならない。
"""

from __future__ import annotations

import ast
import copy
import json
import subprocess
import sys
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.analysis.effects import pure_function_catalog as catalog_module
from scripts.function_tracer_pcode.analysis.effects.pure_function_catalog import (
    CATALOG_SCHEMA_VERSION,
    PROVENANCE_DIRECT_EXTERNAL,
    PROVENANCE_THUNK_TO_EXTERNAL,
    PureFunctionCatalogError,
    catalog_path,
    load_pure_function_catalog,
    parse_pure_function_catalog,
    resolve_call_model_candidate,
)
from scripts.function_tracer_pcode.analysis.effects import external_call_models
from scripts.function_tracer_pcode.analysis.effects.external_call_models import (
    ExternalCallEffectPolicy,
)
from scripts.function_tracer_pcode.core.analysis import DeferredCallInfo
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.runtime_refs.call_models import (
    CallModelCandidateRef,
)


# --- Ghidra object doubles -------------------------------------------------


class _DataTypeManager:
    def __init__(self):
        self.float_types = ()

    def getFloatDataTypes(self):
        return self.float_types


_DTM = _DataTypeManager()


class _FloatType:
    def __init__(self, name, length):
        self._name = name
        self._length = length

    def getName(self):
        return self._name

    def getLength(self):
        return self._length

    def getDataTypeManager(self):
        return _DTM

    def isEquivalent(self, other):
        return isinstance(other, _FloatType) and other._length == self._length


class _IntType:
    def __init__(self, name, length, signed=True):
        self._name = name
        self._length = length
        self._signed = signed

    def getName(self):
        return self._name

    def getLength(self):
        return self._length

    def isSigned(self):
        return self._signed

    def getDataTypeManager(self):
        return _DTM

    def isEquivalent(self, other):
        return isinstance(other, _IntType) and other._length == self._length


class _PointerType:
    def __init__(self, length=8):
        self._length = length

    def getName(self):
        return "double *"

    def getLength(self):
        return self._length

    def isPointer(self):
        return True

    def getDataTypeManager(self):
        return _DTM

    def isEquivalent(self, other):
        return other is self


DOUBLE = _FloatType("double", 8)
FLOAT = _FloatType("float", 4)
INT = _IntType("int", 4)
LONGLONG = _IntType("longlong", 8)
DOUBLE_PTR = _PointerType()
_DTM.float_types = (DOUBLE, FLOAT)


class _ExternalLocation:
    def __init__(self, library_name="<EXTERNAL>", original_imported_name=""):
        self._library_name = library_name
        self._original = original_imported_name

    def getLibraryName(self):
        return self._library_name

    def getOriginalImportedName(self):
        return self._original


class _Parameter:
    def __init__(self, ordinal, data_type):
        self._ordinal = ordinal
        self._data_type = data_type

    def getOrdinal(self):
        return self._ordinal

    def getDataType(self):
        return self._data_type


class _Function:
    """Minimal Ghidra ``Function`` double for provenance + signature reads."""

    def __init__(
        self,
        name,
        *,
        is_external=False,
        is_thunk=False,
        thunked=None,
        external_location=None,
        parameter_types=(DOUBLE,),
        return_type=DOUBLE,
        var_args=False,
    ):
        self._name = name
        self._is_external = is_external
        self._is_thunk = is_thunk
        self._thunked = thunked
        self._external_location = external_location
        self._parameters = tuple(
            _Parameter(index, data_type)
            for index, data_type in enumerate(parameter_types)
        )
        self._return_type = return_type
        self._var_args = var_args

    def getName(self):
        return self._name

    def isExternal(self):
        return self._is_external

    def isThunk(self):
        return self._is_thunk

    def getThunkedFunction(self, _follow=True):
        return self._thunked

    def getExternalLocation(self):
        return self._external_location

    def getParameters(self):
        return list(self._parameters)

    def getReturnType(self):
        return self._return_type

    def hasVarArgs(self):
        return self._var_args


def _external_function(name, **kwargs):
    kwargs.setdefault("external_location", _ExternalLocation())
    return _Function(name, is_external=True, **kwargs)


def _thunk_to_external(wrapper_name, external_name=None, **kwargs):
    external = _external_function(external_name or wrapper_name, **kwargs)
    return _Function(wrapper_name, is_thunk=True, thunked=external)


class _OpaqueCallee:
    """classification API を一切持たない callee（分類不能）。"""

    def getName(self):
        return "log"


def _target(function_obj):
    return CallTargetRef.from_function(function_obj)


NO_OBSERVATION = ExternalCallEffectPolicy()


def _resolve(function_obj, policy=NO_OBSERVATION):
    return resolve_call_model_candidate(_target(function_obj), policy=policy)


# --- catalog schema --------------------------------------------------------


def test_shipped_catalog_loads_and_matches_the_module_schema_version():
    catalog = load_pure_function_catalog(reload=True)
    assert catalog.schema_version == CATALOG_SCHEMA_VERSION
    assert catalog.provider == "c99_math_catalog_v1"
    assert catalog.required_provenance == "external_import"
    assert "log" in catalog.entries
    assert "sqrt" in catalog.entries
    log_entry = catalog.entries["log"]
    assert [spec.key() for spec in log_entry.parameters] == [("float", 64)]
    assert log_entry.return_spec.key() == ("float", 64)


def test_shipped_catalog_is_the_tracked_json_file():
    payload = json.loads(catalog_path().read_text(encoding="utf-8"))
    parsed = parse_pure_function_catalog(payload)
    assert parsed == load_pure_function_catalog(reload=True)


def test_shipped_catalog_declares_no_pointer_or_platform_width_entries():
    """幅が ABI 依存の型と pointer 引数は B1 の schema では表現しない。"""
    catalog = load_pure_function_catalog(reload=True)
    for excluded in ("logl", "sqrtl", "frexp", "modf", "remquo", "nan", "lrint", "scalbln"):
        assert excluded not in catalog.entries
    for entry in catalog.entries.values():
        widths = [spec.width_bits for spec in entry.parameters]
        widths.append(entry.return_spec.width_bits)
        assert all(width in (32, 64) for width in widths)


def _catalog_payload(**overrides):
    payload = {
        "schema_version": CATALOG_SCHEMA_VERSION,
        "provider": "test_catalog_v1",
        "symbol_resolution": {
            "required_provenance": "external_import",
            "strip_elf_version_suffix": True,
        },
        "functions": [
            {
                "canonical_symbol": "log",
                "parameters": [{"type_class": "float", "width_bits": 64}],
                "return": {"type_class": "float", "width_bits": 64},
                "observation_sensitivity": {"errno": True, "fenv": True},
                "aliases": [
                    {
                        "alias_symbol": "__log_finite",
                        "provenance_requirement": "external_import",
                    }
                ],
            }
        ],
    }
    payload.update(overrides)
    return payload


@pytest.mark.parametrize(
    "mutate",
    [
        pytest.param(lambda p: p.__setitem__("schema_version", 2), id="schema_version"),
        pytest.param(lambda p: p.__setitem__("provider", ""), id="empty_provider"),
        pytest.param(lambda p: p.__setitem__("functions", []), id="empty_functions"),
        pytest.param(lambda p: p.__setitem__("unexpected", 1), id="unexpected_top_key"),
        pytest.param(
            lambda p: p["symbol_resolution"].__setitem__("required_provenance", "name_match"),
            id="unsupported_provenance_requirement",
        ),
        pytest.param(
            lambda p: p["symbol_resolution"].__setitem__("strip_elf_version_suffix", 1),
            id="non_bool_normalization_flag",
        ),
        pytest.param(
            lambda p: p["functions"][0].__setitem__(
                "parameters", [{"type_class": "complex", "width_bits": 64}]
            ),
            id="unsupported_type_class",
        ),
        pytest.param(
            lambda p: p["functions"][0].__setitem__(
                "parameters", [{"type_class": "float", "width_bits": 0}]
            ),
            id="non_positive_width",
        ),
        pytest.param(
            lambda p: p["functions"][0].__setitem__("parameters", []),
            id="empty_parameters",
        ),
        pytest.param(
            lambda p: p["functions"][0].__setitem__(
                "observation_sensitivity", {"errno": True}
            ),
            id="incomplete_observation_sensitivity",
        ),
        pytest.param(
            lambda p: p["functions"].append(copy.deepcopy(p["functions"][0])),
            id="duplicate_canonical_symbol",
        ),
        pytest.param(
            lambda p: p["functions"][0]["aliases"].append(
                {"alias_symbol": "log", "provenance_requirement": "external_import"}
            ),
            id="alias_collides_with_canonical",
        ),
        pytest.param(
            lambda p: p["functions"][0]["aliases"].append(
                {"alias_symbol": "__log_finite", "provenance_requirement": "external_import"}
            ),
            id="duplicate_alias",
        ),
        pytest.param(
            lambda p: p["functions"][0]["aliases"].__setitem__(
                0, {"alias_symbol": "__log_finite", "provenance_requirement": "name_match"}
            ),
            id="unsupported_alias_provenance_requirement",
        ),
    ],
)
def test_catalog_schema_violations_are_rejected(mutate):
    payload = _catalog_payload()
    mutate(payload)
    with pytest.raises(PureFunctionCatalogError):
        parse_pure_function_catalog(payload)


# --- canonical / alias resolution -----------------------------------------


def test_direct_external_canonical_symbol_is_accepted():
    resolution = _resolve(_external_function("log"))
    assert resolution.accepted
    assert resolution.canonical_symbol == "log"
    assert resolution.provenance_kind == PROVENANCE_DIRECT_EXTERNAL
    assert resolution.candidate.canonical_symbol == "log"
    assert resolution.candidate.provider == "c99_math_catalog_v1"


def test_external_thunk_is_accepted_with_thunk_provenance():
    resolution = _resolve(_thunk_to_external("log"))
    assert resolution.accepted
    assert resolution.provenance_kind == PROVENANCE_THUNK_TO_EXTERNAL
    assert resolution.candidate.canonical_symbol == "log"


def test_alias_resolves_to_its_canonical_symbol():
    resolution = _resolve(_thunk_to_external("__log_finite"))
    assert resolution.accepted
    assert resolution.canonical_symbol == "log"
    # signature key は canonical のもの: alias でも同じ key になる。
    canonical = _resolve(_thunk_to_external("log"))
    assert resolution.candidate.signature_key == canonical.candidate.signature_key


def test_original_imported_name_resolves_the_alias_when_the_display_name_does_not():
    external = _external_function(
        "FUN_00101234",
        external_location=_ExternalLocation(original_imported_name="__log_finite"),
    )
    resolution = _resolve(external)
    assert resolution.accepted
    assert resolution.canonical_symbol == "log"


def test_elf_version_suffix_is_stripped_by_the_catalog_rule():
    external = _external_function(
        "log",
        external_location=_ExternalLocation(original_imported_name="log@@GLIBC_2.29"),
    )
    assert _resolve(external).canonical_symbol == "log"


def test_symbol_outside_the_catalog_is_not_a_candidate():
    resolution = _resolve(_external_function("client_specific_helper"))
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_SYMBOL_NOT_IN_CATALOG


def test_underscore_prefixed_user_symbol_is_not_canonicalized_by_name_stripping():
    """``_log`` は ``log`` ではない。名前の切り貼りで canonical にしない。"""
    resolution = _resolve(_external_function("_log"))
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_SYMBOL_NOT_IN_CATALOG


def test_names_resolving_to_different_canonical_symbols_are_ambiguous():
    external = _external_function(
        "exp",
        external_location=_ExternalLocation(original_imported_name="log"),
    )
    resolution = _resolve(external)
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_SYMBOL_RESOLUTION_AMBIGUOUS


# --- provenance ------------------------------------------------------------


def test_user_defined_same_name_function_is_not_a_candidate():
    """binary 内に body を持つ ``log`` は catalog の ``log`` ではない。"""
    resolution = _resolve(_Function("log", is_external=False, is_thunk=False))
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_PROVENANCE_NOT_EXTERNAL


def test_thunk_to_internal_function_is_not_a_candidate():
    internal = _Function("log", is_external=False, is_thunk=False)
    wrapper = _Function("log", is_thunk=True, thunked=internal)
    resolution = _resolve(wrapper)
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_PROVENANCE_NOT_EXTERNAL


def test_unresolvable_classification_is_not_a_candidate():
    resolution = _resolve(_OpaqueCallee())
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_PROVENANCE_UNAVAILABLE


def test_external_without_library_evidence_is_not_a_candidate():
    external = _Function("log", is_external=True, external_location=None)
    resolution = _resolve(external)
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_PROVENANCE_UNAVAILABLE


def test_thunk_whose_target_cannot_be_obtained_is_not_a_candidate():
    class _UnresolvableThunk(_Function):
        def getThunkedFunction(self, _follow=True):
            raise RuntimeError("thunk target unavailable")

    wrapper = _UnresolvableThunk("log", is_thunk=True)
    resolution = _resolve(wrapper)
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_PROVENANCE_UNAVAILABLE


def test_non_bool_is_external_is_not_proven_external():
    """``isExternal()`` が ``"true"`` 等の非 bool でも external 扱いしない。

    ``CallTargetRef`` は API 戻り値を ``bool(...)`` 化するので、この truthy 値を
    そのまま authority にすると proven external になってしまう。candidate 分類は
    effect lane と同じ exact-bool classifier を通す。
    """
    external = _Function("log", external_location=_ExternalLocation())
    external._is_external = "true"
    target_ref = _target(external)
    # 弱い projection では external に見えてしまうことを明示しておく。
    assert target_ref.is_external is True

    resolution = resolve_call_model_candidate(target_ref, policy=NO_OBSERVATION)
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_PROVENANCE_UNAVAILABLE


def test_non_bool_is_thunk_is_not_followed():
    wrapper = _thunk_to_external("log")
    wrapper._is_thunk = 1
    target_ref = _target(wrapper)
    assert target_ref.is_thunk is True

    resolution = resolve_call_model_candidate(target_ref, policy=NO_OBSERVATION)
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_PROVENANCE_UNAVAILABLE


def test_non_bool_is_external_on_the_thunk_target_is_not_proven_external():
    wrapper = _thunk_to_external("log")
    wrapper._thunked._is_external = "true"
    target_ref = _target(wrapper)
    assert target_ref.thunked_is_external is True

    resolution = resolve_call_model_candidate(target_ref, policy=NO_OBSERVATION)
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_PROVENANCE_UNAVAILABLE


def test_cyclic_thunk_chain_is_not_a_candidate():
    first = _Function("log", is_thunk=True)
    second = _Function("log", is_thunk=True, thunked=first)
    first._thunked = second
    resolution = _resolve(first)
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_PROVENANCE_UNAVAILABLE


def test_thunk_chain_longer_than_the_bound_is_not_a_candidate():
    external = _external_function("log")
    current = external
    for _ in range(external_call_models.MAX_THUNK_CHAIN_LENGTH + 2):
        current = _Function("log", is_thunk=True, thunked=current)
    resolution = _resolve(current)
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_PROVENANCE_UNAVAILABLE


def test_thunk_chain_within_the_bound_still_resolves_to_the_external_signature():
    external = _external_function("log")
    current = external
    for _ in range(3):
        current = _Function("FUN_00100000", is_thunk=True, thunked=current)
    resolution = _resolve(current)
    assert resolution.accepted
    assert resolution.canonical_symbol == "log"
    assert resolution.provenance_kind == PROVENANCE_THUNK_TO_EXTERNAL


def test_candidate_external_classification_is_a_subset_of_the_effect_lane_verdict():
    """external 判定は effect lane と同じ ``classify_callee_chain()`` を使う。

    その上で B1 は library / symbol / catalog / signature / observation の条件を
    **追加**するので、最終的な candidate 集合は effect lane の confirmed-external
    集合の **部分集合** になる。両者が一致するとは主張しない。
    """
    cases = [
        _external_function("log"),
        _thunk_to_external("log"),
        _Function("log", is_external=False, is_thunk=False),
        _Function("log", is_thunk=True),
        _OpaqueCallee(),
    ]
    non_bool = _Function("log", external_location=_ExternalLocation())
    non_bool._is_external = "true"
    cases.append(non_bool)
    # external location を持たない external: effect lane は external と確定するが、
    # library evidence が無いので candidate にはならない（部分集合である例）。
    cases.append(_Function("log", is_external=True, external_location=None))
    for function_obj in cases:
        resolution = external_call_models.resolve_effect_callee(
            function_obj, ExternalCallEffectPolicy()
        )
        effect_lane_external = external_call_models.resolution_is_confirmed_external(
            resolution
        )
        provenance, _reason = catalog_module.external_symbol_provenance(_target(function_obj))
        if provenance is not None:
            assert effect_lane_external, function_obj.getName()
        candidate = resolve_call_model_candidate(
            _target(function_obj), policy=NO_OBSERVATION
        ).candidate
        if candidate is not None:
            assert effect_lane_external, function_obj.getName()


def test_candidate_set_is_strictly_smaller_than_the_confirmed_external_set():
    """confirmed external でも B1 固有条件を満たさなければ candidate にならない。"""
    library_less = _Function("log", is_external=True, external_location=None)
    non_catalog = _external_function("client_specific_helper")
    for function_obj in (library_less, non_catalog):
        resolution = external_call_models.resolve_effect_callee(
            function_obj, ExternalCallEffectPolicy()
        )
        assert external_call_models.resolution_is_confirmed_external(resolution)
        assert not _resolve(function_obj).accepted


def test_unknown_call_target_is_not_a_candidate():
    resolution = resolve_call_model_candidate(
        CallTargetRef.unknown("log"), policy=NO_OBSERVATION
    )
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_TARGET_NOT_FUNCTION


def test_alias_requires_provenance_beyond_the_name():
    """alias 規則は provenance 要件を満たすときにだけ適用される。"""
    catalog = load_pure_function_catalog(reload=True)
    canonical, reason = catalog.resolve("__log_finite", provenance_kind=None)
    assert canonical is None
    assert reason == catalog_module.REJECT_PROVENANCE_NOT_EXTERNAL

    payload = _catalog_payload()
    payload["functions"][0]["aliases"][0]["provenance_requirement"] = "external_import"
    restricted = parse_pure_function_catalog(payload)
    canonical, reason = restricted.resolve(
        "__log_finite", provenance_kind="internal_definition"
    )
    assert canonical is None
    assert reason == catalog_module.REJECT_PROVENANCE_NOT_EXTERNAL


def test_alias_rule_with_an_unsatisfiable_requirement_rejects_the_alias():
    catalog = load_pure_function_catalog(reload=True)
    rule = catalog.alias_rules["__log_finite"]
    unsatisfiable = catalog_module.CatalogAliasRule(
        alias_symbol=rule.alias_symbol,
        canonical_symbol=rule.canonical_symbol,
        provenance_requirement="signed_provider_attestation",
    )
    patched = catalog_module.PureFunctionCatalog(
        schema_version=catalog.schema_version,
        provider=catalog.provider,
        required_provenance=catalog.required_provenance,
        strip_elf_version_suffix=catalog.strip_elf_version_suffix,
        entries=catalog.entries,
        alias_rules=dict(catalog.alias_rules, __log_finite=unsatisfiable),
    )
    resolution = resolve_call_model_candidate(
        _target(_thunk_to_external("__log_finite")),
        policy=NO_OBSERVATION,
        catalog=patched,
    )
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_ALIAS_PROVENANCE_INSUFFICIENT


# --- signature validation --------------------------------------------------


def test_signature_arity_mismatch_is_rejected():
    resolution = _resolve(_thunk_to_external("log", parameter_types=(DOUBLE, DOUBLE)))
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_SIGNATURE_ARITY_MISMATCH


def test_argument_width_mismatch_is_rejected():
    resolution = _resolve(_thunk_to_external("log", parameter_types=(FLOAT,)))
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_ARGUMENT_WIDTH_MISMATCH


def test_argument_type_class_mismatch_is_rejected():
    resolution = _resolve(_thunk_to_external("log", parameter_types=(LONGLONG,)))
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_ARGUMENT_TYPE_MISMATCH


def test_return_width_mismatch_is_rejected():
    resolution = _resolve(_thunk_to_external("log", return_type=FLOAT))
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_RETURN_WIDTH_MISMATCH


def test_return_type_class_mismatch_is_rejected():
    resolution = _resolve(_thunk_to_external("log", return_type=LONGLONG))
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_RETURN_TYPE_MISMATCH


def test_pointer_argument_is_rejected_as_unusable_signature():
    resolution = _resolve(_thunk_to_external("log", parameter_types=(DOUBLE_PTR,)))
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_SIGNATURE_UNAVAILABLE


def test_varargs_signature_is_rejected():
    resolution = _resolve(_thunk_to_external("log", var_args=True))
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_SIGNATURE_VARARGS


def test_unreadable_signature_is_rejected():
    class _NoSignature(_Function):
        def hasVarArgs(self):
            raise RuntimeError("signature unavailable")

    external = _NoSignature("log", is_external=True, external_location=_ExternalLocation())
    resolution = _resolve(external)
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_SIGNATURE_UNAVAILABLE


def test_integral_signature_entry_is_accepted_with_exact_widths():
    """``ilogb`` は float→int32。型クラスと幅の両方が一致して初めて成立する。"""
    accepted = _resolve(_thunk_to_external("ilogb", return_type=INT))
    assert accepted.accepted
    rejected = _resolve(_thunk_to_external("ilogb", return_type=LONGLONG))
    assert rejected.reject_reason == catalog_module.REJECT_RETURN_WIDTH_MISMATCH


# --- observation boundary --------------------------------------------------


def test_errno_observation_rejects_an_errno_sensitive_candidate():
    resolution = _resolve(
        _thunk_to_external("log"), policy=ExternalCallEffectPolicy(observe_errno=True)
    )
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_ERRNO_OBSERVED


def test_fenv_observation_rejects_an_fenv_sensitive_candidate():
    resolution = _resolve(
        _thunk_to_external("log"), policy=ExternalCallEffectPolicy(observe_fenv=True)
    )
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_FENV_OBSERVED


@pytest.mark.parametrize("symbol", ["log", "fabs"])
@pytest.mark.parametrize(
    "policy,expected",
    [
        (ExternalCallEffectPolicy(observe_errno=True), catalog_module.REJECT_ERRNO_OBSERVED),
        (ExternalCallEffectPolicy(observe_fenv=True), catalog_module.REJECT_FENV_OBSERVED),
        (
            ExternalCallEffectPolicy(observe_errno=True, observe_fenv=True),
            catalog_module.REJECT_ERRNO_OBSERVED,
        ),
    ],
)
def test_any_observation_mode_rejects_every_candidate(symbol, policy, expected):
    """B1 の条件は「errno / fenv を observation 対象にしていないこと」。

    catalog の ``observation_sensitivity`` は metadata として残すが、gate を緩める
    根拠にはしない。``fabs`` のように感度が無いとされる関数でも観測中は不成立。
    """
    resolution = _resolve(_thunk_to_external(symbol), policy=policy)
    assert not resolution.accepted
    assert resolution.reject_reason == expected


@pytest.mark.parametrize("symbol", ["log", "fabs"])
def test_candidate_is_available_only_when_neither_channel_is_observed(symbol):
    resolution = _resolve(
        _thunk_to_external(symbol),
        policy=ExternalCallEffectPolicy(observe_errno=False, observe_fenv=False),
    )
    assert resolution.accepted
    assert resolution.canonical_symbol == symbol


def test_observation_sensitivity_remains_catalog_metadata():
    """gate では使わないが、schema からは落とさない（B2 以降で使う情報）。"""
    catalog = load_pure_function_catalog(reload=True)
    assert catalog.entries["log"].observation_sensitivity == ("errno", "fenv")
    assert catalog.entries["fabs"].observation_sensitivity == ()


def test_missing_observation_policy_fails_closed():
    resolution = _resolve(_thunk_to_external("log"), policy=None)
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_OBSERVATION_POLICY_UNAVAILABLE


def test_unusable_catalog_fails_closed_instead_of_raising(monkeypatch):
    def _explode(**_kwargs):
        raise PureFunctionCatalogError("catalog is broken")

    monkeypatch.setattr(catalog_module, "load_pure_function_catalog", _explode)
    resolution = _resolve(_thunk_to_external("log"))
    assert not resolution.accepted
    assert resolution.reject_reason == catalog_module.REJECT_CATALOG_UNAVAILABLE


# --- candidate metadata ----------------------------------------------------


def test_candidate_metadata_is_deterministic():
    first = _resolve(_thunk_to_external("log")).candidate
    second = _resolve(_thunk_to_external("log")).candidate
    assert first == second
    assert first.candidate_key == second.candidate_key
    assert first.to_dict() == second.to_dict()
    assert first.candidate_key[0] == "call_model_candidate"
    for field_name in ("provider", "canonical_symbol", "signature_key", "provenance_key"):
        assert getattr(first, field_name)


def test_candidate_key_cannot_be_supplied_out_of_band():
    candidate = _resolve(_thunk_to_external("log")).candidate
    with pytest.raises(ValueError):
        CallModelCandidateRef(
            provider=candidate.provider,
            canonical_symbol=candidate.canonical_symbol,
            signature_key=candidate.signature_key,
            provenance_key=candidate.provenance_key,
            candidate_key=("call_model_candidate", "forged"),
        )
    # 導出値と一致する場合は受け入れる（永続化からの復元を壊さない）。
    restored = CallModelCandidateRef(
        provider=candidate.provider,
        canonical_symbol=candidate.canonical_symbol,
        signature_key=candidate.signature_key,
        provenance_key=candidate.provenance_key,
        candidate_key=candidate.candidate_key,
    )
    assert restored == candidate


def test_candidate_carries_no_purity_or_effect_claim():
    candidate = _resolve(_thunk_to_external("log")).candidate
    payload = json.dumps(candidate.to_dict())
    for forbidden in ("pure", "no_write", "effect_class", "assumption"):
        assert forbidden not in payload


def test_distinct_symbols_get_distinct_candidate_keys():
    log_candidate = _resolve(_thunk_to_external("log")).candidate
    exp_candidate = _resolve(_thunk_to_external("exp")).candidate
    assert log_candidate.candidate_key != exp_candidate.candidate_key


# --- effect_class must not move -------------------------------------------


def test_effect_class_is_unchanged_when_a_candidate_is_attached():
    external = _thunk_to_external("log")
    target_ref = _target(external)
    candidate = _resolve(external).candidate
    assert candidate is not None

    without = DeferredCallInfo(target_ref=target_ref, sequence=0)
    with_candidate = DeferredCallInfo(
        target_ref=target_ref, sequence=0, call_model_candidate=candidate
    )
    assert without.effect_class == "unknown_effect"
    assert with_candidate.effect_class == without.effect_class
    assert with_candidate.call_model_candidate is candidate


def test_sqrt_is_a_catalog_candidate_and_no_longer_a_pure_return_special_case():
    """PR-20-B3 の cutover 後、sqrt の値意味は catalog 候補としてだけ現れる。

    B1 の candidate は立つが、``effect_class`` を名前で ``pure_return`` へ
    上げる旧特例は無い（仮定は conditional lane が明示的に負う）。
    """
    external = _thunk_to_external("sqrt")
    target_ref = _target(external)
    candidate = _resolve(external).candidate
    assert candidate is not None and candidate.canonical_symbol == "sqrt"
    info = DeferredCallInfo(
        target_ref=target_ref, sequence=0, call_model_candidate=candidate
    )
    assert info.effect_class == "unknown_effect"


def test_candidate_survives_clone_and_stays_out_of_the_correspondence_identity():
    external = _thunk_to_external("log")
    target_ref = _target(external)
    candidate = _resolve(external).candidate
    with_candidate = DeferredCallInfo(
        target_ref=target_ref, sequence=0, call_model_candidate=candidate
    )
    without = DeferredCallInfo(target_ref=target_ref, sequence=0)

    assert with_candidate.clone().call_model_candidate == candidate
    # candidate は判定に効かない metadata なので identity / match evidence を動かさない。
    assert with_candidate.identity_key() == without.identity_key()
    assert with_candidate.match_evidence == without.match_evidence


def test_candidate_only_appears_in_to_dict_when_present():
    external = _thunk_to_external("log")
    target_ref = _target(external)
    without = DeferredCallInfo(target_ref=target_ref, sequence=0).to_dict()
    assert "call_model_candidate" not in without
    with_candidate = DeferredCallInfo(
        target_ref=target_ref,
        sequence=0,
        call_model_candidate=_resolve(external).candidate,
    ).to_dict()
    assert with_candidate["call_model_candidate"]["canonical_symbol"] == "log"
    assert set(without) == set(with_candidate) - {"call_model_candidate"}


def test_deferred_call_info_rejects_a_foreign_candidate_object():
    with pytest.raises(TypeError):
        DeferredCallInfo(
            target_ref=_target(_thunk_to_external("log")),
            sequence=0,
            call_model_candidate={"canonical_symbol": "log"},
        )


# --- ownership -------------------------------------------------------------


def test_core_call_model_dto_does_not_depend_on_the_analysis_catalog():
    """``core`` は DTO の形だけを持ち、catalog lookup を持たない。"""
    source = Path(catalog_module.__file__).resolve()
    core_module = source.parents[2] / "core" / "runtime_refs" / "call_models.py"
    tree = ast.parse(core_module.read_text(encoding="utf-8"))
    imported = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imported.add(node.module)
    assert not [name for name in imported if ".analysis" in name or ".proof" in name]


def test_importing_the_core_call_model_dto_does_not_load_the_catalog():
    """core の DTO を import しても catalog module は読み込まれない。"""
    repo_root = Path(catalog_module.__file__).resolve().parents[4]
    probe = (
        "import sys;"
        "import scripts.function_tracer_pcode.core.runtime_refs.call_models as m;"
        "loaded=[n for n in sys.modules"
        " if 'pure_function_catalog' in n or n.startswith('scripts.function_tracer_pcode.analysis')];"
        "print(sorted(loaded))"
    )
    completed = subprocess.run(
        [sys.executable, "-B", "-c", probe],
        cwd=str(repo_root),
        capture_output=True,
        text=True,
        check=True,
    )
    assert completed.stdout.strip() == "[]", completed.stdout
