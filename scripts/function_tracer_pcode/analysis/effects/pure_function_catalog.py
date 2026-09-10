# -*- coding: utf-8 -*-
"""C99 math catalog and decision-neutral call-model candidate classification.

Issue #20 PR-B1。external call が explicit-assumption model の **候補になり得るか**
を、object-derived evidence だけから分類する。

この module が決めること:

* catalog schema（canonical symbol / 引数型・幅 / 戻り型・幅 / alias 解決規則 /
  errno・fenv 感度）の読み込みと検証
* alias から canonical symbol への解決（catalog 規則 + provenance evidence）
* Ghidra 側 signature と catalog signature の一致検証
* 上記がすべて成立したときだけ ``CallModelCandidateRef`` を作ること

callee が external かどうかの判定は **この module では行わない**。
``external_call_models.classify_callee_chain``（effect lane と同一の exact-bool +
thunk chain fail-closed classifier）に委ね、candidate 分類が独自の弱い判定器を
持たないようにする。``CallTargetRef.is_external`` / ``is_thunk`` は API 戻り値を
``bool(...)`` 化した projection なので、``"true"`` のような非 bool を proven
external として通し得る。authority にしない。

この module が決め **ない** こと:

* callee が pure かどうか、メモリを書くかどうか
* ``DeferredCallInfo.effect_class``（候補が付いても変えない）
* 左右の callsite が対応するかどうか

candidate は「仮定を置けば model 化できるかもしれない」という分類にすぎず、
pure / no-write の証拠として使ってはならない。仮定の下で意味を与えるのは proof
層の conditional view（PR-20-B2 以降）であり、そこでは ``AssumptionPremise`` が
明示的に付随する。``analysis`` 層は assumption を所有しない。

fail closed の原則: 名前が一致するだけ、provenance が不明（missing API / 例外 /
non-bool / thunk 解決不能 / 循環 / chain 上限超過）、alias が曖昧、signature が
取れない・食い違う、errno / fenv を観測中 — いずれも candidate **不成立**
（``None`` と reject reason）を返す。

errno / fenv は **関数ごとの感度で緩めない**。``observe_errno or observe_fenv``
なら catalog を引くまでもなく不成立にする（正本 v4 §4.3.4 の B1 条件）。

catalog scope（B1 で意図的に載せていないもの）:

* ``long double`` 変種（``*l``）と ``long`` を取る/返す関数（``lrint`` /
  ``lround`` / ``scalbln``）。これらの幅は ABI 依存で、B1 の schema は幅を
  厳密一致で検証するため、固定値を書くと嘘になる。
* pointer 引数を取る関数（``frexp`` / ``modf`` / ``remquo`` / ``nan``）。
  引数経由の書き込み/読み出しを B1 の最小 schema では表現できない。
* ``memcpy`` / ``memset`` 等の非 math 関数（Issue #20 の scope 外）。

これらは「載っていない → candidate 不成立」なので fail closed 側に倒れる。
"""

from __future__ import annotations

import json
import threading
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.analysis.effects.external_call_models import (
    CALLEE_CHAIN_EXTERNAL,
    CALLEE_CHAIN_INTERNAL,
    classify_callee_chain,
)
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.runtime_refs.call_models import (
    CallModelCandidateRef,
)
from scripts.function_tracer_pcode.core.signature import (
    get_declared_type_size_bits,
    is_floating_data_type,
    is_integral_data_type,
    is_pointer_data_type,
    is_undefined_data_type,
    is_void_data_type,
)

#: この module が理解する catalog schema 版。JSON 側と一致しなければ読み込まない。
CATALOG_SCHEMA_VERSION = 1

CATALOG_FILENAME = "pure_functions.json"

#: 対応している型クラス（catalog の ``type_class`` に書ける値）。
SUPPORTED_TYPE_CLASSES = ("float", "int")

#: 対応している provenance 要件。alias 解決と canonical 解決の両方で使う。
PROVENANCE_REQUIREMENT_EXTERNAL_IMPORT = "external_import"
SUPPORTED_PROVENANCE_REQUIREMENTS = (PROVENANCE_REQUIREMENT_EXTERNAL_IMPORT,)

#: 対応している observation channel。
OBSERVATION_CHANNELS = ("errno", "fenv")

#: object-derived provenance の種別。どちらも ``external_import`` を満たす。
PROVENANCE_DIRECT_EXTERNAL = "direct_external"
PROVENANCE_THUNK_TO_EXTERNAL = "thunk_to_external"

_PROVENANCE_KINDS_SATISFYING_EXTERNAL_IMPORT = frozenset(
    {PROVENANCE_DIRECT_EXTERNAL, PROVENANCE_THUNK_TO_EXTERNAL}
)

#: ``signature_key`` の schema tag（catalog signature の同一性判定に使う）。
SIGNATURE_KEY_KIND = "c99_math_signature_v1"

#: ``provenance_key`` の schema tag。
PROVENANCE_KEY_KIND = "external_import_provenance_v1"

# --- reject reasons -------------------------------------------------------
# 診断専用の識別子。UNKNOWN reason registry には登録しない（B1 は decision
# neutral であり、candidate の有無はどの判定にも影響しない）。
REJECT_TARGET_NOT_FUNCTION = "call_model_target_not_function"
REJECT_PROVENANCE_UNAVAILABLE = "call_model_provenance_unavailable"
REJECT_PROVENANCE_NOT_EXTERNAL = "call_model_provenance_not_external"
REJECT_SYMBOL_UNAVAILABLE = "call_model_symbol_unavailable"
REJECT_SYMBOL_NOT_IN_CATALOG = "call_model_symbol_not_in_catalog"
REJECT_SYMBOL_RESOLUTION_AMBIGUOUS = "call_model_symbol_resolution_ambiguous"
REJECT_ALIAS_PROVENANCE_INSUFFICIENT = "call_model_alias_provenance_insufficient"
REJECT_SIGNATURE_UNAVAILABLE = "call_model_signature_unavailable"
REJECT_SIGNATURE_VARARGS = "call_model_signature_varargs"
REJECT_SIGNATURE_ARITY_MISMATCH = "call_model_signature_arity_mismatch"
REJECT_ARGUMENT_TYPE_MISMATCH = "call_model_argument_type_mismatch"
REJECT_ARGUMENT_WIDTH_MISMATCH = "call_model_argument_width_mismatch"
REJECT_RETURN_TYPE_MISMATCH = "call_model_return_type_mismatch"
REJECT_RETURN_WIDTH_MISMATCH = "call_model_return_width_mismatch"
REJECT_ERRNO_OBSERVED = "call_model_errno_observed"
REJECT_FENV_OBSERVED = "call_model_fenv_observed"
REJECT_OBSERVATION_POLICY_UNAVAILABLE = "call_model_observation_policy_unavailable"
REJECT_CATALOG_UNAVAILABLE = "call_model_catalog_unavailable"


class PureFunctionCatalogError(ValueError):
    """catalog schema 違反。読み込み時に必ず失敗させる（黙って無視しない）。"""


# --- catalog model --------------------------------------------------------


@dataclass(frozen=True)
class CatalogTypeSpec:
    """catalog が要求する 1 個の型（型クラスと厳密なビット幅）。"""

    type_class: str
    width_bits: int

    def key(self) -> Tuple[Any, ...]:
        return (self.type_class, self.width_bits)


@dataclass(frozen=True)
class CatalogAliasRule:
    """alias symbol を canonical symbol へ解決する規則。

    名前が一致するだけでは解決しない。``provenance_requirement`` が示す
    object-derived evidence が揃っている場合にだけ適用される。
    """

    alias_symbol: str
    canonical_symbol: str
    provenance_requirement: str


@dataclass(frozen=True)
class CatalogEntry:
    """1 個の canonical symbol の catalog 定義。"""

    canonical_symbol: str
    parameters: Tuple[CatalogTypeSpec, ...]
    return_spec: CatalogTypeSpec
    observation_sensitivity: Tuple[str, ...]

    def signature_key(self) -> Tuple[Any, ...]:
        return (
            SIGNATURE_KEY_KIND,
            self.canonical_symbol,
            tuple(spec.key() for spec in self.parameters),
            self.return_spec.key(),
        )


@dataclass(frozen=True)
class PureFunctionCatalog:
    """検証済み catalog。lookup は canonical と alias の両方を引く。"""

    schema_version: int
    provider: str
    required_provenance: str
    strip_elf_version_suffix: bool
    entries: Mapping[str, CatalogEntry]
    alias_rules: Mapping[str, CatalogAliasRule]

    def normalize_symbol(self, symbol: Optional[str]) -> Optional[str]:
        """object-derived symbol 名を catalog 照合用に正規化する。

        規則として書かれている正規化しか行わない。underscore を剥がす、
        小文字化する、部分一致を取る等は **しない**（``_log`` が ``log`` に
        なってしまう）。
        """

        if not isinstance(symbol, str):
            return None
        text = symbol.strip()
        if not text:
            return None
        if self.strip_elf_version_suffix and "@" in text:
            text = text.split("@", 1)[0].strip()
        return text or None

    def resolve(
        self,
        symbol: Optional[str],
        *,
        provenance_kind: Optional[str],
    ) -> Tuple[Optional[str], Optional[str]]:
        """``symbol`` を canonical symbol へ解決する。

        戻り値は ``(canonical_symbol, reject_reason)``。canonical が返る場合
        reject_reason は ``None``。catalog に無い場合は両方 ``None``（呼び出し側
        が「この名前では引けなかった」と扱う）。
        """

        normalized = self.normalize_symbol(symbol)
        if normalized is None:
            return None, None
        if normalized in self.entries:
            if not _provenance_satisfies(self.required_provenance, provenance_kind):
                return None, REJECT_PROVENANCE_NOT_EXTERNAL
            return normalized, None
        rule = self.alias_rules.get(normalized)
        if rule is None:
            return None, None
        if not _provenance_satisfies(self.required_provenance, provenance_kind):
            return None, REJECT_PROVENANCE_NOT_EXTERNAL
        if not _provenance_satisfies(rule.provenance_requirement, provenance_kind):
            return None, REJECT_ALIAS_PROVENANCE_INSUFFICIENT
        return rule.canonical_symbol, None


def _provenance_satisfies(requirement: str, provenance_kind: Optional[str]) -> bool:
    if requirement != PROVENANCE_REQUIREMENT_EXTERNAL_IMPORT:
        # schema 検証で弾いているはずだが、未知の要件は満たせないものとして扱う。
        return False
    return provenance_kind in _PROVENANCE_KINDS_SATISFYING_EXTERNAL_IMPORT


# --- catalog loading ------------------------------------------------------


def catalog_path() -> Path:
    return Path(__file__).resolve().parent / CATALOG_FILENAME


def _require_mapping(value: Any, what: str) -> Mapping[str, Any]:
    if not isinstance(value, dict):
        raise PureFunctionCatalogError(f"{what} must be an object")
    return value


def _require_exact_bool(value: Any, what: str) -> bool:
    if type(value) is not bool:
        raise PureFunctionCatalogError(f"{what} must be an exact boolean")
    return value


def _require_positive_int(value: Any, what: str) -> int:
    if type(value) is not int or isinstance(value, bool) or value <= 0:
        raise PureFunctionCatalogError(f"{what} must be a positive integer")
    return value


def _require_symbol(value: Any, what: str) -> str:
    if not isinstance(value, str):
        raise PureFunctionCatalogError(f"{what} must be a string")
    text = value.strip()
    if not text or text != value:
        raise PureFunctionCatalogError(
            f"{what} must be a non-empty symbol written without surrounding whitespace"
        )
    if any(character.isspace() for character in text):
        raise PureFunctionCatalogError(f"{what} must not contain whitespace")
    return text


def _parse_type_spec(payload: Any, what: str) -> CatalogTypeSpec:
    mapping = _require_mapping(payload, what)
    unexpected = set(mapping) - {"type_class", "width_bits"}
    if unexpected:
        raise PureFunctionCatalogError(f"{what} has unexpected keys: {sorted(unexpected)}")
    type_class = mapping.get("type_class")
    if type_class not in SUPPORTED_TYPE_CLASSES:
        raise PureFunctionCatalogError(
            f"{what} type_class must be one of {list(SUPPORTED_TYPE_CLASSES)}"
        )
    width_bits = _require_positive_int(mapping.get("width_bits"), f"{what} width_bits")
    return CatalogTypeSpec(type_class=type_class, width_bits=width_bits)


def parse_pure_function_catalog(payload: Any) -> PureFunctionCatalog:
    """catalog payload を検証して読み込む。違反は必ず例外にする。"""

    document = _require_mapping(payload, "catalog")
    unexpected = set(document) - {
        "schema_version",
        "provider",
        "symbol_resolution",
        "functions",
    }
    if unexpected:
        raise PureFunctionCatalogError(f"catalog has unexpected keys: {sorted(unexpected)}")

    schema_version = document.get("schema_version")
    if schema_version != CATALOG_SCHEMA_VERSION:
        raise PureFunctionCatalogError(
            f"catalog schema_version must be {CATALOG_SCHEMA_VERSION}"
        )
    provider = _require_symbol(document.get("provider"), "catalog provider")

    resolution = _require_mapping(
        document.get("symbol_resolution"), "catalog symbol_resolution"
    )
    unexpected = set(resolution) - {"required_provenance", "strip_elf_version_suffix"}
    if unexpected:
        raise PureFunctionCatalogError(
            f"catalog symbol_resolution has unexpected keys: {sorted(unexpected)}"
        )
    required_provenance = resolution.get("required_provenance")
    if required_provenance not in SUPPORTED_PROVENANCE_REQUIREMENTS:
        raise PureFunctionCatalogError(
            "catalog symbol_resolution.required_provenance must be one of "
            f"{list(SUPPORTED_PROVENANCE_REQUIREMENTS)}"
        )
    strip_version = _require_exact_bool(
        resolution.get("strip_elf_version_suffix"),
        "catalog symbol_resolution.strip_elf_version_suffix",
    )

    functions = document.get("functions")
    if not isinstance(functions, list) or not functions:
        raise PureFunctionCatalogError("catalog functions must be a non-empty list")

    entries: Dict[str, CatalogEntry] = {}
    alias_rules: Dict[str, CatalogAliasRule] = {}
    for index, raw_entry in enumerate(functions):
        what = f"catalog functions[{index}]"
        entry_payload = _require_mapping(raw_entry, what)
        unexpected = set(entry_payload) - {
            "canonical_symbol",
            "parameters",
            "return",
            "observation_sensitivity",
            "aliases",
        }
        if unexpected:
            raise PureFunctionCatalogError(f"{what} has unexpected keys: {sorted(unexpected)}")
        canonical = _require_symbol(
            entry_payload.get("canonical_symbol"), f"{what} canonical_symbol"
        )
        if canonical in entries:
            raise PureFunctionCatalogError(f"{what} duplicates canonical symbol {canonical!r}")

        raw_parameters = entry_payload.get("parameters")
        if not isinstance(raw_parameters, list):
            raise PureFunctionCatalogError(f"{what} parameters must be a list")
        parameters = tuple(
            _parse_type_spec(raw, f"{what} parameters[{position}]")
            for position, raw in enumerate(raw_parameters)
        )
        if not parameters:
            raise PureFunctionCatalogError(f"{what} parameters must be non-empty")
        return_spec = _parse_type_spec(entry_payload.get("return"), f"{what} return")

        sensitivity_payload = _require_mapping(
            entry_payload.get("observation_sensitivity"),
            f"{what} observation_sensitivity",
        )
        if set(sensitivity_payload) != set(OBSERVATION_CHANNELS):
            raise PureFunctionCatalogError(
                f"{what} observation_sensitivity must declare exactly "
                f"{list(OBSERVATION_CHANNELS)}"
            )
        sensitivity = tuple(
            channel
            for channel in OBSERVATION_CHANNELS
            if _require_exact_bool(
                sensitivity_payload.get(channel),
                f"{what} observation_sensitivity.{channel}",
            )
        )

        entries[canonical] = CatalogEntry(
            canonical_symbol=canonical,
            parameters=parameters,
            return_spec=return_spec,
            observation_sensitivity=sensitivity,
        )

        raw_aliases = entry_payload.get("aliases")
        if not isinstance(raw_aliases, list):
            raise PureFunctionCatalogError(f"{what} aliases must be a list")
        for position, raw_alias in enumerate(raw_aliases):
            alias_what = f"{what} aliases[{position}]"
            alias_payload = _require_mapping(raw_alias, alias_what)
            unexpected = set(alias_payload) - {"alias_symbol", "provenance_requirement"}
            if unexpected:
                raise PureFunctionCatalogError(
                    f"{alias_what} has unexpected keys: {sorted(unexpected)}"
                )
            alias_symbol = _require_symbol(
                alias_payload.get("alias_symbol"), f"{alias_what} alias_symbol"
            )
            requirement = alias_payload.get("provenance_requirement")
            if requirement not in SUPPORTED_PROVENANCE_REQUIREMENTS:
                raise PureFunctionCatalogError(
                    f"{alias_what} provenance_requirement must be one of "
                    f"{list(SUPPORTED_PROVENANCE_REQUIREMENTS)}"
                )
            if alias_symbol in alias_rules:
                raise PureFunctionCatalogError(
                    f"{alias_what} duplicates alias symbol {alias_symbol!r}"
                )
            alias_rules[alias_symbol] = CatalogAliasRule(
                alias_symbol=alias_symbol,
                canonical_symbol=canonical,
                provenance_requirement=requirement,
            )

    collisions = sorted(set(alias_rules) & set(entries))
    if collisions:
        raise PureFunctionCatalogError(
            f"catalog alias symbols collide with canonical symbols: {collisions}"
        )

    return PureFunctionCatalog(
        schema_version=schema_version,
        provider=provider,
        required_provenance=required_provenance,
        strip_elf_version_suffix=strip_version,
        entries=dict(entries),
        alias_rules=dict(alias_rules),
    )


_CATALOG_LOCK = threading.Lock()
_CATALOG_CACHE: Optional[PureFunctionCatalog] = None


def load_pure_function_catalog(*, reload: bool = False) -> PureFunctionCatalog:
    """同梱 catalog を読み込む（プロセス内でキャッシュする）。"""

    global _CATALOG_CACHE
    with _CATALOG_LOCK:
        if _CATALOG_CACHE is None or reload:
            payload = json.loads(catalog_path().read_text(encoding="utf-8"))
            _CATALOG_CACHE = parse_pure_function_catalog(payload)
        return _CATALOG_CACHE


# --- provenance extraction ------------------------------------------------


@dataclass(frozen=True)
class ExternalSymbolProvenance:
    """object-derived な「この callee は external import である」という証拠。"""

    kind: str
    library_name: str
    symbol_names: Tuple[str, ...]
    signature_function: Any = field(default=None, compare=False, hash=False, repr=False)

    def provenance_key(self) -> Tuple[Any, ...]:
        return (
            PROVENANCE_KEY_KIND,
            self.kind,
            self.library_name,
            self.symbol_names,
        )


def _safe_call(owner: Any, method_name: str, *args: Any) -> Any:
    method = getattr(owner, method_name, None)
    if not callable(method):
        return None
    try:
        return method(*args)
    except Exception:  # noqa: BLE001 - 取得失敗は「不明」であって「偽」ではない
        return None


def _optional_symbol_text(value: Any) -> Optional[str]:
    if value is None:
        return None
    try:
        text = str(value).strip()
    except Exception:  # noqa: BLE001
        return None
    return text or None


def _external_symbol_names(function_obj: Any) -> Tuple[str, ...]:
    """external 側の object-derived な symbol 名を順に返す。

    caller 側の呼び名ではなく、external location の original imported name と
    external function 自身の名前を使う。
    """

    names: List[str] = []
    external_location = _safe_call(function_obj, "getExternalLocation")
    if external_location is not None:
        original = _optional_symbol_text(
            _safe_call(external_location, "getOriginalImportedName")
        )
        if original is not None:
            names.append(original)
    own_name = _optional_symbol_text(_safe_call(function_obj, "getName"))
    if own_name is not None:
        names.append(own_name)
    deduplicated: List[str] = []
    for name in names:
        if name not in deduplicated:
            deduplicated.append(name)
    return tuple(deduplicated)


def _external_library_name(function_obj: Any) -> Optional[str]:
    """proven external function から library 名を読む（無ければ ``None``）。"""

    external_location = _safe_call(function_obj, "getExternalLocation")
    if external_location is None:
        return None
    return _optional_symbol_text(_safe_call(external_location, "getLibraryName"))


def external_symbol_provenance(
    target_ref: Any,
) -> Tuple[Optional[ExternalSymbolProvenance], Optional[str]]:
    """call target から external import provenance を取り出す。

    分類は effect lane と **同一の** ``classify_callee_chain``（exact-bool + thunk
    chain の fail-closed 解決）に委ねる。``CallTargetRef`` が持つ ``is_external`` /
    ``is_thunk`` は API 戻り値を ``bool(...)`` 化したものなので、``"true"`` のような
    非 bool を proven external として通し得る。candidate 分類が独自の弱い判定器を
    持たないよう、ここでは使わない。

    thunk の signature / 名前は、chain が **proven external に解決できた場合だけ**
    その終端から読む。循環 / 解決不能 / 上限超過 / non-bool は candidate なし。
    """

    if not isinstance(target_ref, CallTargetRef) or not target_ref.is_function():
        return None, REJECT_TARGET_NOT_FUNCTION
    function_obj = getattr(target_ref, "function_obj", None)
    if function_obj is None:
        return None, REJECT_PROVENANCE_UNAVAILABLE

    classification = classify_callee_chain(function_obj)
    if classification.kind == CALLEE_CHAIN_INTERNAL:
        # binary 内に body を持つ関数。同名の user-defined `log` はここで落ちる。
        return None, REJECT_PROVENANCE_NOT_EXTERNAL
    if classification.kind != CALLEE_CHAIN_EXTERNAL:
        return None, REJECT_PROVENANCE_UNAVAILABLE

    external_function = classification.function
    if external_function is None:
        return None, REJECT_PROVENANCE_UNAVAILABLE
    library = _external_library_name(external_function)
    if library is None:
        return None, REJECT_PROVENANCE_UNAVAILABLE
    kind = (
        PROVENANCE_DIRECT_EXTERNAL
        if external_function is function_obj
        else PROVENANCE_THUNK_TO_EXTERNAL
    )

    symbol_names = _external_symbol_names(external_function)
    if not symbol_names:
        return None, REJECT_SYMBOL_UNAVAILABLE
    return (
        ExternalSymbolProvenance(
            kind=kind,
            library_name=library,
            symbol_names=symbol_names,
            signature_function=external_function,
        ),
        None,
    )


# --- signature validation -------------------------------------------------


def _declared_type_class(data_type: Any) -> Optional[str]:
    """宣言型の型クラスを object から判定する。名前は使わない。"""

    if data_type is None:
        return None
    try:
        if is_void_data_type(data_type) or is_undefined_data_type(data_type):
            return None
        if is_pointer_data_type(data_type):
            return None
        if is_floating_data_type(data_type):
            return "float"
        if is_integral_data_type(data_type):
            return "int"
    except Exception:  # noqa: BLE001
        return None
    return None


def _declared_width_bits(data_type: Any) -> Optional[int]:
    if data_type is None:
        return None
    try:
        width = get_declared_type_size_bits(data_type)
    except Exception:  # noqa: BLE001
        return None
    if type(width) is not int or isinstance(width, bool) or width <= 0:
        return None
    return width


def _match_type_spec(data_type: Any, spec: CatalogTypeSpec) -> Optional[str]:
    """catalog spec と宣言型が一致するか。一致すれば ``None``、不一致なら理由。"""

    observed_class = _declared_type_class(data_type)
    if observed_class is None:
        return REJECT_SIGNATURE_UNAVAILABLE
    if observed_class != spec.type_class:
        return REJECT_ARGUMENT_TYPE_MISMATCH
    observed_width = _declared_width_bits(data_type)
    if observed_width is None:
        return REJECT_SIGNATURE_UNAVAILABLE
    if observed_width != spec.width_bits:
        return REJECT_ARGUMENT_WIDTH_MISMATCH
    return None


def validate_catalog_signature(function_obj: Any, entry: CatalogEntry) -> Optional[str]:
    """Ghidra signature が catalog signature と一致するか検証する。

    一致すれば ``None``、しなければ reject reason。取得できない情報がある場合も
    reject（幅・型が不明なまま candidate にしない）。
    """

    has_var_args = _safe_call(function_obj, "hasVarArgs")
    if type(has_var_args) is not bool:
        return REJECT_SIGNATURE_UNAVAILABLE
    if has_var_args:
        return REJECT_SIGNATURE_VARARGS

    raw_parameters = _safe_call(function_obj, "getParameters")
    if raw_parameters is None:
        return REJECT_SIGNATURE_UNAVAILABLE
    try:
        parameters = list(raw_parameters)
    except Exception:  # noqa: BLE001
        return REJECT_SIGNATURE_UNAVAILABLE
    if len(parameters) != len(entry.parameters):
        return REJECT_SIGNATURE_ARITY_MISMATCH

    for parameter, spec in zip(parameters, entry.parameters):
        mismatch = _match_type_spec(_safe_call(parameter, "getDataType"), spec)
        if mismatch is not None:
            return mismatch

    return_mismatch = _match_type_spec(
        _safe_call(function_obj, "getReturnType"), entry.return_spec
    )
    if return_mismatch is None:
        return None
    if return_mismatch == REJECT_ARGUMENT_TYPE_MISMATCH:
        return REJECT_RETURN_TYPE_MISMATCH
    if return_mismatch == REJECT_ARGUMENT_WIDTH_MISMATCH:
        return REJECT_RETURN_WIDTH_MISMATCH
    return return_mismatch


# --- observation boundary -------------------------------------------------


def observation_conflict(policy: Any) -> Optional[str]:
    """errno / fenv を観測しているなら candidate を作らない。

    正本 v4 §4.3.4 の B1 成立条件は「errno / fenv を observation 対象にしていない
    こと」であり、関数ごとの感度で緩めてよいとは書かれていない。catalog の
    ``observation_sensitivity`` は metadata として保持するが、**B1 の gate を
    緩める根拠には使わない**（`fabs` のように感度が無いとされる関数でも、観測中は
    candidate 不成立）。観測境界の判断は観測を止めたときにだけ有効にする。
    """

    observe_errno = getattr(policy, "observe_errno", None)
    observe_fenv = getattr(policy, "observe_fenv", None)
    if type(observe_errno) is not bool or type(observe_fenv) is not bool:
        return REJECT_OBSERVATION_POLICY_UNAVAILABLE
    if observe_errno:
        return REJECT_ERRNO_OBSERVED
    if observe_fenv:
        return REJECT_FENV_OBSERVED
    return None


# --- candidate resolution -------------------------------------------------


@dataclass(frozen=True)
class CallModelCandidateResolution:
    """candidate 判定の結果。``candidate`` が ``None`` なら ``reject_reason`` が入る。"""

    candidate: Optional[CallModelCandidateRef] = None
    reject_reason: Optional[str] = None
    canonical_symbol: Optional[str] = None
    provenance_kind: Optional[str] = None

    def __post_init__(self) -> None:
        if (self.candidate is None) == (self.reject_reason is None):
            raise ValueError(
                "call model candidate resolution must carry exactly one of "
                "candidate / reject_reason"
            )

    @property
    def accepted(self) -> bool:
        return self.candidate is not None


def _rejected(
    reason: str,
    *,
    canonical_symbol: Optional[str] = None,
    provenance_kind: Optional[str] = None,
) -> CallModelCandidateResolution:
    return CallModelCandidateResolution(
        candidate=None,
        reject_reason=reason,
        canonical_symbol=canonical_symbol,
        provenance_kind=provenance_kind,
    )


def _resolve_canonical_symbol(
    catalog: PureFunctionCatalog,
    provenance: ExternalSymbolProvenance,
) -> Tuple[Optional[str], Optional[str]]:
    """object-derived な名前群から canonical symbol を 1 つに決める。"""

    resolved: List[str] = []
    blocking_reason: Optional[str] = None
    for symbol in provenance.symbol_names:
        canonical, reason = catalog.resolve(symbol, provenance_kind=provenance.kind)
        if reason is not None:
            blocking_reason = reason
            continue
        if canonical is not None and canonical not in resolved:
            resolved.append(canonical)
    if len(resolved) > 1:
        # 別々の canonical symbol へ解決してしまう名前が同居している。
        return None, REJECT_SYMBOL_RESOLUTION_AMBIGUOUS
    if len(resolved) == 1:
        return resolved[0], None
    if blocking_reason is not None:
        return None, blocking_reason
    return None, REJECT_SYMBOL_NOT_IN_CATALOG


def resolve_call_model_candidate(
    target_ref: Any,
    *,
    policy: Any,
    catalog: Optional[PureFunctionCatalog] = None,
) -> CallModelCandidateResolution:
    """1 個の callsite について call-model candidate を判定する。

    成立条件（すべて object-derived evidence で確認できる場合だけ）:

    1. proven external、または proven external へ解決される thunk
    2. alias を catalog 規則 + provenance evidence で canonical symbol へ解決できる
    3. Ghidra signature の引数個数 / 型クラス / 幅、戻り型クラス / 幅が catalog と一致
    4. errno / fenv を **どちらも** observation 対象にしていない

    どれか 1 つでも欠ける・曖昧・食い違うなら candidate を作らない。
    """

    provenance, reason = external_symbol_provenance(target_ref)
    if provenance is None:
        return _rejected(reason or REJECT_PROVENANCE_UNAVAILABLE)

    # observation 境界は関数によらない大域の前提なので、catalog を引く前に判定する。
    conflict = observation_conflict(policy)
    if conflict is not None:
        return _rejected(conflict, provenance_kind=provenance.kind)

    if catalog is None:
        try:
            catalog = load_pure_function_catalog()
        except (PureFunctionCatalogError, OSError, ValueError):
            return _rejected(
                REJECT_CATALOG_UNAVAILABLE, provenance_kind=provenance.kind
            )

    canonical_symbol, reason = _resolve_canonical_symbol(catalog, provenance)
    if canonical_symbol is None:
        return _rejected(
            reason or REJECT_SYMBOL_NOT_IN_CATALOG, provenance_kind=provenance.kind
        )
    entry = catalog.entries[canonical_symbol]

    signature_mismatch = validate_catalog_signature(provenance.signature_function, entry)
    if signature_mismatch is not None:
        return _rejected(
            signature_mismatch,
            canonical_symbol=canonical_symbol,
            provenance_kind=provenance.kind,
        )

    candidate = CallModelCandidateRef(
        provider=catalog.provider,
        canonical_symbol=canonical_symbol,
        signature_key=entry.signature_key(),
        provenance_key=provenance.provenance_key(),
    )
    return CallModelCandidateResolution(
        candidate=candidate,
        reject_reason=None,
        canonical_symbol=canonical_symbol,
        provenance_kind=provenance.kind,
    )


def resolve_call_model_candidate_ref(
    target_ref: Any,
    *,
    policy: Any,
) -> Optional[CallModelCandidateRef]:
    """``resolve_call_model_candidate`` の candidate だけを返す薄い入口。"""

    return resolve_call_model_candidate(target_ref, policy=policy).candidate
