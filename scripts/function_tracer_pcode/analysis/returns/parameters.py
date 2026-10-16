"""Parameter descriptors: collection, storage info, passthrough synthesis, sealed return ABI facts."""

from __future__ import annotations

from typing import Any, Callable, Dict, Iterable, List, Optional, Set, Tuple, cast
from scripts.function_tracer_pcode.core.analysis import (
    FunctionReturnAnalysis,
    ReturnInfo,
    SignednessResult,
)
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.signature import (
    get_declared_type_signedness,
    is_void_data_type,
)
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.analysis.returns._shared import (
    SignednessDetector,
    _TrackedReturnValue,
    _resolve_call_target_ref,
)
from scripts.function_tracer_pcode.analysis.returns.debug_reporter import DebugReporter
from scripts.function_tracer_pcode.analysis.returns._api import PcodeTracer
from scripts.function_tracer_pcode.analysis.returns.pcode_sites import PcodeSiteService


def _sealed_return_abi_facts(function_prototype, return_type_obj, return_type):
    """Snapshot Ghidra ABI API objects without retaining Java object identity."""

    def fact(status, value, source):
        return {"status": status, "value": value, "source": source}

    calling = None
    calling_source = None
    calling_error = False
    for getter_name in ("getModelName", "getCallingConventionName"):
        getter = getattr(function_prototype, getter_name, None)
        if not callable(getter):
            continue
        try:
            value = getter()
        except Exception:
            calling_error = True
            continue
        # Ghidra uses ``None`` for a prototype whose calling convention is not
        # available.  That is missing provenance, not malformed authority.
        if value is None:
            continue
        if str(value).strip():
            calling = ("ghidra_calling_convention_v1", str(value).strip())
            calling_source = getter_name
            break
        calling_error = True
    if calling is not None:
        calling_fact = fact("PRESENT", calling, calling_source)
    elif calling_error:
        calling_fact = fact("MALFORMED", None, "ghidra_prototype_calling_convention")
    else:
        calling_fact = fact("MISSING", None, "ghidra_prototype_calling_convention")

    type_value = None
    type_error = False
    if return_type_obj is not None:
        try:
            name_getter = getattr(return_type_obj, "getPathName", None)
            if not callable(name_getter):
                name_getter = getattr(return_type_obj, "getName", None)
            if not callable(name_getter):
                raise TypeError("return type object lacks an exact name API")
            raw_type_name = name_getter()
            if raw_type_name is None or not str(raw_type_name).strip():
                raise ValueError("return type API returned an empty name")
            type_name = str(raw_type_name).strip()
            length_getter = getattr(return_type_obj, "getLength", None)
            if not callable(length_getter):
                raise TypeError("return type object lacks an exact length API")
            raw_type_length = length_getter()
            if type(raw_type_length) is bool:
                raise TypeError("return type API returned a boolean length")
            type_length = int(raw_type_length)
            if type_length < 0:
                raise ValueError("return type API returned a negative length")
            type_value = ("ghidra_return_type_v1", type_name, type_length)
        except Exception:
            type_error = True
    type_fact = (
        fact("PRESENT", type_value, "ghidra_function_prototype_return_type")
        if type_value is not None
        else fact(
            "MALFORMED" if type_error else "MISSING", None,
            "ghidra_function_prototype_return_type",
        )
    )

    storage_value = None
    storage_error = False
    storage_missing = False
    storage_source = "ghidra_function_prototype.getReturnStorage"
    getter = getattr(function_prototype, "getReturnStorage", None)
    if callable(getter):
        try:
            storage = getter()
            if storage is None:
                storage_missing = True
            elif not callable(getattr(storage, "getVarnodes", None)):
                raise ValueError("return storage API returned no typed storage")
            varnodes = (
                tuple(storage.getVarnodes())
                if not storage_missing
                else ()
            )
            if not varnodes:
                storage_missing = True
            members = []
            for varnode in varnodes:
                address = varnode.getAddress()
                space = address.getAddressSpace()
                raw_space_name = space.getName()
                if raw_space_name is None or not str(raw_space_name).strip():
                    raise ValueError("return storage member has an empty address space")
                raw_offset = address.getOffset()
                raw_size = varnode.getSize()
                if type(raw_offset) is bool or type(raw_size) is bool:
                    raise TypeError("return storage member uses boolean coordinates")
                offset = int(raw_offset)
                size = int(raw_size)
                if offset < 0 or size <= 0:
                    raise ValueError("return storage member coordinates are invalid")
                members.append((
                    "ghidra_return_storage_member_v1",
                    str(raw_space_name).strip(),
                    offset,
                    size,
                ))
            if not storage_missing:
                if len(members) != len(set(members)):
                    raise ValueError("return storage members are duplicated")
                storage_value = (
                    "ghidra_return_storage_v1",
                    tuple(sorted(members, key=lambda item: (item[1], item[2], item[3]))),
                )
        except Exception:
            storage_error = True
    storage_fact = (
        fact("PRESENT", storage_value, storage_source)
        if storage_value is not None
        else fact(
            "MALFORMED" if storage_error else "MISSING", None,
            storage_source,
        )
    )
    return {
        "schema_version": 1,
        "calling_convention": calling_fact,
        "declared_or_effective_return_type": type_fact,
        "return_storage_descriptor": storage_fact,
    }


class ParameterService:
    """ReturnAnalyzer から切り出したパラメータ記述子（収集・同期・符号推定・暗黙 passthrough 合成）の collaborator。

    facade 状態のうち読むのは program / debug フラグ（引数なし supplier）。
    ``synchronize_parameters_with_referenced_parameter_expressions`` は解析全体のパラメータ一覧を更新するため
    facade の現在パラメータへ **書き込む** 唯一の collaborator であり、書き込みは注入された
    ``set_current_parameters`` setter を通す（facade 側の属性を直接触らない）。
    optional int 変換は ``PcodeSiteService`` を直接依存として受け取る。
    未抽出 family（lifecycle / call_recovery / return_extraction）が所有する helper は facade 経由で遅延 dispatch
    する callable として注入する。``_sealed_return_abi_facts`` は module 関数のまま据え置く。
    """

    def __init__(
        self,
        *,
        pcode_sites: PcodeSiteService,
        debug_reporter: DebugReporter,
        target_active_key: Callable[..., Any],
        should_synthesize_implicit_passthrough_for_call: Callable[..., Any],
        make_tracked_return_value: Callable[..., Any],
        get_freshest_callee_parameters: Callable[..., Any],
        program_value: Callable[..., Any],
        debug_flag: Callable[..., Any],
        set_current_parameters: Callable[..., Any],
    ) -> None:
        self.pcode_sites = pcode_sites
        self.debug_reporter = debug_reporter
        self.target_active_key = target_active_key
        self.should_synthesize_implicit_passthrough_for_call = should_synthesize_implicit_passthrough_for_call
        self.make_tracked_return_value = make_tracked_return_value
        self.get_freshest_callee_parameters = get_freshest_callee_parameters
        self.program_value = program_value
        self.debug_flag = debug_flag
        self.set_current_parameters = set_current_parameters

    def synchronize_parameters_with_referenced_parameter_expressions(
        self,
        analysis: FunctionReturnAnalysis,
    ) -> None:
        parameters = [dict(param) for param in (analysis.parameters or [])]
        referenced = self.collect_referenced_parameter_descriptors(analysis.returns)
        changed = False

        for candidate in referenced:
            match_index = self.find_matching_parameter_descriptor_index(parameters, candidate)
            if match_index is None:
                parameters.append(candidate)
                changed = True
                continue

            merged = self.merge_parameter_descriptors(parameters[match_index], candidate)
            if merged != parameters[match_index]:
                parameters[match_index] = merged
                changed = True

        if not changed:
            return

        parameters.sort(key=lambda param: int(param.get("index", 1 << 20)))
        analysis.parameters = parameters
        self.set_current_parameters(parameters)

    def collect_referenced_parameter_descriptors(
        self,
        return_infos: List[ReturnInfo],
    ) -> List[Dict]:
        discovered: Dict[str, Dict] = {}

        for return_info in return_infos or []:
            self.collect_parameter_descriptors_from_expression(return_info.value, discovered)
            for condition in return_info.conditions or []:
                self.collect_parameter_descriptors_from_expression(
                    getattr(condition, "expression", None),
                    discovered,
                )

        descriptors = list(discovered.values())
        descriptors.sort(key=lambda param: int(param.get("index", 1 << 20)))
        return descriptors

    def collect_parameter_descriptors_from_expression(
        self,
        expr: Optional[Expression],
        discovered: Dict[str, Dict],
    ) -> None:
        if expr is None:
            return

        if expr.expr_type == ExpressionType.PARAMETER:
            descriptor = self.parameter_descriptor_from_expression(expr)
            key = self.parameter_descriptor_key(descriptor)
            existing = discovered.get(key)
            discovered[key] = self.merge_parameter_descriptors(existing, descriptor)
            return

        if expr.expr_type in {
            ExpressionType.BINARY_OP,
            ExpressionType.UNARY_OP,
            ExpressionType.CALL,
            ExpressionType.INTRINSIC,
            ExpressionType.MEMORY,
        }:
            for operand in expr.operands or []:
                self.collect_parameter_descriptors_from_expression(operand, discovered)
            return

        if expr.expr_type == ExpressionType.PHI and expr.value:
            for branch_condition, branch_value in expr.value:
                if branch_condition is not None:
                    self.collect_parameter_descriptors_from_expression(
                        getattr(branch_condition, "expression", None),
                        discovered,
                    )
                self.collect_parameter_descriptors_from_expression(branch_value, discovered)

    def parameter_descriptor_from_expression(self, expr: Expression) -> Dict:
        index_value = expr.value if isinstance(expr.value, int) and expr.value >= 0 else -1

        descriptor = {
            "name": expr.name or (f"param_{index_value + 1}" if index_value >= 0 else None),
            "index": index_value,
            "size": expr.size or 0,
            "data_type": expr.data_type,
            "is_signed": True,
            "implicit_passthrough": True,
        }
        if expr.storage_info is not None:
            descriptor["storage"] = expr.storage_info.to_dict()
        return descriptor

    def parameter_descriptor_key(self, descriptor: Dict) -> str:
        name = descriptor.get("name")
        if name:
            return f"name:{name}"
        index = descriptor.get("index")
        if isinstance(index, int) and index >= 0:
            return f"index:{index}"

        storage = descriptor.get("storage")
        if storage:
            base_name = storage.get("base_register_name") or storage.get("register_name") or storage.get("space_name")
            offset = int(storage.get("bit_offset_in_base", storage.get("offset", 0)) or 0)
            size_bits = int(storage.get("size_bits") or (storage.get("size", 0) * 8) or 0)
            return f"storage:{base_name}:{offset}:{size_bits}"
        return f"anonymous:{id(descriptor)}"

    def find_matching_parameter_descriptor_index(
        self,
        parameters: List[Dict],
        candidate: Dict,
    ) -> Optional[int]:
        candidate_name = candidate.get("name")
        if candidate_name:
            for index, param in enumerate(parameters):
                if param.get("name") == candidate_name:
                    return index

        candidate_index = candidate.get("index")
        if isinstance(candidate_index, int) and candidate_index >= 0:
            for index, param in enumerate(parameters):
                if int(param.get("index", -1)) == candidate_index:
                    return index

        candidate_storage = candidate.get("storage")
        if candidate_storage:
            for index, param in enumerate(parameters):
                if self.parameter_storages_match_for_passthrough(
                    param.get("storage"),
                    candidate_storage,
                ):
                    return index
        return None

    def merge_parameter_descriptors(
        self,
        existing: Optional[Dict],
        candidate: Dict,
    ) -> Dict:
        if existing is None:
            return dict(candidate)

        merged = dict(existing)
        if not merged.get("name") and candidate.get("name"):
            merged["name"] = candidate.get("name")
        if int(merged.get("index", -1)) < 0 and int(candidate.get("index", -1)) >= 0:
            merged["index"] = candidate.get("index")
        if int(merged.get("size", 0) or 0) <= 0 and int(candidate.get("size", 0) or 0) > 0:
            merged["size"] = candidate.get("size")
        if not merged.get("data_type") and candidate.get("data_type"):
            merged["data_type"] = candidate.get("data_type")
        if not merged.get("storage") and candidate.get("storage"):
            merged["storage"] = candidate.get("storage")
        if candidate.get("implicit_passthrough"):
            merged["implicit_passthrough"] = True
        if "is_signed" not in merged and "is_signed" in candidate:
            merged["is_signed"] = candidate.get("is_signed")
        return merged

    def parameter_expression(
        self,
        analysis: FunctionReturnAnalysis,
        index: int,
    ) -> Optional[Expression]:
        params = list(getattr(analysis, "parameters", []) or [])
        if index < 0 or index >= len(params):
            return None
        param = dict(params[index] or {})
        size = int(param.get("size", 0) or 4)
        return Expression.parameter(
            str(param.get("name") or f"param_{index + 1}"),
            index=index,
            data_type=param.get("data_type"),
            data_type_obj=param.get("data_type_obj"),
            size=max(1, size),
        )

    def propagate_passthrough_input_from_op(
        self,
        pcode_op,
        tracer: Optional[PcodeTracer],
    ) -> List[_TrackedReturnValue]:
        input_varnode = getattr(pcode_op, "getInput", lambda _idx: None)(0)
        if input_varnode is None:
            return []
        return [self.make_tracked_return_value(input_varnode, tracer)]

    def parameter_storages_overlap_for_passthrough(
        self,
        caller_storage: Optional[Dict],
        callee_storage: Optional[Dict],
    ) -> bool:
        caller = self.coerce_wrapper_storage_info(caller_storage)
        callee = self.coerce_wrapper_storage_info(callee_storage)
        if caller is None or callee is None:
            return False
        if not caller.is_register or not callee.is_register:
            return False
        try:
            return (
                caller.shares_base_register_with(callee)
                and caller.bit_range_overlaps_with(callee)
            )
        except Exception:
            return False

    def parameter_storages_match_for_passthrough(
        self,
        caller_storage: Optional[Dict],
        callee_storage: Optional[Dict],
    ) -> bool:
        caller = self.coerce_wrapper_storage_info(caller_storage)
        callee = self.coerce_wrapper_storage_info(callee_storage)
        if caller is None or callee is None:
            return False
        if not caller.is_register or not callee.is_register:
            return False
        if not caller.shares_base_register_with(callee):
            return False
        if int(caller.bit_offset_in_base or 0) != int(callee.bit_offset_in_base or 0):
            return False
        caller_bits = int(caller.size_bits or (caller.size or 0) * 8)
        callee_bits = int(callee.size_bits or (callee.size or 0) * 8)
        return caller_bits == callee_bits and caller_bits > 0

    def coerce_wrapper_storage_info(self, storage: Optional[object]) -> Optional[StorageInfo]:
        if storage is None:
            return None
        if isinstance(storage, StorageInfo):
            return storage
        if isinstance(storage, dict):
            try:
                return StorageInfo(
                    is_register=bool(storage.get("is_register", False)),
                    space_name=str(storage.get("space_name", "")),
                    space_id=self.pcode_sites.coerce_optional_int(storage.get("space_id")),
                    offset=int(storage.get("offset", 0)),
                    size=int(storage.get("size", 0)),
                    size_bits=int(storage.get("size_bits", 0)),
                    register_name=storage.get("register_name"),
                    register_offset=self.pcode_sites.coerce_optional_int(storage.get("register_offset")),
                    register_size=self.pcode_sites.coerce_optional_int(storage.get("register_size")),
                    register_size_bits=self.pcode_sites.coerce_optional_int(storage.get("register_size_bits")),
                    base_register_name=storage.get("base_register_name"),
                    base_register_offset=int(storage.get("base_register_offset", 0)),
                    base_register_size=int(storage.get("base_register_size", 0)),
                    base_register_size_bits=int(storage.get("base_register_size_bits", 0)),
                    bit_offset_in_base=int(storage.get("bit_offset_in_base", 0)),
                    is_stack_pointer=bool(storage.get("is_stack_pointer", False)),
                    is_frame_pointer=bool(storage.get("is_frame_pointer", False)),
                )
            except Exception:
                return None
        return None

    def parameter_descriptor_quality(self, parameters: Optional[List[Dict]]) -> Tuple[int, int, int, int]:
        params = list(parameters or [])
        return (
            len(params),
            sum(1 for param in params if param.get("storage")),
            sum(1 for param in params if param.get("data_type")),
            sum(1 for param in params if int(param.get("size", 0) or 0) > 0),
        )

    def choose_richer_parameter_descriptors(
        self,
        cached_parameters: Optional[List[Dict]],
        fresh_parameters: Optional[List[Dict]],
    ) -> List[Dict]:
        cached = list(cached_parameters or [])
        fresh = list(fresh_parameters or [])
        if self.parameter_descriptor_quality(fresh) > self.parameter_descriptor_quality(cached):
            return fresh
        return cached

    def augment_parameters_with_implicit_passthrough(
        self,
        parameters: List[Dict],
        tracer: Any,
        active_functions: Set[Tuple[Any, ...]],
    ) -> List[Dict]:
        augmented = [dict(param) for param in (parameters or [])]
        changed = False

        try:
            pcode_ops = list(tracer.get_all_pcode_ops())
        except Exception:
            return augmented

        for op in pcode_ops:
            try:
                if op.getMnemonic() not in {"CALL", "CALLIND"} or op.getNumInputs() < 1:
                    continue
            except Exception:
                continue

            target_ref = _resolve_call_target_ref(tracer, op)
            if target_ref is None:
                continue
            active_key = self.target_active_key(target_ref)
            if target_ref.is_unknown():
                continue
            if active_key is not None and active_key in active_functions:
                continue

            explicit_count = max(0, int(op.getNumInputs()) - 1)
            callee_parameters = self.get_freshest_callee_parameters(target_ref)
            if len(callee_parameters) <= explicit_count:
                continue

            for callee_param in callee_parameters[explicit_count:]:
                callee_storage = self.coerce_wrapper_storage_info(callee_param.get("storage"))
                if callee_storage is None or not callee_storage.is_register:
                    continue
                if any(
                    self.parameter_storages_overlap_for_passthrough(
                        existing.get("storage"),
                        callee_param.get("storage"),
                    )
                    for existing in augmented
                ):
                    continue
                if not self.should_synthesize_implicit_passthrough_for_call(
                    tracer,
                    op,
                    callee_storage,
                ):
                    continue
                augmented.append(
                    self.synthesize_implicit_passthrough_parameter(
                        augmented,
                        callee_param,
                        callee_storage,
                    )
                )
                changed = True

        if changed:
            augmented.sort(key=lambda param: int(param.get("index", 1 << 20)))
        return augmented

    def has_non_parameter_symbol_for_storage(
        self,
        tracer: PcodeTracer,
        target_storage: StorageInfo,
    ) -> bool:
        high_function = getattr(tracer, "high_function", None)
        if high_function is None:
            return False
        try:
            local_map = high_function.getLocalSymbolMap()
        except Exception:
            return False
        if local_map is None:
            return False

        for sym in local_map.getSymbols() or []:
            try:
                if sym.isParameter():
                    continue
            except Exception:
                continue
            candidate_storage = self.coerce_wrapper_storage_info(self.get_storage_info(sym))
            if candidate_storage is None or not candidate_storage.is_register:
                continue
            try:
                same_base = candidate_storage.shares_base_register_with(target_storage)
                overlaps = candidate_storage.bit_range_overlaps_with(target_storage)
            except Exception:
                same_base = False
                overlaps = False
            if same_base and overlaps:
                return True
        return False

    def synthesize_implicit_passthrough_parameter(
        self,
        current_parameters: List[Dict],
        callee_param: Dict,
        callee_storage: StorageInfo,
    ) -> Dict:
        used_names = {param.get("name") for param in current_parameters if param.get("name")}
        next_index = max((int(param.get("index", -1)) for param in current_parameters), default=-1) + 1
        suggested_name = callee_param.get("name") or f"param_{next_index + 1}"
        if suggested_name in used_names:
            suggested_name = f"param_{next_index + 1}"

        return {
            "name": suggested_name,
            "index": next_index,
            "size": callee_param.get("size") or callee_storage.size or 0,
            "data_type": callee_param.get("data_type"),
            "data_type_obj": callee_param.get("data_type_obj"),
            "is_signed": callee_param.get("is_signed", True),
            "storage": callee_storage.to_dict(),
            "implicit_passthrough": True,
        }

    def deduplicate_storage_infos(
        self,
        storages: List[StorageInfo],
    ) -> List[StorageInfo]:
        deduped: List[StorageInfo] = []
        seen: Set[Tuple[Any, ...]] = set()
        for storage in storages:
            key = (
                bool(getattr(storage, "is_register", False)),
                getattr(storage, "space_name", None),
                getattr(storage, "offset", None),
                getattr(storage, "size", None),
                getattr(storage, "size_bits", None),
                getattr(storage, "register_name", None),
                getattr(storage, "base_register_name", None),
                getattr(storage, "bit_offset_in_base", None),
            )
            if key in seen:
                continue
            seen.add(key)
            deduped.append(storage)
        return deduped

    def detect_signedness(self, high_function) -> Optional[SignednessResult]:
        """
        Phase 1: P-code証拠から符号性を推定

        Args:
            high_function: GhidraのHighFunctionオブジェクト

        Returns:
            SignednessResult: 推定結果（エラー時はNone）
        """
        try:
            detector = SignednessDetector(high_function, debug=self.debug_flag())
            evidence = detector.detect()
            return SignednessResult.from_evidence(evidence)
        except Exception as e:
            self.debug_reporter.debug_print(f"Signedness detection failed: {e}")
            return None

    def collect_parameters(self, high_function) -> List[Dict]:
        """パラメータ情報を収集（ストレージ情報付き）"""
        params = []
        local_map = high_function.getLocalSymbolMap()
        owner_program_id = None
        owner_entry_offset = None
        try:
            if self.program_value() is not None and hasattr(self.program_value(), "getUniqueProgramID"):
                owner_program_id = int(self.program_value().getUniqueProgramID())
        except Exception:
            owner_program_id = None
        try:
            function = getattr(high_function, "getFunction", lambda: None)()
            if function is not None and hasattr(function, "getEntryPoint"):
                entry_point = function.getEntryPoint()
                if entry_point is not None:
                    owner_entry_offset = int(entry_point.getOffset())
        except Exception:
            owner_entry_offset = None

        if local_map:
            for sym in local_map.getSymbols():
                if sym.isParameter():
                    data_type = sym.getDataType()
                    param_info = {
                        "name": sym.getName(),
                        "data_type": str(data_type) if data_type else None,
                        "data_type_obj": data_type,
                        "size": sym.getSize(),
                        "is_signed": self.is_signed_type(data_type),
                        "storage": self.get_storage_info(sym),
                        "owner_program_id": owner_program_id,
                        "owner_entry_offset": owner_entry_offset,
                    }
                    try:
                        param_info["index"] = sym.getCategoryIndex()
                    except:
                        param_info["index"] = -1

                    if self.debug_flag():
                        self.debug_reporter.debug_print(f"Parameter '{sym.getName()}': "
                                         f"type={param_info['data_type']}, "
                                         f"signed={param_info['is_signed']}, "
                                         f"storage={param_info['storage']}")

                    params.append(param_info)

        params.sort(key=lambda x: x.get("index", -1))
        return params

    def is_signed_type(self, data_type) -> bool:
        """データ型が符号付きかどうかを判定"""
        return get_declared_type_signedness(data_type, fallback_signed=True)

    def is_void_type(self, data_type) -> bool:
        """データ型が void かどうかを判定"""
        return is_void_data_type(data_type)

    def get_storage_info(self, sym) -> Optional[Dict]:
        """シンボルのストレージ情報を取得"""
        try:
            storage = sym.getStorage()
            if storage is None:
                return None

            # Varnodeリストを取得
            raw_varnodes = getattr(storage, "getVarnodes", lambda: [])()
            varnodes = [vn for vn in cast(Iterable[Any], raw_varnodes) if vn is not None]
            if not varnodes:
                return None

            first_vn = varnodes[0]
            addr = first_vn.getAddress()
            space = addr.getAddressSpace()

            storage_info = {
                "is_register": space.isRegisterSpace(),
                "offset": first_vn.getOffset(),
                "size": first_vn.getSize(),
                "size_bits": first_vn.getSize() * 8,
                "space_name": space.getName(),
            }

            if space.isRegisterSpace():
                # レジスタ情報を取得
                reg = self.program_value().getRegister(addr, first_vn.getSize())
                if reg:
                    storage_info["register_name"] = reg.getName()

                    # 親レジスタ情報
                    base_reg = reg.getBaseRegister()
                    if base_reg and base_reg != reg:
                        storage_info["base_register_name"] = base_reg.getName()
                        storage_info["base_register_size"] = base_reg.getBitLength() // 8
                        storage_info["base_register_size_bits"] = base_reg.getBitLength()
                        # パラメータのビットオフセット（親レジスタ内での位置）
                        byte_offset_in_base = reg.getOffset() - base_reg.getOffset()
                        storage_info["bit_offset_in_base"] = byte_offset_in_base * 8
                    else:
                        # 親レジスタと同じ場合
                        storage_info["base_register_name"] = reg.getName()
                        storage_info["base_register_size"] = reg.getBitLength() // 8
                        storage_info["base_register_size_bits"] = reg.getBitLength()
                        storage_info["bit_offset_in_base"] = 0

            return storage_info
        except Exception as e:
            if self.debug_flag():
                self.debug_reporter.debug_print(f"Failed to get storage info: {e}")
            return None

