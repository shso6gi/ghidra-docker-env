# -*- coding: utf-8 -*-
"""式の表現クラス"""
import copy
from enum import Enum, auto
from typing import List, NamedTuple, Optional, Any, Dict, Set, Mapping
from dataclasses import is_dataclass, fields

from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.core.render_python import (
    expression_to_string,
    get_python_operator,
)
from scripts.function_tracer_pcode.core.render_smt import expression_to_smt, get_smt_operator
from scripts.function_tracer_pcode.core.runtime_refs import UnknownValueRef
from scripts.function_tracer_pcode.core.variable_collection import (
    collect_variables,
    collect_variables_into,
    contains_memory_access,
    collect_variables_with_storage,
    collect_variables_with_storage_into,
)


_EXPR_UNSET = object()


class PhiBranch(NamedTuple):
    """PHI の 1 分岐（条件と値）。

    `tuple` の subclass なので、`isinstance(branch, tuple)` / `len(branch) == 2` /
    unpack / index で branch を読む既存の consumer はそのまま動く。型を与えるのは
    凍結後の branch を **不変** にし、`branch.condition` / `branch.value` という
    名前で読めるようにするため。
    """

    condition: Optional["Condition"]
    value: "Expression"


def coerce_phi_branches(branches: Any) -> tuple:
    """PHI の branch 列を `PhiBranch` の tuple へ正規化する。

    形が `(condition, value)` でない要素はそのまま通す。ここで別の例外型に
    化けさせるより、`to_dict()` / renderer の既存の typed な失敗で落ちる方が
    どこが壊れているか分かりやすい。
    """

    if branches is None:
        return ()
    normalized = []
    for branch in branches:
        if isinstance(branch, PhiBranch):
            normalized.append(branch)
        elif isinstance(branch, (tuple, list)) and len(branch) == 2:
            normalized.append(PhiBranch(branch[0], branch[1]))
        else:
            normalized.append(branch)
    return tuple(normalized)


class ExpressionType(Enum):
    """式の種類"""
    CONSTANT = auto()
    PARAMETER = auto()
    VARIABLE = auto()
    BINARY_OP = auto()
    UNARY_OP = auto()
    CALL = auto()
    INTRINSIC = auto()
    MEMORY = auto()
    PHI = auto()
    UNKNOWN = auto()
    LITERAL = auto()



#: 凍結後に書き換えてはいけない **意味 field**。ここに無い属性（診断用の
#: 補助 flag 等）は凍結後も置けるが、意味 consumer はそれを読まない。
SEMANTIC_FIELDS = frozenset({
    "expr_type",
    "value",
    "operator",
    "operands",
    "size",
    "name",
    "data_type",
    "data_type_obj",
    "storage_info",
    "read_order_key",
    "runtime_ref",
    "opcode",
    "call_argument_width_evidence",
    "_recurrence_semantic_key",
})

#: 凍結そのものを表す内部 field（deepcopy では引き継がない）。
_FREEZE_STATE_FIELDS = (
    "_frozen",
    "_snapshot",
    "_local_payload",
    "_structural_hash",
    "_equivalence_digest",
    "_tree_size",
    "_identity_complete",
)


class Expression:
    """
    式を表現するクラス（AST的な構造）

    生存期間は construction → freeze → immutable consumption の 3 段階
    （`core/semantic_freeze.py`）。凍結後に意味 field を書き換えようとすると
    `FrozenExpressionError`（内部バグ）になるので、値を変えたい処理は
    `clone_with(...)` / `derive_with(...)` で新しい式を作る。
    """
    
    # クラス変数: 定数表示形式 ("dec", "hex", "auto")
    _constant_format: str = "dec"
    _hex_threshold: int = 256

    #: 凍結状態の既定値（instance が持たない限りこれが読まれる）。
    _frozen: bool = False
    _snapshot: Any = None
    _local_payload: Any = None
    _structural_hash: Optional[bytes] = None
    _equivalence_digest: Optional[bytes] = None
    _tree_size: Optional[int] = None
    _identity_complete: bool = False
    _recurrence_semantic_key: Any = None
    
    def __init__(
        self,
        expr_type: ExpressionType,
        value: Any = None,
        operator: Optional[str] = None,
        operands: Optional[List[Optional['Expression']]] = None,
        size: int = 0,
        name: Optional[str] = None,
        data_type: Optional[str] = None,
        data_type_obj: Any = None,
        storage_info: Optional[StorageInfo] = None,
        read_order_key: Optional[int] = None,
        runtime_ref: Any = None,
        opcode: Optional[int] = None,
        call_argument_width_evidence: Any = None,
        recurrence_semantic_key: Any = None,
    ):
        resolved_operands = []
        for operand in operands or []:
            if operand is None:
                raise ValueError("Expression operands must not contain None")
            resolved_operands.append(operand)
        # 構築は必ず未凍結なので `__setattr__` の判定を通す必要がない。
        # `__dict__` へ直接置いて構築費用を増やさない。
        self.__dict__.update(
            expr_type=expr_type,
            value=value,
            operator=operator,
            operands=resolved_operands,
            size=size,
            name=name,
            data_type=data_type,
            data_type_obj=data_type_obj,
            storage_info=storage_info,
            read_order_key=read_order_key,
            runtime_ref=runtime_ref,
            opcode=opcode,
            call_argument_width_evidence=call_argument_width_evidence,
        )
        if recurrence_semantic_key is not None:
            self.__dict__["_recurrence_semantic_key"] = recurrence_semantic_key

    def __setattr__(self, name: str, value: Any) -> None:
        """凍結後の意味 field 書き換えを内部バグとして拒否する。

        `TypeError` / `AttributeError` 派生ではない専用の型を投げるのは、
        「回復可能」な例外 tuple に吸収されて UNKNOWN や `None` に化けるのを
        防ぐため（`core/errors.py` の `FrozenExpressionError` を参照）。
        """

        if name in SEMANTIC_FIELDS and self.__dict__.get("_frozen", False):
            from scripts.function_tracer_pcode.core.semantic_freeze import (
                frozen_mutation_error,
            )

            raise frozen_mutation_error(self, name)
        object.__setattr__(self, name, value)

    def __deepcopy__(self, memo: Dict[int, Any]) -> 'Expression':
        """凍結を引き継がない deep copy。

        deep copy は「これから組み立て直す材料」なので、凍結状態と snapshot は
        持ち越さない。持ち越すと copy 先で size を直すだけの既存処理が内部バグ
        扱いになってしまう。
        """

        cls = self.__class__
        clone = cls.__new__(cls)
        memo[id(self)] = clone
        state = {
            key: copy.deepcopy(item, memo)
            for key, item in self.__dict__.items()
            if key not in _FREEZE_STATE_FIELDS
        }
        operands = state.get("operands")
        if isinstance(operands, tuple):
            state["operands"] = list(operands)
        clone.__dict__.update(state)
        return clone

    # -- freeze 境界 --------------------------------------------------------

    def freeze(self) -> 'Expression':
        """式 graph を凍結して自分を返す（冪等）。"""

        if self.__dict__.get("_frozen", False):
            return self
        from scripts.function_tracer_pcode.core.semantic_freeze import freeze_expression

        return freeze_expression(self)

    @property
    def is_frozen(self) -> bool:
        return bool(self.__dict__.get("_frozen", False))

    def structural_hash(self) -> Optional[bytes]:
        """凍結時に確定した candidate hash（未凍結なら `None`）。

        **候補の絞り込み専用**。等価の確定にも、外へ出す stable identity にも
        使ってはいけない（前者は `structural_equals`、後者は
        `structural_identity_digest` が担う）。
        """

        return self.__dict__.get("_structural_hash")

    def tree_size(self) -> Optional[int]:
        """木に展開したときの node 数（未凍結なら `None`）。共有は展開して数える。"""

        return self.__dict__.get("_tree_size")

    def semantic_projection(self):
        """凍結時に固定した意味投影（未凍結ならその場で作る）。"""

        from scripts.function_tracer_pcode.core.semantic_snapshot import (
            semantic_projection,
        )

        return semantic_projection(self)

    def derive_with(self, **fields: Any) -> 'Expression':
        """指定した意味 field を持つ **新しい式** を返す。元の式は変えない。

        自分が作ったのではない式（引数で受け取った式、helper が返した式、
        cache から来た式）へ幅などを書き足す site はこれを使う。凍結の有無で
        振る舞いを変えない: 未凍結でも複製する。未凍結なら書き換えてよい、に
        すると「まだ誰も見ていない」という前提が共有 node では成り立たず、
        同じ式を持つ別の consumer に変更が漏れる。

        自分がその場で作った式（factory の直後に幅を入れる等）はこの API の
        対象ではない。そちらは構築中なので直接代入してよい。
        """

        if not fields:
            return self
        return self.clone_with(**fields)
    
    @classmethod
    def set_constant_format(cls, fmt: str, threshold: int = 256):
        """定数の表示形式を設定"""
        cls._constant_format = fmt
        cls._hex_threshold = threshold
    
    @classmethod
    def constant(
        cls,
        value: int,
        size: int = 4,
        runtime_ref: Any = None,
    ) -> 'Expression':
        return cls(
            expr_type=ExpressionType.CONSTANT,
            value=value,
            size=size,
            runtime_ref=runtime_ref,
        )
    
    @classmethod
    def parameter(
        cls,
        name: str,
        index: int = -1,
        data_type: Optional[str] = None,
        data_type_obj: Any = None,
        size: int = 4,
        storage_info: Optional[StorageInfo] = None,
        runtime_ref: Any = None,
    ) -> 'Expression':
        return cls(
            expr_type=ExpressionType.PARAMETER,
            name=name,
            value=index,
            data_type=data_type,
            data_type_obj=data_type_obj,
            size=size,
            storage_info=storage_info,
            runtime_ref=runtime_ref,
        )
    
    @classmethod
    def variable(
        cls,
        name: str,
        data_type: Optional[str] = None,
        data_type_obj: Any = None,
        size: int = 4,
        storage_info: Optional[StorageInfo] = None,
        runtime_ref: Any = None,
    ) -> 'Expression':
        return cls(
            expr_type=ExpressionType.VARIABLE,
            name=name,
            data_type=data_type,
            data_type_obj=data_type_obj,
            size=size,
            storage_info=storage_info,
            runtime_ref=runtime_ref,
        )
    
    @classmethod
    def binary_op(
        cls,
        operator: Optional[str],
        left: Optional['Expression'],
        right: Optional['Expression'],
    ) -> 'Expression':
        """二項演算式を作成（サイズを適切に継承）"""
        if operator is None:
            raise ValueError("Binary operator must not be None")
        if left is None or right is None:
            raise ValueError("Binary operands must not be None")
        if operator == "PIECE":
            # PIECE: output.size = input0.size + input1.size
            size = (left.size if left.size else 0) + (right.size if right.size else 0)
        elif operator == "SUBPIECE":
            # SUBPIECE: サイズは呼び出し元で設定される（pcode_tracerで出力Varnodeから取得）
            size = 0
        elif operator in ["INT_LEFT", "INT_RIGHT", "INT_SRIGHT"]:
            # シフト演算: 結果は第1オペランドと同じサイズ
            size = left.size if left.size else 0
        elif operator in ["INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", 
                          "INT_SLESS", "INT_LESSEQUAL", "INT_SLESSEQUAL",
                          "FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL"]:
            # 比較演算: 結果は1バイト（ブール値）
            size = 1
        elif operator in ["BOOL_AND", "BOOL_OR", "BOOL_XOR"]:
            # 論理演算: 結果は1バイト
            size = 1
        else:
            # その他の二項演算: 大きい方のサイズ
            left_size = left.size if left.size else 0
            right_size = right.size if right.size else 0
            size = max(left_size, right_size)
        return cls(expr_type=ExpressionType.BINARY_OP, operator=operator, operands=[left, right], size=size)
    
    @classmethod
    def unary_op(cls, operator: Optional[str], operand: Optional['Expression']) -> 'Expression':
        """単項演算式を作成"""
        if operator is None:
            raise ValueError("Unary operator must not be None")
        if operand is None:
            raise ValueError("Unary operand must not be None")
        # INT_ZEXT/INT_SEXTのサイズは呼び出し元で設定される（pcode_tracerで出力Varnodeから取得）
        return cls(expr_type=ExpressionType.UNARY_OP, operator=operator, operands=[operand], size=operand.size)
    
    @classmethod
    def call(cls, func_name: str, arguments: List['Expression']) -> 'Expression':
        return cls(expr_type=ExpressionType.CALL, name=func_name, operands=arguments)

    @classmethod
    def intrinsic(
        cls,
        mnemonic: str,
        arguments: List['Expression'],
        *,
        size: int = 0,
        runtime_ref: Any = None,
        opcode: Optional[int] = None,
    ) -> 'Expression':
        inferred_size = size
        if inferred_size <= 0 and arguments:
            inferred_size = max(
                int(getattr(argument, "size", 0) or 0)
                for argument in arguments
            )
        return cls(
            expr_type=ExpressionType.INTRINSIC,
            name=mnemonic,
            operands=arguments,
            size=inferred_size,
            runtime_ref=runtime_ref,
            opcode=opcode,
        )
    
    @classmethod
    def memory(
        cls,
        address: 'Expression',
        size: int = 4,
        read_order_key: Optional[int] = None,
        runtime_ref: Any = None,
    ) -> 'Expression':
        return cls(
            expr_type=ExpressionType.MEMORY,
            operands=[address],
            size=size,
            read_order_key=read_order_key,
            runtime_ref=runtime_ref,
        )
    
    @classmethod
    def phi(cls, branches: List[tuple]) -> 'Expression':
        """PHIノード（条件分岐による値の選択）を作成"""
        return cls(expr_type=ExpressionType.PHI, value=coerce_phi_branches(branches))
    
    @classmethod
    def unknown(cls, description: str = "unknown", runtime_ref: Any = None) -> 'Expression':
        if runtime_ref is None:
            runtime_ref = UnknownValueRef.opaque(
                reason=description,
                display_hint=description,
            )
        return cls(expr_type=ExpressionType.UNKNOWN, name=description, runtime_ref=runtime_ref)

    def semantic_key(self):
        """Return an explicitly attached canonical semantic identity when present."""

        canonical = getattr(self, "_recurrence_semantic_key", None)
        if canonical is not None:
            return canonical
        return None
    
    def get_bit_width(self) -> int:
        """
        式のビット幅を取得
        
        Returns:
            int: ビット幅（ビット単位）
        """
        # サイズが明示的に設定されている場合
        if self.size and self.size > 0:
            return self.size * 8
        
        # 式の種類ごとにビット幅を推測
        if self.expr_type == ExpressionType.CONSTANT:
            # 定数のサイズが設定されていない場合のフォールバック
            return 32
        
        elif self.expr_type == ExpressionType.PARAMETER:
            return 32  # パラメータのデフォルト
        
        elif self.expr_type == ExpressionType.VARIABLE:
            return 32  # 変数のデフォルト
        
        elif self.expr_type == ExpressionType.BINARY_OP:
            if self.operator in ["INT_LEFT", "INT_RIGHT", "INT_SRIGHT"]:
                # シフト演算: 結果は第1オペランドと同じビット幅
                return self.operands[0].get_bit_width()
            elif self.operator == "PIECE":
                # PIECE: 両オペランドの合計
                return self.operands[0].get_bit_width() + self.operands[1].get_bit_width()
            elif self.operator == "SUBPIECE":
                # SUBPIECE: 出力サイズ（設定されているはず）
                return (self.size if self.size else 4) * 8
            elif self.operator in ["INT_EQUAL", "INT_NOTEQUAL", "INT_LESS", 
                                   "INT_SLESS", "INT_LESSEQUAL", "INT_SLESSEQUAL",
                                   "FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL"]:
                # 比較演算: 結果は1ビット（ブール値）
                return 1
            elif self.operator in ["BOOL_AND", "BOOL_OR", "BOOL_XOR"]:
                # 論理演算: 結果は1ビット
                return 1
            else:
                # その他の二項演算: 大きい方のビット幅
                left_bits = self.operands[0].get_bit_width()
                right_bits = self.operands[1].get_bit_width()
                return max(left_bits, right_bits)
        
        elif self.expr_type == ExpressionType.UNARY_OP:
            if self.operator in ["INT2FLOAT", "INT_ZEXT", "INT_SEXT"]:
                # The output Varnode owns an extension's width.  The operand
                # width and historical defaults are not evidence for an
                # unavailable conversion output width.
                return self.size * 8 if self.size and self.size > 0 else 0
            elif self.operator in ["BOOL_NEGATE"]:
                return 1
            else:
                # その他の単項演算: オペランドと同じ
                return self.operands[0].get_bit_width()

        elif self.expr_type == ExpressionType.INTRINSIC:
            if self.size and self.size > 0:
                return self.size * 8
            if self.operands:
                return max(
                    operand.get_bit_width()
                    for operand in self.operands
                    if hasattr(operand, "get_bit_width")
                )
            return 32

        elif self.expr_type == ExpressionType.MEMORY:
            return (self.size if self.size else 4) * 8
        
        elif self.expr_type == ExpressionType.PHI:
            # PHI: 最初の値のビット幅
            if self.value and len(self.value) > 0:
                _, first_val = self.value[0]
                if hasattr(first_val, 'get_bit_width'):
                    return first_val.get_bit_width()
            return 32
        
        return 32  # フォールバック
    
    def _format_constant(self, value: int) -> str:
        """定数を指定された形式でフォーマット"""
        if value < 0:
            # 負の値
            if self._constant_format == "hex":
                return f"(-0x{abs(value):x})"
            return f"({value})"
        
        if self._constant_format == "hex":
            return f"0x{value:x}"
        elif self._constant_format == "auto":
            if value >= self._hex_threshold:
                return f"0x{value:x}"
            return str(value)
        else:  # dec
            return str(value)
    
    def to_string(self, simplify: bool = True) -> str:
        """式を Python 互換の文字列に変換"""
        return expression_to_string(self, simplify)
    
    def _to_string_internal(self, simplify: bool) -> str:
        return expression_to_string(self, simplify)
    
    def _get_python_operator(self, operator: Optional[str]) -> str:
        return get_python_operator(operator)

    def clone_with(
        self,
        *,
        expr_type: Any = _EXPR_UNSET,
        value: Any = _EXPR_UNSET,
        operator: Any = _EXPR_UNSET,
        operands: Any = _EXPR_UNSET,
        size: Any = _EXPR_UNSET,
        name: Any = _EXPR_UNSET,
        data_type: Any = _EXPR_UNSET,
        data_type_obj: Any = _EXPR_UNSET,
        storage_info: Any = _EXPR_UNSET,
        read_order_key: Any = _EXPR_UNSET,
        runtime_ref: Any = _EXPR_UNSET,
        opcode: Any = _EXPR_UNSET,
        call_argument_width_evidence: Any = _EXPR_UNSET,
    ) -> 'Expression':
        """Clone an expression while preserving semantic metadata by default.

        The clone is **not** frozen even when the source is: a clone exists to be
        finished, and the recurrence semantic key rides along so that deriving a
        value does not silently drop the canonical identity it was given.
        """

        resolved_operands = self.operands if operands is _EXPR_UNSET else operands
        return Expression(
            expr_type=self.expr_type if expr_type is _EXPR_UNSET else expr_type,
            value=self.value if value is _EXPR_UNSET else value,
            operator=self.operator if operator is _EXPR_UNSET else operator,
            operands=list(resolved_operands or []),
            size=self.size if size is _EXPR_UNSET else size,
            name=self.name if name is _EXPR_UNSET else name,
            data_type=self.data_type if data_type is _EXPR_UNSET else data_type,
            data_type_obj=getattr(self, "data_type_obj", None) if data_type_obj is _EXPR_UNSET else data_type_obj,
            storage_info=self.storage_info if storage_info is _EXPR_UNSET else storage_info,
            read_order_key=self.read_order_key if read_order_key is _EXPR_UNSET else read_order_key,
            runtime_ref=getattr(self, "runtime_ref", None) if runtime_ref is _EXPR_UNSET else runtime_ref,
            opcode=getattr(self, "opcode", None) if opcode is _EXPR_UNSET else opcode,
            call_argument_width_evidence=(
                getattr(self, "call_argument_width_evidence", None)
                if call_argument_width_evidence is _EXPR_UNSET
                else call_argument_width_evidence
            ),
            recurrence_semantic_key=getattr(self, "_recurrence_semantic_key", None),
        )
    
    def equals(self, other: 'Expression') -> bool:
        """式が等価かどうかを判定"""
        if not isinstance(other, Expression):
            return False
        if self.expr_type != other.expr_type:
            return False
        if self.operator != other.operator:
            return False
        if self.value != other.value:
            return False
        if self.name != other.name:
            return False
        if self.size != other.size:
            return False
        if self.read_order_key != other.read_order_key:
            return False
        if self.runtime_ref != other.runtime_ref:
            return False
        if getattr(self, "opcode", None) != getattr(other, "opcode", None):
            return False
        if len(self.operands) != len(other.operands):
            return False
        for a, b in zip(self.operands, other.operands):
            if not a.equals(b):
                return False
        return True

    def structural_key(
        self,
        *,
        budget: int = 256,
        normalize_commutative: bool = True,
        strip_width_adapters: bool = False,
        collapse_full_masks: bool = False,
        include_memory_read_order: bool = True,
        include_semantic_runtime_refs: bool = True,
    ):
        """Hashable structural key for AST/P-code based comparisons."""
        from scripts.function_tracer_pcode.core.structural import expression_key

        return expression_key(
            self,
            budget=budget,
            normalize_commutative=normalize_commutative,
            strip_width_adapters=strip_width_adapters,
            collapse_full_masks=collapse_full_masks,
            include_memory_read_order=include_memory_read_order,
            include_semantic_runtime_refs=include_semantic_runtime_refs,
        )
    
    def to_smt(
        self,
        *,
        symbol_name_mapping: Optional[Mapping[str, str]] = None,
        float_mode: str = "uf",
    ) -> str:
        """SMT ソルバー用の式に変換"""
        return expression_to_smt(
            self,
            symbol_name_mapping=symbol_name_mapping,
            float_mode=float_mode,
        )
    
    def _to_smt_internal(
        self,
        *,
        symbol_name_mapping: Optional[Mapping[str, str]] = None,
        float_mode: str = "uf",
    ) -> str:
        return expression_to_smt(
            self,
            symbol_name_mapping=symbol_name_mapping,
            float_mode=float_mode,
        )

    def _get_smt_operator(self, operator: Optional[str] = None) -> str:
        return get_smt_operator(operator)
    
    def to_dict(self) -> Dict[str, Any]:
        return self._to_dict(set())

    def _to_dict(self, active: Set[int]) -> Dict[str, Any]:
        node_id = id(self)
        if node_id in active:
            return {
                "type": self.expr_type.name,
                "cycle_ref": self._serialize_runtime_ref(
                    self.structural_key(budget=512)
                ),
            }
        active.add(node_id)
        try:
            return self._to_dict_active(active)
        finally:
            active.remove(node_id)

    def _to_dict_active(self, active: Set[int]) -> Dict[str, Any]:
        result: Dict[str, Any] = {"type": self.expr_type.name}
        if self.value is not None:
            if self.expr_type == ExpressionType.PHI:
                branches = []
                for branch in self.value:
                    if not isinstance(branch, (tuple, list)) or len(branch) != 2:
                        raise TypeError("PHI branch must be a condition/value pair")
                    condition, value = branch
                    if not isinstance(value, Expression):
                        raise TypeError("PHI branch value must be an Expression")
                    condition_payload = None
                    if condition is not None:
                        from scripts.function_tracer_pcode.core.condition import Condition

                        if not isinstance(condition, Condition):
                            raise TypeError("PHI branch condition must be a Condition")
                        condition_payload = {
                            "expression": condition.expression._to_dict(active),
                            "negated": bool(condition.negated),
                        }
                    branches.append({
                        "condition": condition_payload,
                        "value": value._to_dict(active),
                    })
                result["value"] = branches
            else:
                result["value"] = self.value
        if self.operator:
            result["operator"] = self.operator
        if self.name:
            result["name"] = self.name
        if self.data_type:
            result["data_type"] = self.data_type
        if self.size:
            result["size"] = self.size
        if self.operands:
            result["operands"] = [op._to_dict(active) for op in self.operands]
        if self.storage_info:
            result["storage_info"] = self.storage_info.to_dict()
        if self.read_order_key is not None:
            result["read_order_key"] = self.read_order_key
        if self.runtime_ref is not None:
            result["runtime_ref"] = self._serialize_runtime_ref(self.runtime_ref)
        if self.opcode is not None:
            result["opcode"] = int(self.opcode)
        return result

    def _serialize_runtime_ref(self, value: Any) -> Any:
        if value is None or isinstance(value, (bool, int, float, str)):
            return value
        if isinstance(value, tuple):
            return [self._serialize_runtime_ref(item) for item in value]
        if isinstance(value, list):
            return [self._serialize_runtime_ref(item) for item in value]
        if isinstance(value, dict):
            return {
                str(key): self._serialize_runtime_ref(item)
                for key, item in value.items()
            }
        to_dict = getattr(value, "to_dict", None)
        if callable(to_dict):
            try:
                return to_dict()
            except Exception:
                pass
        if is_dataclass(value):
            return {
                field.name: self._serialize_runtime_ref(getattr(value, field.name))
                for field in fields(value)
            }
        return {
            "type": f"{type(value).__module__}.{type(value).__qualname__}",
            "object_id": id(value),
        }
    
    def get_all_variables(self) -> Set[str]:
        """式に含まれる全ての変数名（パラメータ・変数）を取得"""
        return collect_variables(self)

    def contains_memory_access(self) -> bool:
        """式木のどこかに MEMORY ノードが含まれるか判定する。"""
        return contains_memory_access(self)
    
    def _collect_variables(self, variables: Set[str]) -> None:
        """再帰的に変数を収集"""
        collect_variables_into(self, variables)
    
    def get_all_variables_with_storage(self) -> Dict[str, Optional['StorageInfo']]:
        """式に含まれる全ての変数名とストレージ情報を取得"""
        return collect_variables_with_storage(self)
    
    def _collect_variables_with_storage(self, variables: Dict[str, Optional['StorageInfo']]) -> None:
        """再帰的に変数とストレージ情報を収集"""
        collect_variables_with_storage_into(self, variables)




# Re-exported for callers that import Condition from model.expression.
from scripts.function_tracer_pcode.core.condition import Condition
