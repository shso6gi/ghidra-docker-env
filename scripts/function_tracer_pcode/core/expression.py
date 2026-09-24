# -*- coding: utf-8 -*-
"""式の表現クラス"""
import copy
import weakref
from enum import Enum, auto
from typing import List, NamedTuple, Optional, Any, Dict, Set, Mapping
from dataclasses import is_dataclass, fields

from scripts.function_tracer_pcode.core.semantic_lifecycle import (
    SemanticLifecycle,
    inherited_by_a_new_value,
    state_of,
)
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.core.render_output import utf8_length
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


def _new_value_fields(fields: Mapping[str, Any]) -> Dict[str, Any]:
    """既存の値の `__dict__` から、**新しい値**が持ってよい分だけを取り出す。

    落とす field を決めるのは `core/semantic_lifecycle.py`（状態の owner）。
    ここは「どの複製もその規則を通る」ことだけを担う。
    """

    return {
        key: item for key, item in fields.items() if inherited_by_a_new_value(key)
    }


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

class Expression:
    """
    式を表現するクラス（AST的な構造）

    生存期間は CONSTRUCTION → VALIDATED → PUBLISHED → solver consumption
    （状態は `core/semantic_lifecycle.py`、遷移は `core/semantic_freeze.py`）。
    検証後に意味 field を書き換えようとすると `FrozenExpressionError`（内部
    バグ）になるので、値を変えたい処理は `clone_with(...)` / `derive_with(...)`
    で新しい式を作る。複製（`copy` / `deepcopy` を含む）は状態も派生値も
    引き継がず CONSTRUCTION から始まる。
    """
    
    # クラス変数: 定数表示形式 ("dec", "hex", "auto")
    _constant_format: str = "dec"
    _hex_threshold: int = 256

    #: lifecycle 状態の既定値（instance が持たない限りこれが読まれる）。
    #: 意味は `core/semantic_lifecycle.py` が決める: `_frozen` = 検証済み、
    #: `_published` = producer が完成を宣言済み（`_frozen` を含む）。
    _frozen: bool = False
    _published: bool = False
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

    def __copy__(self) -> 'Expression':
        """浅い複製。**新しい root は CONSTRUCTION、子 object は元と共有する**。

        独立した複製ではない: 子は同じ object なので、子を書き換えれば元の式
        からも見える（子が検証済みならその書き換え自体が
        `FrozenExpressionError` になる）。独立が要るときは `copy.deepcopy`。

        root だけは独立している。`operands` は新しい list に入れ直すので、
        複製に子を足しても元の式は変わらない。これが無いと、検証済みの式を
        浅く複製したときに「CONSTRUCTION なのに `operands` が tuple」という
        仕上げられない値になる。

        状態を落とす規則を deep copy と揃えてあるのは、`copy.copy` を「安い
        deepcopy」と思って使った site が、そこだけ公開済みの値を作れてしまわ
        ないようにするため。複製は複製で、深さは関係ない。
        """

        clone = self.__class__.__new__(self.__class__)
        state = _new_value_fields(self.__dict__)
        state["operands"] = list(state.get("operands") or ())
        clone.__dict__.update(state)
        return clone

    def __deepcopy__(self, memo: Dict[int, Any]) -> 'Expression':
        """子まで複製する deep copy。**状態は引き継がない**。

        複製は「これから組み立て直す材料」なので、状態（`_frozen` /
        `_published`）も検証時の派生値（snapshot / digest）も持ち越さない。
        持ち越すと (a) copy 先で size を直すだけの既存処理が内部バグ扱いになり、
        (b) 元の宣言を名乗る複製が solver へ渡せてしまう。何を引き継がないかは
        `core/semantic_lifecycle.inherited_by_a_new_value` が決める。
        """

        cls = self.__class__
        clone = cls.__new__(cls)
        memo[id(self)] = clone
        state = {
            key: copy.deepcopy(item, memo)
            for key, item in _new_value_fields(self.__dict__).items()
        }
        operands = state.get("operands")
        if isinstance(operands, tuple):
            # 複製はまだ組み立て中なので、検証で畳んだ tuple を list へ戻す。
            state["operands"] = list(operands)
        clone.__dict__.update(state)
        return clone

    # -- freeze 境界 --------------------------------------------------------

    def freeze(self) -> 'Expression':
        """式 graph を検証して凍結し、自分を返す（冪等）。

        **これは公開ではない**。凍結は「閉路が無く、意味が immutable snapshot
        として確定した」ことしか言っておらず、作った側が「完成した」と宣言した
        ことにはならない。solver へ渡せる値にするのは
        `core/semantic_freeze.publish()` だけ。
        """

        if self.__dict__.get("_frozen", False):
            return self
        from scripts.function_tracer_pcode.core.semantic_freeze import freeze_expression

        return freeze_expression(self)

    @property
    def lifecycle(self) -> SemanticLifecycle:
        """今どの段階に居るか（`core/semantic_lifecycle.py` が定義）。"""

        return state_of(self.__dict__)

    @property
    def is_frozen(self) -> bool:
        """検証済み（immutable snapshot 確定済み）か。公開済みかは問わない。"""

        return self.lifecycle >= SemanticLifecycle.VALIDATED

    @property
    def is_published(self) -> bool:
        """producer が完成を宣言済みか。solver へ渡せるのはこれだけ。"""

        return self.lifecycle is SemanticLifecycle.PUBLISHED

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

        できた式は **CONSTRUCTION から始まる**（元が公開済みでも引き継がない）。
        精緻化した値は別の値なので、その完成を宣言できるのは作った側だけ。
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
        # Issue #22 PR-22-D: この表現は共有部分式を **親ごとに展開した木** なので、
        # 共有 DAG では distinct node が少なくても指数的な大きさになり得る。木は
        # walker（`core/json_encoding`）の sized leaf として、DAG のまま大きさを
        # 求めて予算と比べてから作る。解析 1 件分の表現を作っている最中なら
        # その作業量（`SerializationWork`）へ合流し、単独ならこの 1 本だけの作業量。
        from scripts.function_tracer_pcode.core.budget_policy import (
            active_serialization_work,
            budget_scope_is_active,
            serialization_scope,
        )

        work = active_serialization_work()
        if work is not None:
            return work.tree(self, build=True)[0]
        if not budget_scope_is_active():
            return self._to_dict(set())
        with serialization_scope(
            site=LEGACY_TREE_SERIALIZATION_SITE, target_parts=("legacy_tree",),
        ) as work:
            return work.tree(self, build=True)[0]

    # -- walker の sized leaf（`core/json_encoding`）------------------------------

    def __json_tree__(self) -> Dict[str, Any]:
        """木表現を作る（大きさは呼ぶ側が `__json_tree_bytes__` で確かめ済み）。"""

        return self._to_dict(set())

    def __json_tree_bytes__(self, policy: Any, remaining: Optional[int]) -> Optional[int]:
        """木表現の byte 数を **作らずに** 求める（`remaining` を超えたら `remaining + 1`）。"""

        try:
            return estimate_legacy_dict_bytes(self, policy=policy, max_bytes=remaining)
        except (TypeError, ValueError):
            return None

    def __json_tree_metered__(self, policy: Any, charge: Any) -> Dict[str, Any]:
        """木表現を、node を 1 つ作る **前** にその node の byte を `charge` しながら作る。

        DAG のまま見積もれない形（閉路）でだけ使う。閉路は経路ごとに `cycle_ref` へ
        置き換わるので、数える量は実際に作る木の byte と同じ。`charge` が予算超過で
        例外を上げた時点で、残りの木を作らない。
        """

        meters = _TREE_BUILD_METERS
        meters.append((policy, charge))
        try:
            return self._to_dict(set())
        finally:
            meters.pop()

    def __json_identity__(self) -> str:
        """証拠の digest に流す identity（DAG のまま求める構造 digest）。"""

        from scripts.function_tracer_pcode.core.structural import structural_identity_digest

        return str(structural_identity_digest(self))

    def _to_dict(self, active: Set[int]) -> Dict[str, Any]:
        node_id = id(self)
        if node_id in active:
            key = self.structural_key(budget=512)
            if _TREE_BUILD_METERS:
                # 数えながら作る: cycle_ref の表現も作りながら数える
                policy, charge = _TREE_BUILD_METERS[-1]
                charge(policy.measure({"type": self.expr_type.name, "cycle_ref": 0}) - 1)
                return {
                    "type": self.expr_type.name,
                    "cycle_ref": policy.materialize(
                        runtime_ref_source(key), budget=_ChargeOnlyBudget(charge),
                    ),
                }
            return {
                "type": self.expr_type.name,
                "cycle_ref": self._serialize_runtime_ref(key),
            }
        if _TREE_BUILD_METERS:
            policy, charge = _TREE_BUILD_METERS[-1]
            charge(_node_local_bytes(self, policy))
        active.add(node_id)
        try:
            return self._to_dict_active(active)
        finally:
            active.remove(node_id)

    def _to_dict_active(
        self, active: Optional[Set[int]], collect: Optional[List[Any]] = None,
    ) -> Dict[str, Any]:
        """木表現 1 node 分の dict。**schema の唯一の定義**。

        `collect` が `None` なら子を再帰的に描く（実際の直列化）。list を渡すと
        子を描かずにその list へ積み、代わりに placeholder `0` を置く — 大きさの
        見積り（`estimate_legacy_dict_bytes`）が node 1 つ分だけを測るため。
        同じ関数を通すので、field を足しても見積りと実出力が食い違わない。

        子を描く分岐を helper / lambda へ切り出さないのは、1 段あたりの Python
        frame を増やさないため（この表現は再帰なので、frame が増えると扱える
        深さがそのまま縮む）。
        """

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
                        if collect is None:
                            condition_value = condition.expression._to_dict(active)
                        else:
                            collect.append(condition.expression)
                            condition_value = 0
                        condition_payload = {
                            "expression": condition_value,
                            "negated": bool(condition.negated),
                        }
                    if collect is None:
                        branch_value = value._to_dict(active)
                    else:
                        collect.append(value)
                        branch_value = 0
                    branches.append({
                        "condition": condition_payload,
                        "value": branch_value,
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
            if collect is None:
                result["operands"] = [op._to_dict(active) for op in self.operands]
            else:
                collect.extend(self.operands)
                result["operands"] = [0] * len(self.operands)
        if self.storage_info:
            result["storage_info"] = self.storage_info.to_dict()
        if self.read_order_key is not None:
            result["read_order_key"] = self.read_order_key
        if self.runtime_ref is not None:
            if collect is None:
                result["runtime_ref"] = self._serialize_runtime_ref(self.runtime_ref)
            else:
                # 見積り: runtime ref は子と同じく node の外で数える（node の dict に
                # ref の表現を作らない）
                collect.append(_RuntimeRefChild(self.runtime_ref))
                result["runtime_ref"] = 0
        if self.opcode is not None:
            result["opcode"] = int(self.opcode)
        return result

    def _serialize_runtime_ref(self, value: Any) -> Any:
        # 木を作るのは大きさ（runtime ref を含む）を数え終えた後なので、ここは数えない
        from scripts.function_tracer_pcode.core.budget_policy import active_serialization_work
        from scripts.function_tracer_pcode.core.json_encoding import (
            RESULT_JSON_POLICY,
            copy_legacy_containers,
        )

        work = active_serialization_work()
        if work is None:
            return RESULT_JSON_POLICY.materialize(runtime_ref_source(value))
        # 共有 DAG を木に展開すると同じ ref が何度も現れる。直列化 1 回の間は同じ object
        # の表現は同じなので memo し、置くたびに容器を作り直す（`SerializationWork`）
        memo = work.runtime_ref_memo
        hit = memo.get(id(value))
        if hit is None or hit[0] is not value:
            hit = memo[id(value)] = (value, RESULT_JSON_POLICY.materialize(runtime_ref_source(value)))
        return copy_legacy_containers(hit[1])

    
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




# ---------------------------------------------------------------------------
# 木表現の大きさ（Issue #22 PR-22-D）
# ---------------------------------------------------------------------------

#: 木表現の直列化予算を見る観測点（`ExpressionSizeBudgetExceeded.site`）。
LEGACY_TREE_SERIALIZATION_SITE = "core.expression.to_dict"


def _opaque_local_text(value: Any) -> str:
    """JSON 型でない local 値（`to_dict` はそのまま置く）の大きさの代用表現。"""

    return type(value).__qualname__


#: 凍結済み node の木表現の大きさ（JSON byte、飽和していない正確な値）。
#: 凍結後は field も子も変わらないので、同じ node の大きさを pair の中で何度
#: 求め直しても同じ値になる。snapshot は同じ解析を何度も `to_dict()` するので、
#: ここで再利用しないと見積りが `to_dict` 本体より重くなる（実測で 6 倍）。
#: 弱参照なので式と一緒に消える（process 寿命の identity cache にはならない）。
_FROZEN_TREE_BYTES: "weakref.WeakKeyDictionary[Expression, int]" = (
    weakref.WeakKeyDictionary()
)


def estimate_legacy_dict_bytes(
    root: "Expression",
    *,
    policy: Any = None,
    max_bytes: Optional[int] = None,
) -> Optional[int]:
    """`root.to_dict()` を JSON にしたときの byte 数を **作らずに** 見積もる。

    木表現は同じ子を参照の数だけ展開するので、distinct node ごとに 1 回だけ
    大きさを求め（反復 post-order・memo）、辺の数だけ足す（同じ子への辺が 2 本
    なら 2 回）。node 1 つ分の大きさは `_to_dict_active` を子 = placeholder で
    呼んだ dict を `policy` の encoder で書いた長さ（実出力と schema・encoder を
    共有するので等しい）。node 1 つ分の dict は小さいので、これは「巨大な値を
    書いてから測る」ことにはならない — 木全体は作らない。

    `max_bytes` を超えた時点で `max_bytes + 1` を返し、残りを計算しない
    （子の大きさは根の大きさ以下なので、どこかの部分木が超えれば根も超える）。
    閉路（未凍結の式の中だけで起き得る）では `None`: 実出力は閉路を
    `cycle_ref` に置き換えるので、木の大きさが経路に依存し DAG の memo が使えない。
    """

    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

    policy = RESULT_JSON_POLICY if policy is None else policy
    cache = _FROZEN_TREE_BYTES if policy is RESULT_JSON_POLICY else None
    sizes: Dict[int, int] = {}
    pending: Dict[int, Any] = {}
    active: Set[int] = set()
    stack: List[Any] = [(root, False)]
    # distinct な node の node 1 つ分の大きさの合計。木は distinct な node を 1 回以上含むので
    # 木の大きさ ≥ この合計: 超えた時点で止まる（兄弟の部分木を全部数え終える前に）
    distinct_total = 0
    while stack:
        node, exiting = stack.pop()
        node_id = id(node)
        if exiting:
            active.discard(node_id)
            local, children = pending.pop(node_id)
            # placeholder の `0` は 1 byte。子の実際の大きさと差し替える
            local_size = _bounded_local_bytes(
                policy, local, None if max_bytes is None else max_bytes - distinct_total + len(children),
            ) - len(children)
            for child in children:
                if type(child) is _RuntimeRefChild:
                    local_size += child.measure(
                        policy, None if max_bytes is None else max_bytes - distinct_total - local_size,
                    )
            distinct_total += local_size
            if max_bytes is not None and distinct_total > max_bytes:
                return max_bytes + 1
            size = local_size
            for child in children:
                if type(child) is not _RuntimeRefChild:
                    size += sizes[id(child)]
            if max_bytes is not None and size > max_bytes:
                return max_bytes + 1
            sizes[node_id] = size
            if cache is not None and state_of(node.__dict__) >= SemanticLifecycle.VALIDATED:
                cache[node] = size
            continue
        if node_id in sizes:
            continue
        if cache is not None and state_of(node.__dict__) >= SemanticLifecycle.VALIDATED:
            known = cache.get(node)
            if known is not None:
                if max_bytes is not None and known > max_bytes:
                    return max_bytes + 1
                sizes[node_id] = known
                continue
        if node_id in active:
            return None
        active.add(node_id)
        children: List[Any] = []
        pending[node_id] = (node._to_dict_active(None, collect=children), children)
        stack.append((node, True))
        for child in reversed(children):
            if type(child) is not _RuntimeRefChild and id(child) not in sizes:
                stack.append((child, False))
    return sizes.get(id(root))


#: 数えながら木を作る間の (policy, charge)（`Expression.__json_tree_metered__`）。
#: 同期処理で入れ子になり得るので stack。空なら通常の構築（数えない）。
_TREE_BUILD_METERS: List[Any] = []


class _ChargeOnlyBudget:
    """walker へ渡す予算の代わり（数えた byte を `charge` へ流すだけ。上限は `charge` が持つ）。"""

    __slots__ = ("_charge",)

    def __init__(self, charge: Any) -> None:
        self._charge = charge

    def charge(self, size: int) -> None:
        self._charge(size)

    def remaining(self) -> Optional[int]:
        return None

    def tree(self, leaf: Any, *, build: bool) -> Any:
        from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

        return leaf.__json_tree_metered__(RESULT_JSON_POLICY, self._charge) if build else None, 0


def _node_local_bytes(node: "Expression", policy: Any, max_bytes: Optional[int] = None) -> int:
    """node 1 つ分の byte（子は含まない。runtime ref は含む）。見積りと同じ規則。

    `max_bytes` を超えたと分かった時点で `max_bytes + 1` 以上を返す（残りを数えない）。
    """

    children: List[Any] = []
    local = node._to_dict_active(None, collect=children)
    size = _bounded_local_bytes(
        policy, local, None if max_bytes is None else max_bytes + len(children),
    ) - len(children)
    for child in children:
        if type(child) is _RuntimeRefChild:
            size += child.measure(policy, None if max_bytes is None else max_bytes - size)
    return size


def _bounded_local_bytes(policy: Any, local: Any, max_bytes: Optional[int]) -> int:
    """node 1 つ分の dict を書いた byte。書く前に中の文字列の長さを数え、上限を超える
    （1 文字 1 byte 以上）と分かれば書かずに `max_bytes + 1` を返す。"""

    if max_bytes is not None:
        total = 0
        stack = [local]
        while stack:
            value = stack.pop()
            if isinstance(value, str):
                total += len(value)
            elif isinstance(value, dict):
                total += len(value)
                stack.extend(value.keys())
                stack.extend(value.values())
            elif isinstance(value, (list, tuple)):
                total += len(value)
                stack.extend(value)
            if total > max_bytes:
                return max_bytes + 1
    return utf8_length(policy.dumps(local, default=_opaque_local_text))


class _RuntimeRefChild:
    """見積りで node の外に置く runtime ref（walker が作らずに数える）。"""

    __slots__ = ("ref",)

    def __init__(self, ref: Any) -> None:
        self.ref = ref

    def measure(self, policy: Any, max_bytes: Optional[int]) -> int:
        from scripts.function_tracer_pcode.core.json_encoding import (
            LEGACY,
            JsonBudgetExhausted,
        )

        if max_bytes is not None and max_bytes < 0:
            return 1
        try:
            return policy.measure(runtime_ref_source(self.ref), max_bytes=max_bytes, mode=LEGACY)
        except JsonBudgetExhausted as exc:
            return exc.consumed_bytes


def runtime_ref_source(value: Any) -> Any:
    """`Expression.runtime_ref` の表現（旧 `_serialize_runtime_ref`）の JSON source。

    scalar はそのまま、tuple / list は配列、dict は key を文字列にした object、
    record（`json_items()`）は record の表現、dataclass は field の object、それ以外は
    型と object id。walker が 1 要素ずつ写す（ref の表現を先に作らない）。
    """

    from scripts.function_tracer_pcode.core.json_encoding import (
        each,
        inline,
        is_json_record,
        mapping_of,
        pairs_of,
    )

    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, (tuple, list)):
        return each(value, runtime_ref_source)
    if isinstance(value, dict):
        return mapping_of(value, runtime_ref_source, key=str)
    if is_json_record(value):
        return value
    if is_dataclass(value) and not isinstance(value, type):
        return pairs_of(
            (field.name, runtime_ref_source(getattr(value, field.name))) for field in fields(value)
        )
    return inline(
        ("type", f"{type(value).__module__}.{type(value).__qualname__}"),
        ("object_id", id(value)),
    )


# Re-exported for callers that import Condition from model.expression.
from scripts.function_tracer_pcode.core.condition import Condition
