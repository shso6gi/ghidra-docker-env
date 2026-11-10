"""P-code op / block references and their ordinal signatures."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple
from scripts.function_tracer_pcode.core.live_values import (
    attribute_of, equal, exact_scalar, exact_tree, inert, inert_key, is_kind, method_of, scalar_int, scalar_text,
)
from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_entry, runtime_ref_key, runtime_ref_record
from scripts.function_tracer_pcode.core.json_encoding import (as_list, each, inline, is_json_record, mapping_of, materialize, nested, raw)


_MAX_PARENT_PCODE_OP_SCAN = 10000


#: P-code の opcode の番号（Ghidra 12.0.1 の ``ghidra.program.model.pcode.PcodeOp`` の定数）。repo の唯一の表で、
#: analysis はここから読む（同じ番号を別の場所で持たない）。判定層はこの表で op を判定し、Ghidra を import
#: しない。値は単体 test で固定し、PyGhidra のある環境では opt-in の test で Ghidra の定数と照合する。
PCODE_OPCODE_BY_MNEMONIC: Dict[str, int] = {
    "COPY": 1, "LOAD": 2, "STORE": 3, "BRANCH": 4, "CBRANCH": 5, "BRANCHIND": 6,
    "CALL": 7, "CALLIND": 8, "CALLOTHER": 9, "RETURN": 10,
    "INT_EQUAL": 11, "INT_NOTEQUAL": 12, "INT_SLESS": 13, "INT_SLESSEQUAL": 14,
    "INT_LESS": 15, "INT_LESSEQUAL": 16, "INT_ZEXT": 17, "INT_SEXT": 18,
    "INT_ADD": 19, "INT_SUB": 20, "BOOL_NEGATE": 37,
    "MULTIEQUAL": 60, "INDIRECT": 61, "PIECE": 62, "SUBPIECE": 63, "CAST": 64,
    "POPCOUNT": 72, "LZCOUNT": 73,
}
PCODE_MNEMONIC_BY_OPCODE: Dict[int, str] = {
    opcode: mnemonic for mnemonic, opcode in PCODE_OPCODE_BY_MNEMONIC.items()
}


def _coerce_nonnegative_int(value: Any) -> Optional[int]:
    if type(value) is int:
        return value if value >= 0 else None  # exact な整数（最も多い形: API の offset / seq）
    if value is None or is_kind(value, bool):
        return None
    try:
        coerced = scalar_int(value)
    except (TypeError, ValueError):
        return None
    return coerced if coerced >= 0 else None


def _coerce_optional_text(value: Any) -> Optional[str]:
    if value is None:
        return None
    text = scalar_text(value)
    return text if text else None


def _coerce_opcode(value: Any) -> Optional[Any]:
    if value is None or is_kind(value, bool):
        return None
    try:
        return scalar_int(value)
    except (TypeError, ValueError):
        return scalar_text(value)


def _address_components(address: Any) -> Tuple[Optional[str], Optional[int]]:
    if address is None:
        return None, None
    space_name = None
    # 受け手は 1 度だけ葉を写して読む（`method_of` と同じ読み: 親の block の走査の hot path なので method ごとに写さない）
    address = exact_scalar(address)
    try:
        space = address.getAddressSpace()
    except Exception:
        space = None
    if space is not None:
        try:
            space_name = exact_scalar(space).getName()
        except Exception:
            space_name = None
    try:
        offset = address.getOffset()
    except Exception:
        offset = None
    return _coerce_optional_text(space_name), _coerce_nonnegative_int(offset)


def _pcode_op_ordinal_signature(pcode_op: Any, target: Optional[Tuple[Any, ...]] = None) -> Optional[Tuple[Any, ...]]:
    """op の (target_space, target_offset, seq_time, seq_order, opcode, mnemonic)。

    `target` を渡すと、親の block の走査の候補の比較: field を違いが出やすい順（seq の order・time、target、opcode、
    mnemonic）に読み、`target` の field と違う最初の field で読むのを止めて `None` を返す（同じ block の他の op は多く
    order で違う: 候補ごとに 6 つの field 全部を読まない）。違わなければ signature（`== target`）。field の値はどれも
    写した組み込みの値なので、読む順も止める位置も、`signature == target` の真偽を変えない。
    """

    if target is not None:
        target = exact_tree(target)  # 比べる前の読み（呼ぶ側が渡す値: 組み込みの木）
        shape = type(target)
        if shape is not tuple or len(target) != 6:
            return None  # signature（6 つの field の tuple）と等しくなり得ない値
        if not inert(target):
            # 葉に外の object を持つ target: field ごとに止める比べ方は、tuple の比較（左から順に、外の object の
            # `__eq__` を呼ぶ）と例外の起き方が違う。signature 全体を `equal`（tuple の比較の規則）で比べる
            signature = _pcode_op_ordinal_signature(pcode_op)
            return signature if signature is not None and equal(signature, target) else None
        target = inert_key(target)  # 不活性な木（field の比較は組み込みの code だけ）
    target_space = None
    target_offset = None
    seq_time = None
    seq_order = None
    # 受け手は 1 度だけ葉を写して読む（`_address_components` と同じ）
    pcode_op = exact_scalar(pcode_op)
    try:
        seq = pcode_op.getSeqnum()
    except Exception:
        seq = None
    if seq is not None:
        seq = exact_scalar(seq)
        try:
            seq_order = _coerce_nonnegative_int(seq.getOrder())
        except Exception:
            seq_order = None
        if target is not None and seq_order != target[3]:
            return None
        try:
            seq_time = _coerce_nonnegative_int(seq.getTime())
        except Exception:
            seq_time = None
        if target is not None and seq_time != target[2]:
            return None
        try:
            target_space, target_offset = _address_components(seq.getTarget())
        except Exception:
            target_space, target_offset = None, None
    if target is not None and (
        target_offset != target[1] or target_space != target[0] or seq_time != target[2] or seq_order != target[3]
    ):
        return None
    try:
        opcode = _coerce_opcode(pcode_op.getOpcode())
    except Exception:
        opcode = None
    if target is not None and opcode != target[4]:
        return None
    try:
        mnemonic = _coerce_optional_text(pcode_op.getMnemonic())
    except Exception:
        mnemonic = None
    if target is not None and mnemonic != target[5]:
        return None
    return (target_space, target_offset, seq_time, seq_order, opcode, mnemonic)


def _local_op_ordinal_from_parent(pcode_op: Any) -> Optional[int]:
    try:
        parent = method_of(pcode_op, "getParent")()
    except Exception:
        parent = None
    if parent is None:
        return None
    iterator = attribute_of(parent, "getIterator", lambda: None)()
    if iterator is None:
        return None
    iterator = exact_scalar(iterator)  # 受け手は 1 度だけ葉を写す（候補ごとに写さない）
    target_signature = _pcode_op_ordinal_signature(pcode_op)
    # `pcode_op` の読み（初めて要るときに 1 度だけ: 走査の op ごとに読み直さない）
    target_tree = None
    target_read = False
    ordinal = 0
    while ordinal < _MAX_PARENT_PCODE_OP_SCAN:
        try:
            has_next = iterator.hasNext()
        except Exception:
            return None
        # 組み込みの bool だけを受ける（`bool` は subclass を作れないので、真偽は identity で読める）
        if has_next is not True:
            return None
        try:
            candidate = iterator.next()
        except Exception:
            return None
        # API の object どうしの等しさ（Java の equals）。どちらかが scalar の subclass でも、その `__eq__` を呼ばない。
        # 比較の戻り値（暗黙の callback の値）も基底型の値で読む
        if candidate is pcode_op:
            return ordinal
        candidate_tree = exact_tree(candidate)  # 読む順は変えない（候補が先）
        if not target_read:
            target_tree = exact_tree(pcode_op)
            target_read = True
        # 葉の外の object（Java の object）の `__eq__` の戻り値は基底型の値の真偽で読む（`live_values.equal`）
        if equal(candidate_tree, target_tree):
            return ordinal
        if _pcode_op_ordinal_signature(candidate, target_signature) is not None:
            return ordinal
        ordinal += 1
    return None


@dataclass(frozen=True)
@runtime_ref_record
class PcodeOpRef:
    """Stable identity for a concrete Ghidra P-code operation."""

    address_offset: Optional[int] = None
    seq_time: Optional[int] = None
    seq_order: Optional[int] = None
    block_index: Optional[int] = None
    mnemonic: Optional[str] = None
    input_sizes: Tuple[int, ...] = ()
    output_size: Optional[int] = None
    binary_id: Optional[Any] = None
    function_entry_space: Optional[str] = None
    function_entry_offset: Optional[int] = None
    target_space: Optional[str] = None
    target_offset: Optional[int] = None
    opcode: Optional[Any] = None
    local_op_ordinal: Optional[int] = None
    program_uid: Optional[int] = None

    def __post_init__(self) -> None:
        # `binary_id` は注釈が Any だが stable key の scalar（側の識別子）: 基底型の値で持つ（Issue #242。
        # stable key を並べる・比べる読み手が subclass の code を呼ばない）
        object.__setattr__(self, "binary_id", exact_tree(self.binary_id))
        normalized_input_sizes = []
        for size in tuple(self.input_sizes or ()):
            try:
                int_size = scalar_int(size)
            except (TypeError, ValueError):
                continue
            if int_size > 0:
                normalized_input_sizes.append(int_size)
        object.__setattr__(self, "input_sizes", tuple(normalized_input_sizes))
        try:
            output_size = scalar_int(self.output_size) if self.output_size is not None else None
        except (TypeError, ValueError):
            output_size = None
        object.__setattr__(self, "output_size", output_size if output_size and output_size > 0 else None)
        object.__setattr__(self, "address_offset", _coerce_nonnegative_int(self.address_offset))
        object.__setattr__(self, "seq_time", _coerce_nonnegative_int(self.seq_time))
        object.__setattr__(self, "seq_order", _coerce_nonnegative_int(self.seq_order))
        object.__setattr__(self, "block_index", _coerce_nonnegative_int(self.block_index))
        object.__setattr__(
            self,
            "function_entry_offset",
            _coerce_nonnegative_int(self.function_entry_offset),
        )
        normalized_target_offset = _coerce_nonnegative_int(self.target_offset)
        if normalized_target_offset is None:
            normalized_target_offset = self.address_offset
        object.__setattr__(self, "target_offset", normalized_target_offset)
        object.__setattr__(self, "local_op_ordinal", _coerce_nonnegative_int(self.local_op_ordinal))
        object.__setattr__(self, "function_entry_space", _coerce_optional_text(self.function_entry_space))
        object.__setattr__(self, "target_space", _coerce_optional_text(self.target_space))
        object.__setattr__(self, "mnemonic", _coerce_optional_text(self.mnemonic))
        object.__setattr__(self, "opcode", _coerce_opcode(self.opcode))
        object.__setattr__(self, "program_uid", _coerce_nonnegative_int(self.program_uid))

    def input_size(self, index: int = 0) -> Optional[int]:
        try:
            return self.input_sizes[scalar_int(index)]
        except (IndexError, TypeError, ValueError):
            return None

    @classmethod
    @runtime_ref_entry
    def from_pcode_op(
        cls,
        pcode_op: Any,
        *,
        binary_id: Optional[Any] = None,
        program_uid: Optional[int] = None,
        function_entry: Any = None,
        function_entry_space: Optional[str] = None,
        function_entry_offset: Optional[int] = None,
        local_op_ordinal: Optional[int] = None,
    ) -> Optional["PcodeOpRef"]:
        """Build a stable, object-derived reference for a concrete Ghidra P-code op."""
        if pcode_op is None:
            return None

        address_offset = None
        target_space = None
        seq_time = None
        seq_order = None
        block_index = None
        mnemonic = None
        input_sizes = []
        output_size = None
        opcode = None

        try:
            mnemonic = method_of(pcode_op, "getMnemonic")()
        except Exception:
            mnemonic = None
        try:
            opcode = method_of(pcode_op, "getOpcode")()
        except Exception:
            opcode = None

        try:
            seq = method_of(pcode_op, "getSeqnum")()
        except Exception:
            seq = None
        if seq is not None:
            try:
                target = method_of(seq, "getTarget")()
                target_space, address_offset = _address_components(target)
            except Exception:
                address_offset = None
            try:
                time = attribute_of(seq, "getTime", lambda: None)()
                seq_time = None if time is None else scalar_int(time)
            except Exception:
                seq_time = None
            try:
                order = method_of(seq, "getOrder")()
                seq_order = None if order is None else scalar_int(order)
            except Exception:
                seq_order = None

        try:
            parent = method_of(pcode_op, "getParent")()
        except Exception:
            parent = None
        if parent is not None:
            try:
                block_index = scalar_int(method_of(parent, "getIndex")())
            except Exception:
                block_index = None
        if local_op_ordinal is None:
            local_op_ordinal = _local_op_ordinal_from_parent(pcode_op)

        try:
            num_inputs = scalar_int(method_of(pcode_op, "getNumInputs")())
        except Exception:
            num_inputs = 0
        for input_index in range(max(0, num_inputs)):
            try:
                input_varnode = method_of(pcode_op, "getInput")(input_index)
                input_size = scalar_int(method_of(input_varnode, "getSize")())
            except Exception:
                continue
            if input_size > 0:
                input_sizes.append(input_size)

        try:
            output_varnode = method_of(pcode_op, "getOutput")()
            output_size = scalar_int(method_of(output_varnode, "getSize")()) if output_varnode is not None else None
        except Exception:
            output_size = None

        return cls(
            address_offset=address_offset,
            seq_time=seq_time,
            seq_order=seq_order,
            block_index=block_index,
            mnemonic=mnemonic,
            input_sizes=tuple(input_sizes),
            output_size=output_size,
            binary_id=binary_id,
            program_uid=program_uid,
            function_entry_space=(
                function_entry_space
                if function_entry_space is not None
                else _address_components(function_entry)[0]
            ),
            function_entry_offset=(
                function_entry_offset
                if function_entry_offset is not None
                else _address_components(function_entry)[1]
            ),
            target_space=target_space,
            target_offset=address_offset,
            opcode=opcode,
            local_op_ordinal=local_op_ordinal,
        )

    @runtime_ref_key(proven=True)
    def stable_key(self) -> Tuple[Any, ...]:
        if self._has_full_identity_context():
            return (
                "pcode_op",
                self.binary_id,
                (
                    "function_entry",
                    self.function_entry_space,
                    int(self.function_entry_offset),
                ),
                (
                    "seq_target",
                    self.target_space,
                    int(self.target_offset),
                ),
                int(self.seq_time),
                int(self.seq_order),
                self.opcode,
                int(self.local_op_ordinal),
            )
        return (
            "pcode_op",
            None if self.address_offset is None else int(self.address_offset),
            None if self.seq_time is None else int(self.seq_time),
            None if self.seq_order is None else int(self.seq_order),
            None if self.block_index is None else int(self.block_index),
            self.mnemonic,
        )

    def _has_full_identity_context(self) -> bool:
        return (
            self.binary_id is not None
            and self.function_entry_space is not None
            and self.function_entry_offset is not None
            and self.target_space is not None
            and self.target_offset is not None
            and self.seq_time is not None
            and self.seq_order is not None
            and self.opcode is not None
            and self.local_op_ordinal is not None
        )

    def json_items(self):
        yield "kind", "pcode_op"
        yield "address_offset", self.address_offset
        yield "seq_time", self.seq_time
        yield "seq_order", self.seq_order
        yield "block_index", self.block_index
        yield "mnemonic", self.mnemonic
        yield "input_sizes", as_list(self.input_sizes)
        yield "output_size", self.output_size
        if self.binary_id is not None:
            yield "binary_id", self.binary_id
        if self.program_uid is not None:
            yield "program_uid", self.program_uid
        if self.function_entry_space is not None:
            yield "function_entry_space", self.function_entry_space
        if self.function_entry_offset is not None:
            yield "function_entry_offset", self.function_entry_offset
        if self.target_space is not None:
            yield "target_space", self.target_space
        if self.target_offset is not None:
            yield "target_offset", self.target_offset
        if self.opcode is not None:
            yield "opcode", self.opcode
        if self.local_op_ordinal is not None:
            yield "local_op_ordinal", self.local_op_ordinal

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
@runtime_ref_record
class PcodeBlockRef:
    """Stable identity for a concrete Ghidra decompiler basic block."""

    block_index: Optional[int] = None
    start_address_offset: Optional[int] = None
    binary_id: Optional[Any] = None
    function_entry_space: Optional[str] = None
    function_entry_offset: Optional[int] = None

    def __post_init__(self) -> None:
        # `binary_id` は stable key の scalar（`PcodeOpRef` と同じ読み方。Issue #242）
        object.__setattr__(self, "binary_id", exact_tree(self.binary_id))

    @runtime_ref_key(proven=True)
    def stable_key(self) -> Tuple[Any, ...]:
        if (
            self.binary_id is not None
            and self.function_entry_space is not None
            and self.function_entry_offset is not None
        ):
            return (
                "pcode_block",
                self.binary_id,
                (
                    "function_entry",
                    self.function_entry_space,
                    int(self.function_entry_offset),
                ),
                None if self.block_index is None else int(self.block_index),
                None if self.start_address_offset is None else int(self.start_address_offset),
            )
        return (
            "pcode_block",
            None if self.block_index is None else int(self.block_index),
            None if self.start_address_offset is None else int(self.start_address_offset),
        )

    def json_items(self):
        yield "kind", "pcode_block"
        yield "block_index", self.block_index
        yield "start_address_offset", self.start_address_offset
        yield "binary_id", self.binary_id
        yield "function_entry_space", self.function_entry_space
        yield "function_entry_offset", self.function_entry_offset

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)
