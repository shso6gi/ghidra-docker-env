# -*- coding: utf-8 -*-
"""program の image の値を、具体化してよいときだけ読む（Issue #282, Q1 / I7）。

**image の byte を解析の値にする（具体化する）経路の唯一の入口**。memory の読み出しを image の値に置き換えて
よいのは、次をすべて満たすときだけ（設計 v3 §7.2）。満たさなければ None（具体化しない）:

1. `[addr, addr+size)` が、overlay でない 1 つの block に収まる（block をまたぐ読み出しは、後ろの block の
   属性を見ていない）。
2. その block の init・read が True、write・volatile が False。取得できない属性（例外・bool でない値）は
   不成立（以前は `None` を「書き込めない」と読む経路があった）。
3. 範囲に再配置が無い。または、purpose が `CODE_TARGET`（switch の表・呼び出し先の解決: 値は同じ側の制御の
   解決にだけ使う）で、範囲に掛かるすべての再配置の status が `APPLIED`（`PARTIAL` などは不成立）。
   再配置のある値は配置に依存する番地で、比べる値（`DATA_VALUE`）には入れない。
4. byte の順は `Language.isBigEndian`（bool でなければ不成立）。

**根拠（意味領域 D の条項。#188 が所有）**: D-L（各側の image は Ghidra の配置にある）、D-F（比べるのは
fault せず、単一 thread で、page の権限を変えずに終わる実行）。write が False の block の cell は、D-F の
実行ではどの pointer 経由でも書き換わらない（書けば fault）ので、関数の中の先行する store を見なくてよい。
read-only と分類した場所への store は効果を不完全にする（`store_effect`: 黙って捨てない）。
"""

from __future__ import annotations

from typing import Optional, Tuple

DATA_VALUE = "data_value"
CODE_TARGET = "code_target"

#: 読み出しの範囲より前から始まって範囲に掛かり得る再配置を探す幅（byte）。再配置の長さは高々この幅と仮定せず、
#: 見つけた再配置の長さで範囲との交わりを判定する
_RELOCATION_LOOKBEHIND = 16
_DEFAULT_RELOCATION_LENGTH = 8


class _Unreadable(Exception):
    pass


def _exact_bool(value) -> bool:
    if isinstance(value, bool):
        return value
    # JPype の boolean は Python の bool の subclass ではないことがある
    text = str(value)
    if text in ("True", "true"):
        return True
    if text in ("False", "false"):
        return False
    raise _Unreadable(f"attribute is not a boolean: {text!r}")


def _call(target, name: str, *args):
    method = getattr(target, name, None)
    if not callable(method):
        raise _Unreadable(f"{name} is unavailable")
    try:
        return method(*args)
    except _read_errors() as exc:
        raise _Unreadable(f"{name} failed: {type(exc).__name__}") from exc


def _read_errors() -> Tuple[type, ...]:
    """読めないとみなす例外。JVM（JPype の `JException`）は解析の途中で読み込まれるので、呼ぶたびに引く。
    `LookupError` は、記録した fixture や代わりの object が値を持たないとき（Ghidra の `MemoryAccessException` に当たる）。"""

    from scripts.function_tracer_pcode.analysis.program_points import ghidra_read_errors

    return ghidra_read_errors() + (LookupError,)


def _offset(address) -> int:
    return int(_call(address, "getOffset"))


def _relocation_span(relocation) -> Tuple[int, int]:
    start = _offset(_call(relocation, "getAddress"))
    length = _DEFAULT_RELOCATION_LENGTH
    get_bytes = getattr(relocation, "getBytes", None)
    if callable(get_bytes):
        try:
            raw = get_bytes()
        except _read_errors():
            raw = None
        if raw is not None:
            try:
                length = max(1, len(raw))
            except TypeError:
                length = _DEFAULT_RELOCATION_LENGTH
    return start, start + length


def _relocations_allow(program, space, address_value: int, size_bytes: int, purpose: str) -> None:
    table = _call(program, "getRelocationTable")
    if table is None:
        raise _Unreadable("relocation table is unavailable")
    lo = max(0, address_value - _RELOCATION_LOOKBEHIND)
    for start in range(lo, address_value + size_bytes):
        address = _call(space, "getAddress", start)
        iterator = _call(table, "getRelocations", address)
        if iterator is None:
            continue
        for relocation in _iterate(iterator):
            reloc_lo, reloc_hi = _relocation_span(relocation)
            if reloc_hi <= address_value or reloc_lo >= address_value + size_bytes:
                continue
            if purpose != CODE_TARGET:
                raise _Unreadable("relocated bytes are layout-dependent")
            status = str(_call(relocation, "getStatus"))
            if status != "APPLIED":
                raise _Unreadable(f"relocation status {status}")


def _iterate(iterator):
    has_next = getattr(iterator, "hasNext", None)
    if callable(has_next):
        while _exact_bool(_call(iterator, "hasNext")):
            yield _call(iterator, "next")
        return
    try:
        yield from iter(iterator)
    except TypeError as exc:
        raise _Unreadable("relocation iterator is not iterable") from exc


def _checked_bytes(program, address_value: int, size_bytes: int, purpose: str) -> Tuple[Tuple[int, ...], bool]:
    memory = _call(program, "getMemory")
    factory = _call(program, "getAddressFactory")
    space = _call(factory, "getDefaultAddressSpace")
    address = _call(space, "getAddress", address_value)
    if memory is None or address is None:
        raise _Unreadable("memory is unavailable")
    block = _call(memory, "getBlock", address)
    if block is None:
        raise _Unreadable("address is not in a block")
    if _exact_bool(_call(block, "isOverlay")):
        raise _Unreadable("overlay block")
    block_start = _offset(_call(block, "getStart"))
    block_end = _offset(_call(block, "getEnd"))
    if address_value < block_start or address_value + size_bytes - 1 > block_end:
        raise _Unreadable("read crosses the block end")
    if not (
        _exact_bool(_call(block, "isInitialized"))
        and _exact_bool(_call(block, "isRead"))
        and not _exact_bool(_call(block, "isWrite"))
        and not _exact_bool(_call(block, "isVolatile"))
    ):
        raise _Unreadable("block is not initialized read-only memory")
    _relocations_allow(program, space, address_value, size_bytes, purpose)
    big_endian = _exact_bool(_call(_call(program, "getLanguage"), "isBigEndian"))
    raw = tuple(int(_call(memory, "getByte", _call(address, "add", offset))) & 0xFF for offset in range(size_bytes))
    return raw, big_endian


def read_image_value(
    program,
    address_value: int,
    size_bytes: int,
    *,
    purpose: str = DATA_VALUE,
) -> Optional[int]:
    """`program` の image の、具体化してよい読み出しの値（符号なし整数）。それ以外は None。"""

    if program is None or not isinstance(address_value, int) or isinstance(address_value, bool):
        return None
    if address_value < 0 or not isinstance(size_bytes, int) or size_bytes <= 0:
        return None
    if purpose not in (DATA_VALUE, CODE_TARGET):
        raise ValueError(f"unknown image read purpose: {purpose!r}")
    try:
        raw, big_endian = _checked_bytes(program, address_value, size_bytes, purpose)
    except _Unreadable:
        return None
    ordered = raw if big_endian else tuple(reversed(raw))
    value = 0
    for byte in ordered:
        value = (value << 8) | byte
    return value


def image_ranges(program) -> Optional[Tuple[Tuple[int, int], ...]]:
    """`program` の image の範囲: default の空間（ram）の、overlay でない block の `[start, end + 1)`（整列済み）。

    D-L（各側の image は Ghidra が読み込んだ配置にある）のもとで、反例の番地が image の外にあることの制約に使う。
    `Program.getMaxAddress()` は overlay の空間の番地を返し得るので使わない。読めない block が 1 つでもあれば None。
    """

    if program is None:
        return None
    cached = _IMAGE_RANGES.get(id(program))
    if cached is not None and cached[0] is program:
        return cached[1]
    try:
        memory = _call(program, "getMemory")
        default_space = _call(_call(program, "getAddressFactory"), "getDefaultAddressSpace")
        default_name = str(_call(default_space, "getName"))
        ranges = []
        for block in _iterate(_call(memory, "getBlocks")):
            if _exact_bool(_call(block, "isOverlay")):
                continue
            start = _call(block, "getStart")
            if str(_call(_call(start, "getAddressSpace"), "getName")) != default_name:
                continue
            ranges.append((_offset(start), _offset(_call(block, "getEnd")) + 1))
    except _Unreadable:
        result = None
    else:
        result = tuple(sorted(ranges))
    if len(_IMAGE_RANGES) > 64:
        _IMAGE_RANGES.clear()
    _IMAGE_RANGES[id(program)] = (program, result)
    return result


#: program ごとの image の範囲（program の object も持って、id の再利用で別の program の値を返さない）
_IMAGE_RANGES: dict = {}
