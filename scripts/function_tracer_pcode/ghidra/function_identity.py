# -*- coding: utf-8 -*-
"""Program 側から観測する関数の同一性（Issue #15）。

「同じバイナリの同じ関数」を早期に確定するための根拠は、解析結果でも
decompiler 出力でもなく **Program から直接読んだ事実**だけにする。この module は
そのための Ghidra 境界で、`getExecutableSHA256()` / `getLanguage()` /
`getCompilerSpec()` / `getImageBase()` / `getFunctionManager().getFunctions(True)`
を 1 回ずつ読む以上のことをしない（decompiler・`ReturnAnalyzer`・
decompilation broker は使わない）。

`analysis/returns/lifecycle.py::find_function_by_name` は「最初の名前一致」を
返し、欠落も例外も `None` に潰すので同一性の根拠には使えない。ここでは
`getFunctions(True)` を全走査して名前一致の**件数**を数え、ちょうど 1 件の
ときだけ entry / body を読む。

観測できなかった事実は握り潰さず `FunctionIdentityUnavailable` にする
（包括捕捉は Issue #125-B の凍結 baseline で禁止されているので、この module に
`except Exception` は無い）。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Optional, Tuple


#: `BinaryFunctionIdentity.as_tuple()` の先頭に置く schema tag。
BINARY_FUNCTION_IDENTITY_SCHEMA = "binary_function_identity_v1"

_SHA256_HEX_DIGITS = frozenset("0123456789abcdef")


class FunctionIdentityUnavailable(Exception):
    """Program / Function から identity を完全には観測できなかった。"""


@dataclass(frozen=True)
class BinaryFunctionIdentity:
    """1 つの Program 内の 1 つの関数について観測した同一性。

    `match_count` は「その名前に一致した関数の件数」で、1 以外のときは
    `entry` / `body_range` を観測していない（`None`）。
    """

    executable_sha256: str
    function_name: str
    language_id: str
    compiler_spec_id: str
    image_base: int
    entry: Optional[Tuple[str, int]]
    body_range: Optional[Tuple[Tuple[str, int], Tuple[str, int]]]
    match_count: int

    def __post_init__(self) -> None:
        if type(self.executable_sha256) is not str or len(
            self.executable_sha256
        ) != 64 or not set(self.executable_sha256) <= _SHA256_HEX_DIGITS:
            raise FunctionIdentityUnavailable(
                "program executable SHA-256 is not canonical"
            )
        for name in ("function_name", "language_id", "compiler_spec_id"):
            value = getattr(self, name)
            if type(value) is not str or not value:
                raise FunctionIdentityUnavailable(f"{name} is unavailable")
        if type(self.image_base) is not int or type(self.image_base) is bool:
            raise FunctionIdentityUnavailable("program image base is unavailable")
        if type(self.match_count) is not int or type(
            self.match_count
        ) is bool or self.match_count < 0:
            raise FunctionIdentityUnavailable("function name match count is invalid")
        resolved = self.match_count == 1
        if resolved == (self.entry is None) or resolved == (self.body_range is None):
            raise FunctionIdentityUnavailable(
                "function entry/body observation does not match the name resolution"
            )

    def as_tuple(self) -> Tuple[Any, ...]:
        """判定に使わない安定な射影（結果 JSON の `function*_identity`）。"""

        return (
            BINARY_FUNCTION_IDENTITY_SCHEMA,
            self.executable_sha256,
            self.function_name,
            self.language_id,
            self.compiler_spec_id,
            self.image_base,
            self.entry,
            self.body_range,
            self.match_count,
        )


def _call_noarg(obj: Any, name: str) -> Any:
    """引数なし API を呼ぶ。存在しなければ観測不能として扱う。"""

    member = getattr(obj, name, None)
    if not callable(member):
        raise FunctionIdentityUnavailable(f"{name}() is unavailable")
    return member()


def _exact_text(value: Any, what: str) -> str:
    """Ghidra の ID object（`LanguageID` 等）を文字列へ射影する。"""

    if value is None:
        raise FunctionIdentityUnavailable(f"{what} is unavailable")
    if type(value) is str:
        text = value
    else:
        text = str(value)
        if type(text) is not str:
            raise FunctionIdentityUnavailable(f"{what} is not a text identity")
    if not text:
        raise FunctionIdentityUnavailable(f"{what} is empty")
    return text


def _ghidra_integer(value: Any, what: str) -> int:
    """JPype の Java 整数を欠落なく Python int へ射影する。"""

    if value is None or type(value) is bool or isinstance(
        value, (str, bytes, bytearray, float, complex)
    ):
        raise FunctionIdentityUnavailable(f"{what} is not an integral value")
    try:
        projected = int(value)
    except (TypeError, ValueError, OverflowError) as exc:
        raise FunctionIdentityUnavailable(
            f"{what} is not an integral value"
        ) from exc
    if str(value) != str(projected):
        raise FunctionIdentityUnavailable(f"{what} cannot be projected losslessly")
    return projected


def _address_identity(address: Any, what: str) -> Tuple[str, int]:
    """アドレスを (space 名, offset) へ射影する。"""

    if address is None:
        raise FunctionIdentityUnavailable(f"{what} is unavailable")
    space = _call_noarg(address, "getAddressSpace")
    if space is None:
        raise FunctionIdentityUnavailable(f"{what} address space is unavailable")
    space_name = _exact_text(_call_noarg(space, "getName"), f"{what} address space")
    return (space_name, _ghidra_integer(_call_noarg(address, "getOffset"), what))


def resolve_binary_function_identity(
    program: Any, function_name: str,
) -> BinaryFunctionIdentity:
    """Program から `function_name` の同一性を観測する。

    名前一致が 0 件 / 2 件以上でも `BinaryFunctionIdentity` は返す（`match_count`
    がそれを言う）。呼び出し側はその件数で不適用の理由を分けられる。
    """

    if type(function_name) is not str or not function_name:
        raise FunctionIdentityUnavailable("function name is not an exact string")
    executable_sha256 = _exact_text(
        _call_noarg(program, "getExecutableSHA256"), "program executable SHA-256"
    ).lower()
    language_id = _exact_text(
        _call_noarg(_call_noarg(program, "getLanguage"), "getLanguageID"),
        "program language ID",
    )
    compiler_spec_id = _exact_text(
        _call_noarg(_call_noarg(program, "getCompilerSpec"), "getCompilerSpecID"),
        "program compiler spec ID",
    )
    image_base = _ghidra_integer(
        _call_noarg(_call_noarg(program, "getImageBase"), "getOffset"),
        "program image base",
    )
    function_manager = _call_noarg(program, "getFunctionManager")
    if function_manager is None:
        raise FunctionIdentityUnavailable("program function manager is unavailable")
    iterate = getattr(function_manager, "getFunctions", None)
    if not callable(iterate):
        raise FunctionIdentityUnavailable("getFunctions() is unavailable")
    # 件数は打ち切らずに数える（`match_count` は「その名前に一致した関数の
    # 件数」であって「2 件以上見つかった」ではない）。entry / body を読むのは
    # ちょうど 1 件のときだけ、という fail-closed 条件は変えない。
    match_count = 0
    first_match = None
    for function in iterate(True):
        if _exact_text(_call_noarg(function, "getName"), "function name") != function_name:
            continue
        match_count += 1
        if match_count == 1:
            first_match = function
    matched = first_match if match_count == 1 else None
    entry = None
    body_range = None
    if matched is not None:
        entry = _address_identity(
            _call_noarg(matched, "getEntryPoint"), "function entry point"
        )
        body = _call_noarg(matched, "getBody")
        if body is None:
            raise FunctionIdentityUnavailable("function body is unavailable")
        body_range = (
            _address_identity(_call_noarg(body, "getMinAddress"), "function body start"),
            _address_identity(_call_noarg(body, "getMaxAddress"), "function body end"),
        )
    return BinaryFunctionIdentity(
        executable_sha256=executable_sha256,
        function_name=function_name,
        language_id=language_id,
        compiler_spec_id=compiler_spec_id,
        image_base=image_base,
        entry=entry,
        body_range=body_range,
        match_count=match_count,
    )
