# -*- coding: utf-8 -*-
"""Issue #122: production execution identity はバイナリのみから決まる。

`--print-production-execution-identity` は runner が pair ごとに呼ぶ署名付き
identity の生成口である。以前はバイナリ隣接 `.c` から推定した戻り値型を payload
に含めていたため、同じバイナリ対でも隣接 `.c` の有無・内容で identity が変わった。
入力契約は 2 バイナリのみなので、3 レイアウト（`.c` なし / 正しい `.c` / 偽の `.c`）で
1 行 3 フィールドが完全一致することを固定する。
"""

import pytest

from scripts.function_tracer_pcode.authority.decision import production_cutover


_CORRECT_SOURCE = "long f(long a) { return a; }\n"
_FALSE_SOURCE = "void f(long a) { (void)a; }\n"


def _write_binaries(directory):
    binary1 = directory / "newV-arm64-clang-O0"
    binary2 = directory / "newV-mips64-clang-O0"
    binary1.write_bytes(b"\x7fELF-binary-1")
    binary2.write_bytes(b"\x7fELF-binary-2")
    return binary1, binary2


def _execution_identity_fields(capsys, directory):
    binary1, binary2 = _write_binaries(directory)
    exit_code = production_cutover.main([
        "--print-production-execution-identity",
        "--binary1-path", str(binary1),
        "--binary2-path", str(binary2),
        "--binary1-id", "B1",
        "--binary2-id", "B2",
        "--function-name1", "f",
        "--function-name2", "f",
        "--result-entry-occurrence-nonce", "fixed-nonce",
    ])
    assert exit_code == 0
    fields = capsys.readouterr().out.strip().split("\t")
    assert len(fields) == 3
    return tuple(fields)


def test_production_execution_identity_ignores_adjacent_c_source(capsys, tmp_path):
    absent = tmp_path / "absent"
    absent.mkdir()

    correct = tmp_path / "correct"
    correct.mkdir()
    (correct / "newV.c").write_text(_CORRECT_SOURCE, encoding="utf-8")

    false = tmp_path / "false"
    false.mkdir()
    (false / "newV.c").write_text(_FALSE_SOURCE, encoding="utf-8")

    without_source = _execution_identity_fields(capsys, absent)
    with_correct_source = _execution_identity_fields(capsys, correct)
    with_false_source = _execution_identity_fields(capsys, false)

    assert without_source == with_correct_source == with_false_source


def test_production_execution_identity_still_separates_binary_content(capsys, tmp_path):
    """identity が入力に無反応になっていないこと（バイナリ内容には反応する）。"""

    first = tmp_path / "first"
    first.mkdir()
    baseline = _execution_identity_fields(capsys, first)

    second = tmp_path / "second"
    second.mkdir()
    binary1, binary2 = _write_binaries(second)
    binary2.write_bytes(b"\x7fELF-binary-2-different")
    exit_code = production_cutover.main([
        "--print-production-execution-identity",
        "--binary1-path", str(binary1),
        "--binary2-path", str(binary2),
        "--binary1-id", "B1",
        "--binary2-id", "B2",
        "--function-name1", "f",
        "--function-name2", "f",
        "--result-entry-occurrence-nonce", "fixed-nonce",
    ])
    assert exit_code == 0
    changed = tuple(capsys.readouterr().out.strip().split("\t"))

    assert changed != baseline
