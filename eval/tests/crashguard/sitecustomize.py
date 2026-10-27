# -*- coding: utf-8 -*-
"""test 用: wrapper の process を、永続化・外部操作の境界の前後で強制終了させる。

``EVAL_TEST_CRASH=<role>:<n>:<before|after>`` のとき、``--matrix <m> <role>`` で動く wrapper の
process だけが対象。境界は記録の確定点（``os.link`` / ``os.replace`` / ``os.rename`` /
``os.mkdir`` / ``os.write``）と外部操作（``subprocess.Popen``）。``n`` 番目の境界の前（呼ばずに）
または後（呼んでから）に ``os._exit(137)`` する（SIGKILL と同じく、後始末を何も走らせない）。
``n`` に ``supervise`` を書くと、supervisor を起動する ``Popen`` の境界だけを数える。発火したら
``EVAL_TEST_CRASH_MARK`` に印を書く（発火しなかった = その n は境界の数より大きい）。
"""

import os
import subprocess
import sys

_SPEC = os.environ.get("EVAL_TEST_CRASH")


def _role():
    argv = sys.argv
    if "--matrix" in argv:
        index = argv.index("--matrix")
        if index + 2 < len(argv):
            return argv[index + 2]
    return None


if _SPEC:
    _target, _index, _when = _SPEC.split(":")
    _count = [0]
    _write = os.write
    _open = os.open
    _close = os.close

    def _boundary(label, call, *args, **kwargs):
        if _role() != _target:
            return call(*args, **kwargs)
        if _index == "supervise":
            hit = label == "Popen" and any("_supervise" in str(a) for a in (args[0] if args else []))
        else:
            _count[0] += 1
            hit = _count[0] == int(_index)
        if not hit:
            return call(*args, **kwargs)
        mark = os.environ.get("EVAL_TEST_CRASH_MARK")
        if _when == "after":
            result = call(*args, **kwargs)
        if mark:
            fd = _open(mark, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o644)
            _write(fd, f"{label} {_when}\n".encode())
            _close(fd)
        os._exit(137)
        return result  # pragma: no cover

    class _Guard:
        """関数ではなく呼び出し可能な object（class 属性に入れられても method にならない）。"""

        def __init__(self, name, original):
            self.name, self.original = name, original

        def __call__(self, *args, **kwargs):
            return _boundary(self.name, self.original, *args, **kwargs)

    for _name in ("link", "replace", "rename", "mkdir", "write"):
        setattr(os, _name, _Guard(_name, getattr(os, _name)))

    _popen_init = subprocess.Popen.__init__

    def _patched(self, *args, **kwargs):
        if _role() != _target:
            return _popen_init(self, *args, **kwargs)
        return _boundary("Popen", lambda *a, **k: _popen_init(self, *a, **k), *args, **kwargs)

    subprocess.Popen.__init__ = _patched
