# -*- coding: utf-8 -*-
"""静的な guard が読む source の text と AST の、test session で 1 つの owner（Issue #224）。

静的な guard（import 層・境界・debug の描画・broad except・束縛の衛生・live な値の流れ…）は、
package の source を parse して規則を確かめる。guard と test が増えるたびに、同じ source を
file ごと・test ごと・helper ごとに parse し直していた（main `d398073` で 1 session に約
25,000 回、package 全体の約 59 回分）。ここが text と AST を 1 回だけ作り、guard はここから
受け取る。

* **鍵は path と今の text**。読むたびに text を読み、前に parse した text と同じなら同じ AST を
  返す。test が source を書き換えた・一時 directory に合成した場合は text（か path）が違うので
  parse し直す。共有が test の観測を覆い隠さない。
* **返す AST は共有の値で、受け取った側は書き換えない**（書き換えると別の test の結果が test の
  順序に依存する）。守られていることは test session の終わりに確かめる（`changed_trees`。
  `tests/conftest.py` が呼ぶ）: parse したときの木の形（`ast.dump`。位置の属性は含めない）を
  覚えておき、終わりの形と比べる。位置（`lineno` など）だけの書き換えはこの確かめの外。
"""

from __future__ import annotations

import ast
import pathlib
import threading
from typing import Dict, List, Optional, Tuple, Union

PathLike = Union[str, pathlib.Path]

#: 絶対 path → (parse した text, filename の引数, AST, parse したときの木の形)
_TREES: Dict[str, Tuple[str, Optional[str], ast.Module, str]] = {}
_LOCK = threading.Lock()


def source_text(path: PathLike) -> str:
    """source の今の text（UTF-8）。"""

    return pathlib.Path(path).read_text(encoding="utf-8")


def parse_source(path: PathLike, *, filename: Optional[str] = None) -> ast.Module:
    """`ast.parse(source_text(path), filename=...)` と同じ AST（今の text が前と同じなら共有）。

    `filename` は `ast.parse` の引数と同じ（既定は `<unknown>`）。同じ text でも `filename` が
    違えば別の値として扱う（SyntaxError の文面・`co_filename` が違うため）。
    """

    key = str(pathlib.Path(path).resolve())
    text = source_text(path)
    with _LOCK:
        cached = _TREES.get(key)
        if cached is not None and cached[0] == text and cached[1] == filename:
            return cached[2]
    tree = ast.parse(text, filename=filename) if filename is not None else ast.parse(text)
    shape = ast.dump(tree)
    with _LOCK:
        _TREES[key] = (text, filename, tree, shape)
    return tree


def changed_trees() -> List[str]:
    """覚えた AST のうち、parse したときと形が違うもの（= 誰かが書き換えた）。"""

    with _LOCK:
        entries = list(_TREES.items())
    return [key for key, (_text, _filename, tree, shape) in entries if ast.dump(tree) != shape]
