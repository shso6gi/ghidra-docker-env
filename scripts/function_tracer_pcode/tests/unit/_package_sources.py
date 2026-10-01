# -*- coding: utf-8 -*-
"""静的な guard が読む source の text と AST の、test session で 1 つの owner（Issue #224）。

静的な guard（import 層・境界・debug の描画・broad except・束縛の衛生・live な値の流れ…）は、
package の source を parse して規則を確かめる。guard と test が増えるたびに、同じ source を
file ごと・test ごと・helper ごとに parse し直していた（main `d398073` で 1 session に約
25,000 回、package 全体の約 59 回分）。ここが text と AST を 1 回だけ作り、guard はここから
受け取る。

**再利用と監査は別の表で、寿命も別**:

* **cache**（再利用だけ）: 鍵は ``(path, filename, text)`` の全部で、entry を上書きしない。
  source を書き換えた・別の root を合成した・``filename`` が違う呼び出しは、別の鍵の新しい木に
  なる（共有が test の観測を覆い隠さない）。cache は捨ててよい（``clear_cache``）。
* **台帳**（変更の検出）: ここが作って渡した木を **すべて**、渡した時点の形の digest と一緒に
  session の終わりまで追記だけで持つ。cache の entry が増えても捨てられても、古い木への参照が
  残っていても、台帳の記録は消えない。形は ``ast.dump(..., include_attributes=True)``（位置の
  属性を含む）で、session の終わりに今の形と比べる（``changed_trees``。``tests/conftest.py`` が
  呼ぶ）。

返す AST は共有の値で、受け取った側は書き換えない（書き換えると別の test の結果が test の順序に
依存する）。
"""

from __future__ import annotations

import ast
import hashlib
import pathlib
import threading
from typing import Dict, Iterable, List, Optional, Tuple, Union

PathLike = Union[str, pathlib.Path]

#: (絶対 path, filename の引数, text) → AST（再利用だけ。上書きしない、捨ててよい）
_CACHE: Dict[Tuple[str, Optional[str], str], ast.Module] = {}
#: 渡した木の台帳（追記だけ）: (説明, 木, 渡した時点の形の digest)
_ISSUED: List[Tuple[str, ast.Module, str]] = []
_LOCK = threading.Lock()


def source_text(path: PathLike) -> str:
    """source の今の text（UTF-8）。"""

    return pathlib.Path(path).read_text(encoding="utf-8")


def _shape(tree: ast.Module) -> str:
    return hashlib.sha256(ast.dump(tree, include_attributes=True).encode("utf-8")).hexdigest()


def parse_source(path: PathLike, *, filename: Optional[str] = None) -> ast.Module:
    """`ast.parse(source_text(path), filename=...)` と同じ AST（同じ path・filename・text なら共有）。

    `filename` は `ast.parse` の引数と同じ（既定は `<unknown>`）。同じ text でも `filename` が
    違えば別の木（SyntaxError の文面・`co_filename` が違うため）。
    """

    resolved = str(pathlib.Path(path).resolve())
    text = source_text(path)
    key = (resolved, filename, text)
    with _LOCK:
        cached = _CACHE.get(key)
    if cached is not None:
        return cached
    tree = ast.parse(text, filename=filename) if filename is not None else ast.parse(text)
    label = f"{resolved} (filename={filename!r})"
    shape = _shape(tree)
    with _LOCK:
        existing = _CACHE.get(key)
        if existing is not None:
            return existing
        _CACHE[key] = tree
        _ISSUED.append((label, tree, shape))
    return tree


def clear_cache() -> None:
    """再利用の表を捨てる（台帳は捨てない: 渡した木の変更の検出は session の終わりまで続く）。"""

    with _LOCK:
        _CACHE.clear()


def changed_trees(among: Optional[Iterable[ast.Module]] = None) -> List[str]:
    """渡した木のうち、渡した時点と形（位置の属性を含む）が違うもの（= 誰かが書き換えた）。

    `among` を渡すとその木（identity）だけを確かめる（台帳の記録は同じものを使う）。
    """

    with _LOCK:
        issued = list(_ISSUED)
    if among is not None:
        wanted = {id(tree) for tree in among}
        issued = [entry for entry in issued if id(entry[1]) in wanted]
    return [label for label, tree, shape in issued if _shape(tree) != shape]
