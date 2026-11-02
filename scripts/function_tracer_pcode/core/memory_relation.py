# -*- coding: utf-8 -*-
"""2 つの memory の範囲（または記憶域）の関係の値（Issue #281 / #282）。

判定は持たない。値の型だけを共有する:

* 呼び出しの前の op と引数の記憶域（`analysis.effects.call_argument._op_write_relation`。#281）
* 同じ関数の中の 2 つの memory の位置（`analysis.effects.location_relation.location_relation`。#282）

`DISJOINT` は **重ならないと証明できた** ときだけ。重なりを否定できないときは `UNKNOWN` で、`OVERLAP`
（一部だけ重なると分かっている）と同じく、読み出しの値は決まらない。`SAME` は同じ範囲（同じ番地・同じ幅）。

値（0〜3）は #281 の `_storage_match_rank` の rank と並びが同じだが、rank から作るときは明示の写像
（`call_argument._relation_from_storage_rank`）を通す: rank の値の意味が変わったとき、型の上で衝突させない。
"""

from __future__ import annotations

from enum import IntEnum


class MemoryRelation(IntEnum):
    DISJOINT = 0
    OVERLAP = 1
    UNKNOWN = 2
    SAME = 3
