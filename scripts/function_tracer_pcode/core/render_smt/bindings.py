# -*- coding: utf-8 -*-
"""共有部分式の `let` 束縛（名前の owner と組み立て）。

責務は 2 つだけ:

* **名前空間** — 生成する束縛名が、その式に出てくるどの symbol とも衝突しない
  こと。衝突したら決定的に次の候補へ進む（hash だけで「衝突しない」と決めない）。
* **依存順の組み立て** — 束縛は必ず自分より前の束縛しか参照しないので、
  入れ子の `let` で並べれば依存順が構文で保証される。

名前は束縛の並び順（= 依存順）から決まるので決定的で、`id()` にも走査中の
偶然にも依存しない。`let` は SMT-LIB の scope 付きなので、同じ名前を使う 2 つの
項を 1 つの script に並べても干渉しない。
"""

from __future__ import annotations

import re
from typing import Dict, List, Sequence, Tuple

from scripts.function_tracer_pcode.core.render_output import CountingWriter
from scripts.function_tracer_pcode.core.render_plan import (
    BindingNamespace,
    RenderPlan,
    SharingPolicy,
    collect_reserved_symbols,
    write_expansion,
)


#: SMT-LIB の symbol（素の simple symbol と `|...|` の引用符付き）。
#: 演算子名や `bv1` のような語も拾うが、**多めに予約する側へ倒す**のは安全側。
SMT_SYMBOL_RE = re.compile(
    r"\|(?P<quoted>[^|\\]*)\|"
    r"|(?P<bare>[A-Za-z~!@$%^&*_\-+=<>.?/][A-Za-z0-9~!@$%^&*_\-+=<>.?/]*)"
)

#: 束縛名の接頭辞と形。引用符付きにして、素の symbol 規則の差を跨がないようにする。
SMT_BINDING_PREFIX = "?sh"
SMT_BINDING_TEMPLATE = "|{prefix}_{index}|"

#: SMT 描画の共有方針。小さい式は今までどおり展開する（既存の出力が理由なく
#: 変わらない）。`inline_max_bytes` は深い線形式で中間文字列が伸び続けるのを
#: 止めるためのもので、出力量の上限ではない（上限は `CountingWriter`）。
SMT_SHARING_POLICY = SharingPolicy(
    min_shared_bytes=32,
    inline_max_bytes=8192,
    min_shared_tree_nodes=2,
    reference_bytes_estimate=len(SMT_BINDING_TEMPLATE.format(prefix=SMT_BINDING_PREFIX, index=0)),
)

#: 出力 schema の名前。`let` 共有を入れた描画であることを consumer が言える。
SMT_RENDER_SCHEMA = "smt-shared-let-v1"


def smt_binding_namespace(plan: RenderPlan) -> BindingNamespace:
    """fragment に現れる symbol を避ける名前空間を作る。"""

    return BindingNamespace(
        collect_reserved_symbols(plan, pattern=SMT_SYMBOL_RE),
        prefix=SMT_BINDING_PREFIX,
        template=SMT_BINDING_TEMPLATE,
    )


def assign_binding_names(plan: RenderPlan, namespace: BindingNamespace) -> Dict[int, str]:
    """束縛する instance へ依存順で名前を割り当てる。"""

    names = namespace.allocate(len(plan.bound_order))
    return {index: names[position] for position, index in enumerate(plan.bound_order)}


def write_let_term(
    writer: CountingWriter,
    plan: RenderPlan,
    names: Dict[int, str],
) -> None:
    """`(let ((n body)) ...)` を依存順に入れ子で書き出す。

    書き出しは fragment を **流しながら**展開する（`write_expansion`）。途中で
    1 つの大きな文字列を組み立てないので、上限に達した時点で止まる。束縛が
    0 個なら root を展開しただけの文字列になる（既存の出力と同じ）。
    """

    order: Sequence[int] = plan.bound_order
    for index in order:
        writer.write("(let ((")
        writer.write(names[index])
        writer.write(" ")
        write_expansion(writer, plan, index, names)
        writer.write(")) ")
    write_expansion(writer, plan, plan.root_index, names)
    writer.write_repeated(")", len(order))


def binding_dependency_order_is_valid(plan: RenderPlan, names: Dict[int, str]) -> bool:
    """束縛が自分より前の束縛しか参照しないこと（test 用の検査）。"""

    defined: set = set()
    for index in plan.bound_order:
        for child in plan.instances[index].used_children:
            if child in names and child not in defined:
                return False
        defined.add(index)
    return True


def rendered_binding_names(text: str) -> Tuple[str, ...]:
    """text 中に現れる束縛名（`?sh` 接頭辞の引用符付き symbol）。"""

    found: List[str] = []
    for match in SMT_SYMBOL_RE.finditer(text):
        quoted = match.groupdict().get("quoted")
        if quoted is None:
            continue
        if quoted.startswith(SMT_BINDING_PREFIX) and f"|{quoted}|" not in found:
            found.append(f"|{quoted}|")
    return tuple(found)
