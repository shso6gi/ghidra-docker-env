# -*- coding: utf-8 -*-
"""SMT 描画の **文脈**（共有可否を決める側の owner）。

同じ意味 node でも、ここに入っている値が違えば描画結果が違う。だから共有
（`let` の束縛）の単位は node ではなく `(node, SmtRenderContext)`。文脈を
無視して node identity だけで束ねると、別の幅・別の符号拡張で描いた式を
同じ名前にしてしまい、SMT の意味が変わる。

文脈に入れる条件は 1 つだけ: **その値が描画結果を変えるか**。

* `prefer_signed_arithmetic` — 幅を広げるときに sign / zero extend を選ぶ
* `address_context` — address として描くか（global object の base symbol 化）
* `float_mode` — `fp` 理論を使うか UF に落とすか
* `symbol_mapping_key` — parameter / variable / CALL 名の対応表の identity

対応表そのものではなく identity を持つのは、hash 可能な小さい key にするため。
対応表の中身は描画 1 回のあいだ固定で、driver の closure 側が持つ。

この型は renderer 内部に閉じる。`StructuralIdentity` / `SolverQueryIdentity` /
`RewriteIdentity` へ混ぜない（描画の都合で意味の一致条件を動かさない）。
"""

from __future__ import annotations

from typing import Any, Mapping, NamedTuple, Optional


class SmtRenderContext(NamedTuple):
    """描画結果を変える文脈。共有 key の片側。"""

    prefer_signed_arithmetic: bool = False
    address_context: bool = False
    float_mode: str = "uf"
    symbol_mapping_key: Optional[int] = None

    def derive(
        self,
        *,
        prefer_signed_arithmetic: Optional[bool] = None,
        address_context: Optional[bool] = None,
    ) -> "SmtRenderContext":
        """子を描くときの文脈。指定しなかった軸は引き継ぐ。

        `float_mode` と `symbol_mapping_key` は 1 回の描画のあいだ変わらない
        （変える呼び出し側が無い）。変える必要が出たらここに引数を足す。
        """

        if prefer_signed_arithmetic is None and address_context is None:
            return self
        return SmtRenderContext(
            prefer_signed_arithmetic=(
                self.prefer_signed_arithmetic
                if prefer_signed_arithmetic is None
                else bool(prefer_signed_arithmetic)
            ),
            address_context=(
                self.address_context if address_context is None else bool(address_context)
            ),
            float_mode=self.float_mode,
            symbol_mapping_key=self.symbol_mapping_key,
        )


def build_smt_render_context(
    *,
    prefer_signed_arithmetic: Any = False,
    address_context: Any = False,
    float_mode: str = "uf",
    symbol_name_mapping: Optional[Mapping[str, str]] = None,
) -> SmtRenderContext:
    """呼び出し側の引数から文脈を作る。

    `address_context` は歴史的に `None` / `False` / `True` が来る（真偽としてしか
    読まれない）。文脈 key にそのまま入れると `None` と `False` が別の共有単位に
    なるので、ここで真偽へ正規化する。
    """

    return SmtRenderContext(
        prefer_signed_arithmetic=bool(prefer_signed_arithmetic),
        address_context=bool(address_context),
        float_mode=str(float_mode),
        symbol_mapping_key=None if symbol_name_mapping is None else id(symbol_name_mapping),
    )
