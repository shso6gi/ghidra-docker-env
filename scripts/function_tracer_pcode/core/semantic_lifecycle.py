# -*- coding: utf-8 -*-
"""意味値の一生（Issue #22 PR-22-B）。**状態を持つのはここだけ**。

意味値（`Expression` / `Condition`）は 3 つの状態を順に通る:

.. code-block:: text

    CONSTRUCTION   組み立て・精緻化の途中。意味 field を書き換えてよい
         |
         | freeze / validation（`core/semantic_freeze.freeze_expression`）
         v
    VALIDATED      graph に閉路が無いことを確かめ、生 object を投影し終えた
                   immutable snapshot。**意味は確定したが、作った側はまだ
                   「完成した」と言っていない**
         |
         | publication（`core/semantic_freeze.publish` — producer だけが呼ぶ）
         v
    PUBLISHED      producer が「この値はもう変わらない」と宣言した。
                   solver consumer が受け取ってよいのはこれだけ

なぜ 2 つに分けるか: 「immutable だから solver へ渡してよい」と「producer が
完成を宣言したから solver へ渡してよい」は別の話。identity（candidate hash /
完全比較 / digest）は計算のために graph の健全性を要求するので、未凍結の入力を
その場で validated にする。そこで 1 bit しか持たないと、

.. code-block:: python

    expr = build_expression()
    candidate_hash(expr)   # identity の都合で validated になる
    expr.to_smt()          # producer は何も宣言していないのに通ってしまう

という迂回ができてしまい、「construction/refinement → producer publication →
solver consumption」という契約が identity API 経由で破れる。

**状態の表し方**: 意味値 1 つあたり `__dict__` の bool 2 つ（`_frozen` /
`_published`）。node 数が数百万になり得るので、状態 object を 1 つずつ持たせない。
その代わり **読み書きの規則をこの module へ集める** ので、状態遷移を知っている
場所は 1 つで済む。`_published` は単独では意味を持たない（`is_published` は
両方の bit を見る）ので、「published は validated を含む」は表現の側で閉じている。

**遷移は単調**。逆行する API は置かない。値を変えたいときは新しい値を作る
（`derive_with` / `clone_with` / `copy` / `deepcopy`）。

**複製・派生は公開の権限を持たない**。新しい値は CONSTRUCTION から始まり、
`NON_INHERITED_FIELDS` に挙げた field を 1 つも引き継がない。**これから仕上げる
材料だから**であって、「派生値は公開しない」という規則ではない:
`Condition.negate()` は仕上げる余地の無い派生（条件には refinement 段階が無い）
なので、公開済みの条件からは公開済みで始まる。**その 1 つだけが例外**で、
理由と closure の保たれ方は `Condition.negate()` の docstring にある。

引き継がない規則を carrier 側の書き忘れに頼らないため、「新しい値が持ってよい
field か」の判定はこの module が答える（`inherited_by_a_new_value`）。汎用の
copy 機構は置かない: 複製の作り方（何を deep に、何を共有するか）は値の型が
決めることで、**lifecycle が決めるのは「何を引き継がないか」だけ**。

.. code-block:: text

    値の型が決める            lifecycle が決める
    ---------------------     ------------------------------
    どの field を deep copy   状態と派生値を引き継がない
    どう再構築するか          （`NON_INHERITED_FIELDS`）
    LEGACY 表現の schema      表現が読む field ごとの不変性の規則
                              （`*_SERIALIZATION_INPUTS`）

**直列化の不変性（Issue #219 C-RS2）**: VALIDATED な値のうち
`serialization_closed(value)` が真のものは、LEGACY 表現（`to_dict()` / snapshot の
木）が **不変な状態だけの関数** になる。PR-22-B の isolation 契約（凍結後に生 object が
変わっても structural key・solver query identity・SMT・幅は動かない）を、LEGACY 表現へ
広げたもの。cache のための特別規則ではなく、「検証済みの値の直列化が何に依存するか」
という lifecycle の契約で、答えは凍結時に 1 回だけ決まる:

.. code-block:: text

    表現が読む field           closed の規則（凍結時に子から上へ畳む）
    ------------------------   ---------------------------------------------
    scalar の意味 field        不変な scalar（None / bool / int / float / str / bytes / enum）
    value                      不変な scalar・その tuple、PHI なら PhiBranch の tuple
                               （branch の条件と値がどちらも closed）
    operands / 条件の式        子がすべて closed
    storage_info               凍結時に写した payload から描く（写せなければ closed でない）
    runtime_ref                深く不変（frozen dataclass・tuple・scalar・closed な式だけ）

表（`EXPRESSION_SERIALIZATION_INPUTS` / `CONDITION_SERIALIZATION_INPUTS`）に無い field を
表現が読むようになると、closed の判定がその field を見落とす。静的な監査
（`tests/unit/test_issue219_serialization_closed.py` の T-A5）がそれを落とす。
closed でない値について、この契約は何も約束しない（表現は従来どおり生 object を読み得る）。

前提（明示する）: frozen dataclass の LEGACY 表現（record なら `json_items`）は、その
field の値だけの関数であること。runtime ref の値 object の契約で、package の runtime ref
が frozen であることは `tests/unit/test_architecture_boundaries.py` が固定している
（`display_name()` のような field からの導出はこの前提の内側）。field 以外の instance
状態を持つ object は、凍結時の判定が closed にしない。
"""

from __future__ import annotations

from enum import Enum, IntEnum
from types import MappingProxyType
from typing import Any, Dict, Mapping

from scripts.function_tracer_pcode.core import live_values


class SemanticLifecycle(IntEnum):
    """意味値が今どの段階に居るか。

    `IntEnum` にしてあるのは「後戻りしない」を `>=` で書けるようにするため
    （`state >= SemanticLifecycle.VALIDATED` が「検証は済んでいる」になる）。
    """

    CONSTRUCTION = 0
    VALIDATED = 1
    PUBLISHED = 2


#: 状態そのものを表す field。複製（`clone_with` / `copy` / `deepcopy`）はこれを
#: **引き継がない**: 複製は「これから仕上げる材料」なので、元の値の宣言を名乗れない。
LIFECYCLE_STATE_FIELDS = ("_frozen", "_published")

#: 検証のときに確定する派生値の field。状態そのものではないが、**状態と対に
#: なってしか意味を持たない**: VALIDATED でない値に載った snapshot / digest は
#: 「まだ確かめていない graph を投影した何か」でしかない。だから状態と一緒に
#: 引き継がない。名前の一覧をここに置くのは、`core/semantic_freeze` が作る
#: 派生値と、複製が捨てる field が 1 つの表から出るようにするため。
DERIVED_STATE_FIELDS = (
    "_snapshot",
    "_local_payload",
    "_structural_hash",
    "_equivalence_digest",
    "_tree_size",
    "_identity_complete",
    # 直列化の不変性（Issue #219）: 凍結時に写した storage の LEGACY 表現と、
    # 「LEGACY 表現が不変な状態だけの関数か」の答え
    "_storage_payload",
    "_serialization_closed",
)

#: **新しい値へ引き継いではいけない field**（状態 + 状態から導いた値）。
NON_INHERITED_FIELDS = LIFECYCLE_STATE_FIELDS + DERIVED_STATE_FIELDS


def inherited_by_a_new_value(name: str) -> bool:
    """`name` を新しい値（複製・派生）の `__dict__` へ持ち越してよいか。

    複製・派生の実装（`Expression.__copy__` / `__deepcopy__` / `clone_with`、
    `Condition.__copy__` / `__deepcopy__`）が **唯一参照する規則**。各 call site
    が「どの field を落とすか」を自前で列挙すると、状態や派生値が 1 つ増えた
    ときに片方だけ直って、公開済みを名乗る半端な複製ができる。
    """

    return name not in NON_INHERITED_FIELDS


def state_of(fields: Dict[str, Any]) -> SemanticLifecycle:
    """`__dict__` から状態を読む。

    `_published` は単独では状態を作れない — validated を経ずに published には
    ならない、という不変条件をここで閉じている。
    """

    # `__dict__` は owner の API で読む（出力の入口から live な値の `__dict__` が渡る）
    if not _flag(live_values.lookup(fields, "_frozen", False)):
        return SemanticLifecycle.CONSTRUCTION
    if _flag(live_values.lookup(fields, "_published", False)):
        return SemanticLifecycle.PUBLISHED
    return SemanticLifecycle.VALIDATED


def _flag(value: Any) -> bool:
    """状態の bit の真偽（`mark_*` が書くのは `True`。それ以外の値は owner の API で読む）。"""

    if value is True:
        return True
    if value is False or value is None:
        return False
    return live_values.as_bool(value)


def mark_validated(fields: Dict[str, Any]) -> None:
    """検証・凍結が終わった値として印を付ける（公開はしない）。"""

    fields["_frozen"] = True


def mark_published(fields: Dict[str, Any]) -> None:
    """producer の宣言として印を付ける。

    validated を経ていない値へ付けても `state_of` は PUBLISHED を返さない
    （上の不変条件）。呼ぶのは `core/semantic_freeze` の公開境界だけ。
    """

    fields["_published"] = True


def lifecycle_of(value: Any) -> SemanticLifecycle:
    """意味値の状態。`Expression` / `Condition` にだけ使う。

    任意の object には使わない: 記録再生中の Ghidra proxy に属性を尋ねると、
    記録済みの観測列に無い問い合わせを作ってしまう。呼ぶ側が `isinstance` で
    種別を確かめてから渡すこと。
    """

    # instance の `__dict__` の値だけを読む（`__getattr__` / descriptor を呼ばない。`__dict__`
    # を持たない値は bit も持たないので CONSTRUCTION）。規則は `state_of` と同じ
    if not _flag(live_values.instance_state(value, "_frozen", False)):
        return SemanticLifecycle.CONSTRUCTION
    if _flag(live_values.instance_state(value, "_published", False)):
        return SemanticLifecycle.PUBLISHED
    return SemanticLifecycle.VALIDATED


def is_validated(value: Any) -> bool:
    """検証済み（immutable snapshot 確定済み）か。公開済みかは問わない。"""

    return lifecycle_of(value) >= SemanticLifecycle.VALIDATED


def is_published(value: Any) -> bool:
    """producer が完成を宣言済みか。solver consumer が要求するのはこれ。"""

    return lifecycle_of(value) is SemanticLifecycle.PUBLISHED


# ---------------------------------------------------------------------------
# 直列化の不変性（Issue #219 C-RS2）
# ---------------------------------------------------------------------------


class SerializationInput(Enum):
    """LEGACY 表現が読む field の種類。種類ごとに closed の規則が 1 つある。

    規則そのもの（どう確かめるか）は `core/semantic_freeze.SERIALIZATION_CLOSURE_RULES`
    が種類ごとに 1 つ持つ。ここは「どの field がどの種類か」だけを決める。
    """

    #: 不変な scalar であること
    SCALAR = "scalar"
    #: 不変な scalar / その tuple。PHI なら `PhiBranch` の tuple で、条件と値が closed
    VALUE = "value"
    #: 子の列（tuple）。子がすべて closed
    OPERANDS = "operands"
    #: 子 1 つ（条件の式）。その子が closed
    EXPRESSION = "expression"
    #: 凍結時に写した payload から描く（写せたこと）
    STORAGE = "storage"
    #: 深く不変な runtime ref（中の式・条件も closed）
    RUNTIME_REF = "runtime_ref"


#: `Expression` の LEGACY 表現（`Expression._to_dict_active`）が読む field と、その種類。
#: 表現が field を 1 つ読むようにしたら、ここへ 1 行足す（足さなければ T-A5 が落ちる）。
EXPRESSION_SERIALIZATION_INPUTS: Mapping[str, SerializationInput] = MappingProxyType({
    "expr_type": SerializationInput.SCALAR,
    "value": SerializationInput.VALUE,
    "operator": SerializationInput.SCALAR,
    "name": SerializationInput.SCALAR,
    "data_type": SerializationInput.SCALAR,
    "size": SerializationInput.SCALAR,
    "operands": SerializationInput.OPERANDS,
    "storage_info": SerializationInput.STORAGE,
    "read_order_key": SerializationInput.SCALAR,
    "runtime_ref": SerializationInput.RUNTIME_REF,
    "opcode": SerializationInput.SCALAR,
})

#: `Condition` の LEGACY 表現（`Condition.json_items` と、PHI の branch の描画）が読む field。
CONDITION_SERIALIZATION_INPUTS: Mapping[str, SerializationInput] = MappingProxyType({
    "expression": SerializationInput.EXPRESSION,
    "negated": SerializationInput.SCALAR,
})


def serialization_closed(value: Any) -> bool:
    """`value` の LEGACY 表現が、不変な状態だけの関数か（C-RS2 の読み口）。

    VALIDATED 以上で、凍結時に `core/semantic_freeze` が closed と決めた値だけが真。
    `Expression` / `Condition` にだけ使う（`lifecycle_of` と同じく instance の
    `__dict__` だけを読み、`__getattr__` を呼ばない）。答えは凍結時に 1 回だけ決まり、
    ここは読むだけで計算しない。
    """

    if lifecycle_of(value) < SemanticLifecycle.VALIDATED:
        return False
    return live_values.instance_state(value, "_serialization_closed", False) is True
