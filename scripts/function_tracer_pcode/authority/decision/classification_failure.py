# -*- coding: utf-8 -*-
"""分類に失敗した pair が残す診断（Issue #204 Scope 3）。

runner は分類（``canonical_result --classify-pair-log``）の後に、pair の一時 dir と process の
store（projection を含む）を消す。分類が失敗したとき、その理由を後から追えるのは pair の成果物
だけなので、分類器は消される前に次の 2 つを残す:

* **message**（pair-status の ``detail`` と pair log）: supervisor が projection に記録した判断
  （``error_code`` と child の rc）と、いま durable な evidence から同じ規則で読んだ判断の 1 行。
* **record**（``--classification-failure-output``、run dir の ``.runtime-metrics``）: 例外の
  detail、supervisor が公開した projection の写し、durable な evidence の読み（``next_step`` の
  判断と、それを決めた snapshot の事実）。

どちらも **判定の入力にしない**。読み方は supervisor と同じ ``terminal_driver.inspect``（読むだけ）
で、分類は従来どおり失敗する（pair-status は operational diagnostic のまま）。
"""

from __future__ import annotations

import dataclasses
import json
import os
import tempfile
from enum import Enum
from pathlib import Path
from typing import Any, Mapping, Optional

from scripts.function_tracer_pcode.authority.process.process_identity import (
    process_is_alive,
)
from scripts.function_tracer_pcode.authority.process.terminal_driver import (
    Inspection,
    inspect as inspect_terminal,
)

#: ``--classification-failure-output`` の file の schema
CLASSIFICATION_FAILURE_SCHEMA = "pair-classification-failure-v1"

#: 読みの失敗として扱う例外（store の file・署名・schema の不整合）
_READ_ERRORS = (OSError, ValueError, KeyError, TypeError)


class ProjectionNotAdoptedError(ValueError):
    """projection を durable な終端 authority として採用できない。

    ``durable`` は分類器が読んだ evidence の判断（``durable_reading`` の値）で、record に残す。
    """

    def __init__(self, message: str, *, durable: Mapping[str, Any]) -> None:
        super().__init__(message)
        self.durable = dict(durable)


def _plain(value: Any) -> Any:
    """snapshot の事実を JSON の値にする（dataclass / Enum / 集合 / Mapping を再帰で）。"""

    if isinstance(value, Enum):
        return value.value
    if dataclasses.is_dataclass(value) and not isinstance(value, type):
        return {item.name: _plain(getattr(value, item.name)) for item in dataclasses.fields(value)}
    if isinstance(value, Mapping):
        return {str(key): _plain(item) for key, item in value.items()}
    if isinstance(value, (set, frozenset)):
        return sorted(_plain(item) for item in value)
    if isinstance(value, (list, tuple)):
        return [_plain(item) for item in value]
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    return repr(value)


def reading_of(inspection: Inspection) -> dict:
    """``inspect`` の結果を、判断（step）と根拠（snapshot の事実）の dict にする。"""

    step = inspection.step
    return {
        "readable": True,
        "step": {
            "kind": step.kind.value,
            "invalid_code": getattr(step.invalid_code, "value", None),
            "detail": step.detail,
        },
        "snapshot": _plain(inspection.snapshot),
    }


def durable_reading(store: Any) -> dict:
    """supervisor と同じ規則で、durable な evidence がいま決める判断を読む（書かない）。"""

    try:
        inspection = inspect_terminal(store, mode=None, process_alive=process_is_alive)
    except _READ_ERRORS as exc:
        return {"readable": False, "error": f"{type(exc).__name__}: {exc}"[:500]}
    return reading_of(inspection)


def describe(reading: Mapping[str, Any]) -> str:
    """``durable_reading`` の 1 行（message 用）。"""

    if not reading.get("readable"):
        return f"unreadable ({reading.get('error')})"
    step = reading["step"]
    return f"{step['kind']} {step['invalid_code']} {step['detail']}"[:500]


def _projection_copy(path: Optional[Path]) -> dict:
    if path is None:
        return {"readable": False, "error": "no projection path"}
    try:
        return {"readable": True, "value": json.loads(Path(path).read_text(encoding="utf-8"))}
    except (OSError, ValueError) as exc:
        return {"readable": False, "error": f"{type(exc).__name__}: {exc}"[:500]}


def failure_record(
    *, detail: str, projection_path: Optional[Path], durable: Optional[Mapping[str, Any]],
) -> dict:
    """分類の失敗 1 件の record。``durable`` は例外が運んだ読み（無ければ未読と書く）。"""

    return {
        "schema": CLASSIFICATION_FAILURE_SCHEMA,
        "detail": detail,
        "projection": _projection_copy(projection_path),
        "durable": (
            dict(durable) if durable is not None
            else {"readable": False, "error": "classification failed before the store was read"}
        ),
    }


def write_failure_record(path: Path, record: Mapping[str, Any]) -> None:
    """record を atomic に書く（途中の file を読ませない）。失敗は ``OSError`` で返す。"""

    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{target.name}.", dir=str(target.parent))
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            json.dump(record, stream, sort_keys=True, indent=1)
            stream.write("\n")
        os.replace(temporary, target)
    except OSError:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def recorded_child_returncode(path: Path) -> Optional[int]:
    """record に写した projection が記録した child の rc（無ければ ``None``）。

    分類に失敗した pair は署名済みの status を持たないので、runtime receipt に残す child の
    終了は record からしか読めない。**rc だけを返し、原因を推定しない**（SIGKILL の -9 は
    外部からの kill を示すだけで、OOM かどうかは cgroup の記録と突き合わせないと分からない）。
    """

    try:
        record = json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    projection = record.get("projection") if isinstance(record, Mapping) else None
    if not isinstance(projection, Mapping) or projection.get("readable") is not True:
        return None
    value = projection.get("value")
    if not isinstance(value, Mapping):
        return None
    returncode = value.get("child_returncode")
    return returncode if type(returncode) is int else None


def main(arguments: Optional[list] = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--print-child-returncode", required=True,
                        help="record の path。rc が読めなければ '-' を出す")
    args = parser.parse_args(arguments)
    returncode = recorded_child_returncode(Path(args.print_child_returncode))
    print("-" if returncode is None else returncode)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
