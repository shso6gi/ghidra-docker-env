# -*- coding: utf-8 -*-
"""Issue #165 Phase 0: 実装前 gate G1〜G3 を実 child の store で確かめる probe。

計画 v5 §10 の gate を、production の store / factory / 分類器と PR #193 の
harness（実 worker child）で確かめる。広い store 変更（terminal 状態機械）
より前に、次の 3 つが成り立つかだけを見る。

* **G1 E receipt**: supervisor が wait で取った int rc を
  ``SupervisorChildExitReceipt`` として supervisor role で発行し、
  永続化 → 読み直し → 署名 / schema / launch join の検証 → その rc で
  canonical resolved receipt を作り、production の分類器（CLI join を含む）
  が受理する。worker role の署名で E を名乗る receipt は拒否する。rc の無い
  restart は rc を作らない（E 無しでは CLI join を組めない）。
* **G2 archive adapter**: 実 child が作った 2 chain（history 1 + live 1）の
  live chain を A で固定し、member を 0..N 個動かした各分割配置から
  ``inspect_union`` + 意味検証 adapter で member 集合 / digest / role /
  stage を検証して移動を再開できる。改ざん・両側欠落・history の余分な
  file・A 無しの部分 archive は拒否する。
* **G3 ACTIVE error stage**: ``DURING_DECOMPILATION`` を ERROR の issuer が
  受理するか（封の語彙にあるか）。対照として ``NON_DECOMPILATION`` の ERROR
  bundle が分類器 → pair-status 封 → CLI（``canonical_result`` の main）まで
  通るか。

出力は 1 行 1 check の JSON。``passed`` は「gate の成立条件どおりに振る舞った
か」で、G3 の DURING_DECOMPILATION 拒否は「gate 不成立」の事実として
``gate_satisfied: false`` を付けて出す。

    python3 -B -m scripts.function_tracer_pcode.tests.fixtures.issue165.phase0_gates

Phase 0 では、supervisor がまだ E を書かない段階（terminal evidence 層と
archive だけを足した段階）で同じ検査をした。この file は PR の head で再現
できる形にしてある: E は production の supervisor が書いたものを読み、G2 は
E が durable になった直後で supervisor を落として live chain を残した store を
使う。
"""

from __future__ import annotations

import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from typing import Any

from scripts.function_tracer_pcode.authority.process import child_exit as ce
from scripts.function_tracer_pcode.tests.unit._supervisor_support import (
    REPO_ROOT,
    Checkpoint,
    ChildScript,
    Envelope,
    Exit,
    FileBoundary,
    classify,
    crash_at,
    run_supervisor,
    supervisor_case,
)

def _emit(gate: str, check: str, passed: bool, **detail: Any) -> None:
    print(json.dumps({"gate": gate, "check": check, "passed": passed, **detail},
                     sort_keys=True), flush=True)


def _factory(case: Any) -> Any:
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        ProcessSupervisorAuthorityFactory,
    )

    config = case.config
    return ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id=config.supervisor_signing_key_id,
        supervisor_signing_key=Path(config.supervisor_signing_key_file).read_bytes(),
        worker_signing_key_id=config.worker_signing_key_id,
        worker_signing_key=Path(config.worker_signing_key_file).read_bytes(),
    )


def _store(case: Any, factory: Any) -> Any:
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        DurableCheckpointStore,
    )

    return DurableCheckpointStore(
        case.config.checkpoint_root, factory, case.config.execution_nonce,
    )


# ---------------------------------------------------------------------------
# G1
# ---------------------------------------------------------------------------


def gate_g1(directory: Path) -> None:
    from scripts.function_tracer_pcode.authority.contracts import (
        CLI_EXIT_CODE_BY_OUTCOME,
        Outcome,
    )
    from scripts.function_tracer_pcode.authority.process import terminal_evidence as te

    script = ChildScript((Checkpoint(), Envelope("UNKNOWN"), Exit()))
    with supervisor_case(directory, script, allow_child_exit_resolution=True) as case:
        run = run_supervisor(case)
        # 実測 rc: supervisor が Popen.wait / poll で取った値（projection に出る）。
        measured = run.projection["child_returncode"]
        _emit("G1", "measured_rc_is_the_cli_code", measured == CLI_EXIT_CODE_BY_OUTCOME[Outcome.UNKNOWN],
              measured=measured)
        supervisor_factory = _factory(case)
        store = _store(case, supervisor_factory)
        launch = supervisor_factory.decode(json.loads((store.directory / "launch.json").read_text()))
        path = store.directory / te.CHILD_EXIT_FILENAME
        anchor = te.child_exit_anchor(supervisor_factory.decode(json.loads(path.read_text())))
        # 読み直し: 署名（supervisor role）→ schema / launch join。
        reread = supervisor_factory.decode(json.loads(path.read_text()))
        te.validate_child_exit(reread, launch, None)
        _emit("G1", "issue_persist_reread_validate",
              reread.payload["child_returncode"] == measured
              and reread.signing_key_id == case.keys.supervisor_key_id,
              kind=reread.receipt_kind, signing_key_id=reread.signing_key_id)
        # E の kind は supervisor role の署名でだけ受理する（worker role は拒否）。
        forged = supervisor_factory._sign(
            reread.receipt_kind, dict(reread.payload), signer_role="worker",
        )
        try:
            supervisor_factory.validate(forged)
        except ValueError as exc:
            _emit("G1", "worker_role_cannot_claim_E", True, error=str(exc))
        else:
            _emit("G1", "worker_role_cannot_claim_E", False)
        # 改ざん: rc を 1 つずらして digest を計算し直しても署名で拒否。
        tampered = json.loads(path.read_text())
        tampered["payload"]["child_returncode"] = 0
        try:
            supervisor_factory.decode(tampered)
        except ValueError as exc:
            _emit("G1", "tampered_E_is_rejected", True, error=str(exc))
        else:
            _emit("G1", "tampered_E_is_rejected", False)
        # E の rc から canonical resolved receipt を作り直し、分類器が受理する
        # （CLI join: receipt rc == projection rc == CLI_EXIT_MATRIX[outcome]）。
        stored = json.loads((store.directory / "canonical-resolved-receipt.json").read_text())
        _emit("G1", "existing_receipt_rc_equals_E_rc",
              stored["child_returncode"] == reread.payload["child_returncode"],
              receipt_rc=stored["child_returncode"], e_rc=reread.payload["child_returncode"])
        # store を probe が書き足したので harness の ``classify(run)`` は
        # （正しく）stale として拒否する。同じ production 分類器を直接呼ぶ。
        classified = classify(run)
        _emit("G1", "canonical_cli_join_classifies",
              classified["classification_valid"] is True
              and classified["child_returncode"] == reread.payload["child_returncode"],
              canonical_outcome=classified["canonical_outcome"])
        # E が無い restart は rc を持たない: 同じ join を rc=None で組めない。
        try:
            ce.validate_durable_child_returncode_observation(
                child_exit_disposition="EXIT_CODE_2", child_returncode=None,
                observation_kind=ce.LIVE_PROCESS_WAIT,
            )
        except ValueError as exc:
            _emit("G1", "no_rc_without_E", True, error=str(exc))
        else:
            _emit("G1", "no_rc_without_E", False)
        # 自然終了の E は signal / deadline を名乗れない。
        try:
            te.child_exit_payload(
                launch, deadline=None, child_returncode=-15,
                child_exit_disposition="SIGTERM_AFTER_DEADLINE",
                signal_actions=(te.SignalAction("SIGTERM", ce.SIGNAL_SENT),),
                envelope=te.EnvelopeObservation(False, None), anchor=anchor,
                exit_mode=te.EXIT_MODE_CANONICAL_RESULT_REQUIRED,
            )
        except te.TerminalEvidenceInvalid as exc:
            _emit("G1", "natural_E_cannot_claim_signal_death", True, error=str(exc))
        else:
            _emit("G1", "natural_E_cannot_claim_signal_death", False)


# ---------------------------------------------------------------------------
# G2
# ---------------------------------------------------------------------------


def _two_chain_case(directory: Path):
    """2 checkpoint の child（history 1 + live 1）。supervisor は E の直後で落とす。"""

    script = ChildScript((Checkpoint(), Checkpoint(), Exit(1)))
    return supervisor_case(directory, script)


def _build_manifest(store: Any, factory: Any, launch: Any, exit_receipt: Any) -> Any:
    from scripts.function_tracer_pcode.authority.process import checkpoint_archive as ca
    from scripts.function_tracer_pcode.authority.process import terminal_evidence as te

    present = ca.live_chain_members(store.directory)
    chain = store.validate_resolved_chain_members(ca.directory_reader(store.directory), present=present)
    destination = ca.history_destination(chain.resolved.receipt_digest)
    roles = {spec.name: spec.role for spec in ca.CHAIN_MEMBERS}
    members = tuple(
        te.ArchiveMember(
            name, roles[name], len((store.directory / name).read_bytes()),
            ca.sha256_bytes((store.directory / name).read_bytes()),
        )
        for name in present
    )
    payload = te.archive_payload(
        launch, child_exit=exit_receipt,
        checkpoint_receipt_digest=chain.checkpoint.receipt_digest,
        resolved_state_receipt_digest=chain.resolved.receipt_digest,
        anchor_state=chain.resolved.payload["state"],
        error_kind="operational_authority_invalid", error_stage="NON_DECOMPILATION",
        destination=destination, members=members,
    )
    return factory.issue_terminal_evidence(te.ARCHIVE_MANIFEST_KIND, payload)


def _resume_archive(store: Any, factory: Any, launch: Any, exit_receipt: Any, manifest_path: Path) -> dict:
    """A と union だけから再開する（live の state.json には頼らない）。"""

    from scripts.function_tracer_pcode.authority.process import checkpoint_archive as ca
    from scripts.function_tracer_pcode.authority.process import terminal_evidence as te

    manifest = factory.decode(json.loads(manifest_path.read_text()))
    te.validate_archive(manifest, launch, exit_receipt)
    members = te.archive_members(manifest)
    destination = manifest.payload["destination"]
    inspection = ca.inspect_union(store.directory, members, destination)
    chain = store.validate_resolved_chain_members(
        ca.union_reader(store.directory, destination, inspection),
        present=tuple(member.name for member in members),
    )
    if (
        chain.resolved.receipt_digest != manifest.payload["resolved_state_receipt_digest"]
        or chain.checkpoint.receipt_digest != manifest.payload["checkpoint_receipt_digest"]
    ):
        raise ca.ArchiveConflict("union chain differs from the manifest")
    ca.move_remaining(store.directory, destination, inspection)
    final = ca.inspect_union(store.directory, members, destination)
    return {
        "stage": manifest.payload["error_stage"],
        "complete": final.complete,
        "live_members_left": list(ca.live_chain_members(store.directory)),
    }


def gate_g2(directory: Path) -> None:
    from scripts.function_tracer_pcode.authority.process import checkpoint_archive as ca
    from scripts.function_tracer_pcode.authority.process import terminal_evidence as te

    template = directory / "template"
    with _two_chain_case(template) as case:
        run = run_supervisor(case, faults=(crash_at(FileBoundary(te.CHILD_EXIT_FILENAME)),))
        histories = sorted({f.split("/")[1] for f in run.store.files if f.startswith("checkpoint-history/")})
        _emit("G2", "real_child_left_history_and_live_chain",
              len(histories) == 1 and run.store.state == "RESOLVED" and run.crashed,
              history_chains=len(histories), live_state=run.store.state)
        config = case.config
    members_n = None
    for moved in range(0, len(ca.CHAIN_MEMBERS)):
        work = directory / f"split-{moved}"
        shutil.copytree(template, work, ignore=shutil.ignore_patterns("harness"))
        from scripts.function_tracer_pcode.authority.process.supervisor import (
            DurableCheckpointStore,
            ProcessSupervisorAuthorityFactory,
        )

        factory = ProcessSupervisorAuthorityFactory(
            supervisor_signing_key_id=config.supervisor_signing_key_id,
            supervisor_signing_key=(work / "keys" / "supervisor.key").read_bytes(),
            worker_signing_key_id=config.worker_signing_key_id,
            worker_signing_key=(work / "keys" / "worker.key").read_bytes(),
        )
        store = DurableCheckpointStore(work / "checkpoints", factory, config.execution_nonce)
        launch = factory.decode(json.loads((store.directory / "launch.json").read_text()))
        exit_receipt = factory.decode(
            json.loads((store.directory / te.CHILD_EXIT_FILENAME).read_text())
        )
        manifest = _build_manifest(store, factory, launch, exit_receipt)
        members_n = len(manifest.payload["members"])
        manifest_path = store.directory / te.ARCHIVE_INTENT_FILENAME
        store._atomic_write(manifest_path, store._bytes(manifest))
        destination = manifest.payload["destination"]
        # 最初の ``moved`` 個だけ移した分割配置（crash 境界の再現）。
        for member in te.archive_members(manifest)[:moved]:
            ca.move_member(store.directory, destination, member.name)
        if moved > members_n:
            continue
        try:
            result = _resume_archive(store, factory, launch, exit_receipt, manifest_path)
        except (ValueError, OSError) as exc:
            _emit("G2", f"resume_after_{moved}_moved", False, error=f"{type(exc).__name__}: {exc}")
            continue
        _emit("G2", f"resume_after_{moved}_moved",
              result["complete"] and not result["live_members_left"] and result["stage"] == "NON_DECOMPILATION",
              **result)
        if moved == 3:
            _g2_negative(store, factory, launch, exit_receipt, manifest_path, manifest)
    _emit("G2", "manifest_member_count", members_n == 6, members=members_n)


def _g2_negative(store: Any, factory: Any, launch: Any, exit_receipt: Any,
                 manifest_path: Path, manifest: Any) -> None:
    """完了した archive に対して、壊れた配置を 1 つずつ作り拒否されることを見る。"""

    from scripts.function_tracer_pcode.authority.process import checkpoint_archive as ca
    from scripts.function_tracer_pcode.authority.process import terminal_evidence as te

    members = te.archive_members(manifest)
    destination = manifest.payload["destination"]
    history = store.directory / destination

    def expect_conflict(check: str, mutate, restore) -> None:
        mutate()
        try:
            ca.inspect_union(store.directory, members, destination)
        except ca.ArchiveConflict as exc:
            _emit("G2", check, True, error=str(exc))
        else:
            _emit("G2", check, False)
        finally:
            restore()

    target = history / "ready.json"
    original = target.read_bytes()
    expect_conflict(
        "tampered_member_rejected",
        lambda: target.write_bytes(original.replace(b"\"", b"'", 1)),
        lambda: target.write_bytes(original),
    )
    expect_conflict(
        "both_sides_missing_rejected",
        lambda: target.rename(store.directory / ".hidden-ready"),
        lambda: (store.directory / ".hidden-ready").rename(target),
    )
    extra = history / "stray.json"
    expect_conflict(
        "extra_history_file_rejected",
        lambda: extra.write_text("{}"),
        lambda: extra.unlink(),
    )
    # manifest 改ざん（member digest を書き換え）→ 署名で拒否。
    body = json.loads(manifest_path.read_text())
    body["payload"]["members"][0]["sha256"] = "0" * 64
    try:
        factory.decode(body)
    except ValueError as exc:
        _emit("G2", "tampered_manifest_rejected", True, error=str(exc))
    else:
        _emit("G2", "tampered_manifest_rejected", False)
    # 別 E（rc 違い）に対する A は join しない。
    other = factory.issue_terminal_evidence(
        te.CHILD_EXIT_RECEIPT_KIND,
        {**exit_receipt.payload, "child_returncode": 7,
         "child_exit_disposition": ce.natural_exit_disposition(7)},
    )
    try:
        te.validate_archive(factory.decode(json.loads(manifest_path.read_text())), launch, other)
    except te.TerminalEvidenceInvalid as exc:
        _emit("G2", "manifest_bound_to_its_E", True, error=str(exc))
    else:
        _emit("G2", "manifest_bound_to_its_E", False)


# ---------------------------------------------------------------------------
# G3
# ---------------------------------------------------------------------------


def gate_g3(directory: Path) -> None:
    from scripts.function_tracer_pcode.authority.process import supervisor as sv
    from scripts.function_tracer_pcode.authority.contracts import authority_digest

    from scripts.function_tracer_pcode.authority.process.checkpoint_vocabulary import (
        SUPERVISOR_DEADLINE_STAGES,
    )

    _emit("G3", "sealed_stage_vocabulary", True, stages=sorted(SUPERVISOR_DEADLINE_STAGES))
    with _two_chain_case(directory / "g3") as case:
        run = run_supervisor(case)
        supervisor_factory = _factory(case)
        store = _store(case, supervisor_factory)
        launch = supervisor_factory.decode(json.loads((store.directory / "launch.json").read_text()))
        # issuer が DURING_DECOMPILATION を受理するか（語彙に無ければ拒否）。
        try:
            supervisor_factory._issue_operational_error(
                launch=launch, error_kind="operational_authority_invalid",
                deadline_stage="DURING_DECOMPILATION", child_exit_disposition="EXIT_CODE_1",
                _capability=sv._OPERATIONAL_ERROR_CAPABILITY_TOKEN,
            )
        except ValueError as exc:
            _emit("G3", "during_decompilation_accepted_by_issuer", True,
                  gate_satisfied=False, error=str(exc))
        else:
            _emit("G3", "during_decompilation_accepted_by_issuer", True, gate_satisfied=True)
        # 対照: 閉じた chain を A で退避した後の NON_DECOMPILATION ERROR（supervisor が作る）。
        error = json.loads((store.directory / "operational-error.json").read_text())
        _emit("G3", "supervisor_issued_non_decompilation_error",
              run.projection["status"] == "ERROR"
              and error["payload"]["deadline_stage"] == "NON_DECOMPILATION",
              status=run.projection["status"], stage=error["payload"]["deadline_stage"])
        from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
            generate_pair_status_keypair,
        )
        private_key = directory / "pair-status.key"
        public_key = directory / "pair-status-verification-key.json"
        generate_pair_status_keypair(private_key, public_key)
        target = directory / "target.json"
        target_body = {
            "schema": "eqbench-pair-execution-target-v1",
            "authority_kind": "PairExecutionTargetReceipt",
            **{name: f"issue165-{name}" for name in (
                "sample_identity", "output_sample_relative_path", "function_name",
                "left_binary_id", "right_binary_id", "source_path", "source_sha256",
                "left_binary_path", "left_binary_sha256", "right_binary_path",
                "right_binary_sha256", "analysis_source_digest", "analysis_config_digest",
            )},
        }
        target.write_text(json.dumps({**target_body, "target_digest": authority_digest(target_body)}))
        config = case.config
        cli = subprocess.run(
            [sys.executable, "-B", "-m",
             "scripts.function_tracer_pcode.authority.decision.canonical_result",
             "--classify-pair-log", str(case.pair_log),
             "--supervisor-projection", str(config.authority_output),
             "--checkpoint-root", str(config.checkpoint_root),
             "--execution-nonce", config.execution_nonce,
             "--supervisor-signing-key-id", config.supervisor_signing_key_id,
             "--supervisor-signing-key-file", str(config.supervisor_signing_key_file),
             "--worker-signing-key-id", config.worker_signing_key_id,
             "--worker-signing-key-file", str(config.worker_signing_key_file),
             "--pair-status-signing-private-key-file", str(private_key),
             "--pair-status-verification-key-file", str(public_key),
             "--pair-execution-target-file", str(target)],
            cwd=REPO_ROOT, capture_output=True, text=True,
        )
        try:
            status = json.loads(cli.stdout)
        except ValueError:
            status = {}
        _emit("G3", "non_decompilation_error_through_classifier_and_cli",
              cli.returncode == 1 and status.get("canonical_outcome") == "ERROR"
              and status.get("classification_valid") is True,
              cli_returncode=cli.returncode, canonical_outcome=status.get("canonical_outcome"),
              error_kind=status.get("error_kind"), stderr=cli.stderr.strip()[-300:])


def main(arguments: list[str]) -> int:
    gates = {"G1": gate_g1, "G2": gate_g2, "G3": gate_g3}
    for name in arguments or list(gates):
        with tempfile.TemporaryDirectory(prefix=f"issue165-{name}-") as tmp:
            gates[name](Path(tmp))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
