#!/usr/bin/env python3
"""Package the two already completed, frozen actual-evidence authentications.

This does not execute Lean or either authenticator, synthesize a kernel receipt,
or change a proof source. Fresh-only manifests copy the authenticated rows.
"""
from __future__ import annotations

import datetime
import difflib
import hashlib
import json
import pathlib
import shutil
from zoneinfo import ZoneInfo

HERE = pathlib.Path(__file__).resolve().parent
OLD = HERE.parent / "rg_resume_20261104"
OUT = HERE / "publication" / "patch"
REVIEWS = "Proofs/RG_Lean_20261019/reviews/"
PRIMARY = OLD / "final_joblog_retry_preparation/actual"
ANCHOR = OLD / "anchor029_preparation/continuation_candidate/actual"
PRIMARY_REPORT_SHA = "101fdef6bb0152d1c3458f84c3d22d3c148f62aea2b2c56a538f8528df5ef40d"
ANCHOR_REPORT_SHA = "aa9128492cb857cac5a50fc1823dc7d2b410dadc41e9e996bb952445b4220ca7"
FILES: list[dict] = []


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def bound(path: pathlib.Path, digest: str) -> dict:
    raw = path.read_bytes()
    assert sha(raw) == digest, ("Changed authenticated input", str(path))
    return json.loads(raw)


def emit(relative: str, raw: bytes) -> dict:
    assert relative.startswith("Proofs/RG_Lean_20261019/")
    assert "/Proofs/" not in relative and not relative.endswith(".lean")
    target = OUT / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open("xb") as stream:
        stream.write(raw)
    item = dict(path=relative, local_path=str(target), bytes=len(raw),
                sha256=sha(raw), git_blob_sha1=blob(raw))
    FILES.append(item)
    return item


def emit_json(relative: str, value: dict) -> dict:
    return emit(relative, (json.dumps(value, indent=2, sort_keys=True) + "\n").encode())


def replace_once(text: str, old: str, new: str) -> str:
    assert text.count(old) == 1, ("README match is not unique", old[:100])
    return text.replace(old, new)


def fresh_manifest(report: dict, modules: dict, artifact: dict,
                   digest: str, profile_count: int) -> dict:
    rows = {name: detail["row"] for name, detail in modules.items()}
    assert all(row["mode"] == "FRESH_KERNEL_EXPORT" and row["module"] == name
               for name, row in rows.items())
    assert all("origin" not in row and "transport_capsule" not in row for row in rows.values())
    assert sum(len(row["axiom_profiles"]) for row in rows.values()) == profile_count
    return dict(kind="AUTHENTICATED_FRESH_KERNEL_EXPORTS",
        repository=report["repository"], run=report["run"], job=report["job"],
        source_commit=report["source_commit"], artifact_id=artifact["id"],
        artifact_sha256=artifact["digest"].removeprefix("sha256:"),
        lean_version="4.33.1", mathlib="0df444a360eaa60ab8c11dca51a86af692955474",
        modules=rows, origin_context=dict(run_attempt=1, workflow_event="push",
            actual_run_conclusion="success", actual_job_conclusion="success",
            authenticated_report_sha256=digest,
            complete_endpoint_receipt_present=True,
            receipt_sha256=report.get("receipt_sha256", report.get("archive_audit", {}).get("receipt_sha256")),
            manifest_scope="Only actual fresh objects physically exported by this artifact; no prior row relabelled as fresh",
            actual_fresh_modules=len(rows), named_axiom_profiles=profile_count,
            kernel_receipt_created_by_this_packager=False))


def main() -> None:
    now = datetime.datetime.now(datetime.timezone.utc)
    berlin = now.astimezone(ZoneInfo("Europe/Berlin"))
    p = bound(PRIMARY / "complete_original_authentication.json", PRIMARY_REPORT_SHA)
    a = bound(ANCHOR / "anchor029_continuation_authentication.json", ANCHOR_REPORT_SHA)
    assert p["status"] == "ACTUAL_EXACT_DEGREE_ONE_LARGE_KERNEL_RECEIPT_AUTHENTICATED_THREE_FAMILIES_REMAIN"
    assert p["remaining_main_family_count"] == 3 and not p["full_global_rg_proof_claim"]
    assert a["status"] == "ACTUAL_ORIGINAL_ANCHOR029_CONTINUATION_KERNEL_CLOSURE_AUTHENTICATED"
    assert a["full_original_endpoint_success_authenticated"] and a["family_count_change_from_this_anchor_run"] == 0
    assert not a["full_degree_one_middle_family_claim"] and not a["global_rg_claim"]
    p_review = bound(HERE / "reviews/primary_full_authentication_review.json",
                    "8061c22935896dd685eefcf4177ee41381522cda52b60b4a5473e2dffb3e81fe")
    a_review = bound(HERE / "reviews/anchor029_full_authentication_review.json",
                    "36bc79704209f3a76414b1b071597b57d1a7ba54bdd11eae75c046b9f8f1c4bb")
    assert p_review["findings"] == []
    assert a_review["status"] == "INDEPENDENT_REPORT_SOURCE_AND_NATIVE_CAPTURE_REVIEW_PASSED_NO_CONCRETE_FINDING"

    reports = [
        (PRIMARY / "complete_original_authentication.json", "20261105-degree-one-large-complete-authentication.json"),
        (ANCHOR / "anchor029_continuation_authentication.json", "20261105-anchor029-complete-authentication.json"),
        (HERE / "reviews/primary_full_authentication_review.json", "20261105-degree-one-large-independent-review.json"),
        (HERE / "reviews/anchor029_full_authentication_review.json", "20261105-anchor029-independent-review.json"),
        (PRIMARY / "native_terminal_capture_inventory.json", "20261105-degree-one-large-native-terminal.json"),
        (ANCHOR / "native_terminal_capture_20261105.json", "20261105-anchor029-native-terminal.json"),
        (HERE / "recovery/actual_archive_downloads.json", "20261105-actual-archive-downloads.json"),
        (OLD / "recovery_audit_20261105/frozen_dependency_inventory.json", "20261105-pre-recovery-dependency-inventory.json"),
        (HERE / "recovery/completed_dependency_recovery.json", "20261105-completed-dependency-recovery.json"),
    ]
    for source, name in reports:
        emit(REVIEWS + name, source.read_bytes())
    for label, directory, report in [("degree_one_large", PRIMARY, p), ("anchor029", ANCHOR, a)]:
        for name in ["run.json", "jobs.json", "artifacts.json", "job.log"]:
            raw = (directory / name).read_bytes()
            expected = (report["native_inputs"][name]["sha256"] if label == "degree_one_large"
                        else report["native_capture_sha256"][name])
            assert sha(raw) == expected
            emit(REVIEWS + "native_20261105/" + label + "/" + name, raw)

    p_manifest = fresh_manifest(p, p["modules"], p["artifacts"]["fresh"], PRIMARY_REPORT_SHA, 11)
    a_manifest = fresh_manifest(a, a["archive_audit"]["modules"], a["artifact"], ANCHOR_REPORT_SHA, 293)
    assert len(p_manifest["modules"]) == 3 and len(a_manifest["modules"]) == 55
    p_manifest_item = emit_json(REVIEWS + "20261105-degree-one-large-fresh-prior-exports.json", p_manifest)
    a_manifest_item = emit_json(REVIEWS + "20261105-anchor029-fresh-prior-exports.json", a_manifest)

    state = dict(
        status="ORIGINAL_DEGREE_ONE_LARGE_AND_ANCHOR029_AUTHENTICATED",
        confirmed_at_utc=now.isoformat(), confirmed_at_Europe_Berlin=berlin.isoformat(),
        repository="RhudeJJJJ/formal-conjectures", branch="rg-degree-one-large-20261103",
        publication_parent="f02df37d3d83484fa311b5bfefe9a8fb49fa63cf",
        primary_run=p["run"], primary_job=p["job"],
        primary_workflow_head=p["source_commit"],
        primary_proof_source_commit=p["unchanged_original_proof_source_commit"],
        primary_kernel_milestone_established=True,
        primary_authentication_report_sha256=PRIMARY_REPORT_SHA,
        primary_receipt_sha256=p["receipt_sha256"],
        primary_required_modules=p["required_modules"],
        primary_restore=p["complete_restoration_evidence"],
        primary_fresh_modules=p["fresh_modules"],
        primary_named_axiom_profiles=11,
        primary_limits=dict(module_seconds=900, workers=1, memory_reserve_mib=2048),
        remaining_original_families_now=3,
        remaining_original_families=p["remaining_original_main_families"],
        full_global_rg_proof_claim=False, upstream_submission=False,
        global_theorem_requires="h : RemainingThreeAssembly.Inputs",
        anchor029=dict(run=a["run"], job=a["job"], workflow_head=a["source_commit"],
            original_source_identity_commit=a["reviewed_original_source_identity_commit"],
            certificate_completed=True, full_middle_family_completed=False,
            family_count_change=0, required_modules=281, prior_modules=226,
            fresh_modules=55, named_axiom_profiles=838,
            inherited_profiles=545, new_profiles=293,
            actual_fresh_output_bytes=a["archive_audit"]["actual_fresh_output_bytes"],
            receipt_sha256=a["archive_audit"]["receipt_sha256"],
            authentication_report_sha256=ANCHOR_REPORT_SHA,
            cancelled_producer_origin=a["inherited_producer_identity"],
            limits=dict(module_seconds=600, workers=1, memory_reserve_mib=2048, job_minutes=360)),
        frozen_authenticator_executions=[
            dict(scope="degreeOneLarge", executions_this_resume=1, exit_code=0,
                source_sha256="eaae96913a22c9011facdecbee52f2a7da8739ec9ecea414336d0971d779de9c",
                report_sha256=PRIMARY_REPORT_SHA),
            dict(scope="Anchor029", executions_this_resume=1, exit_code=0,
                source_sha256="5ea66b63d162ae70eb84b9925b87027016d489cf8b0f277144637b65e41469d5",
                report_sha256=ANCHOR_REPORT_SHA)],
        proof_sources_changed=False, runtime_or_workflow_files_changed=False,
        new_native_Lean_runs_started=False,
        fresh_export_manifests=[p_manifest_item, a_manifest_item],
        historical_failure_and_cancelled_origins_preserved=True,
        interpretation_limits=[
            "The primary actual completed original receipt reduces four remaining families to three.",
            "The separate Anchor029 certificate does not close the degreeOneMiddle family.",
            "The frozen Anchor report's conditional count of four excludes this separate Large completion and is preserved unchanged.",
            "These archived reports and scripts bind the original artifact bytes; they do not replace those external proof artifacts.",
            "The new manifests contain only the 3 and 55 actual fresh rows of their respective native jobs."])
    emit_json(REVIEWS + "20261105-verified-formalization-status.json", state)

    original = (HERE / "source/README.before.md").read_bytes()
    assert sha(original) == "c86ddd4fb534440c7b7148913f449b333780e70e0fbda355d5984a473c4a9f3b"
    text = original.decode()
    text = replace_once(text,
        "Status at 19:11 UTC on 4 November 2026: **incomplete; four original input families remain open in Lean, and no full Lean proof has been submitted**.",
        f"Status at {berlin:%H:%M %Z} on 5 November 2026: **the original `degreeOneLarge` family is kernel-verified; three original input families remain open, and no full Lean proof has been submitted**.")
    text = replace_once(text,
        "Three have complete original kernel-object and source-closure audits at their recorded verified revisions: degree one through order 13, degree at least four through order 12 (all 247 actual-tree comparisons and coverage), and degree at least 46. Four remain open in this formalization: degree one at orders 14–52, degree one from order 53, degree two or three, and degrees 4–45 from order 13.",
        "Four have complete original kernel-object and source-closure audits at their recorded verified revisions: degree one through order 13, degree one from order 53, degree at least four through order 12 (all 247 actual-tree comparisons and coverage), and degree at least 46. Three remain open: degree one at orders 14–52, degree two or three, and degrees 4–45 from order 13.")
    text = replace_once(text, "## Current milestone: the complete degree-one large-order family",
                        "## Verified degree-one large-order family")
    summary = """### Complete original authentication — 5 November 2026

The [actual original run 41890211247](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/41890211247/job/126785297420), at workflow commit `1188a0dbc3ad1c5698671a93b9e27e6d21a718a5`, completed successfully on 4 November at **21:22:12 CET**. On 5 November, the already frozen original authenticator was restored byte-for-byte and executed once against both complete actual archives and their native metadata. It returned exit 0. The [complete authentication report](reviews/20261105-degree-one-large-complete-authentication.json), SHA-256 `101fdef6bb0152d1c3458f84c3d22d3c148f62aea2b2c56a538f8528df5ef40d`, and [independent review](reviews/20261105-degree-one-large-independent-review.json) establish the original large-family milestone.

The complete receipt covers **33,659 modules: 33,656 prior exports and exactly three fresh original exports**. All 767 selected archive identities and the actual full restoration/readback evidence are authenticated, totaling 119,932,353,256 recorded logical bytes. Complete selection coverage includes all 349 numerical batches and 69 named supporting origins. The four completed callback exports preserve their common original failed-job origin. The actual original Lean sources remain those fixed at `10aa67f5f16e8ad00b30ac21332791b008b69cfe`; the successful workflow head is separately identified above.

| Fresh original module | Recorded module seconds | Exact named axiom profiles |
|---|---:|---:|
| `D1OriginalSharedBothLong` | 217.778 | 5 |
| `OriginalDegreeOneLarge` | 351.509 | 2 |
| `RemainingThreeAssembly` | 460.195 | 4 |

All 11 profiles contain only `Classical.choice`, `Quot.sound` and `propext`. The unchanged gates used 900 seconds per module, one worker and 2048 MiB reserve. The actual memory and host guards completed successfully. The owned Btrfs read-ahead policy is authenticated as 4096 → 0 → 0 KiB while Direct I/O remained enabled; this successful configuration is not an isolated causal performance experiment. The [fresh-only export manifest](reviews/20261105-degree-one-large-fresh-prior-exports.json) copies exactly the three authenticated native rows and their actual artifact origin.

The completed original family proves `(189 / 5000 : ℝ) < normalizedIntegral C u p q 2` for every original tree presentation with `C.degree u = 1` and physical order at least 53. There is no upper bound on order or arm lengths. This reduces **four open original families to three**. The global theorem remains conditional on the three exact fields listed below.

### Anchor029 also completed

The separate [Anchor029 continuation 41888401962](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/41888401962/job/126778939548), at `b6924bdabeff35ff4af328c3879c69fc90ecf8f6`, completed successfully on 4 November at **23:30:47 CET**. Its [complete actual authentication](reviews/20261105-anchor029-complete-authentication.json), SHA-256 `aa9128492cb857cac5a50fc1823dc7d2b410dadc41e9e996bb952445b4220ca7`, and [independent review](reviews/20261105-anchor029-independent-review.json) establish the original Anchor029 certificate.

The complete 281-module endpoint has **226 priors and 55 fresh exports**, with **838 ordered named profile occurrences: 545 inherited and 293 new**. All 281 original source files, recursive closures, the 450-member actual archive and the complete receipt were checked. The 108 completed exports reused from the previous cancelled run keep that actual cancelled-job origin. The unchanged bounds were 600 seconds per Lean process, one worker, 2048 MiB reserve and a 360-minute job cap. The [fresh-only continuation manifest](reviews/20261105-anchor029-fresh-prior-exports.json) contains exactly the 55 new native rows; the 226 priors are not relabelled as fresh.

Anchor029 closes one concrete original certificate. It does **not** close the whole `degreeOneMiddle` family, so the aggregate count remains **three**. The frozen Anchor report retains its explicitly conditional field `remaining_original_families_without_separate_large_completion = 4`; the separate Large completion above supplies the reduction. The [current verified status](reviews/20261105-verified-formalization-status.json) records both conclusions together.

### Historical diagnostic and transport checkpoints — 4 November 2026

The following dated attempts preserve what was known before the final original success and its complete authentication. References to four open families or pending checks in these historical records describe those earlier checkpoints.
"""
    text = replace_once(text, "### Latest verified checkpoint — 4 November, 18:43 UTC", summary.rstrip())
    text = replace_once(text, "### Milestone scope and preceding reconstruction history",
                        "### Verified scope and remaining original inputs")
    text = replace_once(text,
        "Within this input, 14 of 15 arm classes have prior complete checks. The remaining class uses the original 122 interval trees and 1,754 leaf positions; alternate proof routes preserve each position and its original payment.",
        "The completed family covers all 15 unordered arm classes; the existing symmetry dispatch covers every ordered pair and all natural arm parameters. The formerly remaining class uses the original 122 interval trees and 1,754 leaf positions; alternate proof routes preserve each position and its original payment.")
    text = replace_once(text,
        "The [candidate complete family](Proofs/RadenkovicGutmanOriginalDegreeOneLarge.lean) now connects the existing `D1FastFullBox20` and `D1FastFullBox40` theorems to their original class fields. The earlier candidate incorrectly referenced nonexistent `D1Long20` and `D1Long40` modules. [RemainingThreeAssembly](Proofs/RadenkovicGutmanRemainingThreeAssembly.lean) supplies the degree-one large-order field from that family and preserves the exact three remaining input fields. **Neither candidate is counted as completed until its complete source-bound kernel check passes.**",
        "The [authenticated complete family](Proofs/RadenkovicGutmanOriginalDegreeOneLarge.lean) connects the existing `D1FastFullBox20` and `D1FastFullBox40` theorems to their original class fields. The earlier candidate incorrectly referenced nonexistent `D1Long20` and `D1Long40` modules. [RemainingThreeAssembly](Proofs/RadenkovicGutmanRemainingThreeAssembly.lean) now supplies the kernel-verified degree-one large-order field and preserves the exact three remaining input fields. Both current modules are covered by the completed original receipt and its full authentication above.")
    text = replace_once(text, "If that complete family check succeeds, `RemainingThreeAssembly.Inputs` retains exactly the following three obligations.",
                        "After the complete family check, `RemainingThreeAssembly.Inputs` retains exactly the following three obligations.")
    text = replace_once(text, "The current four-open-family status remains unchanged until the original large-family evidence is fully authenticated.",
                        "The current global theorem remains conditional on these three fields; a full RG proof is not claimed.")
    text = replace_once(text, "### Current reconstruction results and remaining checks",
                        "### Earlier reconstruction results and checks — 3–4 November 2026")
    emit("Proofs/RG_Lean_20261019/README.md", text.encode())
    diff = "".join(difflib.unified_diff(original.decode().splitlines(True), text.splitlines(True),
                                      fromfile="a/Proofs/RG_Lean_20261019/README.md",
                                      tofile="b/Proofs/RG_Lean_20261019/README.md"))
    (HERE / "publication/README.diff").write_text(diff)
    emit(REVIEWS + "offline_sources_20261105/prepare_verified_checkpoint.py", pathlib.Path(__file__).read_bytes())

    inventory = dict(status="PREPARED_EXACT_SOURCE_ONLY_VERIFIED_RESULT_CHECKPOINT",
        repository="RhudeJJJJ/formal-conjectures", branch="rg-degree-one-large-20261103",
        parent="f02df37d3d83484fa311b5bfefe9a8fb49fa63cf",
        base_tree="3c427bbffde48881cc1fa874022358d577af1f41", files=FILES,
        total_bytes=sum(f["bytes"] for f in FILES), runtime_changes=0, Lean_source_changes=0,
        full_authenticators_reexecuted=False, remaining_original_families=3,
        primary_report_sha256=PRIMARY_REPORT_SHA, anchor_report_sha256=ANCHOR_REPORT_SHA)
    (HERE / "publication/inventory.json").write_text(json.dumps(inventory, indent=2, sort_keys=True) + "\n")
    old_state = OLD / "task_state_current.json"
    saved = HERE / "recovery/rolled_back_task_state_20261104.json"
    assert not saved.exists()
    shutil.copyfile(old_state, saved)
    state["superseded_local_state_snapshot"] = dict(path=str(saved), sha256=sha(saved.read_bytes()),
        interpretation="Recovered historical pre-outage snapshot; not the current native or proof status")
    old_state.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n")
    print(json.dumps(dict(files=len(FILES), bytes=inventory["total_bytes"],
        status=state["status"], remaining_original_families=3, fresh_manifest_counts=[3,55],
        new_native_runs_started=False, runtime_changes=0, Lean_source_changes=0), indent=2))


if __name__ == "__main__":
    main()
