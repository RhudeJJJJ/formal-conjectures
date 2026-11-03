"""Bind the revised final source graph separately from original numeric origins.

This check compiles no Lean modules and authenticates no proof objects. It
materializes the full actual source graph, checks the reviewed current closure,
and checks 4,566 unchanged numeric sources plus one explicitly reorganized leaf.
That leaf retains all original declaration bodies and all original endpoints.
"""
import hashlib
import json
import os
import pathlib
import re
import subprocess

from rg_original_d1_numeric_reproduction import load_plan
from rg_plan_exact_degree_one_large import ROOT, SOURCES, PIN, LC, source_closure

SPEC = ROOT / "ci/rg_current_final_source_binding_20261103.json"
NUMERIC_SPEC = "ci/rg_d1_required_numeric_batches_20261103.json"
NUMERIC_SPEC_SHA = "f47334108b563ae5e20f15fc07b2e4589f6d6e7f49e308bfdb8b4301e689e18e"
OLD_CLOSURE = "9b816edb67214c8c25a0c17e7390be126b53a03cb41bd8165c567755b5c302ac"
ENDPOINT = "Proofs.RadenkovicGutmanRemainingThreeAssembly"
REORGANIZED = "Proofs.RadenkovicGutmanD1Long00Leaf01370"
REORGANIZED_SPEC = "ci/rg_d1_numeric137_decomposed_20261103_spec.json"
REORGANIZED_SHA = "215ae3b2b69a4d7f9f00d694228a45333df0b73e588a6b2f0f61c97b45db4302"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def sealed_json(relative, digest):
    path = pathlib.PurePosixPath(relative)
    assert path.is_relative_to("ci") and ".." not in path.parts
    raw = (ROOT / path).read_bytes()
    assert sha(raw) == digest, ("Changed sealed input", relative)
    return json.loads(raw)


def main():
    spec_raw = SPEC.read_bytes()
    spec = json.loads(spec_raw)
    assert spec["kind"] == "EXACT_CURRENT_FINAL_SOURCE_BINDING_NOT_KERNEL_PROOF"
    assert spec["repository"] == "RhudeJJJJ/formal-conjectures"
    assert spec["endpoint"] == ENDPOINT
    assert (spec["mathlib"], spec["leancert"], spec["lean_version"]) == (PIN, LC, "4.33.1")
    assert spec["original_numeric_spec"] == NUMERIC_SPEC
    assert spec["original_numeric_spec_sha256"] == NUMERIC_SPEC_SHA
    numeric = sealed_json(NUMERIC_SPEC, NUMERIC_SPEC_SHA)
    origin = sealed_json(spec["original_numeric_origin"], spec["original_numeric_origin_sha256"])
    assert (origin["repository"], origin["run"], origin["source_commit"]) == (
        "RhudeJJJJ/formal-conjectures", 41686621300,
        "aaeaec3cec22467d3f0b83b1761bfb40087bb991")
    assert origin["numeric_spec_sha256"] == NUMERIC_SPEC_SHA
    assert origin["source_endpoint_closure_sha256"] == numeric["source_endpoint_closure_sha256"] == OLD_CLOSURE
    assert numeric["required_modules"] == 33472
    scheduled = numeric["scheduled_numeric_modules"]
    assert isinstance(scheduled, list)
    assert len(scheduled) == len(set(scheduled)) == 4567
    assert origin["numeric_jobs"] == len(numeric["jobs"]) == 349
    assert spec["current_required_modules"] == 33583
    assert spec["current_endpoint_source_sha256"] == numeric["source_endpoint_sha256"]
    assert spec["current_endpoint_closure_sha256"] != OLD_CLOSURE
    assert spec["numeric_source_reorganization"] == {
        "original_module": REORGANIZED, "original_batch": "00_137",
        "spec": REORGANIZED_SPEC, "spec_sha256": REORGANIZED_SHA,
        "original_declarations_preserved_verbatim": True,
        "unchanged_original_numeric_modules": 4566,
        "source_reorganized_original_numeric_modules": 1,
        "added_support_modules": 11,
        "additional_final_current_source_recheck": "Proofs.RadenkovicGutmanD1OriginalSharedSlice0080Complete",
    }
    import rg_numeric137_decomposed_recovery as decomposition
    current, original_plan, original_rows, base, snapshot = decomposition.context(REORGANIZED_SHA)
    decomposition.preserve_declarations(current, original_rows, snapshot)
    # The pinned producer checks all original data in memory. It materializes
    # only the other nine original leaves, so a missing sibling cannot cause
    # a later generic materializer to overwrite the reorganized leaf.
    decomposition.materialize_unchanged(current, original_rows, snapshot)
    decomposition.preserve_declarations(current, original_rows, snapshot)
    decomposition.source_scope(current, original_rows, base)
    hashes, dependencies, closures = source_closure(ENDPOINT)
    assert len(hashes) == spec["current_required_modules"]
    assert hashes[ENDPOINT] == spec["current_endpoint_source_sha256"]
    assert closures[ENDPOINT] == spec["current_endpoint_closure_sha256"]
    for name, digest in spec["reviewed_changed_sources"].items():
        assert hashes[name] == digest, ("Changed reviewed source", name)

    expected_names = set()
    unchanged = set()
    reorganized = set()
    plan_digests = {}
    for job in numeric["jobs"]:
        relative = job["plan"]
        sealed_json(relative, job["plan_sha256"])
        plan, expected = load_plan(ROOT / relative)
        assert plan["scope"] in ("original00_leaves", "original_long_chunk")
        assert not (expected_names & expected.keys()), ("Repeated original batch", job["batch"])
        expected_names.update(expected)
        plan_digests[relative] = job["plan_sha256"]
        for name, row in expected.items():
            if name == REORGANIZED:
                assert job["batch"] == "00_137" and plan == original_plan
                assert row == original_rows[name]
                assert hashes[name] == current["modules"][name]["source_sha256"] != row["source_sha256"]
                assert closures[name] == current["modules"][name]["source_closure_sha256"] != row["source_closure_sha256"]
                reorganized.add(name)
                continue
            assert hashes[name] == row["source_sha256"], ("Changed numeric source", name)
            assert closures[name] == row["source_closure_sha256"], ("Changed numeric closure", name)
            unchanged.add(name)
    assert expected_names == set(scheduled) and len(expected_names) == 4567
    assert reorganized == {REORGANIZED} and len(unchanged) == 4566
    assert unchanged | reorganized == expected_names and not unchanged & reorganized
    for name in current["new_source_exports"]:
        assert hashes[name] == current["modules"][name]["source_sha256"]
        assert closures[name] == current["modules"][name]["source_closure_sha256"]
    sealed_json(numeric["head_plan"], numeric["head_plan_sha256"])
    head_plan, heads = load_plan(ROOT / numeric["head_plan"])
    assert head_plan["scope"] == "original_long_heads"
    assert set(heads) == {
        "Proofs.RadenkovicGutmanD1Long10", "Proofs.RadenkovicGutmanD1Long30"}
    assert not (expected_names & heads.keys())
    for name, row in heads.items():
        assert hashes[name] == row["source_sha256"], ("Changed historical head source", name)
        assert closures[name] == row["source_closure_sha256"], ("Changed historical head closure", name)

    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    assert re.fullmatch(r"[0-9a-f]{40}", commit)
    assert os.environ["GITHUB_SHA"] == commit
    assert os.environ["GITHUB_REPOSITORY"] == spec["repository"]
    assert os.environ["GITHUB_REF"] == "refs/heads/rg-degree-one-large-20261103"
    report = {
        "status": "CURRENT_SOURCE_CLOSURE_BOUND_WITH_EXPLICIT_DECLARATION_PRESERVING_REORGANIZATION",
        "kernel_proof": "NOT_CHECKED_BY_THIS_SOURCE_PREFLIGHT",
        "compiled_object_coverage": "NOT_CHECKED_BY_THIS_SOURCE_PREFLIGHT",
        "remaining_original_main_families": 4,
        "repository": spec["repository"], "source_commit": commit,
        "workflow_run": int(os.environ["GITHUB_RUN_ID"]),
        "workflow_attempt": int(os.environ["GITHUB_RUN_ATTEMPT"]),
        "endpoint": ENDPOINT, "required_modules": len(hashes),
        "current_endpoint_source_sha256": hashes[ENDPOINT],
        "current_endpoint_closure_sha256": closures[ENDPOINT],
        "binding_spec_sha256": sha(spec_raw),
        "original_numeric_origin": origin,
        "original_numeric_modules_accounted_for": len(expected_names),
        "unchanged_original_numeric_modules": len(unchanged),
        "source_reorganized_original_numeric_modules": sorted(reorganized),
        "original_numeric_batch_plans_unchanged": len(numeric["jobs"]),
        "fully_unchanged_original_numeric_batches": len(numeric["jobs"]) - 1,
        "numeric_source_reorganization": spec["numeric_source_reorganization"],
        "unchanged_original_long_heads": sorted(heads),
        "original_numeric_plan_sha256": plan_digests,
    }
    output = SOURCES / "build/current_final_source_binding"
    output.mkdir(parents=True, exist_ok=True)
    (output / "source_binding_report.json").write_text(json.dumps(report, indent=2) + "\n")
    graph = {"source_sha256": hashes, "source_dependencies": dependencies,
             "source_closure_sha256": closures}
    (output / "actual_current_source_graph.json").write_text(json.dumps(graph, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ("original_numeric_plan_sha256", "original_numeric_origin")}), flush=True)


if __name__ == "__main__":
    main()
