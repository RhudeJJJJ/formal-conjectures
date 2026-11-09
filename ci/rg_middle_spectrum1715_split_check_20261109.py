#!/usr/bin/env python3
"""Bind one sample-split proof to unchanged original data and propositions.

Source equivalence is not a kernel result. --receipt requires the separately
produced native verifier receipt, one fresh object, and all 23 axiom prints.
The original frozen batch authenticator is deliberately not modified.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

from rg_middle_residual_sample_split_20261109 import split_source

ROOT = Path(__file__).resolve().parent.parent
PROJECT = ROOT / "Proofs/RG_Lean_20261019"
ENDPOINT = "Proofs.RadenkovicGutmanDegreeOneMiddleResidualSpectrum1715"
MANIFEST = ROOT / "ci/rg_middle_spectrum1715_split_candidate_20261109.json"
ORIGINAL = "15d45e8d3ed3bacaf3afe7d85488a42f08302d76"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--retain", action="store_true")
    parser.add_argument("--receipt", action="store_true")
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_bytes())
    assert manifest["original_source_commit"] == ORIGINAL
    assert len(manifest["modules"]) == 1
    row = manifest["modules"][0]
    assert row["module"] == ENDPOINT and row["samples"] == 18
    generator = ROOT / "ci/rg_middle_residual_sample_split_20261109.py"
    assert sha(generator.read_bytes()) == manifest["generator_sha256"]
    original = subprocess.check_output(["git", "show", ORIGINAL + ":" + row["path"]], cwd=ROOT)
    candidate, equivalence = split_source(original, "1715")
    assert (ROOT / row["path"]).read_bytes() == candidate
    assert sha(candidate) == row["candidate_source_sha256"]
    for key, value in equivalence.items():
        assert row[key] == value, key
    sources, dependencies, closures = {}, {}, {}
    sys.path.insert(0, str(PROJECT))
    from verify import without_comments

    def visit(name):
        if name in sources:
            return
        relative = "Proofs/RG_Lean_20261019/" + name.replace(".", "/") + ".lean"
        raw = (ROOT / relative).read_bytes()
        if name != ENDPOINT:
            assert raw == subprocess.check_output(["git", "show", ORIGINAL + ":" + relative], cwd=ROOT), name
        code = without_comments(raw.decode())
        assert not re.search(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", code, re.M), name
        sources[name] = {"path": relative, "sha256": sha(raw)}
        dependencies[name] = sorted(set(re.findall(r"^\s*(?:public\s+)?import\s+(Proofs\.[\w.]+)\s*$", code, re.M)))
        for dep in dependencies[name]:
            visit(dep)
        closures[name] = sha(json.dumps([name, sha(raw), manifest["mathlib"], manifest["leancert"],
            [(dep, closures[dep]) for dep in dependencies[name]]], separators=(",", ":")).encode())

    visit(ENDPOINT)
    assert len(sources) == 19
    assert closures[ENDPOINT] == row["candidate_source_closure_sha256"]
    for name, closure in row["unchanged_dependency_closures"].items():
        assert closures[name] == closure
    proof_sources = {entry["path"]: entry["sha256"] for entry in sources.values()}
    evidence = dict(kind="SAME_ORIGINAL_PROPOSITIONS_SAMPLE_SPLIT_NEW_SOURCE_IDENTITY",
                    endpoint=ENDPOINT, original_source_commit=ORIGINAL,
                    source_sha256=proof_sources, source_closure_sha256=closures,
                    source_count=19, expected_prior_count=18, expected_fresh_count=1,
                    original_statements_and_numerical_data_unchanged=True,
                    status="SOURCE_ONLY_REQUIRES_FRESH_NATIVE_KERNEL_RECEIPT")
    if args.retain:
        fresh = PROJECT / "build/fresh_exports"
        bundle = fresh / "generated_source"
        for relative in proof_sources:
            destination = bundle / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / relative, destination)
        (bundle / "generated_source_manifest.json").write_text(json.dumps(evidence, indent=2) + "\n")
        frozen = fresh / "frozen_validation"
        frozen.mkdir(parents=True, exist_ok=True)
        for path in [MANIFEST, generator, Path(__file__), PROJECT / "verify_extension.py",
                     PROJECT / "verify.py", PROJECT / "module_outputs.py",
                     ROOT / "ci/rg_observed_kernel_verify.py"]:
            shutil.copyfile(path, frozen / path.name)
    if args.receipt:
        build = PROJECT / "build/extension"
        receipt = json.loads((build / "receipt.json").read_bytes())
        assert receipt["endpoints"] == [ENDPOINT]
        assert receipt["mathlib"] == manifest["mathlib"] and receipt["leancert"] == manifest["leancert"]
        assert set(receipt["modules"]) == set(sources)
        fresh = [name for name, record in receipt["modules"].items() if record["mode"] == "FRESH_KERNEL_EXPORT"]
        assert fresh == [ENDPOINT]
        from module_outputs import output_members
        for name, record in receipt["modules"].items():
            assert record["source_sha256"] == sources[name]["sha256"]
            assert record["source_closure_sha256"] == closures[name]
            assert record["axiom_profiles"] and all(set(p) <= ALLOWED for p in record["axiom_profiles"])
            for relative, digest, size in output_members(name, record):
                raw = (build / relative).read_bytes()
                assert sha(raw) == digest and (size is None or len(raw) == size)
        log = (build / (ENDPOINT + ".log")).read_text()
        names = re.findall(r"'([^']+)'\s+(?:depends on axioms:|does not depend on any axioms)", log)
        assert names == row["ordered_axiom_names"] and len(names) == 23
        assert len(receipt["modules"][ENDPOINT]["axiom_profiles"]) == 23
        resource = json.loads((PROJECT / "build/fresh_exports/resource_observer.json").read_bytes())
        assert resource["status"] == "VERIFIER_COMPLETED" and resource["exit_code"] == 0
        evidence["status"] = "FRESH_NATIVE_KERNEL_RECEIPT_CHECKED_FOR_NEW_SOURCE"
        evidence["named_axiom_profiles"] = names
        print("SPECTRUM1715_SPLIT_KERNEL_PASS " + json.dumps(evidence, sort_keys=True))
    else:
        print("SPECTRUM1715_SPLIT_SOURCE_PASS " + json.dumps({key: evidence[key] for key in
            ["status", "endpoint", "source_count", "expected_prior_count", "expected_fresh_count"]}))


if __name__ == "__main__":
    main()
