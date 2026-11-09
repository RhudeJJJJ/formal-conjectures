#!/usr/bin/env python3
"""Freeze Batch024's complete source closure with six sample-split spectra.

Every original file is read from the immutable Git commit. Exactly six source
files receive the reviewed sample split. The original 45 required prior rows
and all 707 restored diagnostic rows are preserved; no pilot export is reused.
This constructs a source plan only and never manufactures a Lean receipt.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys


SOURCE_COMMIT = "15d45e8d3ed3bacaf3afe7d85488a42f08302d76"
INVENTORY_PATH = "ci/rg_middle_residual_batch_inventory_20261109.json"
INVENTORY_SHA256 = "22c745d4fdb281e8cc2172ffcc3b975005da4fb4777e9021e85f46bbc9a665e0"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
LEANCERT = "621a43d7cf21f87872392a01e874f2f1dbddc926"
PREFIX = "Proofs.RadenkovicGutmanDegreeOneMiddleResidual"
ENDPOINT = PREFIX + "FiniteCertificateBatch024"
SPECTRA = ("1715", "1749", "1956", "2356", "2357", "2358")
EXPECTED_KEYS = [(10, 1709, 2, 2), (10, 1736, 2, 2), (10, 1800, 2, 2)]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def serialized(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def write_same(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        assert path.read_bytes() == raw, ("Refuse to replace different frozen bytes", str(path))
    else:
        path.write_bytes(raw)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    args = parser.parse_args()
    repo, output = args.repo.resolve(), args.output_root.resolve()
    assert output != repo and not output.is_relative_to(repo)
    inventory_raw = (repo / INVENTORY_PATH).read_bytes()
    assert sha(inventory_raw) == INVENTORY_SHA256, "Changed original batch plan"
    inventory = json.loads(inventory_raw)
    assert inventory["source_commit"] == SOURCE_COMMIT
    assert inventory["mathlib"] == MATHLIB and inventory["leancert"] == LEANCERT
    assert inventory["lean_version"] == "4.33.1"
    original_row = next(row for row in inventory["batches"] if row["index"] == "024")
    assert original_row["endpoint"] == ENDPOINT
    for path, expected in inventory["input_sha256"].items():
        assert sha((repo / path).read_bytes()) == expected, path

    # Load the same pure transformation used for the successful split pilot.
    generator_path = repo / "ci/rg_middle_residual_sample_split_20261109.py"
    spec = importlib.util.spec_from_file_location("rg_frozen_sample_split", generator_path)
    generator = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(generator)
    sys.path.insert(0, str(repo / "Proofs/RG_Lean_20261019"))
    from verify import without_comments

    paths, original, candidate, code, dependencies, preservation = {}, {}, {}, {}, {}, {}
    for path, expected in sorted(original_row["source_sha256"].items()):
        assert path.startswith("Proofs/RG_Lean_20261019/Proofs/") and path.endswith(".lean")
        name = path.removeprefix("Proofs/RG_Lean_20261019/")[:-5].replace("/", ".")
        raw = subprocess.check_output(["git", "show", SOURCE_COMMIT + ":" + path], cwd=repo)
        assert sha(raw) == expected, path
        paths[name], original[name] = path, raw
        if name in {PREFIX + "Spectrum" + i for i in SPECTRA}:
            candidate[name], preservation[name] = generator.split_source(raw, name[-4:])
        else:
            candidate[name] = raw
        code[name] = without_comments(candidate[name].decode())
        assert not re.search(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", code[name], re.M)
        dependencies[name] = sorted(set(re.findall(
            r"^\s*(?:public\s+)?import\s+((?:Proofs|LeanCert)\.[\w.]+)\s*$", code[name], re.M)))
    assert len(paths) == 56
    assert all(set(deps) <= set(paths) for deps in dependencies.values())
    reachable, topological = set(), []
    def visit(name):
        if name in reachable:
            return
        reachable.add(name)
        for dependency in dependencies[name]:
            visit(dependency)
        topological.append(name)
    visit(ENDPOINT)
    assert reachable == set(paths), "Not the exact full endpoint closure"

    def closures(raws):
        result = {}
        for name in topological:
            result[name] = sha(json.dumps(
                [name, sha(raws[name]), MATHLIB, LEANCERT,
                 [(d, result[d]) for d in dependencies[name]]],
                separators=(",", ":")).encode())
        return result
    original_closures, candidate_closures = closures(original), closures(candidate)
    assert original_closures == original_row["source_closure_sha256"]
    changed_sources = sorted(n for n in paths if original[n] != candidate[n])
    changed_closures = sorted(n for n in paths if original_closures[n] != candidate_closures[n])
    assert changed_sources == sorted(PREFIX + "Spectrum" + i for i in SPECTRA)
    assert changed_closures == original_row["fresh_modules"]
    priors = inventory["expected_prior_rows"]
    assert len(priors) == 707
    assert sorted(set(paths) & set(priors)) == original_row["prior_modules"]
    assert sorted(set(paths) - set(priors)) == original_row["fresh_modules"]
    for name in original_row["prior_modules"]:
        assert original[name] == candidate[name]
        assert priors[name]["mode"] == "PRIOR_VERIFIED_JOB_EXPORT"
        assert priors[name]["source_sha256"] == sha(candidate[name])
        assert priors[name]["source_closure_sha256"] == candidate_closures[name]

    names = {}
    for name in original_row["fresh_modules"]:
        namespaces = re.findall(r"^namespace ([\w.]+)\s*$", code[name], re.M)
        assert len(namespaces) == 1
        local_names = re.findall(r"^#print axioms ([\w.]+)\s*$", code[name], re.M)
        names[name] = [n if n.startswith("Gebendorfer.") else namespaces[0] + "." + n
                       for n in local_names]
        if name in preservation:
            assert names[name] == preservation[name]["ordered_axiom_names"]
            assert names[name][-5:] == original_row["ordered_axiom_names"][name]
        else:
            assert names[name] == original_row["ordered_axiom_names"][name]
    assert sum(map(len, names.values())) == 151

    key_source = code[PREFIX + "FiniteKeysData"]
    key_match = re.findall(r"^def keys024 : List Key := \[(.*?)\]$", key_source, re.M)
    assert len(key_match) == 1
    tuples = [tuple(map(int, row)) for row in re.findall(r"⟨(\d+),(\d+),(\d+),(\d+)⟩", key_match[0])]
    assert tuples == EXPECTED_KEYS
    assert ",".join("⟨" + ",".join(map(str, row)) + "⟩" for row in tuples) == key_match[0]
    keys = [dict(zip(("n", "index", "p", "q"), row)) for row in tuples]
    certificates = re.findall(r"apply certified_cons \(by exact (certified\d+)\)", code[ENDPOINT])
    assert certificates == ["certified1200", "certified1201", "certified1202"]
    bindings = []
    for suffix, key in zip(("1200", "1201", "1202"), keys):
        name = PREFIX + "FiniteActualCase" + suffix
        body = code[name]
        core = re.findall(r"def core(\d+) : Family (\d+) := level(\d+)\.get ⟨(\d+),by decide⟩", body)
        assert core == [(suffix, str(key["n"]), str(key["n"]), str(key["index"]))]
        typed = re.findall(r"theorem certified(\d+) : Certified \(graph core(\d+)\) \(root (\d+)\) (\d+) (\d+) :=", body)
        assert typed == [(suffix, suffix, str(key["n"]), str(key["p"]), str(key["q"]))]
        maps = re.findall(r"of_native_maps core" + suffix + r" DegreeOneMiddleResidualSpectrum(\d+)\.graph DegreeOneMiddleResidualSpectrum(\d+)\.graph", body)
        assert len(maps) == 1
        source, fused = maps[0]
        bindings.append({"key": key, "actual_case": name,
                         "certificate": "Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases.certified" + suffix,
                         "source_spectrum": PREFIX + "Spectrum" + source,
                         "fused_spectrum": PREFIX + "Spectrum" + fused})
    assert [(r["source_spectrum"][-4:], r["fused_spectrum"][-4:]) for r in bindings] == [
        ("2356", "1715"), ("2357", "1749"), ("2358", "1956")]

    row = {
        **original_row,
        "status": "SAME_ORIGINAL_STATEMENTS_WITH_SAMPLE_SPLIT_PROOFS_REQUIRE_NEW_NATIVE_RECEIPT",
        "source_sha256": {paths[n]: sha(candidate[n]) for n in sorted(paths)},
        "source_closure_sha256": candidate_closures,
        "endpoint_source_closure_sha256": candidate_closures[ENDPOINT],
        "original_source_sha256": original_row["source_sha256"],
        "original_source_closure_sha256": original_closures,
        "ordered_axiom_names": names, "fresh_axiom_print_count": 151,
        "original_fresh_axiom_print_count": 43,
        "added_sample_axiom_print_count": 108,
        "changed_source_modules": changed_sources, "changed_closure_modules": changed_closures,
        "keys": keys, "key_bindings": bindings,
        "dependencies": dependencies, "topological_modules": topological,
        "source_preservation": preservation,
    }
    manifest = {
        "kind": "ORIGINAL_MIDDLE_RESIDUAL_BATCH024_SAMPLE_SPLIT_SOURCE_PLAN",
        "original_source_commit": SOURCE_COMMIT,
        "new_workflow_source_commit_must_be_bound_by_native_evidence": True,
        "lean_version": "4.33.1", "mathlib": MATHLIB, "leancert": LEANCERT,
        "original_inventory_sha256": INVENTORY_SHA256,
        "source_generator_sha256": sha(generator_path.read_bytes()),
        "inventory_generator_sha256": sha(Path(__file__).read_bytes()),
        "base_capsule": inventory["base_capsule"], "restore_plan": inventory["restore_plan"],
        "restore_manifests": inventory["restore_manifests"],
        "input_sha256": inventory["input_sha256"],
        "expected_prior_rows": priors,
        "limits": inventory["limits"], "batches": [row],
        "pilot_exports_reused": False,
        "proof_status": "SOURCE_PLAN_ONLY; ALL_ELEVEN_FRESH_MODULES_REQUIRE_NATIVE_KERNEL_VERIFICATION",
        "complete_middle_family": False, "global_rg_proved": False,
    }
    for name in sorted(paths):
        write_same(output / paths[name], candidate[name])
    for path in inventory["input_sha256"]:
        write_same(output / "fixed_inputs" / path, (repo / path).read_bytes())
    write_same(output / "candidate_manifest.json", serialized(manifest))
    print(json.dumps({"status": manifest["proof_status"], "output": str(output),
                      "source_count": 56, "prior_count": 45, "fresh_count": 11,
                      "axiom_profiles": 151, "keys": keys,
                      "endpoint_source_closure_sha256": candidate_closures[ENDPOINT],
                      "manifest_sha256": sha(serialized(manifest))}, indent=2))


if __name__ == "__main__":
    main()
