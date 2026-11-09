#!/usr/bin/env python3
"""Bind six sample splits to the original three-key residual Batch024.

Source equivalence is not a kernel result. --receipt requires all eleven fresh
native exports, the exact forty-five inherited records and 151 ordered prints.
The original frozen batch authenticator and Lean compiler flags are unchanged.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import shutil
import subprocess
import sys

from rg_middle_residual_sample_split_20261109 import split_source

ROOT = Path(__file__).resolve().parent.parent
PROJECT = ROOT / "Proofs/RG_Lean_20261019"
MANIFEST = ROOT / "ci/rg_middle_residual_batch024_split_inventory_20261109.json"
INVENTORY = ROOT / "ci/rg_middle_residual_batch_inventory_20261109.json"
ORIGINAL = "15d45e8d3ed3bacaf3afe7d85488a42f08302d76"
INVENTORY_SHA256 = "22c745d4fdb281e8cc2172ffcc3b975005da4fb4777e9021e85f46bbc9a665e0"
GENERATOR_SHA256 = "5010da3b12a676f9ebd3109eb1f19cf78cb05dd6bb674170d007d4c061fcbc7e"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
LEANCERT = "621a43d7cf21f87872392a01e874f2f1dbddc926"
PREFIX = "Proofs.RadenkovicGutmanDegreeOneMiddleResidualFinite"
SPECTRUM_PREFIX = "Proofs.RadenkovicGutmanDegreeOneMiddleResidualSpectrum"
ENDPOINT = PREFIX + "CertificateBatch024"
SPECTRA = [SPECTRUM_PREFIX + number for number in ("1715", "1749", "1956", "2356", "2357", "2358")]
KEYS = [{"n": 10, "index": index, "p": 2, "q": 2} for index in (1709, 1736, 1800)]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NAMED = re.compile(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def printed_names(code):
    namespaces = re.findall(r"^namespace\s+(\S+)\s*$", code, re.M)
    assert len(namespaces) == 1, namespaces
    namespace = namespaces[0]
    names = re.findall(r"^\s*#print\s+axioms\s+([A-Za-z_][\w.]*)\s*$", code, re.M)
    assert names and len(names) == len(set(names))
    result = []
    for name in names:
        if name.startswith("_root_."):
            result.append(name[len("_root_."):])
        elif name.startswith(namespace + "."):
            result.append(name)
        else:
            assert "." not in name, name
            result.append(namespace + "." + name)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--retain", action="store_true")
    parser.add_argument("--receipt", action="store_true")
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_bytes())
    inventory_raw = INVENTORY.read_bytes()
    assert sha(inventory_raw) == INVENTORY_SHA256 == manifest["original_inventory_sha256"]
    original_inventory = json.loads(inventory_raw)
    original_row = next(row for row in original_inventory["batches"] if row["index"] == "024")
    assert manifest["kind"] == "ORIGINAL_MIDDLE_RESIDUAL_BATCH024_SAMPLE_SPLIT_SOURCE_PLAN"
    assert manifest["original_source_commit"] == ORIGINAL
    assert manifest["mathlib"] == MATHLIB and manifest["leancert"] == LEANCERT
    assert manifest["lean_version"] == "4.33.1"
    assert (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1"
    assert manifest["pilot_exports_reused"] is False
    assert manifest["global_rg_proved"] is False and manifest["complete_middle_family"] is False
    for key in ("base_capsule", "restore_plan", "restore_manifests", "input_sha256", "expected_prior_rows", "limits"):
        assert manifest[key] == original_inventory[key], key
    assert manifest["limits"] == dict(job_timeout_minutes=360, memory_reserve_mib=2048,
                                      module_timeout_seconds=600, workers_per_job=1)
    for relative, expected_hash in manifest["input_sha256"].items():
        assert sha((ROOT / relative).read_bytes()) == expected_hash, relative
    priors = manifest["expected_prior_rows"]
    assert len(priors) == 707
    assert len(manifest["batches"]) == 1
    row = manifest["batches"][0]
    assert row["index"] == "024" and row["endpoint"] == ENDPOINT
    assert (row["source_count"], row["prior_count"], row["fresh_count"], row["key_count"]) == (56, 45, 11, 3)
    assert (row["original_fresh_axiom_print_count"], row["added_sample_axiom_print_count"],
            row["fresh_axiom_print_count"]) == (43, 108, 151)
    assert row["keys"] == KEYS
    assert row["changed_source_modules"] == SPECTRA
    assert row["original_source_sha256"] == original_row["source_sha256"]
    assert row["original_source_closure_sha256"] == original_row["source_closure_sha256"]
    for key in ("declaration", "fresh_modules", "prior_modules", "prior_manifest_paths"):
        assert row[key] == original_row[key], key
    generator = ROOT / "ci/rg_middle_residual_sample_split_20261109.py"
    inventory_generator = ROOT / "ci/rg_middle_residual_batch024_split_plan_20261109.py"
    assert sha(generator.read_bytes()) == GENERATOR_SHA256 == manifest["source_generator_sha256"]
    assert sha(inventory_generator.read_bytes()) == manifest["inventory_generator_sha256"]
    sys.path.insert(0, str(PROJECT))
    from verify import without_comments

    sources, code, dependencies, closures, original_closures, preservation = {}, {}, {}, {}, {}, {}

    def visit(name):
        if name in sources:
            return
        assert name.startswith("Proofs.")
        relative = "Proofs/RG_Lean_20261019/" + name.replace(".", "/") + ".lean"
        raw = (ROOT / relative).read_bytes()
        original = subprocess.check_output(["git", "show", ORIGINAL + ":" + relative], cwd=ROOT)
        assert sha(original) == original_row["source_sha256"][relative], name
        if name in SPECTRA:
            expected, equivalent = split_source(original, name[len(SPECTRUM_PREFIX):])
            assert raw == expected, ("Changed sample, data, proposition or later proof", name)
            preservation[name] = equivalent
        else:
            assert raw == original, ("Original surrounding source changed", name)
        code[name] = without_comments(raw.decode())
        assert not re.search(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", code[name], re.M), name
        sources[name] = {"path": relative, "sha256": sha(raw)}
        dependencies[name] = sorted(set(re.findall(r"^\s*(?:public\s+)?import\s+(Proofs\.[\w.]+)\s*$", code[name], re.M)))
        for dependency in dependencies[name]:
            visit(dependency)
        closures[name] = sha(json.dumps([name, sha(raw), MATHLIB, LEANCERT,
            [(dep, closures[dep]) for dep in dependencies[name]]], separators=(",", ":")).encode())
        original_closures[name] = sha(json.dumps([name, sha(original), MATHLIB, LEANCERT,
            [(dep, original_closures[dep]) for dep in dependencies[name]]], separators=(",", ":")).encode())

    visit(ENDPOINT)
    assert len(sources) == 56
    assert set(sources) == set(original_row["source_closure_sha256"])
    assert dependencies == row["dependencies"]
    assert preservation == row["source_preservation"]
    assert original_closures == row["original_source_closure_sha256"]
    assert closures == row["source_closure_sha256"]
    assert closures[ENDPOINT] == row["endpoint_source_closure_sha256"]
    assert sorted(name for name in sources if closures[name] != original_closures[name]) == row["changed_closure_modules"]
    assert row["changed_closure_modules"] == row["fresh_modules"]
    proof_sources = {entry["path"]: entry["sha256"] for entry in sources.values()}
    assert proof_sources == row["source_sha256"]
    fresh = set(sources) - set(priors)
    assert sorted(fresh) == row["fresh_modules"] and len(fresh) == 11
    assert sorted(set(sources) & set(priors)) == row["prior_modules"]
    for name in row["prior_modules"]:
        assert priors[name]["source_sha256"] == sources[name]["sha256"]
        assert priors[name]["source_closure_sha256"] == closures[name]
    names = {name: printed_names(code[name]) for name in sorted(fresh)}
    assert names == row["ordered_axiom_names"] and sum(map(len, names.values())) == 151

    # Bind the unchanged three-key list and the exact certificates that consume it.
    key_body, = re.findall(r"^def keys024 : List Key := \[(.*?)\]$", code[PREFIX + "KeysData"], re.M)
    assert key_body == ",".join("⟨{n},{index},{p},{q}⟩".format(**key) for key in KEYS)
    references = re.findall(r"apply certified_cons \(by exact (certified\d{4})\)", code[ENDPOINT])
    assert references == ["certified1200", "certified1201", "certified1202"]
    expected_bindings = []
    comparisons = code[PREFIX + "Comparisons24"]
    for number, key, fused, source in zip(("1200", "1201", "1202"), KEYS, SPECTRA[:3], SPECTRA[3:]):
        case = PREFIX + "ActualCase" + number
        assert f"def core{number} : Family {key['n']} := level{key['n']}.get ⟨{key['index']},by decide⟩" in code[case]
        assert f"theorem certified{number} : Certified (graph core{number}) (root {key['n']}) {key['p']} {key['q']} :=" in code[case]
        comparison = comparisons.split("theorem comparison" + number + " :", 1)[1].split("#print axioms", 1)[0]
        graphs = re.findall(r"laplacianSpectrum (DegreeOneMiddleResidualSpectrum\d+)\.graph", comparison)
        assert graphs == [fused[len("Proofs.RadenkovicGutman"):], source[len("Proofs.RadenkovicGutman"):]]
        expected_bindings.append(dict(actual_case=case,
            certificate="Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases.certified" + number,
            key=key, fused_spectrum=fused, source_spectrum=source))
    assert row["key_bindings"] == expected_bindings

    evidence = dict(kind="SAME_ORIGINAL_BATCH024_PROPOSITIONS_SAMPLE_SPLIT_NEW_SOURCE_IDENTITY",
                    endpoint=ENDPOINT, original_source_commit=ORIGINAL,
                    source_sha256=proof_sources, source_closure_sha256=closures,
                    source_count=56, expected_prior_count=45, expected_fresh_count=11,
                    expected_fresh_axiom_print_count=151, original_keys=KEYS,
                    original_statements_and_numerical_data_unchanged=True,
                    changed_source_modules=SPECTRA, pilot_exports_reused=False,
                    status="SOURCE_ONLY_REQUIRES_FRESH_NATIVE_KERNEL_RECEIPT")
    frozen_files = [MANIFEST, generator, inventory_generator, Path(__file__), INVENTORY,
                    PROJECT / "verify_extension.py", PROJECT / "verify.py", PROJECT / "module_outputs.py",
                    ROOT / "ci/rg_observed_kernel_verify.py"]
    if args.retain:
        bundle = PROJECT / "build/fresh_exports/generated_source"
        for relative in proof_sources:
            destination = bundle / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / relative, destination)
        (bundle / "generated_source_manifest.json").write_text(json.dumps(evidence, indent=2) + "\n")
        frozen = PROJECT / "build/fresh_exports/frozen_validation"
        frozen.mkdir(parents=True, exist_ok=True)
        for path in frozen_files:
            shutil.copyfile(path, frozen / path.name)
    if args.receipt:
        build = PROJECT / "build/extension"
        receipt = json.loads((build / "receipt.json").read_bytes())
        assert receipt["scope"] == "EXPLICIT_EXTENSION_CLOSURE" and receipt["endpoints"] == [ENDPOINT]
        assert receipt["mathlib"] == MATHLIB and receipt["leancert"] == LEANCERT
        assert "version 4.33.1," in receipt["lean"]
        assert receipt["global_rg"] == "NOT_PROVED" and receipt["complete_submission"] == "NOT_SUBMITTED"
        assert set(receipt["modules"]) == set(sources)
        records = {path.stem: json.loads(path.read_bytes()) for path in build.glob("Proofs.*.json")}
        assert set(records) == set(priors) | fresh
        assert all(records[name] == expected for name, expected in priors.items())
        assert {name for name, record in receipt["modules"].items() if record["mode"] == "FRESH_KERNEL_EXPORT"} == fresh
        from module_outputs import output_members
        for name, record in receipt["modules"].items():
            assert record == records[name] and record["module"] == name
            assert record["source_sha256"] == sources[name]["sha256"]
            assert record["source_closure_sha256"] == closures[name]
            assert record["axiom_profiles"] and all(set(profile) <= ALLOWED for profile in record["axiom_profiles"])
            for relative, digest, size in output_members(name, record):
                path = build / relative
                with path.open("rb") as stream:
                    assert hashlib.file_digest(stream, "sha256").hexdigest() == digest
                assert size is None or path.stat().st_size == size
        checked_names = {}
        for name in sorted(fresh):
            record = records[name]
            assert record["mode"] == "FRESH_KERNEL_EXPORT" and "origin" not in record and "transport_capsule" not in record
            assert type(record["seconds"]) in (int, float) and math.isfinite(record["seconds"]) and record["seconds"] >= 0
            log = (build / (name + ".log")).read_text()
            assert not re.search(r"\b(error|warning)(?:\([^\n]*?\))?:", log)
            matches = list(NAMED.finditer(log))
            checked_names[name] = [match[1] for match in matches]
            assert checked_names[name] == names[name]
            profiles = [sorted(set(a.strip() for a in (match[2] or "").split(",") if a.strip())) for match in matches]
            assert all(set(profile) <= ALLOWED for profile in profiles)
            grouped = [profile for match, profile in zip(matches, profiles) if match[2] is not None]
            grouped += [profile for match, profile in zip(matches, profiles) if match[2] is None]
            assert grouped == record["axiom_profiles"]
        assert sum(map(len, checked_names.values())) == 151
        export = PROJECT / "build/fresh_exports"
        for path in frozen_files:
            assert (export / "frozen_validation" / path.name).read_bytes() == path.read_bytes()
        resource = json.loads((export / "resource_observer.json").read_bytes())
        assert resource["status"] == "VERIFIER_COMPLETED" and resource["exit_code"] == 0
        assert resource["mathlib_and_lean_flags_unchanged"] is True and resource["samples"]
        assert all(type(sample["available_bytes"]) is int and sample["available_bytes"] >= 2048 * 1024**2
                   for sample in resource["samples"] if sample["lean_processes"])
        assert resource["maximum_aggregate_lean_rss"] >= max(sample["aggregate_lean_rss"] for sample in resource["samples"])
        evidence["status"] = "FRESH_NATIVE_KERNEL_RECEIPT_CHECKED_FOR_NEW_SOURCE"
        evidence["named_axiom_profiles"] = checked_names
        print("BATCH024_SPLIT_KERNEL_PASS " + json.dumps(evidence, sort_keys=True))
    else:
        print("BATCH024_SPLIT_SOURCE_PASS " + json.dumps({key: evidence[key] for key in
            ["status", "endpoint", "source_count", "expected_prior_count", "expected_fresh_count",
             "expected_fresh_axiom_print_count", "original_keys"]}))


if __name__ == "__main__":
    main()
