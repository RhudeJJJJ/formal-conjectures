#!/usr/bin/env python3
"""Proof-only continuation of the original Middle residual key (10,10,2,2).

Split the two exact LU checks into eighteen kernel-checked sample lemmas. Move
comparison0493, byte-for-byte, into its own module. The original actual-tree
certificate is unchanged except for its import. A final theorem exposes the
exact original key predicate. Preparation is not a successful kernel check.
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

ORIGINAL = "15d45e8d3ed3bacaf3afe7d85488a42f08302d76"
INV_SHA = "22c745d4fdb281e8cc2172ffcc3b975005da4fb4777e9021e85f46bbc9a665e0"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
LEANCERT = "621a43d7cf21f87872392a01e874f2f1dbddc926"
PROJECT = Path("Proofs/RG_Lean_20261019")
INV_PATH = "ci/rg_middle_residual_batch_inventory_20261109.json"
P = "Proofs.RadenkovicGutman"
F = P + "DegreeOneMiddleResidualFinite"
SOURCE = P + "DegreeOneMiddleResidualSpectrum1120"
FUSED = P + "DegreeTwoThreeSpectrum4972"
COMPARISON = F + "Comparison0493"
BULK = F + "Comparisons09"
CASE = F + "ActualCase0493"
ENDPOINT = F + "Singleton0493"
NS = "Gebendorfer.RadenkovicGutman."
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NAMED = re.compile(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def rel(module):
    return (PROJECT / (module.replace(".", "/") + ".lean")).as_posix()


def names(raw):
    text = raw.decode()
    namespaces = re.findall(r"^namespace\s+(\S+)\s*$", text, re.M)
    assert len(namespaces) == 1
    result = re.findall(r"^#print axioms (\w+)\s*$", text, re.M)
    assert result and len(result) == len(set(result))
    return [namespaces[0] + "." + name for name in result]


def split(raw):
    text = raw.decode()
    start, end = text.index("theorem matrix_certificates :"), text.index("theorem graph_charpoly :")
    original = text[start:end]
    ending = " := by decide +kernel\n"
    assert original.endswith(ending)
    header = original[:-len(ending)]
    match = re.fullmatch(r"theorem matrix_certificates : ∀ k : Fin (\d+),\n(.+)", header, re.S)
    assert match and int(match[1]) == 18
    assert len(re.findall(r"\bk\b", match[2])) == 4
    samples = []
    for index in range(18):
        body = re.sub(r"\bk\b", f"({index} : Fin 18)", match[2])
        samples.append(f"theorem matrix_certificate_{index:02d} :\n{body} := by decide +kernel\n"
                       f"#print axioms matrix_certificate_{index:02d}\n")
    proof = header + " := by\n  intro k\n  fin_cases k\n"
    proof += "".join(f"  · exact matrix_certificate_{index:02d}\n" for index in range(18))
    candidate = (text[:start] + "\n".join(samples) + "\n" + proof + text[end:]).encode()
    assert len(names(raw)) == 5 and len(names(candidate)) == 23
    assert candidate.startswith(text[:start].encode()) and candidate.endswith(text[end:].encode())
    return candidate, dict(original_type_sha256=sha(header.encode()),
                          unchanged_prefix_sha256=sha(text[:start].encode()),
                          unchanged_suffix_sha256=sha(text[end:].encode()), samples=18)


def plan(inventory_raw, read_original):
    assert sha(inventory_raw) == INV_SHA
    inventory = json.loads(inventory_raw)
    assert inventory["source_commit"] == ORIGINAL
    assert inventory["mathlib"] == MATHLIB and inventory["leancert"] == LEANCERT
    row = next(row for row in inventory["batches"] if row["index"] == "009")
    originals = {}

    def original(module):
        if module not in originals:
            raw = read_original(rel(module))
            assert sha(raw) == row["source_sha256"][rel(module)], module
            originals[module] = raw
        return originals[module]

    candidates, preservation = {}, {}
    for module in (SOURCE, FUSED):
        candidates[module], preservation[module] = split(original(module))
    bulk = original(BULK).decode()
    start = bulk.index("theorem comparison0493 :")
    end = bulk.index("theorem comparison0494 :", start)
    block = bulk[start:end]
    assert block.count("#print axioms comparison0493") == 1
    assert "DegreeTwoThreeSpectrum4972.graph" in block
    assert "DegreeOneMiddleResidualSpectrum1120.graph" in block
    namespace = NS + "DegreeOneMiddleResidualFiniteComparisons"
    candidates[COMPARISON] = ("/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/\n"
        f"import {SOURCE}\nimport {FUSED}\nnamespace {namespace}\n"
        "set_option maxHeartbeats 0\n" + block + "end " + namespace + "\n").encode()
    # Preserve the original aggregate interface without duplicate declarations.
    reduced = bulk[:start] + bulk[end:]
    reduced = reduced.replace("namespace " + namespace + "\n",
                              "import " + COMPARISON + "\nnamespace " + namespace + "\n", 1)
    candidates[BULK] = reduced.encode()
    actual = original(CASE)
    assert actual.count(("import " + BULK + "\n").encode()) == 1
    candidates[CASE] = actual.replace(("import " + BULK + "\n").encode(),
                                      ("import " + COMPARISON + "\n").encode(), 1)
    key_ns = NS + "DegreeOneMiddleResidualFiniteKeys"
    candidates[ENDPOINT] = ("/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/\n"
        f"import {F}KeysData\nimport {CASE}\nnamespace {key_ns}\nopen SmallGeFourKeys\n"
        "theorem certified_key0493 : Certified (⟨10,10,2,2⟩ : Key) := by\n"
        "  exact DegreeOneMiddleResidualFiniteActualCases.certified0493\n"
        "#print axioms certified_key0493\nend " + key_ns + "\n").encode()
    sources, dependencies, closures = {}, {}, {}

    def visit(module):
        if module in sources:
            return
        raw = candidates[module] if module in candidates else original(module)
        # These frozen source closures contain no such tokens, even in comments.
        assert not re.search(rb"\b(sorry|admit|native_decide)\b|^\s*axiom\s", raw, re.M), module
        sources[module] = raw
        dependencies[module] = sorted(set(re.findall(
            r"^\s*(?:public\s+)?import\s+(Proofs\.[\w.]+)\s*$", raw.decode(), re.M)))
        for dependency in dependencies[module]:
            visit(dependency)
        closures[module] = sha(json.dumps([module, sha(raw), MATHLIB, LEANCERT,
            [(dependency, closures[dependency]) for dependency in dependencies[module]]],
            separators=(",", ":")).encode())

    visit(ENDPOINT)
    priors = inventory["expected_prior_rows"]
    fresh = sorted(set(sources) - set(priors))
    assert fresh == sorted([SOURCE, FUSED, COMPARISON, CASE, ENDPOINT])
    for module in set(sources) & set(priors):
        assert priors[module]["source_sha256"] == sha(sources[module]), module
        assert priors[module]["source_closure_sha256"] == closures[module], module
    ordered = {module: names(sources[module]) for module in fresh}
    assert sum(map(len, ordered.values())) == 51
    evidence = dict(kind="ORIGINAL_KEY0493_SAME_PROPOSITION_NEW_PROOF_SOURCE",
        status="SOURCE_ONLY_REQUIRES_FRESH_KERNEL_RECEIPT", original_source_commit=ORIGINAL,
        original_inventory_sha256=INV_SHA, endpoint=ENDPOINT, key=dict(n=10,index=10,p=2,q=2),
        lean_version="4.33.1", mathlib=MATHLIB, leancert=LEANCERT,
        source_sha256={rel(module):sha(raw) for module,raw in sources.items()},
        source_closure_sha256=closures, dependencies=dependencies,
        prior_modules=sorted(set(sources)&set(priors)), fresh_modules=fresh,
        ordered_axiom_names=ordered, source_preservation=preservation,
        comparison_body_sha256=sha(block.encode()), original_actual_case_sha256=sha(actual),
        actual_case_only_import_changed=True, complete_middle_family=False, global_rg_proved=False,
        generated_files_sha256={rel(module):sha(raw) for module,raw in candidates.items()})
    return candidates, sources, evidence, inventory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    project = root / PROJECT
    assert (root / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1"
    raw = (root / INV_PATH).read_bytes()
    def read_original(relative):
        return subprocess.check_output(["git", "show", ORIGINAL+":"+relative], cwd=root)
    candidates, sources, evidence, inventory = plan(raw, read_original)
    for relative, digest in inventory["input_sha256"].items():
        assert sha((root/relative).read_bytes()) == digest
    export = project / "build/fresh_exports"
    bundle = export / "generated_source"
    for module, expected in candidates.items():
        path = root / rel(module)
        if args.receipt:
            assert path.read_bytes() == expected, module
        else:
            if path.exists() and path.read_bytes() != expected:
                assert path.read_bytes() == read_original(rel(module)), module
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(expected)
    for module, expected in sources.items():
        assert (root / rel(module)).read_bytes() == expected, module
    frozen = export / "frozen_validation"
    frozen_files = [Path(__file__), root/INV_PATH, project/"verify.py", project/"verify_extension.py",
                    project/"module_outputs.py", root/"ci/rg_observed_kernel_verify.py"]
    if not args.receipt:
        for module, expected in sources.items():
            path = bundle / rel(module)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(expected)
        (bundle/"generated_source_manifest.json").write_text(json.dumps(evidence,indent=2)+"\n")
        frozen.mkdir(parents=True,exist_ok=True)
        for path in frozen_files:
            shutil.copyfile(path, frozen/path.name)
        print("CASE0493_SOURCE_PASS",json.dumps({key:evidence[key] for key in
            ("endpoint","status","key","fresh_modules")}))
        return
    build = project / "build/extension"
    receipt = json.loads((build/"receipt.json").read_bytes())
    assert receipt["endpoints"] == [ENDPOINT] and receipt["scope"] == "EXPLICIT_EXTENSION_CLOSURE"
    assert receipt["mathlib"] == MATHLIB and receipt["leancert"] == LEANCERT
    assert "version 4.33.1," in receipt["lean"]
    assert receipt["global_rg"] == "NOT_PROVED" and receipt["complete_submission"] == "NOT_SUBMITTED"
    assert set(receipt["modules"]) == set(sources)
    records = {path.stem:json.loads(path.read_bytes()) for path in build.glob("Proofs.*.json")}
    priors = inventory["expected_prior_rows"]
    assert set(records) == set(priors)|set(evidence["fresh_modules"])
    assert all(records[module] == row for module,row in priors.items())
    sys.path.insert(0,str(project))
    from module_outputs import output_members
    for module,row in receipt["modules"].items():
        assert row == records[module] and row["module"] == module
        assert row["source_sha256"] == sha(sources[module])
        assert row["source_closure_sha256"] == evidence["source_closure_sha256"][module]
        assert row["axiom_profiles"] and all(set(p)<=ALLOWED for p in row["axiom_profiles"])
        assert (row["mode"] == "FRESH_KERNEL_EXPORT") == (module in evidence["fresh_modules"])
        for relative,digest,size in output_members(module,row):
            path = build/relative
            with path.open("rb") as stream:
                assert hashlib.file_digest(stream,"sha256").hexdigest() == digest
            assert size is None or path.stat().st_size == size
    for module in evidence["fresh_modules"]:
        row = records[module]
        assert "origin" not in row and "transport_capsule" not in row
        assert type(row["seconds"]) in (int,float) and math.isfinite(row["seconds"]) and row["seconds"]>=0
        log = (build/(module+".log")).read_text()
        assert not re.search(r"\b(error|warning)(?:\([^\n]*?\))?:",log)
        matches = list(NAMED.finditer(log))
        assert [match[1] for match in matches] == evidence["ordered_axiom_names"][module]
        profiles = [sorted(set(a.strip() for a in (match[2] or "").split(",") if a.strip())) for match in matches]
        assert all(set(p)<=ALLOWED for p in profiles)
        grouped = [p for m,p in zip(matches,profiles) if m[2] is not None]
        grouped += [p for m,p in zip(matches,profiles) if m[2] is None]
        assert grouped == row["axiom_profiles"]
    resource = json.loads((export/"resource_observer.json").read_bytes())
    assert resource["status"] == "VERIFIER_COMPLETED" and resource["exit_code"] == 0
    assert resource["mathlib_and_lean_flags_unchanged"] is True
    assert resource["samples"] and all(s["available_bytes"]>=2048*1024**2
        for s in resource["samples"] if s["lean_processes"])
    for path in frozen_files:
        assert path.read_bytes() == (frozen/path.name).read_bytes()
    evidence["status"] = "FRESH_KERNEL_RECEIPT_CHECKED"
    evidence["maximum_aggregate_lean_rss"] = resource["maximum_aggregate_lean_rss"]
    (export/"case0493_validation.json").write_text(json.dumps(evidence,indent=2)+"\n")
    print("CASE0493_KERNEL_PASS",json.dumps({key:evidence[key] for key in ("endpoint","status","key")}))


if __name__ == "__main__":
    main()
