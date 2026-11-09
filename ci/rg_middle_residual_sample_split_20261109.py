#!/usr/bin/env python3
"""Prepare a source-only, sample-by-sample kernel proof candidate.

The numerical data, original matrix_certificates proposition, and every later
declaration remain byte-for-byte unchanged. Each new sample theorem must still
be checked by Lean's kernel. This program neither compiles Lean nor claims a
successful proof. Its output has new source and dependency-closure identities.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


SOURCE_COMMIT = "15d45e8d3ed3bacaf3afe7d85488a42f08302d76"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
LEANCERT = "621a43d7cf21f87872392a01e874f2f1dbddc926"
MODULE_PREFIX = "Proofs.RadenkovicGutmanDegreeOneMiddleResidualSpectrum"
PROJECT = Path("Proofs/RG_Lean_20261019")
ORIGINAL_SHA256 = {
    "1715": "91337c313f94d064a0d94848296b62332905d3fc2323ecd515b546d26cfc264d",
    "1749": "c35778151aea3eff6e48f9c4f9826311f14e2c9b669b7602e5d6c2aa9eef2c96",
    "1956": "efafa5c5b50f9a46e782a73dc0349dea14f7c099eefcd9820faaf37e07a42e50",
    "2356": "6449ad88a1d6051e8dca87ed2e2ae45a18ee09547643b4e5944c75993626fa00",
    "2357": "59c8359ed3c5a2104d4855ce8714e93a6daf1fca4868d36a0aa0a369ace9c942",
    "2358": "9c7127d660aded0582b17123bd39321135064f4098e987f9d28637b1250081ca",
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def split_source(raw, index):
    assert sha(raw) == ORIGINAL_SHA256[index], ("Changed original source", index)
    text = raw.decode("utf-8")
    namespace = "Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualSpectrum" + index
    assert text.count("namespace " + namespace + "\n") == 1
    start = text.index("theorem matrix_certificates :")
    end = text.index("theorem graph_charpoly :", start)
    original = text[start:end]
    old_proof = " := by decide +kernel\n"
    assert original.endswith(old_proof)
    header = original[:-len(old_proof)]
    match = re.fullmatch(r"theorem matrix_certificates : ∀ k : Fin (\d+),\n(.+)",
                         header, re.S)
    assert match and int(match[1]) == 18
    samples, body = int(match[1]), match[2]
    # Freeze the four intended occurrences: the shifted matrix sample, L, U,
    # and the sample argument of polynomial evaluation.
    assert len(re.findall(r"\bk\b", body)) == 4
    names = [f"matrix_certificate_{k:02d}" for k in range(samples)]
    lemmas = []
    for k, name in enumerate(names):
        instance = re.sub(r"\bk\b", f"({k} : Fin {samples})", body)
        lemmas.append(f"theorem {name} :\n{instance} := by decide +kernel\n"
                      f"#print axioms {name}\n")
    joined = (header + " := by\n  intro k\n  fin_cases k\n"
              + "".join("  · exact " + name + "\n" for name in names))
    replacement = "\n".join(lemmas) + "\n" + joined
    result = (text[:start] + replacement + text[end:]).encode("utf-8")
    # Only one proof site is edited; the original proposition and all data
    # remain in the result. The original five terminal axiom prints remain.
    assert result[:len(text[:start].encode())] == text[:start].encode()
    assert result.endswith(text[end:].encode())
    assert joined.startswith(header + " := by\n")
    assert result.count(b"#print axioms ") == 23
    assert b"sorry" not in result and b"native_decide" not in result
    return result, {
        "new_sample_theorems": [namespace + "." + name for name in names],
        "original_matrix_certificates_statement_sha256": sha(header.encode()),
        "original_prefix_sha256": sha(text[:start].encode()),
        "unchanged_suffix_sha256": sha(text[end:].encode()),
        "ordered_axiom_names": [namespace + "." + name for name in names]
        + [namespace + "." + name for name in
           ("matrix_certificates", "graph_charpoly", "boxes_accepted",
            "factorization", "actual_graph_bounds")],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--spectra", nargs="+", choices=sorted(ORIGINAL_SHA256),
                        default=sorted(ORIGINAL_SHA256))
    args = parser.parse_args()
    repo, output = args.repo.resolve(), args.output_root.resolve()
    assert output != repo and not output.is_relative_to(repo), "Use a separate candidate directory"
    assert len(args.spectra) == len(set(args.spectra))
    inventory_path = repo / "ci/rg_middle_residual_batch_inventory_20261109.json"
    inventory_raw = inventory_path.read_bytes()
    inventory = json.loads(inventory_raw)
    assert inventory["source_commit"] == SOURCE_COMMIT
    assert inventory["mathlib"] == MATHLIB and inventory["leancert"] == LEANCERT
    batch = next(b for b in inventory["batches"] if b["index"] == "024")
    rows = []
    for index in args.spectra:
        module = MODULE_PREFIX + index
        relative = PROJECT / (module.replace(".", "/") + ".lean")
        original = (repo / relative).read_bytes()
        candidate, evidence = split_source(original, index)
        deps = sorted(set(re.findall(r"^import (Proofs\.[\w.]+)$",
                                     original.decode(), re.M)))
        assert len(deps) == 2
        closure = sha(json.dumps(
            [module, sha(candidate), MATHLIB, LEANCERT,
             [(d, batch["source_closure_sha256"][d]) for d in deps]],
            separators=(",", ":")).encode())
        destination = output / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        if destination.exists():
            assert destination.read_bytes() == candidate, "Refuse to replace a different candidate"
        else:
            destination.write_bytes(candidate)
        rows.append({
            "module": module, "path": relative.as_posix(),
            "original_source_sha256": sha(original),
            "candidate_source_sha256": sha(candidate),
            "original_source_closure_sha256": batch["source_closure_sha256"][module],
            "candidate_source_closure_sha256": closure,
            "unchanged_dependency_closures": {d: batch["source_closure_sha256"][d] for d in deps},
            "samples": 18, "original_axiom_prints": 5, "candidate_axiom_prints": 23,
            "all_numerical_data_byte_identical": True,
            "original_matrix_certificates_type_byte_identical": True,
            "all_later_declarations_byte_identical": True,
            **evidence,
        })
    manifest = {
        "kind": "SOURCE_ONLY_ORIGINAL_SPECTRAL_PROPOSITION_SAMPLE_SPLIT_CANDIDATE",
        "original_source_commit": SOURCE_COMMIT,
        "original_inventory_sha256": sha(inventory_raw),
        "lean_version": "4.33.1", "mathlib": MATHLIB, "leancert": LEANCERT,
        "generator_sha256": sha(Path(__file__).read_bytes()),
        "status": "REQUIRES_FRESH_NATIVE_KERNEL_CHECK; NOT_AN_ORIGINAL_15D45_PROOF_OBJECT",
        "changed_proof": "Eighteen closed sample theorems plus finite cases on Fin18",
        "modules": rows,
    }
    output.mkdir(parents=True, exist_ok=True)
    manifest_path = output / "candidate_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": manifest["status"], "modules": len(rows),
                      "output": str(output), "manifest": str(manifest_path)}))


if __name__ == "__main__":
    main()
