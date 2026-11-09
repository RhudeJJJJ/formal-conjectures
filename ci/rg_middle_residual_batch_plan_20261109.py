#!/usr/bin/env python3
"""Freeze and check the original remaining Middle residual certificate batches.

This checks source identities and plans a bounded kernel replay. It does not
claim that an object archive is available, authenticate archived objects, or
replace the mandatory native Lean verification and completion receipts.
"""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCE_ROOT = ROOT / "Proofs/RG_Lean_20261019"
sys.path.insert(0, str(SOURCE_ROOT))
from verify import without_comments

SOURCE_COMMIT = "15d45e8d3ed3bacaf3afe7d85488a42f08302d76"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
LEANCERT = "621a43d7cf21f87872392a01e874f2f1dbddc926"
LEAN_VERSION = "4.33.1"
BASE_CAPSULE = "ci/rg_reusable_analytic_kernel_base_complete_scope_capsule.json"
RESTORE_PLAN = "ci/rg_middle_residual_certificates000_restore_plan_20261108.json"
INVENTORY = ROOT / "ci/rg_middle_residual_batch_inventory_20261109.json"
PREFIX = "Proofs.RadenkovicGutmanDegreeOneMiddleResidualFinite"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IMPORTS = re.compile(r"^\s*(?:public\s+)?import\s+((?:Proofs|LeanCert)\.[\w.]+)\s*$", re.M)
FORBIDDEN = re.compile(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", re.M)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def serialized(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


class Sources:
    def __init__(self):
        self.raw = {}
        self.code = {}
        self.paths = {}
        self.dependencies = {}
        self.hashes = {}
        self.closures = {}
        raw = subprocess.check_output([
            "git", "ls-tree", "-rz", SOURCE_COMMIT, "--",
            "Proofs/RG_Lean_20261019/Proofs",
            "Proofs/RG_Lean_20261019/ThirdParty/LeanCert",
        ], cwd=ROOT)
        self.original_blobs = {}
        for entry in raw.split(b"\0"):
            if not entry:
                continue
            fields, path = entry.split(b"\t", 1)
            _mode, kind, digest = fields.decode().split()
            if kind == "blob":
                self.original_blobs[path.decode()] = digest

    def visit(self, name):
        if name in self.raw:
            return
        base = SOURCE_ROOT / "ThirdParty/LeanCert" if name.startswith("LeanCert.") else SOURCE_ROOT
        path = base / (name.replace(".", "/") + ".lean")
        raw = path.read_bytes()
        rel = path.relative_to(ROOT).as_posix()
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        assert self.original_blobs.get(rel) == blob, ("Original source changed", rel)
        code = without_comments(raw.decode())
        assert not FORBIDDEN.search(code), ("Unaccepted proof form", name)
        self.raw[name] = raw
        self.code[name] = code
        self.paths[name] = rel
        self.hashes[name] = sha256(raw)
        self.dependencies[name] = sorted(set(IMPORTS.findall(code)))
        for dependency in self.dependencies[name]:
            self.visit(dependency)

    def closure_hash(self, name):
        if name not in self.closures:
            identity = [name, self.hashes[name], MATHLIB, LEANCERT,
                        [(d, self.closure_hash(d)) for d in self.dependencies[name]]]
            self.closures[name] = sha256(json.dumps(identity, separators=(",", ":")).encode())
        return self.closures[name]

    def scope(self, name):
        result = set()

        def walk(current):
            if current in result:
                return
            result.add(current)
            for dependency in self.dependencies[current]:
                walk(dependency)

        self.visit(name)
        walk(name)
        return result

    def printed_names(self, name):
        code = self.code[name]
        namespaces = re.findall(r"^namespace\s+(\S+)\s*$", code, re.M)
        # Every fresh module in this fixed generated family has one namespace.
        # Refuse to guess if a future source introduces a different structure.
        assert len(namespaces) == 1, ("Unexpected namespace structure", name, namespaces)
        namespace = namespaces[0]
        printed = re.findall(r"^\s*#print\s+axioms\s+(.+?)\s*$", code, re.M)
        assert printed and len(printed) == len(set(printed)), ("Missing or duplicate axiom print", name)
        result = []
        for argument in printed:
            assert re.fullmatch(r"[A-Za-z_][\w.]*", argument), ("Unexpected axiom print", name, argument)
            if argument.startswith("_root_."):
                result.append(argument[len("_root_."):])
            elif argument.startswith(namespace + "."):
                result.append(argument)
            else:
                assert "." not in argument, ("Ambiguous relative axiom name", name, argument)
                result.append(namespace + "." + argument)
        return result


def read_priors():
    paths = json.loads((ROOT / RESTORE_PLAN).read_bytes())
    assert paths == [
        "ci/rg_all111_finite_original_projected_parents_20261028/083.json",
        "ci/rg_middle_residual_list_assembly_run42345489172_prior_exports.json",
    ], "Original fixed restore plan changed"
    prior = {}
    origins = {}
    expected_prior_rows = {}
    manifest_hashes = {RESTORE_PLAN: sha256((ROOT / RESTORE_PLAN).read_bytes())}
    for path in [BASE_CAPSULE, *paths]:
        raw = (ROOT / path).read_bytes()
        manifest_hashes[path] = sha256(raw)
        manifest = json.loads(raw)
        assert manifest["mathlib"] == MATHLIB and manifest["lean_version"] == LEAN_VERSION
        for name, row in manifest["modules"].items():
            assert name == row["module"]
            assert row["mode"] in {"PRIOR_VERIFIED_JOB_EXPORT", "FRESH_KERNEL_EXPORT"}
            assert row["axiom_profiles"] and all(set(a) <= ALLOWED_AXIOMS for a in row["axiom_profiles"])
            if name in prior:
                previous = prior[name]
                for field in ["source_sha256", "source_closure_sha256", "output_sha256", "axiom_profiles"]:
                    assert previous[field] == row[field], ("Conflicting prior identity", name, field)
                assert previous.get("additional_outputs", []) == row.get("additional_outputs", [])
            # Preserve the actual fixed restore order. Existing helpers retain
            # each row's real origin when they install the objects.
            prior[name] = row
            origins.setdefault(name, []).append(path)
            if path == BASE_CAPSULE:
                origin = row["origin"] if row["mode"] == "PRIOR_VERIFIED_JOB_EXPORT" else {
                    key: manifest[key] for key in ["repository", "run", "job", "source_commit", "artifact_id", "artifact_sha256"]
                }
                restored = {
                    **row, "mode": "PRIOR_VERIFIED_JOB_EXPORT", "origin": origin,
                    "transport_capsule": {key: manifest[key] for key in ["run", "job", "source_commit", "artifact_id", "artifact_sha256"]},
                }
            else:
                assert row["mode"] == "FRESH_KERNEL_EXPORT"
                origin = {key: manifest[key] for key in ["repository", "run", "job", "source_commit", "artifact_id", "artifact_sha256"]}
                if "origin_context" in manifest:
                    origin["context"] = manifest["origin_context"]
                restored = {**row, "mode": "PRIOR_VERIFIED_JOB_EXPORT", "origin": origin}
            expected_prior_rows[name] = restored
    assert len(expected_prior_rows) == 707
    return prior, origins, paths, manifest_hashes, expected_prior_rows


def key_batches(sources):
    name = PREFIX + "KeysData"
    sources.visit(name)
    definitions = re.findall(r"^def keys(\d{3}) : List Key := \[(.*?)\]$", sources.code[name], re.M)
    assert [index for index, _ in definitions] == [f"{i:03d}" for i in range(25)]
    result = {}
    for index, body in definitions:
        rows = re.findall(r"⟨(\d+),(\d+),(\d+),(\d+)⟩", body)
        assert ",".join("⟨" + ",".join(row) + "⟩" for row in rows) == body
        result[index] = [tuple(map(int, row)) for row in rows]
    all_keys = [key for rows in result.values() for key in rows]
    assert len(all_keys) == len(set(all_keys)) == 1232
    return result


def actual_case_keys(sources, endpoint):
    result = {}
    imports = sources.dependencies[endpoint]
    cases = [name for name in imports if name.startswith(PREFIX + "ActualCase")]
    assert all(re.fullmatch(re.escape(PREFIX) + r"ActualCase\d{4}", name) for name in cases)
    for name in cases:
        code = sources.code[name]
        core = re.findall(r"^def core(\d{4}) : Family (\d+) := level(\d+)\.get ⟨(\d+),by decide⟩$", code, re.M)
        assert len(core) == 1 and core[0][1] == core[0][2], ("Unexpected original core", name)
        number, order, _level, index = core[0]
        certificates = re.findall(
            r"^theorem (certified\d{4}(?:swap)?) : Certified \(graph core(\d{4})\) \(root (\d+)\) (\d+) (\d+) :=$",
            code, re.M,
        )
        assert len(certificates) in (1, 2)
        for theorem, case, root, p, q in certificates:
            assert case == number and root == order and theorem not in result
            result[theorem] = (int(order), int(index), int(p), int(q))
    references = re.findall(r"apply certified_cons \(by exact (certified\d{4}(?:swap)?)\)", sources.code[endpoint])
    assert len(references) == len(set(references))
    assert set(references) == set(result), ("Unexpected unused or missing case certificate", endpoint)
    return [result[name] for name in references]


def batch_record(index, sources, prior, origins, keys):
    endpoint = PREFIX + "CertificateBatch" + index
    scope = sources.scope(endpoint)
    reused = sorted(scope & prior.keys())
    fresh = sorted(scope - prior.keys())
    assert actual_case_keys(sources, endpoint) == keys[index], ("Key/certificate association mismatch", index)
    for name in reused:
        assert sources.hashes[name] == prior[name]["source_sha256"], ("Prior source mismatch", name)
        assert sources.closure_hash(name) == prior[name]["source_closure_sha256"], ("Prior closure mismatch", name)
    assert len(reused) == 45 and 1 <= len(fresh) <= 512
    names = {name: sources.printed_names(name) for name in fresh}
    return {
        "index": index,
        "endpoint": endpoint,
        "declaration": "Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys.certified_keys" + index,
        "key_count": len(keys[index]),
        "source_count": len(scope),
        "fresh_count": len(fresh),
        "prior_count": len(reused),
        "source_sha256": {sources.paths[name]: sources.hashes[name] for name in sorted(scope)},
        "source_closure_sha256": {name: sources.closure_hash(name) for name in sorted(scope)},
        "endpoint_source_closure_sha256": sources.closure_hash(endpoint),
        "fresh_modules": fresh,
        "prior_modules": reused,
        "prior_manifest_paths": {name: origins[name] for name in reused},
        "ordered_axiom_names": names,
        "fresh_axiom_print_count": sum(map(len, names.values())),
        "status": "SOURCE_PLAN_REQUIRES_SUCCESSFUL_NATIVE_KERNEL_RECEIPT",
    }


def generate():
    assert (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1"
    sources = Sources()
    prior, origins, manifests, manifest_hashes, expected_prior_rows = read_priors()
    keys = key_batches(sources)
    control = batch_record("000", sources, prior, origins, keys)
    assert (control["source_count"], control["fresh_count"], control["key_count"], control["fresh_axiom_print_count"]) == (194, 149, 52, 692)
    batches = [batch_record(f"{i:03d}", sources, prior, origins, keys) for i in [24, *range(1, 24)]]
    assert sum(row["key_count"] for row in batches) == 1180
    source_union = set().union(*(set(row["source_closure_sha256"]) for row in batches))
    fresh_union = set().union(*(set(row["fresh_modules"]) for row in batches))
    return {
        "kind": "ORIGINAL_MIDDLE_RESIDUAL_REMAINING_BATCH_SOURCE_PLAN",
        "source_commit": SOURCE_COMMIT,
        "lean_version": LEAN_VERSION,
        "mathlib": MATHLIB,
        "leancert": LEANCERT,
        "base_capsule": BASE_CAPSULE,
        "restore_plan": RESTORE_PLAN,
        "restore_manifests": manifests,
        "input_sha256": manifest_hashes,
        "expected_prior_rows": expected_prior_rows,
        "total_keys": 1232,
        "reference_batch000": control,
        "remaining_key_count": 1180,
        "remaining_batch_count": 24,
        "remaining_source_union_count": len(source_union),
        "remaining_fresh_union_count": len(fresh_union),
        "scheduled_fresh_export_occurrences": sum(row["fresh_count"] for row in batches),
        "scheduled_fresh_axiom_print_occurrences": sum(row["fresh_axiom_print_count"] for row in batches),
        "limits": {"workers_per_job": 1, "memory_reserve_mib": 2048, "module_timeout_seconds": 600, "job_timeout_minutes": 360},
        "batches": batches,
        "proof_status": "NOT_PROVEN_BY_SOURCE_INVENTORY",
        "family_status": "DEGREE_ONE_MIDDLE_STILL_REQUIRES_COMPLETE_ASSEMBLY",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--inventory", type=pathlib.Path, default=INVENTORY)
    parser.add_argument("--batch", help="Check one three-digit batch against the frozen source inventory")
    args = parser.parse_args()
    if args.batch:
        assert args.check and re.fullmatch(r"(?:00[1-9]|01[0-9]|02[0-4])", args.batch)
        inventory = json.loads(args.inventory.read_bytes())
        assert inventory["source_commit"] == SOURCE_COMMIT
        prior, origins, manifests, hashes, expected_prior_rows = read_priors()
        assert inventory["input_sha256"] == hashes and inventory["restore_manifests"] == manifests
        assert inventory["expected_prior_rows"] == expected_prior_rows
        sources = Sources()
        keys = key_batches(sources)
        actual = batch_record(args.batch, sources, prior, origins, keys)
        expected = [row for row in inventory["batches"] if row["index"] == args.batch]
        assert len(expected) == 1 and expected[0] == actual, "Frozen batch inventory mismatch"
        print(json.dumps({key: actual[key] for key in ["index", "endpoint", "key_count", "source_count", "prior_count", "fresh_count", "fresh_axiom_print_count", "status"]}, sort_keys=True))
        return
    actual = generate()
    if args.write:
        args.inventory.write_bytes(serialized(actual))
    else:
        assert json.loads(args.inventory.read_bytes()) == actual, "Frozen source inventory mismatch"
    print(json.dumps({key: actual[key] for key in ["kind", "remaining_key_count", "remaining_batch_count", "remaining_source_union_count", "remaining_fresh_union_count", "scheduled_fresh_export_occurrences", "proof_status"]}, sort_keys=True))


if __name__ == "__main__":
    main()
