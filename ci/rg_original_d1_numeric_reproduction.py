"""Check bounded original D1 numeric exports without changing their sources.

The only ordinary scopes are original class00 leaf subsets and original
class10/30 chunks. The optional support-head scope contains exactly Long10 and
Long30. Every fresh row must retain historical source, closure, object, axiom,
and complete output-member identities.
"""
import argparse, hashlib, json, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCES = ROOT / "Proofs/RG_Lean_20261019"
sys.path.insert(0, str(SOURCES))
from module_outputs import output_members
from rg_plan_exact_degree_one_large import source_closure

PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
LC = "621a43d7cf21f87872392a01e874f2f1dbddc926"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def load_plan(path):
    plan = json.loads(path.read_bytes())
    assert plan["kind"] == "EXACT_ORIGINAL_D1_NUMERIC_REPRODUCTION"
    assert plan["workers"] in (1, 2) and plan["memory_reserve_mib"] == 2048
    assert plan["module_timeout"] == 1200
    assert plan["base_manifest"] == "ci/rg_reusable_analytic_kernel_base_complete_scope_capsule.json"
    assert sha((ROOT / plan["base_manifest"]).read_bytes()) == plan["base_manifest_sha256"]
    endpoints = plan["endpoints"]
    assert endpoints == sorted(set(endpoints)) and endpoints
    names = set(plan["fresh_module_origins"])
    assert 1 <= len(names) <= 16
    if plan["scope"] == "original00_leaves":
        assert plan["workers"] == 2
        allowed = {f"Proofs.RadenkovicGutmanD1Long00Leaf{i:05d}"
                   for i in range(plan["chunk"] * 10, min(plan["chunk"] * 10 + 10, 1754))}
        assert set(endpoints) == names and names <= allowed and len(names) <= 10
    elif plan["scope"] == "original_long_chunk":
        assert plan["tag"] in ("10", "30") and plan["workers"] == 2
        stem = "Proofs.RadenkovicGutmanD1Long" + plan["tag"]
        assert endpoints == [stem + f"Chunk{plan['chunk']:03d}"]
        assert all(re.fullmatch(re.escape(stem) + r"(?:Leaf\d{5}|Cells\d{4}|Chunk\d{3})", n)
                   for n in names)
    else:
        assert plan["scope"] == "original_long_heads" and plan["workers"] == 1
        assert endpoints == [
            "Proofs.RadenkovicGutmanD1Long10", "Proofs.RadenkovicGutmanD1Long30"]
        assert names == set(endpoints)
    manifests = {}
    for relative, digest in plan["original_manifests"].items():
        p = pathlib.Path(relative)
        assert p.is_relative_to("ci") and ".." not in p.parts
        raw = (ROOT / p).read_bytes()
        assert sha(raw) == digest, relative
        manifest = json.loads(raw)
        assert manifest["mathlib"] == PIN and manifest["lean_version"] == "4.33.1"
        manifests[relative] = manifest
    expected = {}
    for name, relative in plan["fresh_module_origins"].items():
        row = manifests[relative]["modules"][name]
        assert row["module"] == name and row["mode"] == "FRESH_KERNEL_EXPORT"
        assert row["axiom_profiles"] and all(set(p) <= ALLOWED for p in row["axiom_profiles"])
        list(output_members(name, row))
        expected[name] = row
    return plan, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=pathlib.Path, required=True)
    parser.add_argument("--phase", choices=("source-plan", "preflight", "compare"), required=True)
    args = parser.parse_args()
    plan, expected = load_plan(args.plan)
    hashes, closures = {}, {}
    for endpoint in plan["endpoints"]:
        h, _, c = source_closure(endpoint)
        hashes.update(h)
        closures.update(c)
    assert set(expected) <= hashes.keys()
    for name, row in expected.items():
        assert hashes[name] == row["source_sha256"], name
        assert closures[name] == row["source_closure_sha256"], name
    build = SOURCES / "build/extension"
    out = SOURCES / "build/fresh_exports"
    out.mkdir(parents=True, exist_ok=True)
    if args.phase == "source-plan":
        report = {
            "status": "EXACT_ORIGINAL_NUMERIC_SOURCES_MATCH_NO_KERNEL_PROOF",
            "endpoints": plan["endpoints"], "required_modules": len(hashes),
            "expected_fresh_modules": sorted(expected),
        }
    elif args.phase == "preflight":
        observed = set()
        frontiers = []
        for endpoint in plan["endpoints"]:
            subprocess.run([
                sys.executable, "-B", "ci/rg_restore_with_kernel_fallback.py",
                "--plan", "ci/rg_empty_restore_plan.json", "--build-directory", str(build),
                "--endpoint", endpoint, "--max-fresh", str(len(expected)), "--preflight-only",
            ], cwd=ROOT, check=True)
            frontier = json.loads((build / "bounded_kernel_fallback_plan.json").read_bytes())
            assert set(frontier["fresh_modules"]) <= expected.keys()
            observed.update(frontier["fresh_modules"])
            frontiers.append(frontier)
        assert observed == set(expected), ("Exact original frontier mismatch", sorted(observed))
        report = {
            "status": "EXACT_ORIGINAL_NUMERIC_FRONTIER_NO_KERNEL_PROOF",
            "endpoints": plan["endpoints"], "fresh_modules": sorted(observed),
            "frontiers": frontiers,
        }
    else:
        receipt = json.loads((build / "receipt.json").read_bytes())
        assert receipt["scope"] == "EXPLICIT_EXTENSION_CLOSURE"
        assert receipt["endpoints"] == plan["endpoints"]
        assert receipt["mathlib"] == PIN and receipt["leancert"] == LC
        assert "version 4.33.1," in receipt["lean"]
        fresh = {n: r for n, r in receipt["modules"].items() if r["mode"] == "FRESH_KERNEL_EXPORT"}
        assert set(fresh) == set(expected), ("Unexpected fresh modules", sorted(fresh))
        logical = 0
        for name, row in fresh.items():
            old = expected[name]
            assert row == json.loads((build / (name + ".json")).read_bytes())
            for key in ("module", "source_sha256", "source_closure_sha256",
                        "output_sha256", "axiom_profiles"):
                assert row[key] == old[key], (name, key)
            members = tuple(sorted(output_members(name, row)))
            assert members == tuple(sorted(output_members(name, old))), (name, "module members")
            for relative, digest, size in members:
                path = build / relative
                assert path.resolve().is_relative_to(build.resolve())
                assert path.is_file() and (size is None or path.stat().st_size == size)
                with path.open("rb") as stream:
                    assert hashlib.file_digest(stream, "sha256").hexdigest() == digest
                logical += path.stat().st_size
        report = {
            "status": "FRESH_KERNEL_NUMERIC_OUTPUTS_MATCH_ORIGINAL_IDENTITIES",
            "endpoints": plan["endpoints"], "required_modules": len(receipt["modules"]),
            "fresh_modules": len(fresh), "verified_output_bytes": logical,
        }
    (out / ("original_numeric_" + args.phase.replace("-", "_") + ".json")).write_text(
        json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "frontiers"}), flush=True)


if __name__ == "__main__":
    main()

