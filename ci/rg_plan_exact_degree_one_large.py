"""Plan exact original RG reuse before downloading proof objects.

This program proves nothing. It preserves every transitive source dependency,
selects source/closure-matching original exports, and checks current archive
metadata. A separate bounded restore authenticates complete ZIPs and every
selected output member. The unchanged strict verifier remains mandatory.
"""
import argparse, hashlib, json, os, pathlib, re, subprocess, sys
import urllib.error, urllib.request

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCES = ROOT / "Proofs/RG_Lean_20261019"
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
LC = "621a43d7cf21f87872392a01e874f2f1dbddc926"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
RUN_ARTIFACTS = {}
FRESH = {
    "Proofs.RadenkovicGutmanD1OriginalSharedBothLong",
    "Proofs.RadenkovicGutmanOriginalDegreeOneLarge",
    "Proofs.RadenkovicGutmanRemainingThreeAssembly",
}
sys.path.insert(0, str(SOURCES))
from module_outputs import output_members
from verify import without_comments


def sha(data):
    return hashlib.sha256(data).hexdigest()


def materialize_missing(name):
    """Use only existing pinned source producers; never invent a replacement."""
    compositional = re.match(
        r"(Proofs\.RadenkovicGutmanD1Long00Leaf\d{5}CompositionalRepair)", name)
    segmented = re.match(
        r"(Proofs\.RadenkovicGutmanD1Long00Leaf\d{5}Repair)", name)
    original_leaf = re.fullmatch(
        r"Proofs\.RadenkovicGutmanD1Long(00|30)Leaf(\d{5})", name)
    if compositional:
        command = ["ci/rg_compositional_d1_repair.py", "--endpoint", compositional[1]]
    elif segmented:
        command = ["ci/rg_segmented_d1_repair.py", "--endpoint", segmented[1]]
    elif original_leaf:
        command = ["ci/rg_materialize_shared_arm.py", "--tag", original_leaf[1],
                   "--chunk", str(int(original_leaf[2]) // 10)]
    elif name.startswith("Proofs.RadenkovicGutmanCompactFinite"):
        command = ["ci/rg_materialize_compact_closed_families.py",
                   "--endpoint", name, "--max-raw-mib", "512"]
    else:
        raise FileNotFoundError("No existing pinned source producer for " + name)
    subprocess.run([sys.executable, "-B", *command], cwd=ROOT, check=True)


def source_closure(endpoint):
    hashes, dependencies, closures = {}, {}, {}
    active = set()

    def visit(name):
        if name in hashes:
            return
        assert name not in active, ("Cyclic source import", name)
        active.add(name)
        base = SOURCES / "ThirdParty/LeanCert" if name.startswith("LeanCert.") else SOURCES
        path = base / (name.replace(".", "/") + ".lean")
        if not path.is_file():
            materialize_missing(name)
        raw = path.read_bytes()
        code = without_comments(raw.decode())
        assert not re.search(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", code, re.M), name
        deps = sorted(set(re.findall(
            r"^\s*(?:public\s+)?import\s+((?:Proofs|LeanCert)\.[\w.]+)\s*$",
            code, re.M)))
        dependencies[name] = deps
        for dep in deps:
            visit(dep)
        hashes[name] = sha(raw)
        closures[name] = sha(json.dumps(
            [name, hashes[name], PIN, LC, [(dep, closures[dep]) for dep in deps]],
            separators=(",", ":")).encode())
        active.remove(name)

    visit(endpoint)
    return hashes, dependencies, closures


def matching_archives(hashes, closures):
    groups = {}
    identities = {}
    required_keys = {
        "repository", "run", "job", "source_commit", "artifact_id",
        "artifact_sha256", "lean_version", "mathlib", "modules",
    }
    for path in sorted((ROOT / "ci").rglob("*.json")):
        if "_generated_" in str(path):
            continue
        raw = path.read_bytes()
        data = json.loads(raw)
        if not isinstance(data, dict) or not required_keys <= data.keys():
            continue
        if data["mathlib"] != PIN or data["lean_version"] != "4.33.1":
            continue
        assert isinstance(data["modules"], dict), str(path)
        capsule = data.get("kind") == "INDEPENDENTLY_AUDITED_COMPLETE_SCOPE_CAPSULE"
        selected = {}
        for name, row in data["modules"].items():
            if name not in hashes:
                continue
            if (row.get("source_sha256") != hashes[name] or
                    row.get("source_closure_sha256") != closures[name]):
                continue
            assert row["module"] == name
            assert row["mode"] in (
                {"FRESH_KERNEL_EXPORT", "PRIOR_VERIFIED_JOB_EXPORT"} if capsule
                else {"FRESH_KERNEL_EXPORT"}), (str(path), name, row["mode"])
            assert row["axiom_profiles"] and all(
                set(profile) <= ALLOWED for profile in row["axiom_profiles"]), name
            members = tuple(sorted(output_members(name, row)))
            identity = (row["output_sha256"],
                        json.dumps(row["axiom_profiles"], separators=(",", ":")),
                        members)
            if name in identities:
                previous, origin = identities[name]
                assert previous == identity, (
                    "Conflicting source-identical original exports", name,
                    origin, str(path.relative_to(ROOT)))
            else:
                identities[name] = (identity, str(path.relative_to(ROOT)))
            selected[name] = row
        if not selected:
            continue
        artifact = data["artifact_id"]
        descriptor = {key: data[key] for key in required_keys - {"modules"}}
        group = groups.setdefault(artifact, {
            "archive": descriptor, "modules": {}, "manifests": {},
        })
        assert group["archive"] == descriptor, ("Archive metadata conflict", artifact)
        relative = str(path.relative_to(ROOT))
        group["manifests"][relative] = {
            "sha256": sha(raw), "capsule": capsule,
        }
        for name, row in selected.items():
            old = group["modules"].get(name)
            if old is not None:
                # A capsule and an original export cannot share one artifact ID.
                assert old["row"] == row, ("Conflicting archived row", artifact, name)
            else:
                group["modules"][name] = {"row": row, "manifest": relative}
    return groups


def artifact_metadata(descriptor):
    repository, run = descriptor["repository"], descriptor["run"]
    assert re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository)
    key = (repository, run)
    if key not in RUN_ARTIFACTS:
        artifacts = {}
        page = 1
        while True:
            url = ("https://api.github.com/repos/" + repository +
                   "/actions/runs/" + str(run) +
                   "/artifacts?per_page=100&page=" + str(page))
            request = urllib.request.Request(url, headers={
                "Authorization": "Bearer " + os.environ["GITHUB_TOKEN"],
                "Accept": "application/vnd.github+json",
                "X-GitHub-Api-Version": "2022-11-28",
            })
            try:
                with urllib.request.urlopen(request, timeout=120) as response:
                    listing = json.load(response)
            except urllib.error.HTTPError as error:
                if error.code in (404, 410):
                    RUN_ARTIFACTS[key] = {"unavailable": error.code}
                    break
                raise
            rows = listing["artifacts"]
            for row in rows:
                assert row["id"] not in artifacts, (repository, run, row["id"])
                artifacts[row["id"]] = row
            if len(artifacts) == listing["total_count"]:
                RUN_ARTIFACTS[key] = artifacts
                print(json.dumps({
                    "status": "ORIGINAL_RUN_ARTIFACT_CATALOG_CHECKED",
                    "repository": repository, "run": run,
                    "artifacts": len(artifacts), "pages": page,
                }), flush=True)
                break
            assert len(rows) == 100 and len(artifacts) < listing["total_count"]
            page += 1
            assert page <= 100, "Original run exceeds bounded artifact pagination"
    artifacts = RUN_ARTIFACTS[key]
    if "unavailable" in artifacts:
        return {"available": False, "http_status": artifacts["unavailable"]}
    meta = artifacts.get(descriptor["artifact_id"])
    if meta is None:
        return {"available": False, "missing_from_complete_run_catalog": True}
    assert meta["id"] == descriptor["artifact_id"]
    assert meta["digest"] == "sha256:" + descriptor["artifact_sha256"]
    assert meta["workflow_run"]["id"] == descriptor["run"]
    assert meta["workflow_run"]["head_sha"] == descriptor["source_commit"]
    return {
        "available": not meta["expired"], "archive_bytes": meta["size_in_bytes"],
        "expires_at": meta["expires_at"], "created_at": meta["created_at"],
    }


def plan(endpoint, hashes, dependencies, closures, groups, metadata=artifact_metadata):
    remaining = set(hashes) - FRESH
    selected, unavailable = [], []
    candidates = dict(groups)
    while remaining and candidates:
        artifact, group = max(candidates.items(), key=lambda item: (
            len(remaining & item[1]["modules"].keys()),
            any(item[1]["manifests"][row["manifest"]]["capsule"]
                for row in item[1]["modules"].values()),
            item[0],
        ))
        del candidates[artifact]
        names = sorted(remaining & group["modules"].keys())
        if not names:
            break
        observed = metadata(group["archive"])
        if not observed["available"]:
            unavailable.append({
                **group["archive"], "availability": observed,
                "matching_required_modules": names,
            })
            continue
        # Bound the downloaded ZIP before allocating it in the restore process.
        assert 0 <= observed["archive_bytes"] <= 1024**3, (
            "Original ZIP exceeds the explicit one GiB archive-memory bound", artifact)
        chosen = {name: group["modules"][name] for name in names}
        paths = {row["manifest"] for row in chosen.values()}
        selected.append({
            **group["archive"], "availability": observed, "selected_modules": chosen,
            "manifests": {p: group["manifests"][p] for p in sorted(paths)},
        })
        remaining.difference_update(names)
    fresh = sorted(set(hashes) & FRESH)
    report = {
        "kind": "EXACT_SOURCE_BOUND_COMPRESSED_RESTORE_PLAN",
        "endpoint": endpoint, "mathlib": PIN, "leancert": LC, "lean_version": "4.33.1",
        "required_modules": len(hashes), "source_sha256": hashes,
        "source_closure_sha256": closures, "source_dependencies": dependencies,
        "fresh_allowlist": sorted(FRESH), "fresh_modules": fresh,
        "missing_original_modules": sorted(remaining),
        "selected_archives": selected, "unavailable_candidates": unavailable,
        "complete_original_object_coverage": not remaining,
        "kernel_proof": "NOT_PROVEN_BY_PLANNING",
        "physical_capacity": "REQUIRES_OBSERVED_BOUNDED_RESTORE",
        "import_memory": "REQUIRES_OBSERVED_STRICT_KERNEL_RUN",
        "global_rg": "NOT_PROVED",
    }
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", choices=sorted(FRESH), required=True)
    parser.add_argument("--output", type=pathlib.Path, required=True)
    args = parser.parse_args()
    hashes, dependencies, closures = source_closure(args.endpoint)
    groups = matching_archives(hashes, closures)
    report = plan(args.endpoint, hashes, dependencies, closures, groups)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, separators=(",", ":")) + "\n")
    print(json.dumps({
        "status": "EXACT_ORIGINAL_RESTORE_PLANNED" if report["complete_original_object_coverage"]
                  else "MISSING_ORIGINAL_OBJECTS_NO_BULK_RESTORE",
        "endpoint": args.endpoint, "required_modules": report["required_modules"],
        "fresh_modules": report["fresh_modules"],
        "missing_original_modules": report["missing_original_modules"],
        "selected_archives": len(report["selected_archives"]),
        "unavailable_archives": len(report["unavailable_candidates"]),
        "kernel_proof": report["kernel_proof"],
    }), flush=True)
    if not report["complete_original_object_coverage"]:
        raise SystemExit(2)


if __name__ == "__main__":
    main()

