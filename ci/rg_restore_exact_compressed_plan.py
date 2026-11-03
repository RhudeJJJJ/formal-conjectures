"""Restore an exact planned closure through the byte-preserving proofstore.

Only selected modules are written, but the complete original archive is
authenticated. Complete-scope capsule receipts keep their full equality check.
Every selected .olean and declared sidecar is checked before and after writing.
No theorem is proved here, and no unavailable archive becomes a proof assumption.
"""
import argparse, hashlib, io, json, os, pathlib, shutil, subprocess, sys, zipfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCES = ROOT / "Proofs/RG_Lean_20261019"
sys.path.insert(0, str(SOURCES))
from module_outputs import output_members
from rg_github_artifacts import fetch_archive

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
GIB = 1024**3
RESERVE = 8 * GIB
BATCH_BOUND = 2 * GIB


def digest_file(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=pathlib.Path, required=True)
    parser.add_argument("--build-directory", type=pathlib.Path, required=True)
    args = parser.parse_args()
    plan = json.loads(args.plan.read_bytes())
    assert plan["kind"] == "EXACT_SOURCE_BOUND_COMPRESSED_RESTORE_PLAN"
    assert plan["complete_original_object_coverage"] and not plan["missing_original_modules"]
    assert plan["mathlib"] == "0df444a360eaa60ab8c11dca51a86af692955474"
    assert plan["leancert"] == "621a43d7cf21f87872392a01e874f2f1dbddc926"
    assert plan["lean_version"] == "4.33.1"
    assert os.environ.get("GITHUB_ACTIONS") == "true"
    assert os.environ.get("RUNNER_ENVIRONMENT") == "github-hosted"
    host = pathlib.Path(os.environ["RG_PROOFSTORE_HOST_PATH"]).resolve()
    assert host == pathlib.Path(os.environ["GITHUB_WORKSPACE"]).resolve() == ROOT
    build = args.build_directory.resolve()
    assert build == SOURCES / "build/extension"
    filesystem = json.loads(subprocess.check_output(
        ["findmnt", "-J", "-T", str(build)], text=True))["filesystems"][0]
    assert filesystem["fstype"] == "btrfs" and "compress=zstd:6" in filesystem["options"]
    image = ROOT / "rg-ephemeral-proofstore.btrfs"
    assert image.is_file() and not image.is_symlink()
    reports = ROOT / "rg-proofstore-roundtrip-reports"
    reports.mkdir(exist_ok=True)
    seen = set()
    total_logical = 0
    for entry in plan["selected_archives"]:
        manifests = {}
        for relative, expected in entry["manifests"].items():
            path = ROOT / relative
            assert path.resolve().is_relative_to(ROOT / "ci")
            assert digest_file(path) == expected["sha256"], relative
            manifest = json.loads(path.read_bytes())
            for key in ("repository", "run", "job", "source_commit", "artifact_id",
                        "artifact_sha256", "mathlib", "lean_version"):
                assert manifest[key] == entry[key], (relative, key)
            manifests[relative] = manifest
        names = sorted(entry["selected_modules"])
        assert names and not seen.intersection(names), "Repeated selected module"
        assert shutil.disk_usage(host).free >= RESERVE + 2 * GIB
        assert entry["availability"]["archive_bytes"] <= GIB
        data = fetch_archive(entry)
        assert len(data) == entry["availability"]["archive_bytes"]
        assert hashlib.sha256(data).hexdigest() == entry["artifact_sha256"]
        before = shutil.disk_usage(host).free
        archive_logical = 0
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            members = archive.namelist()
            assert len(members) == len(set(members)), "Duplicate ZIP member"
            for relative, manifest in manifests.items():
                if entry["manifests"][relative]["capsule"]:
                    assert manifest["kind"] == "INDEPENDENTLY_AUDITED_COMPLETE_SCOPE_CAPSULE"
                    capsule = json.loads(archive.read("capsule.json"))
                    assert capsule["kind"] == "VERIFIED_COMPLETE_SCOPE_OBJECTS"
                    receipt = json.loads(archive.read("receipt.json"))
                    assert receipt["modules"] == manifest["modules"]
                    assert receipt["endpoints"] == manifest["endpoints"]
                    assert receipt["mathlib"] == manifest["mathlib"]
            pending = []
            batch_bytes = 0

            def flush_batch():
                nonlocal batch_bytes, archive_logical, total_logical
                if not pending:
                    return
                assert batch_bytes <= BATCH_BOUND
                free = shutil.disk_usage(host).free
                # Preserve the original two-worker raw-write reserve even though
                # this implementation deliberately restores only one archive at once.
                assert free >= RESERVE + 2 * batch_bytes
                for name, row, manifest, specs in pending:
                    for relative, expected_sha, expected_size in specs:
                        target = build / relative
                        assert target.resolve().is_relative_to(build)
                        info = archive.getinfo(relative)
                        assert expected_size is None or info.file_size == expected_size
                        with archive.open(relative) as stream:
                            assert hashlib.file_digest(stream, "sha256").hexdigest() == expected_sha
                        target.parent.mkdir(parents=True, exist_ok=True)
                        with archive.open(relative) as source, target.open("wb") as output:
                            shutil.copyfileobj(source, output, length=1024 * 1024)
                        assert target.stat().st_size == info.file_size
                        assert digest_file(target) == expected_sha, (name, relative)
                        archive_logical += info.file_size
                        total_logical += info.file_size
                    if row["mode"] == "PRIOR_VERIFIED_JOB_EXPORT":
                        assert manifest.get("kind") == "INDEPENDENTLY_AUDITED_COMPLETE_SCOPE_CAPSULE"
                        origin = row["origin"]
                    else:
                        assert row["mode"] == "FRESH_KERNEL_EXPORT"
                        origin = {key: manifest[key] for key in (
                            "repository", "run", "job", "source_commit", "artifact_id",
                            "artifact_sha256")}
                    restored = {**row, "mode": "PRIOR_VERIFIED_JOB_EXPORT", "origin": origin}
                    if manifest.get("kind") == "INDEPENDENTLY_AUDITED_COMPLETE_SCOPE_CAPSULE":
                        restored["transport_capsule"] = {key: manifest[key] for key in (
                            "run", "job", "source_commit", "artifact_id", "artifact_sha256")}
                    (build / (name + ".json")).write_text(json.dumps(restored, indent=2) + "\n")
                    seen.add(name)
                subprocess.run(["sync", "-f", str(build)], check=True)
                assert shutil.disk_usage(host).free >= RESERVE
                pending.clear()
                batch_bytes = 0

            for name in names:
                selected = entry["selected_modules"][name]
                row = selected["row"]
                manifest = manifests[selected["manifest"]]
                assert manifest["modules"][name] == row == json.loads(archive.read(name + ".json"))
                assert row["module"] == name
                assert row["source_sha256"] == plan["source_sha256"][name]
                assert row["source_closure_sha256"] == plan["source_closure_sha256"][name]
                assert row["axiom_profiles"] and all(
                    set(profile) <= ALLOWED for profile in row["axiom_profiles"])
                specs = list(output_members(name, row))
                size = sum(archive.getinfo(relative).file_size for relative, _, _ in specs)
                assert size <= BATCH_BOUND, ("Single output bundle exceeds bounded restore", name, size)
                if pending and batch_bytes + size > BATCH_BOUND:
                    flush_batch()
                pending.append((name, row, manifest, specs))
                batch_bytes += size
            flush_batch()
        del data
        report = {
            "status": "EXACT_ORIGINAL_MEMBERS_RESTORED_AND_READ_BACK_THROUGH_COMPRESSION",
            "artifact_id": entry["artifact_id"], "artifact_sha256": entry["artifact_sha256"],
            "modules": len(names), "logical_member_bytes": archive_logical,
            "cumulative_logical_member_bytes": total_logical,
            "host_free_before": before, "host_free_after": shutil.disk_usage(host).free,
            "allocated_image_bytes": image.stat().st_blocks * 512,
            "logical_image_bytes": image.stat().st_size,
            "all_declared_sidecars_preserved": True, "fresh_kernel_compilations": 0,
        }
        (reports / (str(entry["artifact_id"]) + ".json")).write_text(
            json.dumps(report, indent=2) + "\n")
        print(json.dumps(report), flush=True)
    expected = set(plan["source_sha256"]) - set(plan["fresh_modules"])
    assert seen == expected, ("Restored closure differs from planned original closure",
                              sorted(expected - seen), sorted(seen - expected))
    assert shutil.disk_usage(host).free >= RESERVE + 2 * GIB
    print(json.dumps({
        "status": "EXACT_ORIGINAL_CLOSURE_RESTORED_REQUIRES_FRESH_KERNEL_CHECK",
        "modules": len(seen), "fresh_modules": plan["fresh_modules"],
        "logical_member_bytes": total_logical,
        "allocated_image_bytes": image.stat().st_blocks * 512,
        "host_free_bytes": shutil.disk_usage(host).free,
        "global_rg": "NOT_PROVED",
    }), flush=True)


if __name__ == "__main__":
    main()

