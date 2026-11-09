#!/usr/bin/env python3
"""Authenticate completed matrix batches and restore the original finite join.

Run only after every batch job succeeds. This program preserves native origins,
checks the fixed original source closure and leaves exactly the original final
module for the unchanged Lean verifier. It does not create a Lean receipt.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import urllib.error
import urllib.parse
import urllib.request
import zipfile

from rg_github_artifacts import fetch_archive
from rg_middle_residual_batch_plan_20261109 import Sources

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "Proofs/RG_Lean_20261019"
BUILD = PROJECT / "build/extension"
EVIDENCE = PROJECT / "build/fresh_exports/join_evidence"
INVENTORY = ROOT / "ci/rg_middle_residual_batch_inventory_20261109.json"
ENDPOINT = "Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteAllCertificates"
REPOSITORY = "RhudeJJJJ/formal-conjectures"
BRANCH = "rg-middle-residual-certificates-rest-20261109"
FIXED_MANIFESTS = (
    "ci/rg_middle_residual_core_coverage_run42345977030_prior_exports.json",
    "ci/rg_middle_residual_prerequisites_run42346733540_prior_exports.json",
    "ci/rg_middle_residual_certificates000_run42433253830_prior_exports.json",
)
FIXED_SHA256 = {
    FIXED_MANIFESTS[0]: "dc4f02613704bd768a8e6a24e2f5707176adb106d1561457d0de8bfa774d830d",
    FIXED_MANIFESTS[1]: "ddb9d5918d70e41d09bd1590efaab53de429a4fc82d179258e3a2d4855525c1d",
    FIXED_MANIFESTS[2]: "58f04f9c92207b1c0915c6cbf8b0b605bf15be5615d93dbd99b21266424fdbf4",
}
sys.path.insert(0, str(PROJECT))
from module_outputs import output_members


def save_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def run(*args):
    subprocess.run([sys.executable, "-B", *map(str, args)], cwd=ROOT, check=True)


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, new_url):
        return None


def api_bytes(path):
    """GitHub credentials are never forwarded to an external signed redirect."""
    assert path.startswith("/repos/" + REPOSITORY + "/actions/")
    request = urllib.request.Request("https://api.github.com" + path, headers={
        "Authorization": "Bearer " + os.environ["GITHUB_TOKEN"],
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
    })
    try:
        with urllib.request.build_opener(NoRedirect).open(request, timeout=120) as response:
            return response.read()
    except urllib.error.HTTPError as error:
        if error.code not in (301, 302, 303, 307, 308):
            raise
        destination = error.headers["Location"]
        error.close()
        parsed = urllib.parse.urlparse(destination)
        assert parsed.scheme == "https" and parsed.hostname
        assert not parsed.username and not parsed.password
        with urllib.request.urlopen(destination, timeout=120) as response:
            return response.read()


def restore_bounded(manifest_path, archive_path):
    """Project only authenticated rows into at-most-one-GiB restore slices."""
    manifest = json.loads(manifest_path.read_bytes())
    slices, current, size = [], {}, 0
    with zipfile.ZipFile(archive_path) as archive:
        for name, row in sorted(manifest["modules"].items()):
            raw = sum(archive.getinfo(rel).file_size for rel, _, _ in output_members(name, row))
            assert raw <= 1024**3, "Single proof object exceeds the fixed bounded restore size"
            if current and size + raw > 1024**3:
                slices.append(current)
                current, size = {}, 0
            current[name] = row
            size += raw
    if current:
        slices.append(current)
    assert sum(map(len, slices)) == len(manifest["modules"])
    assert set().union(*(set(part) for part in slices)) == set(manifest["modules"])
    for index, part in enumerate(slices):
        path = manifest_path.parent / "restore_slices" / f"{index:03d}.json"
        save_json(path, {**manifest, "modules": part})
        run("ci/rg_restore_job_exports.py", "--manifest", path,
            "--build-directory", BUILD, "--verified-local-archive", archive_path)


def main():
    assert os.environ.get("GITHUB_ACTIONS") == "true"
    assert os.environ.get("GITHUB_REPOSITORY") == REPOSITORY
    run_id = int(os.environ["GITHUB_RUN_ID"])
    commit = os.environ["GITHUB_SHA"]
    assert re.fullmatch(r"[0-9a-f]{40}", commit)
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    prefix = "/repos/" + REPOSITORY + "/actions/"
    run_metadata = json.loads(api_bytes(prefix + "runs/" + str(run_id)))
    jobs = json.loads(api_bytes(prefix + "runs/" + str(run_id) + "/jobs?per_page=100"))
    artifacts = json.loads(api_bytes(prefix + "runs/" + str(run_id) + "/artifacts?per_page=100"))
    assert run_metadata["head_sha"] == commit and run_metadata["head_branch"] == BRANCH
    assert run_metadata["event"] == "push"
    assert jobs["total_count"] == len(jobs["jobs"]) == 25
    assert artifacts["total_count"] == len(artifacts["artifacts"]) == 24
    expected_batches = [f"{i:03d}" for i in range(1, 25)]
    for batch in expected_batches:
        found = [job for job in jobs["jobs"] if job["name"] == "residual-batch-" + batch]
        assert len(found) == 1 and found[0]["status"] == "completed"
        assert found[0]["conclusion"] == "success"
    for name, data in (("run.json", run_metadata), ("jobs.json", jobs), ("artifacts.json", artifacts)):
        save_json(EVIDENCE / name, data)

    # These three already authenticated origins are not relabelled as fresh.
    fixed_receipts = []
    for relative in FIXED_MANIFESTS:
        assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == FIXED_SHA256[relative]
        manifest = json.loads((ROOT / relative).read_bytes())
        run("ci/rg_restore_job_exports.py", "--manifest", relative,
            "--build-directory", BUILD)
        fixed_receipts.append({"manifest": relative,
                               "sha256": hashlib.sha256((ROOT / relative).read_bytes()).hexdigest(),
                               "origin": {k: manifest[k] for k in
                                          ("run", "job", "source_commit", "artifact_id", "artifact_sha256")}})
        save_json(EVIDENCE / Path(relative).name, manifest)

    authenticated = []
    for batch in expected_batches:
        job = next(j for j in jobs["jobs"] if j["name"] == "residual-batch-" + batch)
        name = BRANCH + "-batch" + batch + "-" + str(run_id)
        matching = [a for a in artifacts["artifacts"] if a["name"] == name]
        assert len(matching) == 1
        artifact = matching[0]
        assert artifact["digest"].startswith("sha256:") and not artifact["expired"]
        origin = dict(repository=REPOSITORY, run=run_id, job=job["id"],
                      source_commit=commit, artifact_id=artifact["id"],
                      artifact_sha256=artifact["digest"][7:])
        directory = EVIDENCE / ("batch" + batch)
        directory.mkdir(parents=True, exist_ok=True)
        archive = directory / "original.zip"
        archive.write_bytes(fetch_archive(origin))
        (directory / "job.log").write_bytes(api_bytes(prefix + "jobs/" + str(job["id"]) + "/logs"))
        manifest_path = directory / "prior_exports.json"
        report_path = directory / "authentication.json"
        run("ci/rg_middle_residual_batch_authenticate_20261109.py", "--batch", batch,
            "--archive", archive, "--run-metadata", EVIDENCE / "run.json",
            "--job-metadata", EVIDENCE / "jobs.json", "--artifact-metadata", EVIDENCE / "artifacts.json",
            "--job-log", directory / "job.log", "--inventory", INVENTORY,
            "--output-report", report_path, "--output-manifest", manifest_path)
        restore_bounded(manifest_path, archive)
        report = json.loads(report_path.read_bytes())
        assert report["status"] == "ACTUAL_ORIGINAL_MIDDLE_RESIDUAL_BATCH_AUTHENTICATED"
        authenticated.append({k: report[k] for k in
                              ("batch", "certified_keys", "fresh_modules", "fresh_named_axiom_profiles",
                               "artifact", "restore_manifest_sha256")})
        # Only this temporary duplicate is removed; native artifacts remain.
        archive.unlink()

    assert sum(row["certified_keys"] for row in authenticated) == 1180
    sources = Sources()
    required = sources.scope(ENDPOINT)
    assert len(required) == 3880
    prior = {}
    for name in sorted(required - {ENDPOINT}):
        record = json.loads((BUILD / (name + ".json")).read_bytes())
        assert record["mode"] == "PRIOR_VERIFIED_JOB_EXPORT"
        assert record["source_sha256"] == sources.hashes[name]
        assert record["source_closure_sha256"] == sources.closure_hash(name)
        prior[name] = record
    assert not (BUILD / (ENDPOINT + ".json")).exists()
    bundle = PROJECT / "build/fresh_exports/generated_source"
    for name in sorted(required):
        destination = bundle / sources.paths[name]
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(sources.raw[name])
    save_json(bundle / "generated_source_manifest.json", {
        "endpoint": ENDPOINT, "source_sha256": {sources.paths[n]: sources.hashes[n] for n in sorted(required)},
        "source_closure_sha256": {n: sources.closure_hash(n) for n in sorted(required)},
        "kind": "ORIGINAL_FINITE_JOIN_REQUIRES_FRESH_FINAL_KERNEL_RECEIPT"})
    summary = dict(status="AUTHENTICATED_ORIGINAL_FINITE_JOIN_FRONTIER",
                   endpoint=ENDPOINT, original_sources=3880, prior_modules=3879,
                   mandatory_fresh_modules=[ENDPOINT], key_count=1232,
                   fixed_origins=fixed_receipts, authenticated_batches=authenticated,
                   complete_middle_family=False, global_rg_proved=False)
    save_json(EVIDENCE / "join_frontier.json", summary)
    print(json.dumps({k: v for k, v in summary.items()
                      if k not in ("fixed_origins", "authenticated_batches")}), flush=True)


if __name__ == "__main__":
    main()
