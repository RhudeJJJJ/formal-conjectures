#!/usr/bin/env python3
"""Authenticate one original Middle residual batch from native GitHub evidence.

Checks the complete returned ZIP, immutable source inventory, dependency closures,
fresh object bytes, exact named axiom profiles, preserved prior rows and receipt.
Successful jobs may be audited while the enclosing matrix run is still running.
No Lean receipt is created. Fresh-only output manifests preserve the producer.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re
import zipfile

PREFIX = "Proofs/RG_Lean_20261019/"
REPOSITORY = "RhudeJJJJ/formal-conjectures"
SOURCE_COMMIT = "15d45e8d3ed3bacaf3afe7d85488a42f08302d76"
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
LC = "621a43d7cf21f87872392a01e874f2f1dbddc926"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
BRANCH = "rg-middle-residual-certificates-rest-20261109"
WORKFLOW = ".github/workflows/" + BRANCH + ".yml"
ENDPOINT_PREFIX = "Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch"
FROZEN_FILES = (
    "rg_middle_residual_batch_inventory_20261109.json",
    "rg_middle_residual_batch_plan_20261109.py",
    "rg_middle_residual_batch_authenticate_20261109.py",
)
NAMED = re.compile(
    r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
    re.S,
)


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def decode(raw):
    return json.loads(raw, object_pairs_hook=unique_pairs)


def read(path):
    return decode(path.read_bytes())


def table(rows):
    if isinstance(rows, dict):
        require(all(k == r["module"] for k, r in rows.items()), "Wrong module key")
        return rows
    result = {}
    for row in rows:
        require(row["module"] not in result, "Duplicate module row")
        result[row["module"]] = row
    return result


def payloads(log, prefix):
    result = []
    for line in log.splitlines():
        line = re.sub(r"^\d{4}-\d\d-\d\dT\S+\s", "", line)
        line = re.sub(r"\x1b\[[0-9;]*m", "", line)
        if line.startswith(prefix):
            result.append(decode(line[len(prefix):]))
    return result


def without_comments(text):
    """Remove nested Lean comments and strings, preserving line boundaries."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quoted:
            if text[i] == "\\":
                out.extend("  ")
                i += 2
            elif text[i] == '"':
                quoted = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            out.extend(" " * (end - i))
            i = end
        elif text[i] == '"':
            quoted = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    require(depth == 0 and not quoted, "Unterminated Lean comment/string")
    return "".join(out)


def source_profile_names(code):
    namespaces = re.findall(r"^namespace ([\w.]+)\s*$", code, re.M)
    require(len(namespaces) <= 1, "Nontrivial fresh namespace needs explicit review")
    names = []
    for name in re.findall(r"^#print axioms ([\w.]+)\s*$", code, re.M):
        if name.startswith("Gebendorfer."):
            names.append(name)
        else:
            require(bool(namespaces), "Unqualified print outside namespace")
            names.append(namespaces[0] + "." + name)
    return names


def select_job(data, batch, endpoint, run_id):
    candidates = data["jobs"] if "jobs" in data else [data]
    if batch == "000":
        matches = [j for j in candidates if j["id"] == 128586559182]
    else:
        matches = [j for j in candidates if j["name"] == "residual-batch-" + batch]
    require(len(matches) == 1, "Missing or ambiguous native batch job")
    job = matches[0]
    require(job["run_id"] == run_id, "Job belongs to different run")
    if batch == "000":
        require(endpoint in job["name"], "Legacy job endpoint differs")
    return job


def atomic_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".pending")
    temporary.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batch", required=True)
    for flag in ("archive", "run-metadata", "job-metadata", "artifact-metadata",
                 "job-log", "inventory", "output-report", "output-manifest"):
        parser.add_argument("--" + flag, type=Path, required=True)
    args = parser.parse_args()
    batch = args.batch
    require(re.fullmatch(r"\d{3}", batch) is not None and 0 <= int(batch) <= 24,
            "Batch must be exactly 000 through 024")
    inputs = [args.archive, args.run_metadata, args.job_metadata,
              args.artifact_metadata, args.job_log, args.inventory]
    require(args.output_report.resolve() != args.output_manifest.resolve(),
            "Report and manifest outputs must be distinct")
    require(all(out.resolve() not in {p.resolve() for p in inputs}
                for out in (args.output_report, args.output_manifest)),
            "Output would overwrite input evidence")
    inventory_raw = args.inventory.read_bytes()
    inventory = decode(inventory_raw)
    require(inventory["kind"] == "ORIGINAL_MIDDLE_RESIDUAL_REMAINING_BATCH_SOURCE_PLAN",
            "Wrong inventory kind")
    require(inventory["source_commit"] == SOURCE_COMMIT, "Changed original source")
    require(inventory["mathlib"] == PIN and inventory["leancert"] == LC
            and inventory["lean_version"] == "4.33.1", "Wrong inventory pins")
    require(inventory["limits"] == {
        "job_timeout_minutes": 360, "memory_reserve_mib": 2048,
        "module_timeout_seconds": 600, "workers_per_job": 1}, "Changed proof limits")
    candidates = ([inventory["reference_batch000"]] if batch == "000" else
                  [r for r in inventory["batches"] if r["index"] == batch])
    require(len(candidates) == 1, "Missing or ambiguous inventory batch")
    expected = candidates[0]
    endpoint = ENDPOINT_PREFIX + batch
    require(expected["index"] == batch and expected["endpoint"] == endpoint,
            "Wrong inventory endpoint")
    source_paths = expected["source_sha256"]
    modules = {}
    for path in source_paths:
        require(path.startswith(PREFIX + "Proofs/") and path.endswith(".lean"),
                "Invalid inventory source path")
        name = path[len(PREFIX):-5].replace("/", ".")
        require(name not in modules, "Duplicate inventory source module")
        modules[name] = path
    required = set(modules)
    fresh = set(expected["fresh_modules"])
    priors = table(inventory["expected_prior_rows"])
    require(len(priors) == 707, "Unexpected inherited diagnostic scope")
    require(len(required) == expected["source_count"]
            and len(fresh) == expected["fresh_count"]
            and len(required & set(priors)) == expected["prior_count"],
            "Wrong source frontier counts")
    require(fresh == required - set(priors)
            and set(expected["prior_modules"]) == required & set(priors),
            "Wrong source frontier identities")
    require(set(expected["ordered_axiom_names"]) == fresh,
            "Wrong named profile frontier")

    run = read(args.run_metadata)
    require(run["repository"]["full_name"] == REPOSITORY, "Wrong repository")
    require(type(run["id"]) is int and run["id"] > 0
            and type(run["run_attempt"]) is int and run["run_attempt"] >= 1,
            "Invalid native run identity")
    run_id = run["id"]
    require(run["event"] == "push", "Wrong trigger")
    if batch == "000":
        require(run_id == 42433253830 and run["run_attempt"] == 1
                and run["head_sha"] == SOURCE_COMMIT, "Wrong legacy control run")
        require(run["head_branch"] == "rg-middle-residual-certificates000-20261108"
                and run["path"] == ".github/workflows/rg-middle-residual-certificates000-20261108.yml",
                "Wrong legacy workflow")
        artifact_name = "rg-middle-residual-certificates000-20261108-exports-42433253830-0"
    else:
        require(run["head_branch"] == BRANCH and run["path"] == WORKFLOW,
                "Wrong continuation branch/workflow")
        artifact_name = BRANCH + "-batch" + batch + "-" + str(run_id)
    require(run["status"] in ("in_progress", "completed"), "Native run not started")
    job = select_job(read(args.job_metadata), batch, endpoint, run_id)
    require(job["head_sha"] == run["head_sha"] and job["head_branch"] == run["head_branch"]
            and job["run_attempt"] == run["run_attempt"], "Job/run identity mismatch")
    require(job["status"] == "completed" and job["conclusion"] == "success"
            and job["completed_at"], "Native batch job did not succeed")
    require(job["steps"] and all(s["status"] == "completed" and s["conclusion"] == "success"
                                for s in job["steps"]), "Unsuccessful native job step")
    catalog = read(args.artifact_metadata)
    artifacts = catalog["artifacts"] if "artifacts" in catalog else [catalog]
    matching = [a for a in artifacts if a["name"] == artifact_name]
    require(len(matching) == 1, "Missing or ambiguous batch artifact")
    meta = matching[0]
    require(meta["expired"] is False
            and meta["workflow_run"]["id"] == run_id
            and meta["workflow_run"]["head_sha"] == run["head_sha"], "Wrong artifact origin")
    if batch == "000":
        require(meta["id"] == 13600393574, "Wrong legacy control artifact")
    require(args.archive.stat().st_size == meta["size_in_bytes"], "Wrong archive length")
    with args.archive.open("rb") as stream:
        archive_hash = hashlib.file_digest(stream, "sha256").hexdigest()
    require(meta["digest"] == "sha256:" + archive_hash, "Wrong archive hash")
    log = args.job_log.read_text()
    require(archive_hash in log and str(meta["id"]) in log, "Native artifact upload binding absent")
    logged = table(payloads(log, "COMPLETED_MODULE_JSON "))
    require(set(logged) == fresh, "Native completed fresh rows differ from inventory")
    checked, hashes, dependencies, closures = {}, {}, {}, {}
    with zipfile.ZipFile(args.archive) as archive:
        source_members = {"generated_source/" + path: name for name, path in modules.items()}
        expected_members = set(source_members) | {
            "generated_source/generated_source_manifest.json", "diagnostics_records.json",
            "resource_observer.json", "receipt.json"}
        for name in fresh:
            expected_members.update([name.replace(".", "/") + ".olean",
                                     name + ".json", name + ".log"])
        if batch != "000":
            expected_members.update("frozen_validation/" + f for f in FROZEN_FILES)
        names = archive.namelist()
        require(len(names) == len(set(names)) == len(expected_members)
                and set(names) == expected_members, "Wrong complete archive member scope")
        for name in names:
            path = PurePosixPath(name)
            require(not path.is_absolute() and ".." not in path.parts
                    and "\\" not in name and not archive.getinfo(name).is_dir(),
                    "Unsafe archive member")
        frozen_hashes = {}
        if batch != "000":
            for filename in FROZEN_FILES:
                if filename == FROZEN_FILES[0]:
                    local = inventory_raw
                else:
                    local = Path(__file__).with_name(filename).read_bytes()
                raw = archive.read("frozen_validation/" + filename)
                require(raw == local, "Frozen validator changed: " + filename)
                frozen_hashes[filename] = sha(raw)
                marker = "FROZEN_VALIDATOR_SHA256 ci/" + filename + " " + sha(raw)
                require(marker in log, "Frozen validator native marker absent")
        for path, name in source_members.items():
            raw = archive.read(path)
            hashes[name] = sha(raw)
            require(hashes[name] == source_paths[modules[name]], "Wrong source hash: " + name)
            code = without_comments(raw.decode())
            require(not re.search(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", code, re.M),
                    "Admission or unchecked native proof: " + name)
            dependencies[name] = sorted(set(re.findall(
                r"^\s*(?:public\s+)?import\s+((?:Proofs|LeanCert)\.[\w.]+)\s*$", code, re.M)))
            require(set(dependencies[name]) <= required, "Source dependency missing")
            if name in fresh:
                require(source_profile_names(code) == expected["ordered_axiom_names"][name],
                        "Source named profile sequence differs: " + name)
        visiting = set()
        def closure(name):
            if name not in closures:
                require(name not in visiting, "Cyclic source graph")
                visiting.add(name)
                closures[name] = sha(json.dumps(
                    [name, hashes[name], PIN, LC,
                     [(d, closure(d)) for d in dependencies[name]]],
                    separators=(",", ":")).encode())
                visiting.remove(name)
            return closures[name]
        reachable = set()
        def visit(name):
            if name not in reachable:
                reachable.add(name)
                for dep in dependencies[name]:
                    visit(dep)
        visit(endpoint)
        require(reachable == required, "Inventory is not the exact endpoint closure")
        for name in required:
            closure(name)
        require(closures == expected["source_closure_sha256"]
                and closures[endpoint] == expected["endpoint_source_closure_sha256"],
                "Wrong recursive dependency hashes")
        manifest = decode(archive.read("generated_source/generated_source_manifest.json"))
        require(manifest == {
            "endpoint": endpoint,
            "component_kind": "DEGREE_ONE_MIDDLE_RESIDUAL_CERTIFICATE_BATCH" + batch,
            "source_sha256": source_paths,
            "kind": "ORIGINAL_TARGET_REQUIRES_SUCCESSFUL_KERNEL_RECEIPT"},
            "Wrong complete source manifest")
        diagnostics = table(decode(archive.read("diagnostics_records.json"))["modules"])
        require(set(diagnostics) == set(priors) | fresh, "Wrong diagnostics scope")
        require(all(diagnostics[n] == row for n, row in priors.items()),
                "Inherited proof row or original provenance changed")
        receipt_raw = archive.read("receipt.json")
        receipt = decode(receipt_raw)
        require(receipt["scope"] == "EXPLICIT_EXTENSION_CLOSURE"
                and receipt["endpoints"] == [endpoint], "Wrong completed receipt endpoint")
        require(receipt["mathlib"] == PIN and receipt["leancert"] == LC
                and "version 4.33.1," in receipt["lean"], "Wrong compiler/dependency pins")
        require(receipt["global_rg"] == "NOT_PROVED"
                and receipt["complete_submission"] == "NOT_SUBMITTED", "Overstated receipt")
        rows = table(receipt["modules"])
        require(set(rows) == required and all(rows[n] == diagnostics[n] for n in required),
                "Incomplete receipt or inconsistent diagnostic rows")
        for name, row in rows.items():
            require(row["source_sha256"] == hashes[name]
                    and row["source_closure_sha256"] == closures[name], "Wrong row source identity")
            require(row["axiom_profiles"] and all(set(p) <= ALLOWED for p in row["axiom_profiles"]),
                    "Unapproved inherited or fresh axiom profile")
        for name in sorted(fresh):
            row = rows[name]
            require(row == logged[name] == decode(archive.read(name + ".json")),
                    "Native/archive fresh record mismatch")
            require(row["mode"] == "FRESH_KERNEL_EXPORT" and "origin" not in row
                    and "transport_capsule" not in row, "Fresh export provenance changed")
            require(type(row["seconds"]) in (int, float) and math.isfinite(row["seconds"])
                    and row["seconds"] >= 0, "Invalid recorded duration")
            require(not row.get("additional_outputs"), "Unretained compiled sidecars")
            object_path = name.replace(".", "/") + ".olean"
            with archive.open(object_path) as stream:
                require(hashlib.file_digest(stream, "sha256").hexdigest() == row["output_sha256"],
                        "Compiled object bytes differ")
            module_log = archive.read(name + ".log").decode()
            require(not re.search(r"\b(error|warning)(?:\([^\n]*?\))?:", module_log),
                    "Module warning/error")
            matches = list(NAMED.finditer(module_log))
            require([m[1] for m in matches] == expected["ordered_axiom_names"][name],
                    "Wrong ordered named theorem profiles")
            profiles = [sorted(set(a.strip() for a in (m[2] or "").split(",") if a.strip()))
                        for m in matches]
            require(profiles and all(set(p) <= ALLOWED for p in profiles), "Unapproved theorem axiom")
            grouped = [p for m, p in zip(matches, profiles) if m[2] is not None]
            grouped += [p for m, p in zip(matches, profiles) if m[2] is None]
            require(grouped == row["axiom_profiles"], "Named/logged profile mismatch")
            checked[name] = {
                "output_bytes": archive.getinfo(object_path).file_size,
                "named_axiom_profiles": [{"declaration": m[1], "axioms": p}
                                         for m, p in zip(matches, profiles)]}
        named_count = sum(len(r["named_axiom_profiles"]) for r in checked.values())
        require(named_count == expected["fresh_axiom_print_count"], "Wrong total named profiles")
        resource = decode(archive.read("resource_observer.json"))
        require(payloads(log, "RG_KERNEL_RESOURCE_RESULT ") ==
                [{k: v for k, v in resource.items() if k != "samples"}], "Observer result mismatch")
        require(payloads(log, "RG_KERNEL_RESOURCE_OBSERVATION ") == resource["samples"],
                "Observer samples mismatch")
        require(resource["status"] == "VERIFIER_COMPLETED" and resource["exit_code"] == 0
                and resource["mathlib_and_lean_flags_unchanged"] is True and resource["samples"],
                "Verifier/resource completion absent")
        require(not payloads(log, "RG_KERNEL_RESOURCE_GUARD_LOW_MEMORY "),
                "Memory guard stopped verification")
        require(all(type(s["available_bytes"]) is int
                    and s["available_bytes"] >= 2048 * 1024**2
                    for s in resource["samples"] if s["lean_processes"]),
                "Observed memory reserve violation")
        require(resource["maximum_aggregate_lean_rss"] >=
                max(s["aggregate_lean_rss"] for s in resource["samples"]),
                "Invalid resource maximum")

    restore = {
        "repository": REPOSITORY, "run": run_id, "job": job["id"],
        "source_commit": run["head_sha"], "artifact_id": meta["id"],
        "artifact_sha256": archive_hash, "mathlib": PIN, "lean_version": "4.33.1",
        "modules": {n: rows[n] for n in sorted(fresh)}}
    report = {
        "status": "ACTUAL_ORIGINAL_MIDDLE_RESIDUAL_BATCH_AUTHENTICATED",
        "batch": batch, "endpoint": endpoint, "repository": REPOSITORY,
        "run": run_id, "run_attempt": run["run_attempt"], "run_status": run["status"],
        "run_conclusion": run["conclusion"], "job": job["id"], "job_conclusion": "success",
        "workflow_source_commit": run["head_sha"], "original_source_commit": SOURCE_COMMIT,
        "artifact": {k: meta[k] for k in ("id", "name", "size_in_bytes", "digest")},
        "archive_members": len(names), "required_modules": len(required),
        "required_prior_modules": len(required) - len(fresh), "fresh_modules": len(fresh),
        "diagnostic_prior_rows": len(priors), "diagnostic_rows": len(diagnostics),
        "fresh_named_axiom_profiles": named_count, "certified_keys": expected["key_count"],
        "fresh_output_bytes": sum(r["output_bytes"] for r in checked.values()),
        "receipt_sha256": sha(receipt_raw), "inventory_sha256": sha(inventory_raw),
        "authenticator_sha256": sha(Path(__file__).read_bytes()),
        "frozen_validation": frozen_hashes, "module_checks": checked,
        "resource_seconds": resource["seconds"], "middle_family_complete": False,
        "global_rg_proved": False, "kernel_receipt_created_by_authenticator": False,
        "prior_artifact_bytes_redownloaded_by_authenticator": False,
        "legacy_control_post_run_audit": batch == "000",
        "native_capture_sha256": {p.name: sha(p.read_bytes()) for p in
                                 (args.run_metadata, args.job_metadata,
                                  args.artifact_metadata, args.job_log)}}
    atomic_json(args.output_manifest, restore)
    report["restore_manifest_sha256"] = sha(args.output_manifest.read_bytes())
    atomic_json(args.output_report, report)
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ("module_checks", "native_capture_sha256")}, indent=2))


if __name__ == "__main__":
    main()

