#!/usr/bin/env python3
"""Read the two actual failed-run ZIPs; never claim an original proof receipt."""
import collections
import hashlib
import json
from pathlib import Path, PurePosixPath
import zipfile

HERE = Path(__file__).resolve().parent
ACTUAL = HERE / "actual"
RUN, JOB = 41885793988, 126769775864
HEAD = "fb7be0772514fb2bc800d646cbe29f1d373db4ba"
PREFIX = "ci/rg_d1_20261103_runtime_reconstructed_exports/"
SPECS = {
    "fresh.zip": (13351653248, 631,
        "dce3d3e289856708319c164af892bdd286d3354371ddceeaf1eb78c0fa744193"),
    "evidence.zip": (13352567120, 1403492,
        "894b2f26c6ea5aa9596920e666d77397e71de63b5c0af8d4b4da1c0dca94d8a8"),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key")
        result[key] = value
    return result


def decode(data):
    return json.loads(data, object_pairs_hook=unique)


def main():
    output = ACTUAL / "joblog_transport_failure_observation.json"
    require(not output.exists(), "Refusing to overwrite the original observation")
    captures = {name: (ACTUAL / name).read_bytes() for name in
                ("run.json", "jobs.json", "artifacts.json", "job.log", "terminal_report.json")}
    run, jobs, catalog = (decode(captures[name]) for name in
                          ("run.json", "jobs.json", "artifacts.json"))
    require(run["id"] == RUN and run["run_attempt"] == 1 and run["head_sha"] == HEAD
            and run["head_branch"] == "rg-degree-one-large-20261103"
            and run["repository"]["full_name"] == "RhudeJJJJ/formal-conjectures"
            and run["event"] == "push" and run["status"] == "completed"
            and run["conclusion"] == "failure", "Unexpected native run")
    require(jobs["total_count"] == len(jobs["jobs"]) == 1, "Unexpected native job scope")
    job = jobs["jobs"][0]
    require(job["id"] == JOB and job["run_id"] == RUN and job["run_attempt"] == 1
            and job["head_sha"] == HEAD and job["name"] == "check"
            and job["status"] == "completed" and job["conclusion"] == "failure",
            "Unexpected native job")
    steps = {step["number"]: step for step in job["steps"]}
    require(steps[5]["conclusion"] == "failure"
            and steps[5]["name"] == "Collect exact successful numeric and named prerequisite exports",
            "Failure was not in the original collector")
    require(all(steps[number]["conclusion"] == "skipped" for number in range(6, 19)),
            "Restore/preflight/kernel/milestone was not skipped")
    require(all(steps[number]["conclusion"] == "success" for number in (19, 20, 21)),
            "Failed-run retention or upload did not succeed")
    log = captures["job.log"].decode("utf-8")
    require("raw = api.logs(item['job'])" in log
            and "with urllib.request.urlopen(target, timeout=120) as response: return response.read()" in log
            and "urllib.error.HTTPError: HTTP Error 503: Egress is over the account limit." in log,
            "Missing actual signed-joblog error trace")
    structured, retained = [], []
    for line in log.splitlines():
        start = line.find("{")
        if start < 0:
            continue
        try:
            item = decode(line[start:])
        except (ValueError, TypeError):
            continue
        if isinstance(item, dict):
            structured.append(item)
            if " RETAINED_RECORD_COUNTS " in line:
                retained.append(item)
    require(retained == [dict(total=0, fresh=0, sidecars=0, logical_output_bytes=0)],
            "Unexpected actual fresh-output retention counts")
    collection = [item for item in structured if "key" in item and "status" in item]
    require(len(collection) == len({item["key"] for item in collection}) == 407,
            "Changed observed collector-record scope")
    api502 = [item for item in structured
              if str(item.get("status", "")).startswith("GITHUB_EXACT_PROOF_API_HTTP_502")]
    require(not api502, "This observation expected no API-502 events in the actual log")
    require(catalog["total_count"] == len(catalog["artifacts"]) == 2,
            "Unexpected actual artifact catalog")
    metadata = {item["id"]: item for item in catalog["artifacts"]}
    archives, evidence_keys = {}, set()
    for filename, (artifact_id, size, digest) in SPECS.items():
        meta = metadata[artifact_id]
        require(meta["size_in_bytes"] == size and meta["digest"] == "sha256:" + digest
                and meta["expired"] is False and meta["workflow_run"]["id"] == RUN
                and meta["workflow_run"]["head_sha"] == HEAD, "Wrong artifact origin")
        raw = (ACTUAL / filename).read_bytes()
        require(len(raw) == size and sha(raw) == digest, "Wrong actual ZIP bytes")
        members, parsed = [], {}
        with zipfile.ZipFile(ACTUAL / filename) as archive:
            infos = archive.infolist()
            require(len({info.filename for info in infos}) == len(infos), "Duplicate ZIP member")
            for info in infos:
                path = PurePosixPath(info.filename)
                require(not info.is_dir() and not path.is_absolute() and ".." not in path.parts
                        and "\\" not in info.filename and not info.flag_bits & 1,
                        "Unexpected ZIP member path or encryption")
                data = archive.read(info)  # Full decompression and CRC check for every actual member.
                require(len(data) == info.file_size, "Changed decompressed member size")
                parsed[info.filename] = decode(data)
                members.append(dict(path=info.filename, bytes=len(data), sha256=sha(data)))
        if filename == "fresh.zip":
            require(set(parsed) == {"diagnostics_records.json", "numeric137_decomposed_source.json"},
                    "Unexpected fresh-artifact scope")
            require(parsed["diagnostics_records.json"] == {"modules": []},
                    "Unexpected compiled fresh module")
            require(parsed["numeric137_decomposed_source.json"]["status"] ==
                    "COMPLETE_ORIGINAL_BATCH_SOURCE_CONSERVATION_CHECKED_NO_KERNEL_PROOF",
                    "Unexpected source-only materialization record")
        else:
            require(len(parsed) == 414 and all(name.startswith(PREFIX)
                    and name.endswith("_prior_exports.json") for name in parsed),
                    "Unexpected metadata-only evidence scope")
            require(all(isinstance(row, dict) and isinstance(row.get("modules"), dict)
                        for row in parsed.values()), "Malformed observed metadata manifest")
            evidence_keys = {PurePosixPath(name).name.removesuffix("_prior_exports.json")
                             for name in parsed}
            require({item["key"] for item in collection} <= evidence_keys,
                    "An emitted collection key has no archived metadata manifest")
        archives[filename] = dict(artifact_id=artifact_id, bytes=size, sha256=digest,
            member_count=len(members), uncompressed_bytes=sum(row["bytes"] for row in members),
            all_members_read_with_CRC_and_SHA256=True, members=members)
    report = dict(
        status="ACTUAL_NATIVE_JOBLOG_HTTP503_FAILURE_AND_COMPLETE_ARCHIVE_BYTES_OBSERVED",
        scope="Bounded failed-run observation; not full original proof or prerequisite-object authentication",
        repository="RhudeJJJJ/formal-conjectures", run=RUN, job=JOB, attempt=1,
        source_commit=HEAD, native_run_conclusion="failure", native_job_conclusion="failure",
        native_job_completed_at=job["completed_at"], failed_step=steps[5],
        native_capture_sha256={name: sha(raw) for name, raw in captures.items()},
        observer_sha256=sha(Path(__file__).read_bytes()),
        failure_location=dict(resource="signed workflow job log", collector_line=116,
            caller_line=582, actual_http_status=503,
            message="Egress is over the account limit.",
            failed_download_job_id_explicitly_logged=None,
            last_successful_collection_record_is_not_the_failed_job_identity=True),
        observed_api502_events=api502, actual_retention_counts=retained[0],
        observed_collection_records=len(collection),
        observed_collection_status_counts=dict(collections.Counter(item["status"] for item in collection)),
        last_observed_collection_record=collection[-1],
        archived_runtime_metadata_manifests=414,
        additional_manifest_keys_without_same_named_collection_record=sorted(
            evidence_keys - {item["key"] for item in collection}),
        actual_archives=archives,
        original_kernel_started=False, complete_original_receipt=False,
        original_fresh_exports=0, original_milestone_claim=False,
        complete_selection_coverage_claim=False, historical_object_archives_reauthenticated=False,
        original_success_authenticator_executed=False, family_count_remaining=4,
        limitations=[
            "Archived metadata records describe historical origins; this run never restored their proof objects.",
            "The source-only materialization record's planned fresh count is not an actual kernel-export count.",
            "No unique cause of the provider's HTTP503 is inferred from the response text.",
            "Neither the 407 collection records nor the 414 metadata manifests substitute for full collection coverage."])
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(dict(status=report["status"], output=str(output),
        report_bytes=output.stat().st_size, report_sha256=sha(output.read_bytes()),
        archives={name: {k: value for k, value in row.items() if k != "members"}
                  for name, row in archives.items()}, original_fresh_exports=0,
        original_success_authenticator_executed=False), indent=2))


if __name__ == "__main__":
    main()
