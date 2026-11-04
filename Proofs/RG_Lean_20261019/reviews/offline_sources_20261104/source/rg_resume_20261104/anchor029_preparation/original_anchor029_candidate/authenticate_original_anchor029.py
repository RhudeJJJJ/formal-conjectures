#!/usr/bin/env python3
"""Offline audit of fixed original Anchor029 run 41826563525, attempt 1.

Inputs are root's actual/run.json, jobs.json, artifacts.json, job.log and
artifact.zip. No network, restoration, Lean invocation or receipt generation.
Exit 0 means the entire original 281-module job was authenticated; exit 3
means an actual terminal failed/cancelled job was captured without a success
claim; exit 2 means incomplete, contradictory or rejected evidence.

--check-fixed-inputs-only checks existing pinned source/plan metadata and writes
no actual-result report. This is not an actual kernel or archive test.
"""
import argparse
import ast
import hashlib
import json
import math
import pathlib
import re
import sys
import zipfile

HERE = pathlib.Path(__file__).resolve().parent
PREP = HERE.parent
ACTUAL = HERE / "actual"
REPOSITORY = "RhudeJJJJ/formal-conjectures"
RUN, JOB, ATTEMPT = 41826563525, 126562666235, 1
COMMIT = "5b7bd43a9f3ca170b19450dd4f34fe9d12bbba90"
BRANCH = "rg-middle-anchor029-original-recovery-20261104"
WORKFLOW = ".github/workflows/rg-middle-anchor029-original-recovery-20261104.yml"
WORKFLOW_SHA = "6676ba35ed497f7479d0021a75714af3ab1c1e98086dab171ff2bc5cfd8c1fe2"
PLAN_PATH = "ci/rg_middle_anchor029_generic_recovered_restore_plan_20261104.json"
PLAN_SHA = "fe37ffe775fcc06a969c72349249df46c3fbc051316ffdd699ba30472391177b"
SOURCE_COMMIT = "7a64184a0b353295d4977004066e163375cf3b4b"
ENDPOINT = "Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate029"
JOB_NAME = ("check (Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate029, "
            "ci/rg_middle_anchor029_generic_...")
ARTIFACT_NAME = f"rg-middle-anchor029-original-recovery-20261104-exports-{RUN}-0"
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
LC = "621a43d7cf21f87872392a01e874f2f1dbddc926"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ORIGIN_KEYS = ("repository", "run", "job", "source_commit", "artifact_id", "artifact_sha256")
BASE_MANIFEST = "ci/rg_reusable_analytic_kernel_base_complete_scope_capsule.json"
EXPECTED_PLAN = [
    "ci/rg_middle_generic_recovery_20261104_run41805266301_prior_exports.json",
    "ci/rg_middle_original_integer_payment_generic_prior_exports.json",
    "ci/rg_middle_oct27_anchor028_parts_original_partial_prior_exports.json",
    "ci/rg_middle_oct28_anchor028_original_prior_exports.json",
]
FIXED = {
    "static_source_closure/source_graph.json":
        "f48e155c412d5e75a8a2980851506c48e69985a4b4c2c6ba3ea985af27d93540",
    "static_source_closure/source_inventory.json":
        "1ff4f70a8b85a3637ef5092c8f2e8a2f9d9e95224f8d5522efad7255d99fff94",
    "static_source_closure/offered_identity_comparison.json":
        "57410b1d974ea309b8a020ff59960d81d7e9e99ba5a52480df755f87c936e2c2",
    "static_source_closure/metadata_and_parser_source_capture.json":
        "b7950ca339708c7f54973f5e29049c7d1166d29dd91169013b4224f1c6935ba3",
    "generic_recovered_plan_source_capture.json":
        "d623d5fb55f1f2897c892bf4e82d74c48a2477b85e038f8e76038e1ea0dae2be",
    "availability_and_ci_review/pinned_ci_source_capture_complete.json":
        "997b85dd13bcfe4acd7f19ab85218eb0a94b695be81fd3d33f2b1b425b89f316",
}
KERNEL_STEP = "Check multiplicities and actual graph spectral comparison"
COLLECT_STEP = "Retain completed records and diagnostics"
UPLOAD_STEP = "Retain new exports only"
KERNEL_COMMAND = (
    'python3 -B ci/rg_observed_kernel_verify.py --memory-reserve-mib 2048 -- '
    '--mathlib-project "$GITHUB_WORKSPACE" --endpoint ' + ENDPOINT +
    ' --workers 1 --module-timeout 600 --resume | python3 -B ci/rg_compact_ci_output.py'
)
SOURCE_PREFIX = "generated_source/Proofs/RG_Lean_20261019/"
SOURCE_MANIFEST = "generated_source/generated_source_manifest.json"
BAD_DIAGNOSTIC = re.compile(r"\b(error|warning)(?:\([^\n]*?\))?:")
NAMED_AXIOM = re.compile(
    r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", re.S)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def file_sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def git_blob(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def decode(raw):
    def reject_constant(value):
        raise ValueError("Non-finite JSON constant: " + value)
    return json.loads(raw, object_pairs_hook=unique, parse_constant=reject_constant)


def bound(path, digest):
    raw = path.read_bytes()
    require(sha(raw) == digest, "Changed fixed metadata: " + str(path))
    return decode(raw)


def table(rows):
    require(isinstance(rows, (dict, list)), "Invalid module table")
    if isinstance(rows, list):
        names = [r["module"] for r in rows]
        require(len(names) == len(set(names)), "Repeated module row")
        rows = dict(zip(names, rows))
    require(all(n == r["module"] for n, r in rows.items()), "Row/module mismatch")
    return rows


def origin(manifest):
    result = {k: manifest[k] for k in ORIGIN_KEYS}
    if "origin_context" in manifest:
        result["context"] = manifest["origin_context"]
    return result


def expected_named_declarations(code):
    """Resolve only the simple namespace/section syntax in these pinned sources."""
    stack, namespace, result = [], "", []
    for line in code.splitlines():
        line = line.strip()
        match = re.fullmatch(r"namespace\s+([\w.]+)", line)
        if match:
            name = match[1]
            stack.append(("namespace", name, namespace))
            namespace = namespace + "." + name if namespace else name
            continue
        match = re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+([\w.]+))?", line)
        if match:
            stack.append(("section", match[1], namespace))
            continue
        match = re.fullmatch(r"end(?:\s+([\w.]+))?", line)
        if match:
            require(bool(stack), "Unmatched source end")
            kind, name, previous = stack.pop()
            require(match[1] is None or match[1] == name, "Unexpected named scope end")
            namespace = previous
            continue
        match = re.fullmatch(r"#print\s+axioms\s+([\w.]+)", line)
        if match:
            name = match[1]
            if name.startswith("_root_."):
                name = name.removeprefix("_root_.")
            elif not name.startswith("Gebendorfer."):
                require(bool(namespace), "Unqualified axiom name outside known namespace")
                name = namespace + "." + name
            result.append(name)
    require(not stack and not namespace, "Unclosed source namespace/section")
    return result


def source_graph(sources, without_comments):
    hashes, deps, closures, active = {}, {}, {}, set()
    for name, raw in sources.items():
        code = without_comments(raw.decode())
        require(not re.search(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", code, re.M),
                "Forbidden proof escape in " + name)
        require(not re.search(r"^\s*module\s*$", code, re.M), "Unexpected module-system source")
        hashes[name] = sha(raw)
        deps[name] = sorted(set(re.findall(
            r"^\s*(?:public\s+)?import\s+((?:Proofs|LeanCert)\.[\w.]+)\s*$", code, re.M)))

    def closure(name):
        if name not in closures:
            require(name in hashes and name not in active, "Missing/cyclic import: " + name)
            active.add(name)
            children = [(dep, closure(dep)) for dep in deps[name]]
            closures[name] = sha(json.dumps([name, hashes[name], PIN, LC, children],
                                           separators=(",", ":")).encode())
            active.remove(name)
        return closures[name]

    closure(ENDPOINT)
    require(set(closures) == set(sources), "Source scope exceeds endpoint closure")
    return dict(source_sha256=hashes, source_dependencies=deps, source_closure_sha256=closures)


def fixed_context():
    fixed = {p: bound(PREP / p, h) for p, h in FIXED.items()}
    graph = fixed["static_source_closure/source_graph.json"]
    inventory = fixed["static_source_closure/source_inventory.json"]
    require(inventory["commit"] == SOURCE_COMMIT and inventory["endpoint"] == ENDPOINT,
            "Wrong reviewed source scope")
    workflow = (HERE / "patch" / WORKFLOW).read_bytes()
    require(sha(workflow) == WORKFLOW_SHA, "Changed original workflow")
    require(bound(HERE / "patch" / PLAN_PATH, PLAN_SHA) == EXPECTED_PLAN, "Changed restore plan")
    initial = fixed["generic_recovered_plan_source_capture.json"]
    metadata = fixed["static_source_closure/metadata_and_parser_source_capture.json"]
    files = {}
    for row in metadata["files"] + initial["manifests"] + fixed[
            "availability_and_ci_review/pinned_ci_source_capture_complete.json"]["files"]:
        raw = row["content"].encode()
        require(git_blob(raw) == row["git_blob_sha"], "Native helper/manifest blob mismatch")
        require(row["path"] not in files or files[row["path"]] == raw, "Conflicting captures")
        files[row["path"]] = raw
    parser_path = "Proofs/RG_Lean_20261019/verify.py"
    parsed = ast.parse(files[parser_path])
    functions = [n for n in parsed.body if isinstance(n, ast.FunctionDef)
                 and n.name == "without_comments"]
    require(len(functions) == 1, "Missing pinned source parser")
    scope = {}
    exec(compile(ast.Module(body=functions, type_ignores=[]), parser_path, "exec"), scope)
    without_comments = scope["without_comments"]
    sources = {}
    for capture in inventory["capture_files"]:
        data = bound(PREP / capture["path"], capture["sha256"])
        for row in data["sources"]:
            raw = row["content"].encode()
            require(git_blob(raw) == row["git_blob_sha"], "Source capture blob mismatch")
            require(row["module"] not in sources or sources[row["module"]] == raw,
                    "Conflicting source captures")
            require(row["path"] == "Proofs/RG_Lean_20261019/" +
                    row["module"].replace(".", "/") + ".lean", "Wrong source capture path")
            sources[row["module"]] = raw
    require(len(sources) == 281 and source_graph(sources, without_comments) == graph,
            "Pinned full source/closure mismatch")
    for name, row in inventory["modules"].items():
        require(sha(sources[name]) == row["source_sha256"] and
                git_blob(sources[name]) == row["git_blob_sha"] and
                graph["source_closure_sha256"][name] == row["source_closure_sha256"],
                "Source inventory mismatch: " + name)
    manifests = {p: decode(files[p]) for p in [BASE_MANIFEST, *EXPECTED_PLAN]}
    expected_priors = {}
    for path, manifest in manifests.items():
        require(manifest["repository"] == REPOSITORY and manifest["mathlib"] == PIN
                and manifest["lean_version"] == "4.33.1", "Changed prerequisite pin")
        for name, row in manifest["modules"].items():
            require(name not in expected_priors, "Unexpected overlapping prerequisite selection")
            require(row["module"] == name and row["axiom_profiles"] and
                    all(set(p) <= ALLOWED for p in row["axiom_profiles"]),
                    "Invalid original prerequisite row")
            require(not row.get("additional_outputs"), "Unexpected unretained prerequisite sidecar")
            if path == BASE_MANIFEST:
                require(row["mode"] in {"FRESH_KERNEL_EXPORT", "PRIOR_VERIFIED_JOB_EXPORT"},
                        "Invalid capsule row")
                old_origin = row["origin"] if row["mode"] == "PRIOR_VERIFIED_JOB_EXPORT" else origin(manifest)
                expected_priors[name] = dict(row, mode="PRIOR_VERIFIED_JOB_EXPORT", origin=old_origin,
                    transport_capsule={k: manifest[k] for k in ORIGIN_KEYS if k != "repository"})
            else:
                require(row["mode"] == "FRESH_KERNEL_EXPORT", "Plan row is not original fresh export")
                expected_priors[name] = dict(row, mode="PRIOR_VERIFIED_JOB_EXPORT",
                                             origin=origin(manifest))
    prior = set(sources) & set(expected_priors)
    fresh = set(sources) - prior
    require(len(expected_priors) == 361 and len(prior) == 118 and len(fresh) == 163,
            "Changed 281 = 118 + 163 scope")
    offers = fixed["static_source_closure/offered_identity_comparison.json"]["modules"]
    require(set(offers) == set(sources), "Changed offered scope")
    for name in sources:
        offered = offers[name]
        require(offered["current_source_sha256"] == graph["source_sha256"][name] and
                offered["current_source_closure_sha256"] == graph["source_closure_sha256"][name],
                "Changed offered source identity")
        require(offered["metadata_status"] == ("EXACT_MATCH_OFFERED" if name in prior else "NO_ROW_OFFERED"),
                "Changed prerequisite/fresh classification")
        if name in prior:
            row = expected_priors[name]
            require(row["source_sha256"] == graph["source_sha256"][name] and
                    row["source_closure_sha256"] == graph["source_closure_sha256"][name],
                    "Stale required prerequisite")
    names = {n: expected_named_declarations(without_comments(sources[n].decode())) for n in fresh}
    require(all(names.values()) and sum(map(len, names.values())) == 838,
            "Changed expected 838 named axiom checks")
    return dict(graph=graph, sources=sources, without_comments=without_comments,
                prior=prior, fresh=fresh, expected_priors=expected_priors,
                names=names, workflow=workflow.decode(),
                manifest_origins={p: origin(m) for p, m in manifests.items()})


def native_metadata():
    run, jobs = (decode((ACTUAL / n).read_bytes()) for n in ("run.json", "jobs.json"))
    require(run["id"] == RUN and run["run_attempt"] == ATTEMPT and
            run["repository"]["full_name"] == REPOSITORY, "Wrong native run")
    require(run["head_sha"] == COMMIT and run["head_branch"] == BRANCH and
            run["event"] == "push" and run["path"] == WORKFLOW, "Wrong native workflow origin")
    require(jobs["total_count"] == len(jobs["jobs"]) == 1, "Incomplete/unexpected job catalog")
    job = jobs["jobs"][0]
    require(job["id"] == JOB and job["run_id"] == RUN and job["run_attempt"] == ATTEMPT,
            "Wrong native job identity")
    require(job["head_sha"] == COMMIT and job["head_branch"] == BRANCH and job["name"] == JOB_NAME,
            "Wrong native job scope")
    require(run["status"] == job["status"] == "completed" and job["completed_at"] is not None,
            "Actual run/job is not terminal")
    require(run["conclusion"] == job["conclusion"] and
            job["conclusion"] in {"success", "failure", "cancelled", "timed_out"},
            "Unrecognized or inconsistent native conclusion")
    steps = {s["name"]: s for s in job["steps"]}
    require(len(steps) == len(job["steps"]), "Duplicate native step")
    return run, job, steps


def log_payloads(text, prefix=None):
    values = []
    for line in text.splitlines():
        line = re.sub(r"^\d{4}-\d\d-\d\dT\S+\s", "", line)
        line = re.sub(r"\x1b\[[0-9;]*m", "", line)
        if prefix is not None:
            if not line.startswith(prefix):
                continue
            line = line[len(prefix):]
        if line.startswith("{"):
            values.append(decode(line))
    return values


def validate_source_bundle(archive, ctx, successful):
    names = set(archive.namelist())
    expected = {SOURCE_PREFIX + n.replace(".", "/") + ".lean": n for n in ctx["sources"]}
    present = names & set(expected)
    require(all(sha(archive.read(path)) == ctx["graph"]["source_sha256"][expected[path]]
                for path in present), "Changed actual bundled original source")
    unexpected = {p for p in names if p.startswith("generated_source/")} - set(expected) - {SOURCE_MANIFEST}
    require(not unexpected, "Unexpected generated source member")
    if SOURCE_MANIFEST in names:
        manifest = decode(archive.read(SOURCE_MANIFEST))
        require(manifest["endpoint"] == ENDPOINT and manifest["anchor_index"] == 29 and
                manifest["kind"] == "ORIGINAL_TARGET_REQUIRES_SUCCESSFUL_KERNEL_RECEIPT",
                "Wrong actual source manifest")
        expected_hashes = {"Proofs/RG_Lean_20261019/" + n.replace(".", "/") + ".lean": h
                           for n, h in ctx["graph"]["source_sha256"].items()}
        require(manifest["source_sha256"] == expected_hashes, "Source manifest scope/hash mismatch")
    complete = len(present) == 281 and SOURCE_MANIFEST in names
    if successful:
        require(complete, "Incomplete original source bundle")
    if complete:
        actual_sources = {n: archive.read(path) for path, n in expected.items()}
        require(source_graph(actual_sources, ctx["without_comments"]) == ctx["graph"],
                "Actual recursive source closure differs")
    return dict(actual_original_source_files_checked=len(present),
                complete_281_original_source_bundle=complete,
                actual_recursive_closure_recomputed=complete)


def profiles_from_log(raw, expected):
    text = raw.decode()
    require(not BAD_DIAGNOSTIC.search(text), "Warning/error in completed module log")
    matches = list(NAMED_AXIOM.finditer(text))
    require([m[1] for m in matches] == expected, "Wrong/missing named axiom declaration")
    profiles = [sorted(set(a.strip() for a in (m[2] or "").split(",") if a.strip()))
                for m in matches]
    require(all(set(p) <= ALLOWED for p in profiles), "Nonstandard axiom")
    # verify_extension groups depends-on profiles before axiom-free profiles.
    grouped = [p for m, p in zip(matches, profiles) if m[2] is not None]
    grouped += [p for m, p in zip(matches, profiles) if m[2] is None]
    return grouped, [dict(declaration=m[1], axioms=p) for m, p in zip(matches, profiles)]


def validate_resource(archive, log, successful):
    if "resource_observer.json" not in archive.namelist():
        require(not successful, "Missing actual resource observer")
        return dict(actual_resource_report_available=False)
    raw = archive.read("resource_observer.json")
    resource = decode(raw)
    logged_results = log_payloads(log, "RG_KERNEL_RESOURCE_RESULT ")
    if logged_results:
        require(len(logged_results) == 1 and logged_results[0] ==
                {k: v for k, v in resource.items() if k != "samples"},
                "Native/archived observer result mismatch")
    samples = resource["samples"]
    require(isinstance(samples, list) and resource["mathlib_and_lean_flags_unchanged"] is True,
            "Changed observer contract")
    observed = log_payloads(log, "RG_KERNEL_RESOURCE_OBSERVATION ")
    require(observed == samples, "Native/archived observer samples mismatch")
    require(resource["maximum_aggregate_lean_rss"] >=
            max((s["aggregate_lean_rss"] for s in samples), default=0),
            "Observer maximum below persisted peak")
    if successful:
        require(resource["status"] == "VERIFIER_COMPLETED" and resource["exit_code"] == 0
                and samples and len(logged_results) == 1, "Observer did not finish successfully")
        require(not log_payloads(log, "RG_KERNEL_RESOURCE_GUARD_LOW_MEMORY "),
                "Actual memory reserve guard fired")
        require(all(type(s["available_bytes"]) is int and s["available_bytes"] >= 2048 * 1024**2
                    for s in samples if s["lean_processes"]), "Actual reserve violation")
    return dict(actual_resource_report_available=True, sha256=sha(raw),
                status=resource["status"], exit_code=resource["exit_code"],
                seconds=resource["seconds"], sample_count=len(samples),
                maximum_aggregate_lean_rss=resource["maximum_aggregate_lean_rss"],
                minimum_observed_available_bytes=min(
                    (s["available_bytes"] for s in samples if type(s["available_bytes"]) is int),
                    default=None),
                reserve_mib_from_unchanged_workflow=2048,
                hidden_memory_limits_or_unobserved_intervals_claim=False)


def validate_archive(ctx, meta, log, successful):
    path = ACTUAL / "artifact.zip"
    require(path.stat().st_size == meta["size_in_bytes"] and
            file_sha(path) == meta["digest"][7:], "Actual full artifact size/digest mismatch")
    logged = table(log_payloads(log, "COMPLETED_MODULE_JSON "))
    require(set(logged) <= ctx["fresh"] and
            all(r["mode"] == "FRESH_KERNEL_EXPORT" for r in logged.values()),
            "Native fresh records exceed fixed frontier")
    with zipfile.ZipFile(path) as archive:
        names = archive.namelist()
        require(len(names) == len(set(names)) and len(names) <= 2000, "Duplicate/excess ZIP members")
        for name in names:
            part = pathlib.PurePosixPath(name)
            require(not part.is_absolute() and ".." not in part.parts and "\\" not in name
                    and not archive.getinfo(name).is_dir(), "Unsafe/unexpected ZIP member")
        result = validate_source_bundle(archive, ctx, successful)
        if "diagnostics_records.json" not in names:
            require(not successful, "Missing actual diagnostic records")
            diagnostics = {}
        else:
            diagnostics = table(decode(archive.read("diagnostics_records.json"))["modules"])
        require(set(diagnostics) <= set(ctx["expected_priors"]) | ctx["fresh"],
                "Unexpected diagnostic module")
        fresh = {n for n, r in diagnostics.items() if r["mode"] == "FRESH_KERNEL_EXPORT"}
        require(fresh <= ctx["fresh"], "Unexpected fresh proof export")
        for name, row in diagnostics.items():
            if name not in fresh:
                require(name in ctx["expected_priors"] and row == ctx["expected_priors"][name],
                        "Changed original prior origin/row: " + name)
        if successful:
            require(fresh == ctx["fresh"] and set(diagnostics) ==
                    set(ctx["expected_priors"]) | fresh and len(diagnostics) == 524,
                    "Incomplete 361 prior + 163 fresh diagnostics")
        require(set(logged) == fresh, "Native completed rows differ from exported fresh rows")
        actual_members, audited = set(), {}
        for name in sorted(fresh):
            row = diagnostics[name]
            require(row == logged[name] == decode(archive.read(name + ".json")),
                    "Native/exported fresh record mismatch")
            require("origin" not in row and "transport_capsule" not in row,
                    "New actual proof relabelled as a prior")
            require(row["source_sha256"] == ctx["graph"]["source_sha256"][name] and
                    row["source_closure_sha256"] == ctx["graph"]["source_closure_sha256"][name],
                    "Fresh source/closure mismatch")
            require(type(row["seconds"]) in (int, float) and math.isfinite(row["seconds"]) and
                    row["seconds"] >= 0, "Invalid module elapsed time")
            require(not row.get("additional_outputs"), "Original exporter did not retain declared sidecars")
            relative = name.replace(".", "/") + ".olean"
            with archive.open(relative) as stream:
                require(hashlib.file_digest(stream, "sha256").hexdigest() == row["output_sha256"],
                        "Actual compiled object bytes differ")
            module_log = archive.read(name + ".log")
            profiles, named = profiles_from_log(module_log, ctx["names"][name])
            require(profiles == row["axiom_profiles"] and profiles, "Record/log axiom mismatch")
            actual_members.update({relative, name + ".json", name + ".log"})
            audited[name] = dict(row=row, output_bytes=archive.getinfo(relative).file_size,
                                 log_sha256=sha(module_log), named_axiom_profiles=named)
        receipt_validated = False
        receipt_digest = None
        if "receipt.json" in names:
            raw = archive.read("receipt.json")
            receipt = decode(raw)
            require(receipt["scope"] == "EXPLICIT_EXTENSION_CLOSURE" and
                    receipt["endpoints"] == [ENDPOINT] and receipt["mathlib"] == PIN and
                    receipt["leancert"] == LC and "version 4.33.1," in receipt["lean"],
                    "Wrong actual original receipt scope/compiler/pins")
            require(receipt["global_rg"] == "NOT_PROVED" and
                    receipt["complete_submission"] == "NOT_SUBMITTED", "Overstated receipt")
            rows = table(receipt["modules"])
            require(set(rows) == set(ctx["sources"]) and len(rows) == 281,
                    "Incomplete original 281-module receipt")
            require(all(rows[n] == diagnostics.get(n) for n in rows), "Receipt/diagnostic mismatch")
            require({n for n, r in rows.items() if r["mode"] == "FRESH_KERNEL_EXPORT"} == ctx["fresh"],
                    "Receipt is not exact 118 prior + 163 fresh")
            receipt_validated, receipt_digest = True, sha(raw)
        if successful:
            require(receipt_validated, "Native success lacks complete actual kernel receipt")
            expected = {SOURCE_PREFIX + n.replace(".", "/") + ".lean" for n in ctx["sources"]}
            expected |= actual_members | {SOURCE_MANIFEST, "diagnostics_records.json",
                                         "resource_observer.json", "receipt.json"}
            require(set(names) == expected and len(names) == 774, "Unexpected full-success ZIP scope")
        else:
            # Failed module logs are retained evidence, never completed proof exports.
            allowed = {SOURCE_PREFIX + n.replace(".", "/") + ".lean" for n in ctx["sources"]}
            allowed |= {SOURCE_MANIFEST, "diagnostics_records.json", "resource_observer.json", "receipt.json"}
            allowed |= actual_members | {n + ".log" for n in ctx["fresh"]}
            require(set(names) <= allowed, "Unrecognized failed-run ZIP member")
        result.update(
            artifact_members=len(names), full_original_receipt_validated=receipt_validated,
            receipt_sha256=receipt_digest, completed_fresh_modules=sorted(fresh),
            completed_fresh_count=len(fresh), actual_fresh_output_bytes=sum(
                v["output_bytes"] for v in audited.values()),
            actual_named_axiom_profiles=sum(len(v["named_axiom_profiles"]) for v in audited.values()),
            required_prior_rows_observed=len(set(diagnostics) & ctx["prior"]),
            additional_diagnostic_prior_rows_observed=len(
                set(diagnostics) & (set(ctx["expected_priors"]) - ctx["prior"])),
            observed_original_prior_rows_and_origins_preserved=True, modules=audited,
            resource=validate_resource(archive, log, successful),
            failed_module_logs={n: sha(archive.read(n + ".log")) for n in ctx["fresh"] - fresh
                                if n + ".log" in names})
        if successful:
            require(result["actual_named_axiom_profiles"] == 838, "Incomplete named profile audit")
        return result


def authenticate(ctx, report):
    run, job, steps = native_metadata()
    successful = job["conclusion"] == "success"
    report.update(native_identity_authenticated=True, native_run_conclusion=run["conclusion"],
                  native_job_conclusion=job["conclusion"], actual_job_completed_at=job["completed_at"],
                  non_success_steps=[{k: s.get(k) for k in ("name", "status", "conclusion")}
                                     for s in job["steps"] if s["conclusion"] != "success"])
    required_steps = re.findall(r"^      - name: (.+)$", ctx["workflow"].replace("\r\n", "\n"), re.M)
    require(set(required_steps) <= set(steps), "Missing expected native workflow step")
    if successful:
        require(all(s["status"] == "completed" and s["conclusion"] == "success"
                    for s in job["steps"]), "Native success has unsuccessful steps")
    log_path = ACTUAL / "job.log"
    log = log_path.read_text() if log_path.is_file() else ""
    report["native_job_log_available"] = bool(log)
    if successful:
        require(bool(log) and KERNEL_COMMAND in log, "Missing exact original kernel invocation")
        require(re.search(r"PASS_EXTENSION_SCOPE 281 MODULES; GLOBAL RG NOT_PROVED", log),
                "Missing actual full endpoint completion log")
    if log:
        report["native_job_log_sha256"] = file_sha(log_path)
        report["observed_timeout_modules"] = sorted(set(re.findall(r"RuntimeError: Timeout: (Proofs\.[\w.]+)", log)))
        frontiers = [r for r in log_payloads(log) if
                     r.get("status") == "EXACT_FRONTIER_REQUIRES_MANDATORY_FRESH_KERNEL_EXPORTS"]
        if successful:
            require(len(frontiers) == 2, "Missing actual restore and preflight frontier reports")
        for frontier in frontiers:
            require(frontier == dict(status="EXACT_FRONTIER_REQUIRES_MANDATORY_FRESH_KERNEL_EXPORTS",
                endpoint=ENDPOINT, required_modules=281, verified_prior_objects=118,
                max_fresh=163, within_bound=True, proof_status="NOT_PROVEN_BY_RESTORE",
                complete_submission="NOT_SUBMITTED"), "Changed actual bounded frontier")
        report["native_frontier_reports"] = frontiers
    artifact_path = ACTUAL / "artifacts.json"
    if not artifact_path.is_file():
        require(not successful, "Actual success has no artifact catalog")
        report.update(status="ACTUAL_TERMINAL_FAILURE_CAPTURED_ARCHIVES_NOT_YET_CAPTURED",
                      missing_local_evidence=["artifacts.json", "artifact.zip"])
        return 3
    catalog = decode(artifact_path.read_bytes())
    require(catalog["total_count"] == len(catalog["artifacts"]), "Incomplete artifact catalog")
    artifacts = catalog["artifacts"]
    require(len(artifacts) <= 1, "Unexpected additional artifact")
    if not artifacts:
        require(not successful, "Actual success has no result artifact")
        report.update(status="ACTUAL_TERMINAL_FAILURE_WITH_NO_RESULT_ARTIFACT",
                      artifact_catalog_empty=True)
        return 3
    meta = artifacts[0]
    require(meta["name"] == ARTIFACT_NAME and type(meta["id"]) is int and meta["id"] > 0,
            "Wrong actual artifact name/identity")
    require(meta["workflow_run"]["id"] == RUN and meta["workflow_run"]["head_sha"] == COMMIT and
            meta["workflow_run"]["head_branch"] == BRANCH and
            meta["workflow_run"]["repository_id"] == meta["workflow_run"]["head_repository_id"] == 1416044648,
            "Wrong actual artifact origin")
    require(re.fullmatch(r"sha256:[0-9a-f]{64}", meta["digest"]) is not None,
            "Missing native archive digest")
    report["artifact"] = {k: meta[k] for k in ("id", "name", "size_in_bytes", "digest", "expired")}
    if not (ACTUAL / "artifact.zip").is_file():
        require(not successful, "Actual success archive has not been captured")
        report.update(status="ACTUAL_TERMINAL_FAILURE_CAPTURED_ARCHIVE_BYTES_NOT_YET_CAPTURED",
                      missing_local_evidence=["artifact.zip"])
        return 3
    require(meta["expired"] is False, "Captured native result artifact is expired")
    report["archive_audit"] = validate_archive(ctx, meta, log, successful)
    report["status"] = ("ACTUAL_ORIGINAL_ANCHOR029_KERNEL_CLOSURE_AUTHENTICATED" if successful else
                        "ACTUAL_TERMINAL_FAILURE_PARTIAL_ARCHIVE_EVIDENCE_AUTHENTICATED")
    report["anchor029_certificate_claim"] = successful
    report["full_original_endpoint_success_authenticated"] = successful
    return 0 if successful else 3


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-fixed-inputs-only", action="store_true")
    args = parser.parse_args()
    report = dict(status="EVIDENCE_INCOMPLETE_OR_REJECTED", repository=REPOSITORY,
        run=RUN, job=JOB, run_attempt=ATTEMPT, source_commit=COMMIT, branch=BRANCH,
        workflow=WORKFLOW, workflow_sha256=WORKFLOW_SHA, restore_plan_sha256=PLAN_SHA,
        reviewed_original_source_identity_commit=SOURCE_COMMIT,
        current_original_source_graph_sha256=FIXED["static_source_closure/source_graph.json"],
        authenticator_sha256=file_sha(pathlib.Path(__file__)),
        native_identity_authenticated=False, full_original_endpoint_success_authenticated=False,
        anchor029_certificate_claim=False, full_degree_one_middle_family_claim=False,
        full_degree_one_large_family_claim=False, global_rg_claim=False,
        production_receipt_created_by_authenticator=False, proof_rows_synthesized=False,
        family_count_change_from_this_anchor_run=0,
        remaining_original_families_without_separate_large_completion=4,
        expected_scope=dict(required_modules=281, prior_modules=118, fresh_modules=163,
                            named_axiom_profiles=838, workers=1, module_timeout_seconds=600,
                            memory_reserve_mib=2048),
        interpretation_limits=[
            "Anchor029 alone does not complete degreeOneMiddle or the RG theorem.",
            "Prior object bytes were checked by the successful fixed native restorers and verifier; "
            "this fresh-only ZIP does not re-export those 118 prior objects.",
            "Per-module seconds include export hashing/bookkeeping; the 600-second Lean subprocess "
            "timeout is bound through the unchanged workflow/verifier and native invocation.",
            "Failure observations and partial exports never stand in for a complete successful receipt."])
    try:
        ctx = fixed_context()
        if args.check_fixed_inputs_only:
            print(json.dumps(dict(status="FIXED_REAL_SOURCE_AND_PLAN_METADATA_VALIDATED_ONLY",
                required_modules=281, matching_prior_modules=118, expected_fresh_modules=163,
                expected_named_axiom_profiles=838, diagnostic_prior_rows=361,
                kernel_run_performed=False, archive_test_performed=False,
                actual_result_report_written=False), sort_keys=True))
            return 0
        report["fixed_input_sha256"] = FIXED
        report["preserved_prerequisite_origins"] = ctx["manifest_origins"]
        code = authenticate(ctx, report)
    except (Exception,) as error:
        report["error"] = f"{type(error).__name__}: {error}"
        report["status"] = ("ACTUAL_TERMINAL_FAILURE_EVIDENCE_INCOMPLETE_OR_REJECTED"
                            if report.get("native_job_conclusion") in {"failure", "cancelled", "timed_out"}
                            else "EVIDENCE_INCOMPLETE_OR_REJECTED")
        report["anchor029_certificate_claim"] = False
        report["full_original_endpoint_success_authenticated"] = False
        code = 2
    if args.check_fixed_inputs_only:
        print(json.dumps(report, indent=2, sort_keys=True))
        return code
    report["native_capture_sha256"] = {name: file_sha(ACTUAL / name) for name in
        ("run.json", "jobs.json", "artifacts.json", "job.log") if (ACTUAL / name).is_file()}
    ACTUAL.mkdir(parents=True, exist_ok=True)
    target = ACTUAL / "original_anchor029_authentication.json"
    raw = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode()
    pending = target.with_suffix(".json.pending")
    pending.write_bytes(raw)
    pending.replace(target)
    print(json.dumps({k: v for k, v in report.items() if k not in
                     {"archive_audit", "preserved_prerequisite_origins", "fixed_input_sha256"}},
                     indent=2, sort_keys=True))
    print("LOCAL_AUTHENTICATION_REPORT " + str(target))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
