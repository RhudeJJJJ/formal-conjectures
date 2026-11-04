#!/usr/bin/env python3
"""Offline audit of a separately bound original Anchor029 continuation.

Inputs are root's actual/run.json, jobs.json, artifacts.json, job.log and
artifact.zip. No network, restoration, Lean invocation or receipt generation.
RUN, JOB, COMMIT and JOB_NAME must be bound to the real new native origin before
any continuation evidence is read. They are deliberately unbound in this draft.
The cancelled producer's 108 exports and 545 named checks remain prior evidence.
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
RUN, JOB, ATTEMPT = 41888401962, 126778939548, 1
COMMIT = "b6924bdabeff35ff4af328c3879c69fc90ecf8f6"
JOB_NAME = "check (Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate029, ci/rg_middle_anchor029_partial_..."
BRANCH = "rg-middle-anchor029-partial-resume-20261104"
WORKFLOW = ".github/workflows/rg-middle-anchor029-partial-resume-20261104.yml"
WORKFLOW_SHA = "a6d2e2c84ff5d191a06c94f3fbf057cc4b0555e4cb57cd8190992aff311f3145"
PLAN_PATH = "ci/rg_middle_anchor029_partial_resume_restore_plan_20261104.json"
PLAN_SHA = "5937c30e2f16a6ee9c95cfbc3eb4bfe14e455cc9995a804fbf1446bdbab378ab"
PARTIAL_MANIFEST = "ci/rg_middle_anchor029_run41826563525_partial_prior_exports.json"
PARTIAL_MANIFEST_SHA = "59b460a03405b69f4889c4e6954f6bf1abc53be3cbf96ed38799fe44abbdbf4f"
CONTINUATION_SCOPE_SHA = "b2c7c2b3483d845fa84ff71f7e906cd9dc657a8e73cfc7e09c9d4d09e529a06f"
PRODUCER_AUTH_PATH = PREP / "original_anchor029_candidate/actual/original_anchor029_authentication.json"
PRODUCER_AUTH_SHA = "d5189d1fb0493e394d65054c29f1a4ac3a934e84d2e8873172bb758207312783"
PRODUCER_RUN, PRODUCER_JOB = 41826563525, 126562666235
PRODUCER_COMMIT = "5b7bd43a9f3ca170b19450dd4f34fe9d12bbba90"
PRODUCER_ARTIFACT = 13351145439
PRODUCER_ARTIFACT_SHA = "11c263c3f06adca05f4810ed1d410221f6e2d4b1a479dcf8b731f435d5b98fd5"
PRODUCER_AUTHENTICATOR_SHA = "42443d8649ed3cd5ca7fc73b80f35a6d73c73fed3f80ebef430f677132ca548c"
SOURCE_COMMIT = "7a64184a0b353295d4977004066e163375cf3b4b"
ENDPOINT = "Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate029"
ARTIFACT_NAME = f"rg-middle-anchor029-partial-resume-20261104-exports-{RUN}-0"
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
LC = "621a43d7cf21f87872392a01e874f2f1dbddc926"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ORIGIN_KEYS = ("repository", "run", "job", "source_commit", "artifact_id", "artifact_sha256")
BASE_MANIFEST = "ci/rg_reusable_analytic_kernel_base_complete_scope_capsule.json"
HISTORICAL_PLAN = [
    "ci/rg_middle_generic_recovery_20261104_run41805266301_prior_exports.json",
    "ci/rg_middle_original_integer_payment_generic_prior_exports.json",
    "ci/rg_middle_oct27_anchor028_parts_original_partial_prior_exports.json",
    "ci/rg_middle_oct28_anchor028_original_prior_exports.json",
]
EXPECTED_PLAN = [*HISTORICAL_PLAN, PARTIAL_MANIFEST]
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


def require_actual_binding():
    """Reject an unbound draft before any new actual evidence is inspected."""
    require(type(RUN) is int and RUN > 0 and type(JOB) is int and JOB > 0,
            "Bind the actual new RUN and JOB before reading continuation evidence")
    require(isinstance(COMMIT, str) and re.fullmatch(r"[0-9a-f]{40}", COMMIT) is not None,
            "Bind the actual new COMMIT before reading continuation evidence")
    require(isinstance(JOB_NAME, str) and bool(JOB_NAME.strip()),
            "Bind the exact actual native matrix JOB_NAME; never infer truncation")
    require(RUN != PRODUCER_RUN and JOB != PRODUCER_JOB and COMMIT != PRODUCER_COMMIT,
            "The cancelled producer cannot stand in for a new continuation run")


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


def producer_evidence():
    """Read the frozen authenticated producer report, never its ZIP or checker."""
    producer = bound(PRODUCER_AUTH_PATH, PRODUCER_AUTH_SHA)
    partial = bound(HERE / "patch" / PARTIAL_MANIFEST, PARTIAL_MANIFEST_SHA)
    continuation = bound(HERE / "continuation_scope.json", CONTINUATION_SCOPE_SHA)
    require(producer["status"] == "ACTUAL_TERMINAL_FAILURE_PARTIAL_ARCHIVE_EVIDENCE_AUTHENTICATED"
            and producer["native_identity_authenticated"] is True,
            "Producer is not authenticated actual partial evidence")
    require((producer["repository"], producer["run"], producer["job"], producer["run_attempt"],
             producer["source_commit"]) ==
            (REPOSITORY, PRODUCER_RUN, PRODUCER_JOB, 1, PRODUCER_COMMIT),
            "Changed authenticated producer identity")
    require(producer["native_run_conclusion"] == producer["native_job_conclusion"] == "cancelled",
            "The producer origin must remain cancelled")
    require(producer["authenticator_sha256"] == PRODUCER_AUTHENTICATOR_SHA
            and producer["fixed_input_sha256"] == FIXED,
            "Changed producer authenticator or original fixed evidence")
    require(not producer["full_original_endpoint_success_authenticated"]
            and not producer["anchor029_certificate_claim"]
            and not producer["full_degree_one_middle_family_claim"]
            and not producer["global_rg_claim"]
            and producer["family_count_change_from_this_anchor_run"] == 0
            and not producer["production_receipt_created_by_authenticator"]
            and not producer["proof_rows_synthesized"], "Overstated producer evidence")
    artifact = producer["artifact"]
    require(artifact["id"] == PRODUCER_ARTIFACT and artifact["size_in_bytes"] == 5122551
            and artifact["digest"] == "sha256:" + PRODUCER_ARTIFACT_SHA,
            "Changed authenticated producer archive")
    audit = producer["archive_audit"]
    require(audit["artifact_members"] == 608 and audit["complete_281_original_source_bundle"]
            and audit["actual_original_source_files_checked"] == 281
            and audit["actual_recursive_closure_recomputed"],
            "Producer did not authenticate the entire original source closure")
    require(audit["completed_fresh_count"] == len(audit["modules"]) == 108
            and audit["actual_fresh_output_bytes"] == 15631024
            and audit["actual_named_axiom_profiles"] == 545
            and audit["required_prior_rows_observed"] == 118
            and audit["additional_diagnostic_prior_rows_observed"] == 243
            and audit["observed_original_prior_rows_and_origins_preserved"]
            and not audit["full_original_receipt_validated"] and audit["receipt_sha256"] is None,
            "Changed producer partial-proof scope")
    inherited = audit["modules"]
    require(set(inherited) == set(audit["completed_fresh_modules"]),
            "Producer completed module lists disagree")
    expected_rows = {name: item["row"] for name, item in inherited.items()}
    require(partial["modules"] == expected_rows, "Partial manifest changed an authenticated row")
    require(tuple(partial[k] for k in ORIGIN_KEYS) ==
            (REPOSITORY, PRODUCER_RUN, PRODUCER_JOB, PRODUCER_COMMIT,
             PRODUCER_ARTIFACT, PRODUCER_ARTIFACT_SHA), "Partial manifest changed producer origin")
    context = partial["origin_context"]
    require(context == dict(scope="INDIVIDUAL_COMPLETED_KERNEL_EXPORTS_ONLY",
            whole_job_conclusion="cancelled", completed_endpoint_receipt=False,
            full_original_log_sha256=producer["native_job_log_sha256"],
            authenticated_partial_archive_report_sha256=PRODUCER_AUTH_SHA,
            completed_fresh_modules=108, completed_named_axiom_profiles=545),
            "Partial-origin context overstates or changes the cancelled job")
    require(continuation["kind"] == "AUTHENTICATED_PRIOR_AND_SOURCE_ONLY_CONTINUATION_PLAN"
            and continuation["endpoint"] == ENDPOINT
            and continuation["producer_authentication_report_sha256"] == PRODUCER_AUTH_SHA
            and continuation["original_source_graph_sha256"] == FIXED["static_source_closure/source_graph.json"]
            and continuation["source_identity_commit"] == SOURCE_COMMIT,
            "Changed continuation source/evidence binding")
    require((continuation["required_modules"], continuation["original_prior_modules"],
             continuation["newly_authenticated_prior_modules"],
             continuation["predicted_required_prior_modules"], continuation["predicted_fresh_modules"],
             continuation["original_named_axiom_checks"], continuation["inherited_named_axiom_checks"],
             continuation["remaining_named_axiom_checks"]) == (281, 118, 108, 226, 55, 838, 545, 293),
            "Changed continuation partition")
    require(not continuation["actual_continuation_preflight_performed"]
            and not continuation["actual_continuation_kernel_run_performed"]
            and not continuation["full_original_endpoint_success_claimed"]
            and not continuation["middle_family_success_claimed"]
            and not continuation["global_rg_success_claimed"],
            "Preparation is not an actual continuation result")
    return producer, partial, continuation


def fixed_context():
    fixed = {p: bound(PREP / p, h) for p, h in FIXED.items()}
    graph = fixed["static_source_closure/source_graph.json"]
    inventory = fixed["static_source_closure/source_inventory.json"]
    require(inventory["commit"] == SOURCE_COMMIT and inventory["endpoint"] == ENDPOINT,
            "Wrong reviewed source scope")
    workflow = (HERE / "patch" / WORKFLOW).read_bytes()
    require(sha(workflow) == WORKFLOW_SHA, "Changed original workflow")
    require(bound(HERE / "patch" / PLAN_PATH, PLAN_SHA) == EXPECTED_PLAN, "Changed restore plan")
    producer, partial, continuation = producer_evidence()
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
    manifests = {p: decode(files[p]) for p in [BASE_MANIFEST, *HISTORICAL_PLAN]}
    require(producer["preserved_prerequisite_origins"] ==
            {p: origin(m) for p, m in manifests.items()}, "Changed historical prerequisite origins")
    historical_modules = set().union(*(set(m["modules"]) for m in manifests.values()))
    require(len(historical_modules) == 361, "Changed old offered prerequisite scope")
    manifests[PARTIAL_MANIFEST] = partial
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
    historical_prior = set(sources) & historical_modules
    inherited = producer["archive_audit"]["modules"]
    original_fresh = set(sources) - historical_prior
    require(len(expected_priors) == 469 and len(prior) == 226 and len(fresh) == 55
            and len(historical_prior) == 118 and len(original_fresh) == 163
            and not set(inherited) & historical_modules
            and prior == historical_prior | set(inherited),
            "Changed 281 = 118 + 108 + 55 scope")
    offers = fixed["static_source_closure/offered_identity_comparison.json"]["modules"]
    require(set(offers) == set(sources), "Changed offered scope")
    for name in sources:
        offered = offers[name]
        require(offered["current_source_sha256"] == graph["source_sha256"][name] and
                offered["current_source_closure_sha256"] == graph["source_closure_sha256"][name],
                "Changed offered source identity")
        require(offered["metadata_status"] ==
                ("EXACT_MATCH_OFFERED" if name in historical_prior else "NO_ROW_OFFERED"),
                "Changed historical prerequisite/fresh classification")
        if name in prior:
            row = expected_priors[name]
            require(row["source_sha256"] == graph["source_sha256"][name] and
                    row["source_closure_sha256"] == graph["source_closure_sha256"][name],
                    "Stale required prerequisite")
    original_names = {n: expected_named_declarations(without_comments(sources[n].decode()))
                      for n in original_fresh}
    require(all(original_names.values()) and sum(map(len, original_names.values())) == 838,
            "Changed original 838 named axiom checks")
    require(continuation["original_prior_module_names"] == sorted(historical_prior)
            and continuation["completed_producer_module_names"] == sorted(inherited)
            and continuation["remaining_module_names"] == sorted(fresh),
            "Continuation module identities differ from the unchanged full source graph")
    bindings = continuation["original_fresh_module_bindings"]
    require(set(bindings) == original_fresh, "Incomplete original module/profile binding table")
    for name in sorted(original_fresh):
        binding = bindings[name]
        require(binding["source_sha256"] == graph["source_sha256"][name]
                and binding["source_closure_sha256"] == graph["source_closure_sha256"][name]
                and binding["expected_named_axiom_checks"] == original_names[name],
                "Changed source-derived original profile list: " + name)
        if name in inherited:
            item = inherited[name]
            row = item["row"]
            require(row["module"] == name and row["mode"] == "FRESH_KERNEL_EXPORT"
                    and "origin" not in row and "transport_capsule" not in row
                    and not row.get("additional_outputs"), "Relabelled producer export")
            require(row["source_sha256"] == graph["source_sha256"][name]
                    and row["source_closure_sha256"] == graph["source_closure_sha256"][name],
                    "Producer source/closure identity changed")
            require([p["declaration"] for p in item["named_axiom_profiles"]] == original_names[name]
                    and all(set(p["axioms"]) <= ALLOWED for p in item["named_axiom_profiles"]),
                    "Changed inherited ordered declarations/axiom profile")
            require(binding["status"] == "AUTHENTICATED_COMPLETED_EXPORT_FROM_CANCELLED_PRODUCER"
                    and binding["output_sha256"] == row["output_sha256"]
                    and binding["module_log_sha256"] == item["log_sha256"]
                    and binding["authenticated_named_axiom_profiles"] == item["named_axiom_profiles"],
                    "Inherited profile or original output/log binding changed")
            require(set(graph["source_dependencies"][name]) <= prior,
                    "Producer selected exports do not close over required priors")
        else:
            require(binding["status"] == "REQUIRES_FUTURE_FRESH_KERNEL_EXPORT"
                    and binding["local_dependencies"] == graph["source_dependencies"][name],
                    "Changed remaining proof obligation")
    inherited_count = sum(len(item["named_axiom_profiles"]) for item in inherited.values())
    names = {name: original_names[name] for name in fresh}
    require(inherited_count == 545 and sum(map(len, names.values())) == 293,
            "Original named checks must partition as exact inherited 545 plus fresh 293")
    return dict(graph=graph, sources=sources, without_comments=without_comments,
                prior=prior, fresh=fresh, expected_priors=expected_priors,
                names=names, workflow=workflow.decode(),
                historical_prior=historical_prior, original_fresh=original_fresh,
                original_names=original_names, inherited=inherited,
                producer=producer, continuation=continuation,
                manifest_origins={p: origin(m) for p, m in manifests.items()})


def expected_complete_archive_members(ctx):
    """Derive the exact fresh-only output scope from the fixed original modules."""
    members = {SOURCE_PREFIX + name.replace(".", "/") + ".lean" for name in ctx["sources"]}
    for name in ctx["fresh"]:
        members.update({name.replace(".", "/") + ".olean", name + ".json", name + ".log"})
    return members | {SOURCE_MANIFEST, "diagnostics_records.json", "resource_observer.json", "receipt.json"}


def native_metadata():
    require_actual_binding()
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
    require_actual_binding()
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
                    "Incomplete 469 prior + 55 fresh diagnostics")
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
                    "Receipt is not exact 226 prior + 55 fresh")
            receipt_validated, receipt_digest = True, sha(raw)
        if successful:
            require(receipt_validated, "Native success lacks complete actual kernel receipt")
            expected = expected_complete_archive_members(ctx)
            require(set(names) == expected and len(names) == len(expected),
                    "Unexpected full-success ZIP scope derived from the exact module partition")
        else:
            # Failed module logs are retained evidence, never completed proof exports.
            allowed = {SOURCE_PREFIX + n.replace(".", "/") + ".lean" for n in ctx["sources"]}
            allowed |= {SOURCE_MANIFEST, "diagnostics_records.json", "resource_observer.json", "receipt.json"}
            allowed |= actual_members | {n + ".log" for n in ctx["fresh"]}
            require(set(names) <= allowed, "Unrecognized failed-run ZIP member")
        inherited_checks = {name: item["named_axiom_profiles"]
                            for name, item in ctx["inherited"].items()}
        require(not set(inherited_checks) & set(audited),
                "A producer proof was relabelled as a fresh continuation export")
        combined_checks = {**inherited_checks,
                           **{name: item["named_axiom_profiles"] for name, item in audited.items()}}
        require(set(combined_checks) <= ctx["original_fresh"] and all(
            [profile["declaration"] for profile in checks] == ctx["original_names"][name]
            for name, checks in combined_checks.items()),
            "Combined original profile occurrences changed by module or declaration order")
        inherited_count = sum(map(len, inherited_checks.values()))
        combined_count = sum(map(len, combined_checks.values()))
        result.update(
            artifact_members=len(names), full_original_receipt_validated=receipt_validated,
            receipt_sha256=receipt_digest, completed_fresh_modules=sorted(fresh),
            completed_fresh_count=len(fresh), actual_fresh_output_bytes=sum(
                v["output_bytes"] for v in audited.values()),
            actual_named_axiom_profiles=sum(len(v["named_axiom_profiles"]) for v in audited.values()),
            inherited_named_axiom_profiles=inherited_count,
            combined_original_named_axiom_profiles=combined_count,
            complete_original_profile_module_set=(set(combined_checks) == ctx["original_fresh"]),
            expected_full_success_artifact_members=len(expected_complete_archive_members(ctx)),
            required_prior_rows_observed=len(set(diagnostics) & ctx["prior"]),
            additional_diagnostic_prior_rows_observed=len(
                set(diagnostics) & (set(ctx["expected_priors"]) - ctx["prior"])),
            observed_original_prior_rows_and_origins_preserved=True, modules=audited,
            resource=validate_resource(archive, log, successful),
            failed_module_logs={n: sha(archive.read(n + ".log")) for n in ctx["fresh"] - fresh
                                if n + ".log" in names})
        if successful:
            require(result["actual_named_axiom_profiles"] == 293 and inherited_count == 545
                    and combined_count == 838 and set(combined_checks) == ctx["original_fresh"],
                    "Incomplete ordered original profile audit: inherited 545 plus new 293 must cover all 838")
        return result


def authenticate(ctx, report):
    require_actual_binding()
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
                endpoint=ENDPOINT, required_modules=281, verified_prior_objects=226,
                max_fresh=55, within_bound=True, proof_status="NOT_PROVEN_BY_RESTORE",
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
    report["status"] = ("ACTUAL_ORIGINAL_ANCHOR029_CONTINUATION_KERNEL_CLOSURE_AUTHENTICATED" if successful else
                        "ACTUAL_TERMINAL_FAILURE_PARTIAL_ARCHIVE_EVIDENCE_AUTHENTICATED")
    report["anchor029_certificate_claim"] = successful
    report["full_original_endpoint_success_authenticated"] = successful
    return 0 if successful else 3


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-fixed-inputs-only", action="store_true")
    args = parser.parse_args()
    if not args.check_fixed_inputs_only:
        try:
            require_actual_binding()
        except Exception as error:
            # No continuation ACTUAL path is inspected, hashed or created here.
            print(json.dumps(dict(status="UNBOUND_CONTINUATION_ACTUAL_EVIDENCE_NOT_READ",
                error=f"{type(error).__name__}: {error}", run=RUN, job=JOB, source_commit=COMMIT,
                job_name=JOB_NAME, actual_evidence_read=False, actual_result_report_written=False,
                anchor029_certificate_claim=False, full_degree_one_middle_family_claim=False,
                global_rg_claim=False), indent=2, sort_keys=True))
            return 2
    report = dict(status="EVIDENCE_INCOMPLETE_OR_REJECTED", repository=REPOSITORY,
        run=RUN, job=JOB, run_attempt=ATTEMPT, source_commit=COMMIT, branch=BRANCH,
        workflow=WORKFLOW, workflow_sha256=WORKFLOW_SHA, restore_plan_sha256=PLAN_SHA,
        partial_prior_manifest_sha256=PARTIAL_MANIFEST_SHA,
        continuation_scope_sha256=CONTINUATION_SCOPE_SHA,
        producer_partial_authentication_report_sha256=PRODUCER_AUTH_SHA,
        reviewed_original_source_identity_commit=SOURCE_COMMIT,
        current_original_source_graph_sha256=FIXED["static_source_closure/source_graph.json"],
        authenticator_sha256=file_sha(pathlib.Path(__file__)),
        native_identity_authenticated=False, full_original_endpoint_success_authenticated=False,
        anchor029_certificate_claim=False, full_degree_one_middle_family_claim=False,
        full_degree_one_large_family_claim=False, global_rg_claim=False,
        production_receipt_created_by_authenticator=False, proof_rows_synthesized=False,
        family_count_change_from_this_anchor_run=0,
        remaining_original_families_without_separate_large_completion=4,
        expected_scope=dict(required_modules=281, prior_modules=226, fresh_modules=55,
                            original_named_axiom_profiles=838, inherited_named_axiom_profiles=545,
                            new_named_axiom_profiles=293, diagnostic_prior_rows=469,
                            workers=1, module_timeout_seconds=600,
                            memory_reserve_mib=2048, job_timeout_minutes=360),
        interpretation_limits=[
            "Anchor029 alone does not complete degreeOneMiddle or the RG theorem.",
            "Prior object bytes were checked by the successful fixed native restorers and verifier; "
            "this fresh-only ZIP does not re-export those 226 prior objects.",
            "The cancelled producer's 108 prior rows and 545 ordered named checks remain bound "
            "to its frozen authenticated report; they are never fresh results of this continuation.",
            "Per-module seconds include export hashing/bookkeeping; the 600-second Lean subprocess "
            "timeout is bound through the unchanged workflow/verifier and native invocation.",
            "Failure observations and partial exports never stand in for a complete successful receipt."])
    try:
        ctx = fixed_context()
        if args.check_fixed_inputs_only:
            print(json.dumps(dict(status="FIXED_REAL_SOURCE_AND_PLAN_METADATA_VALIDATED_ONLY",
                required_modules=281, matching_prior_modules=226, expected_fresh_modules=55,
                original_named_axiom_profiles=838, inherited_named_axiom_profiles=545,
                expected_new_named_axiom_profiles=293, diagnostic_prior_rows=469,
                expected_full_success_archive_members=len(expected_complete_archive_members(ctx)),
                kernel_run_performed=False, archive_test_performed=False,
                actual_result_report_written=False), sort_keys=True))
            return 0
        report["fixed_input_sha256"] = FIXED
        report["preserved_prerequisite_origins"] = ctx["manifest_origins"]
        report["inherited_completed_producer_modules"] = ctx["inherited"]
        report["inherited_producer_identity"] = dict(repository=REPOSITORY, run=PRODUCER_RUN,
            job=PRODUCER_JOB, source_commit=PRODUCER_COMMIT, artifact_id=PRODUCER_ARTIFACT,
            artifact_sha256=PRODUCER_ARTIFACT_SHA, whole_job_conclusion="cancelled",
            completed_endpoint_receipt=False, authenticated_report_sha256=PRODUCER_AUTH_SHA)
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
    target = ACTUAL / "anchor029_continuation_authentication.json"
    raw = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode()
    pending = target.with_suffix(".json.pending")
    pending.write_bytes(raw)
    pending.replace(target)
    print(json.dumps({k: v for k, v in report.items() if k not in
                     {"archive_audit", "inherited_completed_producer_modules",
                      "preserved_prerequisite_origins", "fixed_input_sha256"}},
                     indent=2, sort_keys=True))
    print("LOCAL_AUTHENTICATION_REPORT " + str(target))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
