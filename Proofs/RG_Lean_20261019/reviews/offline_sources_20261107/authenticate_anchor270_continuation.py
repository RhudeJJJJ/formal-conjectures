#!/usr/bin/env python3
"""Offline authentication of a separately bound original Anchor270 continuation.

No network, restoration, Lean invocation or production receipt creation.
The actual native run/job/head/name are supplied in a separate fixed binding JSON.
Actual mode rejects an unbound value before inspecting new actual evidence.
The frozen producer checker is loaded by exact SHA only to call fixed_context();
its authenticate() and its historical ZIP are never used here.
--check-fixed-inputs-only reads fixed source/plan/report metadata only.
Exit 0 authenticates a complete endpoint, exit 3 captures a terminal failure,
and exit 2 rejects incomplete, inconsistent or unbound evidence.
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
BASE = HERE.parent.parent
ACTUAL = None
BINDING = None
BINDING_SHA = None
RUN = JOB = COMMIT = JOB_NAME = ARTIFACT_NAME = None
ATTEMPT = 1
REPOSITORY = "RhudeJJJJ/formal-conjectures"
SOURCE_COMMIT = "5aed41513a76d7d22be5087091e796587353bbf5"
ENDPOINT = "Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate270"
BRANCH = "rg-middle-anchor270-partial-resume-20261105"
WORKFLOW = ".github/workflows/rg-middle-anchor270-partial-resume-20261105.yml"
WORKFLOW_SHA = "cc322b35c1b68a4c16f583c4fa2023ef99746b27997e5dbae9b76d8d252325aa"
PLAN_PATH = "ci/rg_middle_anchor270_partial_resume_restore_plan_20261105.json"
PLAN_SHA = "e9c9ef349a347bbaa84945cb020bc8e6226fe7a8923d9f1ec7394485aff9a955"
PARTIAL_MANIFEST = "ci/rg_middle_anchor270_run40714530693_partial_prior_exports.json"
PARTIAL_MANIFEST_SHA = "52b6336b8e6e4f4a9b3a74ce1b47fc782dd5a2224124c824a7486cb9f6e8deb8"
PRODUCER_CHECKER_PATH = BASE / "anchor270_producer/authenticate_original_anchor270_partial.py"
PRODUCER_CHECKER_SHA = "df2890d204d6216006689292da5754502e4e0c90e7eb339355a6b12e8ca46610"
PRODUCER_AUTH_PATH = BASE / "anchor270_producer/actual/original_anchor270_partial_authentication.json"
PRODUCER_AUTH_SHA = "fed1b82a66e787b2b63a0fb81bdaf81dd819e44967fb639a4a411ca45f6e147f"
PRODUCER_RUN, PRODUCER_JOB = 40714530693, 122908481481
PRODUCER_COMMIT = "b5648d132318fe3d955f1ebe79ed333a58abc722"
PRODUCER_ARTIFACT = 12891755528
PRODUCER_ARTIFACT_SHA = "ef6ab324fbaec1259f6fa89fbb05185c28437fd8a2750f43b0ac21fec47d3f0f"
CURRENT_INVENTORY_PATH = BASE / "native_evidence/anchor270_candidate/current_origin/source_inventory.json"
CURRENT_INVENTORY_SHA = "8b2569b52ab47b0a46ee94f467b8ae014acacb76db5b476d12dbacdd28435a1e"
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
LC = "621a43d7cf21f87872392a01e874f2f1dbddc926"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ORIGIN_KEYS = ("repository", "run", "job", "source_commit", "artifact_id", "artifact_sha256")
BASE_MANIFEST = "ci/rg_reusable_analytic_kernel_base_complete_scope_capsule.json"
OLD_GENERIC = "ci/rg_middle_original_predicate_generic_prior_exports.json"
GENERIC = "ci/rg_middle_generic_recovery_20261104_run41805266301_prior_exports.json"
HISTORICAL_PLAN = [
    GENERIC,
    "ci/rg_middle_original_integer_payment_generic_prior_exports.json",
    "ci/rg_middle_oct27_anchor028_parts_original_partial_prior_exports.json",
    "ci/rg_middle_oct28_anchor028_original_prior_exports.json",
]
EXPECTED_PLAN = [*HISTORICAL_PLAN, PARTIAL_MANIFEST]
KERNEL_STEP = "Check multiplicities and actual graph spectral comparison"
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
PRODUCER_FIXED = {'anchor270_scope/anchor270_source_graph.json': '5ffc7c75e7b71207669bcc8bba8edc89531f047a6e3b709a2de38f77a7729275', 'anchor270_scope/anchor270_source_inventory.json': '239dec03575cb3056401dd7c938232369cecf46d15bdfc7a07584f288d06eac5', 'anchor270_scope/source_tree_identity_bridge.json': '6510e8c6f609bd258bfd3032c8c9d2a51e027b99515d41019dc62d5e8683bd49', 'historical_origin/source_inventory.json': '04fde1d2f971735e254bfcd282e32ea51bd423ff856cab3858efdc4632236284'}
FIXED = {
    **PRODUCER_FIXED,
    "native_evidence/anchor270_candidate/current_origin/source_inventory.json": CURRENT_INVENTORY_SHA,
    "anchor270_producer/authenticate_original_anchor270_partial.py": PRODUCER_CHECKER_SHA,
    "anchor270_producer/actual/original_anchor270_partial_authentication.json": PRODUCER_AUTH_SHA,
    "native_evidence/anchor270_candidate/patch/" + WORKFLOW: WORKFLOW_SHA,
    "native_evidence/anchor270_candidate/patch/" + PLAN_PATH: PLAN_SHA,
    "native_evidence/anchor270_candidate/patch/" + PARTIAL_MANIFEST: PARTIAL_MANIFEST_SHA,
}
BINDING_CONSTANTS = {
    "schema": "rg_anchor270_continuation_fixed_binding_v1",
    "repository": REPOSITORY,
    "source_identity_commit": SOURCE_COMMIT,
    "workflow_sha256": WORKFLOW_SHA,
    "restore_plan_sha256": PLAN_SHA,
    "partial_prior_manifest_sha256": PARTIAL_MANIFEST_SHA,
    "producer_authenticator_sha256": PRODUCER_CHECKER_SHA,
    "producer_authentication_report_sha256": PRODUCER_AUTH_SHA,
    "current_inventory_sha256": CURRENT_INVENTORY_SHA,
}



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


def require_actual_binding():
    """Check binding only; do not inspect an actual path until this succeeds."""
    require(BINDING is not None and re.fullmatch(r"[0-9a-f]{64}", BINDING_SHA or ""),
            "Load the fixed external binding before reading actual evidence")
    require(type(RUN) is int and RUN > 0 and type(JOB) is int and JOB > 0,
            "Bind the actual new run and job before reading continuation evidence")
    require(type(ATTEMPT) is int and ATTEMPT == 1,
            "This fixed continuation expects its first native run attempt")
    require(isinstance(COMMIT, str) and re.fullmatch(r"[0-9a-f]{40}", COMMIT) is not None
            and COMMIT != "0" * 40, "Bind the actual new head SHA")
    require(isinstance(JOB_NAME, str) and bool(JOB_NAME.strip()) and ENDPOINT in JOB_NAME,
            "Bind the exact actual native matrix job name; never infer truncation")
    require(RUN != PRODUCER_RUN and JOB != PRODUCER_JOB and COMMIT != PRODUCER_COMMIT,
            "The cancelled producer cannot stand in for the continuation")
    require(RUN != 41888401962 and JOB != 126778939548,
            "Anchor029 is not this new Anchor270 continuation")
    require(RUN != 42052127520 and JOB != 127330696809,
            "The running Anchor030 job is not this new Anchor270 continuation")


def configure_binding(path, require_native):
    global BINDING, BINDING_SHA, RUN, JOB, ATTEMPT, COMMIT, JOB_NAME, ARTIFACT_NAME, ACTUAL
    raw = path.read_bytes()
    data = decode(raw)
    require(set(data) == set(BINDING_CONSTANTS) |
            {"run", "job", "attempt", "head_sha", "job_name", "actual_directory"},
            "Unexpected or missing binding field")
    require(all(data[k] == v for k, v in BINDING_CONSTANTS.items()),
            "Binding changes a frozen source, plan, manifest or producer identity")
    require(isinstance(data["actual_directory"], str) and data["actual_directory"],
            "Missing bound actual directory")
    rel = pathlib.PurePosixPath(data["actual_directory"])
    require(not rel.is_absolute() and ".." not in rel.parts and "\\" not in str(rel),
            "Actual directory must be a relative path within the current work")
    BINDING, BINDING_SHA = data, sha(raw)
    RUN, JOB, ATTEMPT = data["run"], data["job"], data["attempt"]
    COMMIT, JOB_NAME = data["head_sha"], data["job_name"]
    if require_native:
        require_actual_binding()
    # Constructing a path does not inspect it. No is_file/exists/read happens here.
    ACTUAL = BASE / str(rel)
    ARTIFACT_NAME = f"rg-middle-anchor270-partial-resume-20261105-exports-{RUN}-0"


def producer_evidence(core, namespace):
    """Read the frozen authenticated report and manifest, never historical ZIP bytes."""
    producer = bound(PRODUCER_AUTH_PATH, PRODUCER_AUTH_SHA)
    partial = bound(HERE / "patch" / PARTIAL_MANIFEST, PARTIAL_MANIFEST_SHA)
    require(producer["status"] == "ACTUAL_CANCELLED_ORIGINAL_ANCHOR270_PARTIAL_EXPORTS_AUTHENTICATED",
            "Producer is not authenticated actual partial evidence")
    require(tuple(producer[k] for k in ("repository", "run", "job", "run_attempt", "source_commit"))
            == (REPOSITORY, PRODUCER_RUN, PRODUCER_JOB, 1, PRODUCER_COMMIT),
            "Changed authenticated producer identity")
    require(producer["native_run_conclusion"] == producer["native_job_conclusion"] == "cancelled",
            "The producer origin must remain cancelled")
    require(producer["authenticator_sha256"] == PRODUCER_CHECKER_SHA
            and producer["fixed_input_sha256"] == PRODUCER_FIXED
            and producer["native_capture_sha256"] == namespace["NATIVE_SHA256"],
            "Changed frozen producer checker or evidence bindings")
    require(producer["current_source_identity_commit"] == SOURCE_COMMIT
            and producer["endpoint"] == ENDPOINT,
            "Changed producer current source identity")
    require(producer["artifact"] == dict(
        id=PRODUCER_ARTIFACT,
        name="rg-nine-original-anchors-verified-tail-decomposition-20261028-exports-40714530693-2",
        size_in_bytes=5861934, digest="sha256:" + PRODUCER_ARTIFACT_SHA, expired=False),
        "Changed authenticated original archive")
    require(producer["archive_members"] == 668
            and producer["complete_original_source_bundle_files"] == 281
            and producer["historical_and_current_source_bytes_and_recursive_closures_identical"] is True,
            "Producer did not authenticate the full original source closure")
    require((producer["required_modules"], producer["required_historical_prior_modules"],
             producer["additional_historical_diagnostic_prior_modules"],
             producer["completed_fresh_count"], producer["completed_named_axiom_profiles"],
             producer["actual_fresh_output_bytes"], producer["remaining_fresh_count"],
             producer["remaining_named_axiom_profiles"]) ==
            (281, 118, 243, 128, 655, 18129448, 35, 183), "Changed producer partial-proof scope")
    require(producer["original_prior_rows_and_origins_preserved"] is True
            and producer["preserved_prerequisite_origins"] == core["manifest_origins"],
            "Changed actual historical prerequisite origins")
    for name in ("actual_complete_endpoint_receipt_present", "full_original_endpoint_success_authenticated",
                 "anchor270_certificate_claim", "degree_one_middle_family_claim", "global_rg_claim",
                 "proof_rows_synthesized", "production_receipt_created_by_authenticator",
                 "kernel_run_performed_by_authenticator"):
        require(producer[name] is False, "Overstated producer evidence: " + name)
    require(producer["family_count_change_from_this_run"] == 0
            and producer["total_original_families_remaining_after_separate_large_completion"] == 3,
            "Changed formalization scope")
    require(producer["endpoint_source_sha256"] == core["graph"]["source_sha256"][ENDPOINT]
            and producer["endpoint_source_closure_sha256"] ==
            core["graph"]["source_closure_sha256"][ENDPOINT], "Changed producer endpoint")
    inherited = producer["modules"]
    require(set(inherited) == core["completed"] and len(inherited) == 128
            and producer["remaining_module_names"] == sorted(core["remaining"]),
            "Changed completed and remaining original module names")
    require(partial["kind"] == "AUTHENTICATED_PARTIAL_KERNEL_EXPORTS"
            and partial["modules"] == {n: item["row"] for n, item in inherited.items()},
            "Partial manifest changed an authenticated row")
    require(tuple(partial[k] for k in ORIGIN_KEYS) ==
            (REPOSITORY, PRODUCER_RUN, PRODUCER_JOB, PRODUCER_COMMIT,
             PRODUCER_ARTIFACT, PRODUCER_ARTIFACT_SHA), "Changed partial original producer")
    require(partial["origin_context"] == dict(
        scope="INDIVIDUAL_COMPLETED_KERNEL_EXPORTS_ONLY", whole_job_conclusion="cancelled",
        completed_endpoint_receipt=False,
        full_original_log_sha256=producer["native_capture_sha256"]["job.log"],
        authenticated_partial_archive_report_sha256=PRODUCER_AUTH_SHA,
        completed_fresh_modules=128, completed_named_axiom_profiles=655),
        "Partial origin context overstates or changes the cancelled job")
    return producer, partial


def fixed_context():
    """Only the imported producer's fixed_context is called; never authenticate()."""
    checker = PRODUCER_CHECKER_PATH.read_bytes()
    require(sha(checker) == PRODUCER_CHECKER_SHA, "Changed fixed producer checker")
    namespace = {"__name__": "_frozen_anchor270_source_context",
                 "__file__": str(PRODUCER_CHECKER_PATH)}
    exec(compile(checker, str(PRODUCER_CHECKER_PATH), "exec"), namespace)
    require(namespace["FIXED"] == PRODUCER_FIXED and namespace["ENDPOINT"] == ENDPOINT
            and namespace["SOURCE_COMMIT"] == SOURCE_COMMIT,
            "Changed producer fixed-context contract")
    core = namespace["fixed_context"]()
    producer, partial = producer_evidence(core, namespace)
    current = bound(CURRENT_INVENTORY_PATH, CURRENT_INVENTORY_SHA)
    require(current["repository"] == REPOSITORY and current["commit"] == SOURCE_COMMIT
            and len(current["files"]) == 16, "Wrong current helper/manifest inventory")
    files = {}
    for row in current["files"]:
        raw = (BASE / "native_evidence/anchor270_candidate/current_origin/source" / row["path"]).read_bytes()
        require(len(raw) == row["bytes"] and sha(raw) == row["sha256"]
                and git_blob(raw) == row["git_blob_sha"], "Changed current bytes: " + row["path"])
        require(row["path"] not in files, "Duplicate current helper/manifest")
        files[row["path"]] = raw
    require(git_blob(files["ci/rg_github_artifacts.py"]) ==
            "0d6b0ca19ca8b1717621559b426a0a7b0b9d9520",
            "Current artifact transport helper was rolled back")
    workflow = (HERE / "patch" / WORKFLOW).read_bytes()
    require(sha(workflow) == WORKFLOW_SHA, "Changed exact candidate workflow")
    require(bound(HERE / "patch" / PLAN_PATH, PLAN_SHA) == EXPECTED_PLAN,
            "Changed exact candidate restore plan")
    manifests = {p: decode(files[p]) for p in [BASE_MANIFEST, *HISTORICAL_PLAN]}
    old_generic = decode((BASE / "historical_origin/source" / OLD_GENERIC).read_bytes())
    require(set(manifests[GENERIC]["modules"]) == set(old_generic["modules"])
            and len(old_generic["modules"]) == 2, "Wrong exact generic recovery replacement")
    for name, row in manifests[GENERIC]["modules"].items():
        old_row = old_generic["modules"][name]
        require(row["source_sha256"] == old_row["source_sha256"]
                and row["source_closure_sha256"] == old_row["source_closure_sha256"],
                "Generic recovery changed the original source or dependency closure")
    require(tuple(manifests[GENERIC][k] for k in ORIGIN_KEYS) ==
            (REPOSITORY, 41805266301, 126490589025,
             "5ab25f374a5d3d73e98725a44698f0b73423245a", 13310650054,
             "dd081deeb80b417e65c5ada699a30cc05eaf30ab2faa07460c091ddce94676d0"),
            "Changed authenticated generic recovery origin")
    for path in [BASE_MANIFEST, *HISTORICAL_PLAN[1:]]:
        require(files[path] == (BASE / "historical_origin/source" / path).read_bytes(),
                "Historical base/control manifest rows changed")
    historical_modules = set().union(*(set(m["modules"]) for m in manifests.values()))
    require(len(historical_modules) == 361, "Wrong restored base/control scope")
    manifests[PARTIAL_MANIFEST] = partial
    expected_priors = {}
    for path, manifest in manifests.items():
        require(manifest["repository"] == REPOSITORY and manifest["mathlib"] == PIN
                and manifest["lean_version"] == "4.33.1", "Wrong prerequisite pin")
        for name, row in manifest["modules"].items():
            require(name not in expected_priors and row["module"] == name
                    and row["axiom_profiles"] and all(set(p) <= ALLOWED for p in row["axiom_profiles"])
                    and not row.get("additional_outputs"), "Invalid original prior selection")
            if path == BASE_MANIFEST:
                require(row["mode"] in {"FRESH_KERNEL_EXPORT", "PRIOR_VERIFIED_JOB_EXPORT"},
                        "Invalid complete capsule mode")
                old_origin = row["origin"] if row["mode"] == "PRIOR_VERIFIED_JOB_EXPORT" else origin(manifest)
                expected_priors[name] = dict(row, mode="PRIOR_VERIFIED_JOB_EXPORT", origin=old_origin,
                    transport_capsule={k: manifest[k] for k in ORIGIN_KEYS if k != "repository"})
            else:
                require(row["mode"] == "FRESH_KERNEL_EXPORT", "Prior is not an original fresh export")
                expected_priors[name] = dict(row, mode="PRIOR_VERIFIED_JOB_EXPORT", origin=origin(manifest))
    sources, graph = core["sources"], core["graph"]
    prior = set(sources) & set(expected_priors)
    fresh = set(sources) - prior
    inherited = producer["modules"]
    historical_prior = set(sources) & historical_modules
    require(len(expected_priors) == 489 and len(prior) == 246 and len(fresh) == 35
            and historical_prior == core["prior"] and len(historical_prior) == 118
            and not set(inherited) & historical_modules
            and prior == historical_prior | set(inherited)
            and fresh == core["remaining"], "Wrong 281 = 118 + 128 + 35 partition")
    for name in prior:
        row = expected_priors[name]
        require(row["source_sha256"] == graph["source_sha256"][name]
                and row["source_closure_sha256"] == graph["source_closure_sha256"][name],
                "Stale required prior: " + name)
    original_names = core["names"]
    for name, item in inherited.items():
        row = item["row"]
        require(row["module"] == name and row["mode"] == "FRESH_KERNEL_EXPORT"
                and "origin" not in row and "transport_capsule" not in row
                and not row.get("additional_outputs"), "Relabelled original producer export")
        require([p["declaration"] for p in item["named_axiom_profiles"]] == original_names[name]
                and all(set(p["axioms"]) <= ALLOWED for p in item["named_axiom_profiles"]),
                "Changed inherited ordered named profiles")
        require(len(item["named_axiom_profiles"]) == len(row["axiom_profiles"]),
                "Changed inherited profile occurrence count")
        require(set(graph["source_dependencies"][name]) <= prior,
                "Inherited producer prefix does not close over current priors")
    names = {n: original_names[n] for n in fresh}
    require(sum(len(item["named_axiom_profiles"]) for item in inherited.values()) == 655
            and sum(map(len, names.values())) == 183
            and sum(map(len, original_names.values())) == 838,
            "Wrong inherited 655 plus new 183 named profile partition")
    return dict(graph=graph, sources=sources, without_comments=core["without_comments"],
        prior=prior, fresh=fresh, expected_priors=expected_priors, names=names,
        workflow=workflow.decode(), historical_prior=historical_prior,
        original_fresh=core["original_fresh"], original_names=original_names,
        inherited=inherited, producer=producer,
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
        require(manifest["endpoint"] == ENDPOINT and manifest["anchor_index"] == 270 and
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
                    "Incomplete 489 prior + 35 fresh diagnostics")
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
                    "Receipt is not exact 246 prior + 35 fresh")
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
            require(result["actual_named_axiom_profiles"] == 183 and inherited_count == 655
                    and combined_count == 838 and set(combined_checks) == ctx["original_fresh"],
                    "Incomplete ordered original profile audit: inherited 655 plus new 183 must cover all 838")
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
                endpoint=ENDPOINT, required_modules=281, verified_prior_objects=246,
                max_fresh=35, within_bound=True, proof_status="NOT_PROVEN_BY_RESTORE",
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
    report["status"] = ("ACTUAL_ORIGINAL_ANCHOR270_CONTINUATION_KERNEL_CLOSURE_AUTHENTICATED" if successful else
                        "ACTUAL_TERMINAL_FAILURE_PARTIAL_ARCHIVE_EVIDENCE_AUTHENTICATED")
    report["anchor270_certificate_claim"] = successful
    report["full_original_endpoint_success_authenticated"] = successful
    return 0 if successful else 3


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binding", type=pathlib.Path, default=HERE / "continuation_binding.json")
    parser.add_argument("--check-fixed-inputs-only", action="store_true")
    args = parser.parse_args()
    try:
        configure_binding(args.binding, require_native=not args.check_fixed_inputs_only)
    except Exception as error:
        print(json.dumps(dict(status="UNBOUND_CONTINUATION_ACTUAL_EVIDENCE_NOT_READ",
            error=f"{type(error).__name__}: {error}", actual_evidence_read=False,
            actual_result_report_written=False, anchor270_certificate_claim=False,
            full_degree_one_middle_family_claim=False, global_rg_claim=False),
            indent=2, sort_keys=True))
        return 2
    try:
        ctx = fixed_context()
    except Exception as error:
        print(json.dumps(dict(status="FIXED_CONTINUATION_INPUTS_REJECTED_BEFORE_ACTUAL_READ",
            error=f"{type(error).__name__}: {error}", actual_evidence_read=False,
            actual_result_report_written=False, anchor270_certificate_claim=False,
            full_degree_one_middle_family_claim=False, global_rg_claim=False),
            indent=2, sort_keys=True))
        return 2
    if args.check_fixed_inputs_only:
        print(json.dumps(dict(status="FIXED_REAL_SOURCE_AND_PLAN_METADATA_VALIDATED_ONLY",
            required_modules=281, matching_prior_modules=246, expected_fresh_modules=35,
            original_named_axiom_profiles=838, inherited_named_axiom_profiles=655,
            expected_new_named_axiom_profiles=183, diagnostic_prior_rows=489,
            expected_full_success_archive_members=len(expected_complete_archive_members(ctx)),
            binding_sha256=BINDING_SHA, producer_checker_sha256=PRODUCER_CHECKER_SHA,
            kernel_run_performed=False, old_archive_opened=False, new_actual_evidence_read=False,
            actual_result_report_written=False), sort_keys=True))
        return 0
    require_actual_binding()
    target = ACTUAL / "anchor270_continuation_authentication.json"
    if target.exists():
        print(json.dumps(dict(status="EXISTING_ACTUAL_REPORT_NOT_OVERWRITTEN",
            report=str(target), actual_result_report_written=False)))
        return 2
    report = dict(status="EVIDENCE_INCOMPLETE_OR_REJECTED", repository=REPOSITORY,
        run=RUN, job=JOB, run_attempt=ATTEMPT, source_commit=COMMIT, branch=BRANCH,
        workflow=WORKFLOW, workflow_sha256=WORKFLOW_SHA, restore_plan_sha256=PLAN_SHA,
        partial_prior_manifest_sha256=PARTIAL_MANIFEST_SHA,
        external_fixed_binding_sha256=BINDING_SHA, external_fixed_binding=BINDING,
        producer_partial_authentication_report_sha256=PRODUCER_AUTH_SHA,
        producer_source_context_checker_sha256=PRODUCER_CHECKER_SHA,
        reviewed_original_source_identity_commit=SOURCE_COMMIT,
        current_original_source_graph_sha256=PRODUCER_FIXED["anchor270_scope/anchor270_source_graph.json"],
        authenticator_sha256=file_sha(pathlib.Path(__file__)),
        native_identity_authenticated=False, full_original_endpoint_success_authenticated=False,
        anchor270_certificate_claim=False, full_degree_one_middle_family_claim=False,
        full_degree_one_large_family_claim=False, global_rg_claim=False,
        production_receipt_created_by_authenticator=False, proof_rows_synthesized=False,
        family_count_change_from_this_anchor_run=0,
        total_original_families_remaining_after_separate_large_completion=3,
        expected_scope=dict(required_modules=281, prior_modules=246, fresh_modules=35,
                            original_named_axiom_profiles=838, inherited_named_axiom_profiles=655,
                            new_named_axiom_profiles=183, diagnostic_prior_rows=489,
                            workers=1, module_timeout_seconds=600,
                            memory_reserve_mib=2048, job_timeout_minutes=360),
        interpretation_limits=[
            "Anchor270 alone does not complete degreeOneMiddle or the RG theorem.",
            "Prior object bytes are checked by the fixed native restorers and verifier; "
            "this fresh-only ZIP does not re-export those 246 prior objects.",
            "The cancelled producer 128 rows and 655 ordered named checks remain bound "
            "to its frozen authenticated report and original producer.",
            "Only fixed_context() is called in the hash-bound producer checker; "
            "its authenticate() and its historical ZIP are not used.",
            "Per-module seconds include export hashing/bookkeeping; the 600-second Lean "
            "subprocess timeout is bound by unchanged workflow/verifier and native invocation.",
            "Failure observations and partial exports do not replace a successful full receipt."])
    report["fixed_input_sha256"] = FIXED
    report["preserved_prerequisite_origins"] = ctx["manifest_origins"]
    report["inherited_completed_producer_modules"] = ctx["inherited"]
    report["inherited_producer_identity"] = dict(repository=REPOSITORY, run=PRODUCER_RUN,
        job=PRODUCER_JOB, source_commit=PRODUCER_COMMIT, artifact_id=PRODUCER_ARTIFACT,
        artifact_sha256=PRODUCER_ARTIFACT_SHA, whole_job_conclusion="cancelled",
        completed_endpoint_receipt=False, authenticated_report_sha256=PRODUCER_AUTH_SHA)
    try:
        code = authenticate(ctx, report)
    except Exception as error:
        report["error"] = f"{type(error).__name__}: {error}"
        report["status"] = ("ACTUAL_TERMINAL_FAILURE_EVIDENCE_INCOMPLETE_OR_REJECTED"
                            if report.get("native_job_conclusion") in {"failure", "cancelled", "timed_out"}
                            else "EVIDENCE_INCOMPLETE_OR_REJECTED")
        report["anchor270_certificate_claim"] = False
        report["full_original_endpoint_success_authenticated"] = False
        code = 2
    report["native_capture_sha256"] = {name: file_sha(ACTUAL / name) for name in
        ("run.json", "jobs.json", "artifacts.json", "job.log") if (ACTUAL / name).is_file()}
    ACTUAL.mkdir(parents=True, exist_ok=True)
    raw = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode()
    pending = target.with_suffix(".json.pending")
    with pending.open("xb") as stream:
        stream.write(raw)
    require(not target.exists(), "Do not overwrite a completed actual authentication report")
    pending.replace(target)
    print(json.dumps({k: v for k, v in report.items() if k not in
                     {"archive_audit", "inherited_completed_producer_modules",
                      "preserved_prerequisite_origins", "fixed_input_sha256"}},
                     indent=2, sort_keys=True))
    print("LOCAL_AUTHENTICATION_REPORT " + str(target))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
