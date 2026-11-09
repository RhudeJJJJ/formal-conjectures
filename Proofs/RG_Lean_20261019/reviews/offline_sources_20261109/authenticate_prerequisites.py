#!/usr/bin/env python3
"""Independently authenticate original finite-residual prerequisite exports.

This is a post-run byte and provenance audit, not a new Lean kernel run or a
pre-run frozen authenticator. It never creates or rewrites a kernel receipt.
"""
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import zipfile

import argparse
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--component", choices=["core", "prerequisites"], required=True)
component = parser.parse_args().component
CONFIG = {
 "core": dict(run=42345977030, job=128323686026, artifact=13563667766, head="38d23137efc0e946ab67bb31020c14bb59db546f", branch="rg-middle-residual-core-coverage-recovery-20261107", endpoint="Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage", source_count=40, fresh_count=2, prior_total=201, prior_required=38, named_profiles=3, diagnostic_total=203, members=50, zip_bytes=2305637, digest="c3fd2c892fbeb2ae11846df6a406acdcfa928cb9a68f3a5a3f4bcc44e713f618", plan="ci/rg_middle_residual_core_coverage_recovery_restore_plan_20261107.json", component_kind="DEGREE_ONE_MIDDLE_RESIDUAL_FINITE_CORE_COVERAGE", manifests=["ci/rg_middle_residual_list_assembly_run42345489172_prior_exports.json"]),
 "prerequisites": dict(run=42346733540, job=128326007614, artifact=13564132816, head="a5fd179b1e8bc17776a7f6d8e9e9abc652d55f55", branch="rg-middle-residual-prerequisites-recovery-20261107", endpoint="Proofs.RadenkovicGutmanDegreeOneMiddleResidualFinitePrerequisites", source_count=259, fresh_count=117, prior_total=709, prior_required=142, named_profiles=119, diagnostic_total=826, members=614, zip_bytes=2514457, digest="21d595a8f449d7d2f5ec37fb33e50ad808ccea00a06e24a2c069da81a4bc619a", plan="ci/rg_middle_residual_prerequisites_recovery_restore_plan_20261107.json", component_kind="DEGREE_ONE_MIDDLE_RESIDUAL_FINITE_PREREQUISITES", manifests=["ci/rg_all111_finite_original_projected_parents_20261028/083.json", "ci/rg_middle_residual_list_assembly_run42345489172_prior_exports.json", "ci/rg_middle_residual_core_coverage_run42345977030_prior_exports.json"]),
}
cfg = CONFIG[component]
REPO = Path("/workspace/scratch/c269711f9401/rg-work")
ACTUAL = Path("/workspace/scratch/c269711f9401/rg-audit") / component
REF = "15d45e8d3ed3bacaf3afe7d85488a42f08302d76"
ENDPOINT = cfg["endpoint"]
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
LC = "621a43d7cf21f87872392a01e874f2f1dbddc926"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PREFIX = "Proofs/RG_Lean_20261019/"
RUN, JOB, ARTIFACT = cfg["run"], cfg["job"], cfg["artifact"]
EXPECTED_ZIP_SHA256 = cfg["digest"]
NAMED = re.compile(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", re.S)

def require(ok, why):
    if not ok:
        raise ValueError(why)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def pairs(items):
    result = {}
    for k, v in items:
        require(k not in result, "Duplicate JSON key: " + k)
        result[k] = v
    return result

def decode(raw):
    return json.loads(raw, object_pairs_hook=pairs)

def read(path):
    return decode(path.read_bytes())

def git(path):
    return subprocess.check_output(["git", "show", cfg["head"] + ":" + path], cwd=REPO)

def original_git(path):
    return subprocess.check_output(["git", "show", REF + ":" + path], cwd=REPO)

def table(rows):
    if isinstance(rows, dict):
        require(all(k == r["module"] for k, r in rows.items()), "Invalid module keys")
        return rows
    out = {}
    for row in rows:
        require(row["module"] not in out, "Duplicate row")
        out[row["module"]] = row
    return out

def payloads(log, prefix):
    out = []
    for line in log.splitlines():
        line = re.sub(r"^\d{4}-\d\d-\d\dT\S+\s", "", line)
        line = re.sub(r"\x1b\[[0-9;]*m", "", line)
        if line.startswith(prefix):
            out.append(decode(line[len(prefix):]))
    return out

# Read the original parser from the exact fixed Git commit, rather than trust
# a possibly edited working copy.
parser_source = git(PREFIX + "verify.py").decode()
parser_ns = {"__name__": "fixed_verify_parser", "__file__": str(REPO / PREFIX / "verify.py")}
exec(compile(parser_source, str(REPO / PREFIX / "verify.py"), "exec"), parser_ns)
without_comments = parser_ns["without_comments"]

raw_sources, hashes, deps, closures, named_expected = {}, {}, {}, {}, {}
def visit(name):
    if name in raw_sources:
        return
    require(name.startswith("Proofs."), "Unexpected local import " + name)
    raw = git(PREFIX + name.replace(".", "/") + ".lean")
    require(raw == original_git(PREFIX + name.replace(".", "/") + ".lean"), "Producer source differs from original 15d45 basis: " + name)
    code = without_comments(raw.decode())
    require(not re.search(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", code, re.M),
            "Admission or unchecked native proof: " + name)
    raw_sources[name] = raw
    hashes[name] = sha(raw)
    deps[name] = sorted(set(re.findall(r"^\s*(?:public\s+)?import\s+((?:Proofs|LeanCert)\.[\w.]+)\s*$", code, re.M)))
    for dep in deps[name]:
        visit(dep)

def closure(name):
    if name not in closures:
        closures[name] = sha(json.dumps([name, hashes[name], PIN, LC,
            [(d, closure(d)) for d in deps[name]]], separators=(",", ":")).encode())
    return closures[name]

visit(ENDPOINT)
for name in raw_sources:
    closure(name)
required = set(raw_sources)
require(len(required) == cfg["source_count"], "Changed source frontier")

plan_rel = cfg["plan"]
plan = decode(git(plan_rel))
require(plan == cfg["manifests"], "Changed restore plan")

base_rel = "ci/rg_reusable_analytic_kernel_base_complete_scope_capsule.json"
base = decode(git(base_rel))
require(base["kind"] == "INDEPENDENTLY_AUDITED_COMPLETE_SCOPE_CAPSULE", "Wrong base kind")
priors = {}
origin_fields = ["repository", "run", "job", "source_commit", "artifact_id", "artifact_sha256"]
for name, row in base["modules"].items():
    origin = row["origin"] if row["mode"] == "PRIOR_VERIFIED_JOB_EXPORT" else {k: base[k] for k in origin_fields}
    priors[name] = {**row, "mode": "PRIOR_VERIFIED_JOB_EXPORT", "origin": origin,
        "transport_capsule": {k: base[k] for k in origin_fields if k != "repository"}}
for rel in plan:
    manifest = decode(git(rel))
    require(manifest["mathlib"] == PIN and manifest["lean_version"] == "4.33.1", "Wrong prior pin")
    for name, row in manifest["modules"].items():
        require(row["module"] == name and row["mode"] == "FRESH_KERNEL_EXPORT", "Invalid source prior")
        origin = {k: manifest[k] for k in origin_fields}
        if "origin_context" in manifest:
            origin["context"] = manifest["origin_context"]
        priors[name] = {**row, "mode": "PRIOR_VERIFIED_JOB_EXPORT", "origin": origin}
fresh = required - set(priors)
require(len(priors) == cfg["prior_total"] and len(required & set(priors)) == cfg["prior_required"] and len(fresh) == cfg["fresh_count"],
        "Wrong prior/fresh frontier")
# Only fresh module logs are exported by this job. Their full ordered named
# diagnostics must be established from their fixed sources. Prior source files
# still have exact byte/closure checks, and their recorded profiles and origins
# remain unchanged; an inherited source need not have a single namespace.
for name in sorted(fresh):
    code = without_comments(raw_sources[name].decode())
    ns = re.findall(r"^namespace ([\w.]+)\s*$", code, re.M)
    cmds = re.findall(r"^#print axioms ([\w.]+)\s*$", code, re.M)
    require(len(ns) <= 1, "Nontrivial fresh namespace requires explicit review: " + name)
    names = []
    for n in cmds:
        if n.startswith("Gebendorfer."):
            names.append(n)
        else:
            require(bool(ns), "Unqualified print without namespace: " + name)
            names.append(ns[0] + "." + n)
    named_expected[name] = names


run, jobs, catalog = [read(ACTUAL / (f + ".json")) for f in ("run", "jobs", "artifacts")]
require(run["id"] == RUN and run["run_attempt"] == 1, "Wrong run/attempt")
require(run["repository"]["full_name"] == "RhudeJJJJ/formal-conjectures", "Wrong repository")
require(run["head_sha"] == cfg["head"] and run["head_branch"] == cfg["branch"], "Wrong run source")
require(run["event"] == "push" and run["path"] == ".github/workflows/" + cfg["branch"] + ".yml", "Wrong workflow")
require(jobs["total_count"] == len(jobs["jobs"]) == 1, "Wrong jobs")
job = jobs["jobs"][0]
require(job["id"] == JOB and job["run_id"] == RUN and job["run_attempt"] == 1, "Wrong job")
require(job["head_sha"] == cfg["head"] and job["head_branch"] == run["head_branch"], "Wrong job source")
require(run["status"] == job["status"] == "completed" and run["conclusion"] == job["conclusion"] == "success", "Unsuccessful native result")
require(job["completed_at"] and all(s["conclusion"] == "success" for s in job["steps"]), "Unsuccessful step")
require(catalog["total_count"] == len(catalog["artifacts"]) == 1, "Wrong artifacts")
meta = catalog["artifacts"][0]
require(meta["id"] == ARTIFACT and meta["expired"] is False, "Wrong/unavailable artifact")
require(meta["name"] == cfg["branch"] + "-exports-" + str(RUN) + "-0", "Wrong artifact name")
require(meta["workflow_run"]["id"] == RUN and meta["workflow_run"]["head_sha"] == cfg["head"], "Wrong artifact origin")
archive_path = ACTUAL / "artifact.zip"
require(archive_path.stat().st_size == meta["size_in_bytes"] == cfg["zip_bytes"], "Wrong zip length")
with archive_path.open("rb") as stream:
    require(hashlib.file_digest(stream, "sha256").hexdigest() == meta["digest"].removeprefix("sha256:") == EXPECTED_ZIP_SHA256, "Wrong zip hash")
log = (ACTUAL / "job.log").read_text()
require(EXPECTED_ZIP_SHA256 in log and str(ARTIFACT) in log, "Artifact upload missing")
logged = table(payloads(log, "COMPLETED_MODULE_JSON "))
require(set(logged) == fresh, "Fresh native log scope mismatch")
checks = {}
with zipfile.ZipFile(archive_path) as z:
    source_members = {"generated_source/" + PREFIX + n.replace(".", "/") + ".lean": n for n in required}
    expected = set(source_members) | {"generated_source/generated_source_manifest.json", "diagnostics_records.json", "resource_observer.json", "receipt.json"}
    for name in fresh:
        expected.update([name.replace(".", "/") + ".olean", name + ".json", name + ".log"])
    names = z.namelist()
    require(len(names) == len(set(names)) == len(expected) == cfg["members"] and set(names) == expected, "Wrong archive scope")
    for name in names:
        p = PurePosixPath(name)
        require(not p.is_absolute() and ".." not in p.parts and "\\" not in name and not z.getinfo(name).is_dir(), "Unsafe archive member")
    for path, name in source_members.items():
        require(z.read(path) == raw_sources[name], "Source differs from immutable commit: " + name)
    manifest = decode(z.read("generated_source/generated_source_manifest.json"))
    require(manifest["endpoint"] == ENDPOINT and manifest["component_kind"] == cfg["component_kind"], "Wrong source scope")
    require(manifest["kind"] == "ORIGINAL_TARGET_REQUIRES_SUCCESSFUL_KERNEL_RECEIPT", "Wrong source kind")
    require(manifest["source_sha256"] == {PREFIX + n.replace(".", "/") + ".lean": hashes[n] for n in required}, "Wrong source manifest")
    diagnostics = table(decode(z.read("diagnostics_records.json"))["modules"])
    require(len(diagnostics) == cfg["diagnostic_total"] and set(diagnostics) == set(priors) | fresh, "Wrong diagnostics scope")
    require(all(diagnostics[n] == row for n, row in priors.items()), "Changed prior rows or origin")
    receipt_raw = z.read("receipt.json")
    receipt = decode(receipt_raw)
    require(receipt["scope"] == "EXPLICIT_EXTENSION_CLOSURE" and receipt["endpoints"] == [ENDPOINT], "Wrong receipt scope")
    require(receipt["mathlib"] == PIN and receipt["leancert"] == LC and "version 4.33.1," in receipt["lean"], "Wrong toolchain")
    require(receipt["global_rg"] == "NOT_PROVED" and receipt["complete_submission"] == "NOT_SUBMITTED", "Overstated receipt")
    rows = table(receipt["modules"])
    require(set(rows) == required and all(rows[n] == diagnostics[n] for n in required), "Receipt mismatch")
    for name, row in rows.items():
        require(row["source_sha256"] == hashes[name] and row["source_closure_sha256"] == closures[name], "Wrong source/closure: " + name)
        require(row["axiom_profiles"] and all(set(p) <= ALLOWED for p in row["axiom_profiles"]), "Unapproved profile")
    for name in sorted(fresh):
        row = rows[name]
        require(row == logged[name] == decode(z.read(name + ".json")), "Fresh row mismatch")
        require(row["mode"] == "FRESH_KERNEL_EXPORT" and "origin" not in row and "transport_capsule" not in row, "Fresh provenance changed")
        require(type(row["seconds"]) in (int, float) and math.isfinite(row["seconds"]) and row["seconds"] >= 0, "Invalid duration")
        require(not row.get("additional_outputs"), "Unretained sidecars")
        obj = name.replace(".", "/") + ".olean"
        with z.open(obj) as stream:
            require(hashlib.file_digest(stream, "sha256").hexdigest() == row["output_sha256"], "Wrong compiled object")
        module_log = z.read(name + ".log").decode()
        require(not re.search(r"\b(error|warning)(?:\([^\n]*?\))?:", module_log), "Module warning/error")
        found = list(NAMED.finditer(module_log))
        require([m[1] for m in found] == named_expected[name], "Named declaration mismatch: " + name)
        profiles = [sorted(set(a.strip() for a in (m[2] or "").split(",") if a.strip())) for m in found]
        require(profiles and all(set(p) <= ALLOWED for p in profiles), "Unapproved named axiom")
        grouped = [p for m, p in zip(found, profiles) if m[2] is not None] + [p for m, p in zip(found, profiles) if m[2] is None]
        require(grouped == row["axiom_profiles"], "Named profiles differ from row")
        checks[name] = {"output_bytes": z.getinfo(obj).file_size, "named_profiles": [{"declaration":m[1],"axioms":p} for m,p in zip(found,profiles)]}
    require(sum(len(v["named_profiles"]) for v in checks.values()) == cfg["named_profiles"], "Wrong named profile total")
    resource = decode(z.read("resource_observer.json"))
    require(payloads(log, "RG_KERNEL_RESOURCE_RESULT ") == [{k:v for k,v in resource.items() if k != "samples"}], "Observer result mismatch")
    require(payloads(log, "RG_KERNEL_RESOURCE_OBSERVATION ") == resource["samples"], "Observer samples mismatch")
    require(resource["status"] == "VERIFIER_COMPLETED" and resource["exit_code"] == 0 and resource["mathlib_and_lean_flags_unchanged"] is True and resource["samples"], "Resource guard incomplete")
    require(not payloads(log, "RG_KERNEL_RESOURCE_GUARD_LOW_MEMORY "), "Memory guard stopped verifier")
    require(all(type(s["available_bytes"]) is int and s["available_bytes"] >= 2048 * 1024**2 for s in resource["samples"] if s["lean_processes"]), "Memory reserve violation")

# A restore manifest contains only genuinely fresh original exports from this job.
restore = {"repository":"RhudeJJJJ/formal-conjectures","run":RUN,"job":JOB,
    "source_commit":cfg["head"],"artifact_id":ARTIFACT,"artifact_sha256":EXPECTED_ZIP_SHA256,
    "lean_version":"4.33.1","mathlib":PIN,"modules":{n:rows[n] for n in sorted(fresh)}}
restore_name = "rg_middle_residual_" + ("core_coverage" if component == "core" else "prerequisites") + "_run" + str(RUN) + "_prior_exports.json"
restore_path = REPO / "ci" / restore_name
restore_path.write_text(json.dumps(restore, indent=2, sort_keys=True) + "\n")
report = {"status":"ACTUAL_ORIGINAL_MIDDLE_RESIDUAL_" + component.upper() + "_AUTHENTICATED",
    "audit_kind":"POST_RUN_INDEPENDENT_BYTE_PROVENANCE_REVIEW",
    "repository":restore["repository"],"run":RUN,"job":JOB,"source_commit":cfg["head"],"original_source_commit":REF,"endpoint":ENDPOINT,
    "artifact":{k:meta[k] for k in ("id","name","size_in_bytes","digest")},
    "archive_members":cfg["members"],"required_modules":cfg["source_count"],"required_prior_modules":cfg["prior_required"],"fresh_modules":cfg["fresh_count"],
    "all_preserved_prior_rows":cfg["prior_total"],"diagnostic_rows":cfg["diagnostic_total"],"named_fresh_axiom_profiles":cfg["named_profiles"],
    "fresh_output_bytes":sum(v["output_bytes"] for v in checks.values()),"resource_seconds":resource["seconds"],
    "receipt_sha256":sha(receipt_raw),"audit_script_sha256":sha(Path(__file__).read_bytes()),
    "restore_manifest_sha256":sha(restore_path.read_bytes()),
    "fixed_input_sha256":{p:sha(git(p)) for p in [base_rel,plan_rel,*plan,PREFIX+"verify.py",PREFIX+"verify_extension.py"]},
    "native_capture_sha256":{p:sha((ACTUAL/p).read_bytes()) for p in ("run.json","jobs.json","artifacts.json","job.log")},
    "source_sha256":hashes,"source_closure_sha256":closures,"fresh_module_checks":checks,
    "scope":"Original generic residual coverage and transfer; no new concrete spectral certificate keys",
    "middle_family_completed":False,"global_rg_proved":False,"remaining_original_families":3,
    "kernel_receipt_created_by_auditor":False,"prior_archives_redownloaded":False}
(ACTUAL / "completion_authentication.json").write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
(REPO / "Proofs/RG_Lean_20261019/reviews" / ("20261109-residual-" + component + "-authentication.json")).write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
print(json.dumps({k:v for k,v in report.items() if k not in ("source_sha256","source_closure_sha256","fresh_module_checks","fixed_input_sha256","native_capture_sha256")},indent=2))

