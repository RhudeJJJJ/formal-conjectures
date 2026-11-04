"""Check the complete current source graph and both fixed numeric splits.

This check compiles no Lean modules and authenticates no proof objects. All
original numeric endpoints remain required. The five split original leaves
retain their declaration bodies, and all other numeric identities stay fixed.
"""
import hashlib
import json
import os
import re
import subprocess

from rg_plan_exact_degree_one_large import ROOT, SOURCES, source_closure
from rg_exact_final_source_binding import (
    BINDING, NUMERIC_SPEC, NUMERIC_ORIGIN, ENDPOINT,
    binding_metadata, prepare_current_sources, validate_current_graph,
)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    spec_raw = (ROOT / BINDING).read_bytes()
    numeric_raw = (ROOT / NUMERIC_SPEC).read_bytes()
    origin_raw = (ROOT / NUMERIC_ORIGIN).read_bytes()
    spec, summary = binding_metadata(spec_raw, numeric_raw, origin_raw)
    prepare_current_sources(spec)
    hashes, dependencies, closures = source_closure(ENDPOINT)
    verified = validate_current_graph(spec, json.loads(numeric_raw), hashes, closures)
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    assert re.fullmatch(r"[0-9a-f]{40}", commit)
    assert os.environ["GITHUB_SHA"] == commit
    assert os.environ["GITHUB_REPOSITORY"] == spec["repository"]
    assert os.environ["GITHUB_REF"] == "refs/heads/rg-degree-one-large-20261103"
    report = dict(
        status="CURRENT_SOURCE_CLOSURE_BOUND_WITH_EXPLICIT_DECLARATION_PRESERVING_REORGANIZATIONS",
        kernel_proof="NOT_CHECKED_BY_THIS_SOURCE_PREFLIGHT",
        compiled_object_coverage="NOT_CHECKED_BY_THIS_SOURCE_PREFLIGHT",
        remaining_original_main_families=4,
        repository=spec["repository"], source_commit=commit,
        workflow_run=int(os.environ["GITHUB_RUN_ID"]),
        workflow_attempt=int(os.environ["GITHUB_RUN_ATTEMPT"]),
        endpoint=ENDPOINT, required_modules=len(hashes),
        current_endpoint_source_sha256=hashes[ENDPOINT],
        current_endpoint_closure_sha256=closures[ENDPOINT],
        binding_spec_sha256=sha(spec_raw),
        original_numeric_origin=json.loads(origin_raw),
        numeric_source_reorganizations=spec["numeric_source_reorganizations"],
        additional_final_current_source_rechecks=summary["additional_final_current_source_rechecks"],
        **verified,
    )
    output = SOURCES / "build/current_final_source_binding"
    output.mkdir(parents=True, exist_ok=True)
    (output / "source_binding_report.json").write_text(json.dumps(report, indent=2) + "\n")
    graph = dict(source_sha256=hashes, source_dependencies=dependencies,
                 source_closure_sha256=closures)
    (output / "actual_current_source_graph.json").write_text(json.dumps(graph, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ("original_numeric_plan_sha256", "original_numeric_origin",
                                   "added_numeric_support_modules")}), flush=True)


if __name__ == "__main__":
    main()
