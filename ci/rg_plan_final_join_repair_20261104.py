"""Plan the exact three-module final repair using four real callback exports.

All original numeric and auxiliary collection gates remain mandatory. This
planner authenticates the fixed failed callback's four completed modules and
requires their exact origins in the restore plan. It establishes no new proof.
"""
import argparse
import hashlib
import json
import pathlib

from rg_plan_exact_degree_one_large import source_closure, matching_archives, plan, FRESH
from rg_exact_final_source_binding import (
    BINDING, NUMERIC_SPEC, ENDPOINT, REPOSITORY, read_binding,
    prepare_current_sources, validate_current_graph,
)
from rg_collect_exact_d1_reproductions import GitHub
from rg_callback_partial_completion import (
    MANIFEST, MANIFEST_SHA, PROOF_SOURCE, PARTIAL, FINAL, origin,
    load_partial_manifest, authenticate_partial, validate_selected_origins,
)

ROOT = pathlib.Path(__file__).resolve().parents[1]
BUILD = ROOT / 'Proofs/RG_Lean_20261019/build'


def reuse_binding():
    """Use a fixed manifest, never a caller-supplied scope or prior origin."""
    load_partial_manifest()
    assert set(FRESH) == FINAL and len(PARTIAL) == 4
    return dict(kind='EXACT_FOUR_CALLBACK_PRIORS_FOR_THREE_FINAL_KERNEL_EXPORTS',
        manifest=MANIFEST, manifest_sha256=MANIFEST_SHA,
        preserved_origin=origin(), proof_source_commit=PROOF_SOURCE,
        partial_modules=sorted(PARTIAL), required_fresh_modules=sorted(FINAL),
        original_failed_job_unchanged=True, partial_objects_relabelled_as_fresh=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=pathlib.Path, required=True)
    args = parser.parse_args()
    numeric_raw = (ROOT / NUMERIC_SPEC).read_bytes()
    numeric = json.loads(numeric_raw)
    binding, summary = read_binding(ROOT / BINDING, numeric_raw)
    prepare_current_sources(binding)
    hashes, dependencies, closures = source_closure(ENDPOINT)
    validate_current_graph(binding, numeric, hashes, closures)
    authenticated = authenticate_partial(GitHub(REPOSITORY), hashes, closures)
    groups = matching_archives(hashes, closures)
    actual = origin()
    fixed = groups[actual['artifact_id']]
    assert all(fixed['archive'][key] == value for key, value in actual.items())
    assert PARTIAL <= fixed['modules'].keys()
    for artifact, group in groups.items():
        if artifact != actual['artifact_id']:
            for name in PARTIAL:
                group['modules'].pop(name, None)
    report = plan(ENDPOINT, hashes, dependencies, closures, groups, fresh_allowlist=FRESH)
    assert not report['missing_original_modules']
    assert report['complete_original_object_coverage'] is True
    assert set(report['fresh_modules']) == set(report['fresh_allowlist']) == FINAL
    validate_selected_origins(report)
    report['current_source_binding'] = summary
    report['final_partial_reuse'] = reuse_binding()
    BUILD.mkdir(parents=True, exist_ok=True)
    audit = BUILD / 'final_partial_authentication.json'
    audit.write_text(json.dumps(authenticated, indent=2) + '\n')
    report['final_partial_authentication_sha256'] = hashlib.sha256(audit.read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: report[key] for key in (
        'endpoint', 'required_modules', 'fresh_modules', 'missing_original_modules',
        'complete_original_object_coverage', 'final_partial_reuse')}), flush=True)


if __name__ == '__main__':
    main()
