#!/usr/bin/env python3
"""Package already authenticated original Anchor030 partial evidence for Git.

No network access, Lean execution, artifact reads or authenticator reruns.
"""
from pathlib import Path
import hashlib
import json
import shutil

BASE = Path(__file__).resolve().parent
PATCH = BASE / 'publication/patch'
RG = 'Proofs/RG_Lean_20261019/'
REVIEWS = RG + 'reviews/'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def put(path, raw):
    target = PATCH / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(raw)


def put_json(path, value):
    put(path, (json.dumps(value, indent=2, sort_keys=True) + '\n').encode())


def main():
    report_path = BASE / 'anchor030_producer/actual/original_anchor030_partial_authentication.json'
    report_raw = report_path.read_bytes()
    assert sha(report_raw) == '5f3f22f25732b46839e311676485b01273768ceb7605145f6c2b13972fb598f9'
    report = json.loads(report_raw)
    assert report['status'] == 'ACTUAL_CANCELLED_ORIGINAL_ANCHOR030_PARTIAL_EXPORTS_AUTHENTICATED'
    candidate = BASE / 'ci_review/candidate/patch'
    runtime = [
        '.github/workflows/rg-middle-anchor030-partial-resume-20261105.yml',
        'ci/rg_middle_anchor030_partial_resume_restore_plan_20261105.json',
        'ci/rg_middle_anchor030_run40714530693_partial_prior_exports.json',
    ]
    pins = [
        'd6e3816fffe802f700768b9064e709b14cc1ab308d6c8b9e2c5ed2267d17dbae',
        'ca10c314768db5bbdddb3620e0665ef4e1766c9e4cd9e8be028365f9bbdf0e82',
        '53cddc2c55109470c7bb061e507404b87b04e9ca1eafd0e6ce2e59135907b5de',
    ]
    for path, digest in zip(runtime, pins):
        raw = (candidate / path).read_bytes()
        assert sha(raw) == digest
        put(path, raw)
    manifest = json.loads((candidate / runtime[-1]).read_bytes())
    assert manifest['modules'] == {n: row['row'] for n, row in report['modules'].items()}
    assert len(manifest['modules']) == 91
    put(REVIEWS + '20261105-anchor030-original-partial-authentication.json', report_raw)
    copies = {
        'anchor030_producer/authenticate_original_anchor030_partial.py':
            'offline_sources_20261105/anchor030/authenticate_original_anchor030_partial.py',
        'prior_evidence/anchor030_partial_authenticator_review.json':
            '20261105-anchor030-partial-authenticator-independent-review.json',
        'source_scope/anchor030_source_graph.json': '20261105-anchor030-source-graph.json',
        'source_scope/anchor030_source_inventory.json': '20261105-anchor030-source-inventory.json',
        'source_scope/source_tree_identity_bridge.json': '20261105-anchor030-source-tree-identity.json',
        'source_scope/source_scope_report.json': '20261105-anchor030-source-scope-review.json',
        'source_scope/middle_assembly_dag.json': '20261105-middle-original-assembly-dag.json',
        'source_scope/anchor030_native_log_source_match.json': '20261105-anchor030-native-log-source-match.json',
        'source_scope/availability/artifact_availability_report.json': '20261105-anchor030-prerequisite-availability.json',
        'source_scope/bounded_candidate_independent_review.json': '20261105-anchor030-bounded-candidate-independent-review.json',
        'ci_review/historical_origin/source_inventory.json': '20261105-anchor030-historical-helper-inventory.json',
        'ci_review/historical_origin/source_capture.json': 'offline_sources_20261105/anchor030/historical_source_capture.json',
        'prior_evidence/middle_prior_evidence_map.json': '20261105-middle-prior-evidence-map.json',
        'prepare_anchor030_checkpoint.py': 'offline_sources_20261105/anchor030/prepare_anchor030_checkpoint.py',
    }
    for source, target in copies.items():
        put(REVIEWS + target, (BASE / source).read_bytes())
    for name in ('run.json', 'jobs.json', 'artifacts.json', 'job.log'):
        raw = (BASE / 'anchor030_producer/actual' / name).read_bytes()
        assert sha(raw) == report['native_capture_sha256'][name]
        put(REVIEWS + 'native_20261105/anchor030_producer/' + name, raw)
    inventory = json.loads((BASE / 'source_scope/anchor030_source_inventory.json').read_bytes())
    sources = []
    for name, row in sorted(inventory['modules'].items()):
        raw = (BASE / 'source_scope/source' / row['path']).read_bytes()
        assert sha(raw) == row['source_sha256']
        assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == row['git_blob_sha']
        sources.append(dict(module=name, path=row['path'], content=raw.decode(),
                            source_sha256=row['source_sha256'], git_blob_sha=row['git_blob_sha']))
    put_json(REVIEWS + 'offline_sources_20261105/anchor030/current_source_capture.json', dict(
        kind='EXACT_CURRENT_SOURCE_BYTES_FOR_OFFLINE_RECONSTRUCTION',
        repository=report['repository'], commit=report['current_source_identity_commit'],
        endpoint=report['endpoint'], modules=281, sources=sources,
        proof_execution_performed_by_packager=False))
    scope = dict(kind='ORIGINAL_ANCHOR030_CONTINUATION_SCOPE_AFTER_ACTUAL_PARTIAL_AUTHENTICATION',
        repository=report['repository'], source_identity_commit=report['current_source_identity_commit'],
        endpoint=report['endpoint'], source_sha256=report['endpoint_source_sha256'],
        source_closure_sha256=report['endpoint_source_closure_sha256'],
        required_modules=281, original_prior_modules=118, authenticated_partial_modules=91,
        predicted_required_prior_modules=209, predicted_fresh_modules=72,
        all_diagnostic_prior_modules=452, predicted_complete_diagnostic_modules=524,
        inherited_anchor_named_axiom_profiles=455, fresh_anchor_named_axiom_profiles=383,
        original_anchor_named_axiom_profiles=838,
        producer_report_sha256=sha(report_raw), partial_manifest_sha256=pins[-1],
        producer_origin={k: manifest[k] for k in ('repository','run','job','source_commit','artifact_id','artifact_sha256')},
        original_producer_job_conclusion='cancelled', original_producer_endpoint_receipt=False,
        remaining_module_names=report['remaining_module_names'],
        guards=dict(module_timeout_seconds=600, workers=1, reserve_mib=2048, job_timeout_minutes=360),
        current_complete_anchor030_claim=False, current_complete_middle_family_claim=False,
        remaining_original_families=3, global_rg_claim=False,
        new_continuation_actual_kernel_run_performed_by_packager=False,
        actual_continuation_preflight_not_yet_observed=True)
    put_json(REVIEWS + '20261105-anchor030-continuation-scope.json', scope)
    original_readme = BASE.parent / 'publication/patch' / RG / 'README.md'
    readme = original_readme.read_bytes().decode()
    marker = '## Verified degree-one large-order family\n'
    assert readme.count(marker) == 1
    section = '''## Original Anchor030 continuation — 5 November 2026

The next bounded original target is `MiddleOriginalAnchorCertificate030.certificate`.
It retains the original anchor `n = 52`, `p = 9`, `q = 39` and lower bound
`3824018983001674635847799415612737 / 32624163332060752803334972325527552`.
The current 281-source closure is fixed at `eec9bfa2996116bb5f83fc2b6d83d015b5786c6b`;
no Lean statement, source proof, payment or integral threshold changes in this continuation.

The actual [historical partial producer](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/40714530693/job/122908481894)
ended cancelled at its six-hour job boundary. Its original archive `12872778035`
has now been authenticated against its complete native metadata and job log:
**91 completed kernel exports, 455 exact named standard-axiom profiles, and
13,233,776 bytes of compiled objects**. All 281 archived source files and recursive
source closures match the current target exactly. The [authentication report](reviews/20261105-anchor030-original-partial-authentication.json)
has SHA-256 `5f3f22f25732b46839e311676485b01273768ceb7605145f6c2b13972fb598f9`.
These individual exports preserve the cancelled original job as their origin;
the historical run did not produce a complete Anchor030 receipt.

The new restore plan combines **118 existing prerequisites + 91 authenticated
partial exports + 72 mandatory fresh modules = 281 required modules**. The fresh
frontier is Cells072–133, Batches007–013, FinitePayment, OriginalAnchor and
Certificate030, with 383 new named axiom checks. The workflow checks only this
original endpoint, using the unchanged 600-second per-module timeout, one worker,
2048 MiB reserve and 360-minute job cap. All six required archive identities were
listed and unexpired in the native catalog check on 5 November.

This checkpoint prepares the continuation; its complete new kernel receipt is
still required. `degreeOneMiddle`, `degreeTwoThree` and `degreeFourToFortyfive`
remain the three open original families. The current Middle dependency audit
separates its 680 analytic anchors, 39 order-coverage modules and 25 residual
finite batches. The historical successful 3,880-module Middle residual join has
a preserved native log, but its seven-day result archive is no longer listed;
that is an evidence-availability issue, not a new mathematical obligation.

'''
    put(RG + 'README.md', readme.replace(marker, section + marker).encode())
    rows = []
    for path in sorted(p for p in PATCH.rglob('*') if p.is_file()):
        raw = path.read_bytes()
        rows.append(dict(path=str(path.relative_to(PATCH)), bytes=len(raw), sha256=sha(raw),
                         git_blob_sha=hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()))
    out = dict(repository='RhudeJJJJ/formal-conjectures',
        parent_commit='eec9bfa2996116bb5f83fc2b6d83d015b5786c6b',
        branch='rg-middle-anchor030-partial-resume-20261105',
        original_proof_sources_modified=False, runtime_files=runtime,
        file_count=len(rows), total_bytes=sum(r['bytes'] for r in rows), files=rows)
    (BASE / 'publication/inventory.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: out[k] for k in ('branch', 'file_count', 'total_bytes', 'original_proof_sources_modified')}))


if __name__ == '__main__':
    main()
