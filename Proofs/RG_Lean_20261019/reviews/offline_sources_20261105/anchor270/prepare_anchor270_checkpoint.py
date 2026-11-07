#!/usr/bin/env python3
"""Package authenticated original Anchor270 exports and bounded continuation.

Only local source/report packaging; no ZIP reads, proof runs or network calls.
"""
from pathlib import Path
import hashlib
import json

BASE = Path(__file__).resolve().parent
PATCH = BASE / 'anchor270_publication/patch'
RG = 'Proofs/RG_Lean_20261019/'
REV = RG + 'reviews/'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def put(path, raw):
    target = PATCH / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(raw)


def put_json(path, value):
    put(path, (json.dumps(value, indent=2, sort_keys=True) + '\n').encode())


def main():
    report_path = BASE / 'anchor270_producer/actual/original_anchor270_partial_authentication.json'
    raw = report_path.read_bytes()
    assert sha(raw) == 'fed1b82a66e787b2b63a0fb81bdaf81dd819e44967fb639a4a411ca45f6e147f'
    report = json.loads(raw)
    assert report['status'] == 'ACTUAL_CANCELLED_ORIGINAL_ANCHOR270_PARTIAL_EXPORTS_AUTHENTICATED'
    candidate = BASE / 'native_evidence/anchor270_candidate/patch'
    runtime = [
        ('.github/workflows/rg-middle-anchor270-partial-resume-20261105.yml',
         'cc322b35c1b68a4c16f583c4fa2023ef99746b27997e5dbae9b76d8d252325aa'),
        ('ci/rg_middle_anchor270_partial_resume_restore_plan_20261105.json',
         'e9c9ef349a347bbaa84945cb020bc8e6226fe7a8923d9f1ec7394485aff9a955'),
        ('ci/rg_middle_anchor270_run40714530693_partial_prior_exports.json',
         '52b6336b8e6e4f4a9b3a74ce1b47fc782dd5a2224124c824a7486cb9f6e8deb8'),
    ]
    for path, digest in runtime:
        value = (candidate / path).read_bytes()
        assert sha(value) == digest
        put(path, value)
    manifest = json.loads((candidate / runtime[-1][0]).read_bytes())
    assert len(manifest['modules']) == 128
    assert manifest['modules'] == {n: r['row'] for n, r in report['modules'].items()}
    put(REV + '20261105-anchor270-original-partial-authentication.json', raw)
    copies = {
        'anchor270_producer/authenticate_original_anchor270_partial.py':
            'offline_sources_20261105/anchor270/authenticate_original_anchor270_partial.py',
        'anchor270_producer/checker_derivation.json': '20261105-anchor270-partial-checker-derivation.json',
        'anchor270_scope/anchor270_partial_authenticator_independent_review.json':
            '20261105-anchor270-partial-authenticator-independent-review.json',
        'anchor270_scope/anchor270_independent_publication_review.json':
            '20261105-anchor270-bounded-candidate-independent-review.json',
        'anchor270_scope/anchor270_source_graph.json': '20261105-anchor270-source-graph.json',
        'anchor270_scope/anchor270_source_inventory.json': '20261105-anchor270-source-inventory.json',
        'anchor270_scope/source_tree_identity_bridge.json': '20261105-anchor270-source-tree-identity.json',
        'anchor270_scope/source_scope_report.json': '20261105-anchor270-source-scope-review.json',
        'anchor270_scope/anchor270_native_log_source_match.json': '20261105-anchor270-native-log-source-match.json',
        'anchor270_scope/anchor270_remaining_source_profile_requirements.json':
            '20261105-anchor270-remaining-source-profile-requirements.json',
        'historical_origin/source_inventory.json': '20261105-anchor270-historical-helper-inventory.json',
        'historical_origin/source_capture.json': 'offline_sources_20261105/anchor270/historical_source_capture.json',
        'historical_origin/anchor270_restore_plan_capture.json': '20261105-anchor270-historical-plan-capture.json',
        'native_evidence/remaining_seven_native_evidence_map.json': '20261105-middle-remaining-seven-native-evidence.json',
        'prepare_anchor270_checkpoint.py': 'offline_sources_20261105/anchor270/prepare_anchor270_checkpoint.py',
    }
    for source, destination in copies.items():
        put(REV + destination, (BASE / source).read_bytes())
    for name in ('run.json', 'jobs.json', 'artifacts.json', 'job.log'):
        value = (BASE / 'anchor270_producer/actual' / name).read_bytes()
        assert sha(value) == report['native_capture_sha256'][name]
        put(REV + 'native_20261105/anchor270_producer/' + name, value)
    inventory = json.loads((BASE / 'anchor270_scope/anchor270_source_inventory.json').read_bytes())
    source_rows = []
    for name, row in sorted(inventory['modules'].items()):
        value = (BASE / 'anchor270_scope/source' / row['path']).read_bytes()
        assert sha(value) == row['source_sha256']
        assert hashlib.sha1(b'blob ' + str(len(value)).encode() + b'\0' + value).hexdigest() == row['git_blob_sha']
        source_rows.append(dict(module=name, path=row['path'], content=value.decode(),
            source_sha256=row['source_sha256'], git_blob_sha=row['git_blob_sha']))
    put_json(REV + 'offline_sources_20261105/anchor270/current_source_capture.json', dict(
        kind='EXACT_CURRENT_ORIGINAL_SOURCE_BYTES', repository=report['repository'],
        commit=report['current_source_identity_commit'], endpoint=report['endpoint'],
        modules=281, sources=source_rows, proof_execution_performed_by_packager=False))
    scope = dict(kind='ORIGINAL_ANCHOR270_CONTINUATION_AFTER_ACTUAL_PARTIAL_AUTHENTICATION',
        repository=report['repository'], source_identity_commit=report['current_source_identity_commit'],
        endpoint=report['endpoint'], source_sha256=report['endpoint_source_sha256'],
        source_closure_sha256=report['endpoint_source_closure_sha256'],
        required_modules=281, original_prior_modules=118, authenticated_partial_modules=128,
        predicted_required_prior_modules=246, predicted_fresh_modules=35,
        all_diagnostic_prior_modules=489, predicted_complete_diagnostic_modules=524,
        inherited_anchor_named_axiom_profiles=655, fresh_anchor_named_axiom_profiles=183,
        original_anchor_named_axiom_profiles=838, expected_full_success_archive_members=390,
        producer_report_sha256=sha(raw), partial_manifest_sha256=runtime[-1][1],
        producer_origin={k: manifest[k] for k in ('repository','run','job','source_commit','artifact_id','artifact_sha256')},
        original_producer_job_conclusion='cancelled', original_producer_endpoint_receipt=False,
        remaining_module_names=report['remaining_module_names'],
        guards=dict(module_timeout_seconds=600, workers=1, reserve_mib=2048, job_timeout_minutes=360),
        imports_no_anchor029_or_anchor030=True,
        complete_anchor270_claim=False, complete_middle_family_claim=False,
        remaining_original_families=3, global_rg_claim=False,
        new_continuation_actual_kernel_run_performed_by_packager=False,
        actual_continuation_preflight_not_yet_observed=True)
    put_json(REV + '20261105-anchor270-continuation-scope.json', scope)
    readme = (BASE.parent / 'middle_next/bound_checkpoint/patch' / RG / 'README.md').read_bytes().decode()
    marker = '## Original Anchor030 continuation — 5 November 2026\n'
    assert readme.count(marker) == 1
    section = '''## Original Anchor270 continuation — 5 November 2026

The next independent original target is `MiddleOriginalAnchorCertificate270.certificate`.
Its original anchor is `n = 52`, `p = 0`, `q = 46`, with lower bound
`3138901717630130452352892712856689 / 32624163332060752803334972325527552`.
All 281 current source files are pinned at `5aed41513a76d7d22be5087091e796587353bbf5`;
their recursive closure contains no Anchor029 or Anchor030 module.

The [actual historical producer](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/40714530693/job/122908481481)
ended cancelled after six hours. Its original archive `12891755528` has now
passed complete root authentication: **128 completed kernel exports, 655 exact
ordered named standard-axiom profiles and 18,129,448 bytes of compiled objects**.
All 281 original source bytes and recursive dependency hashes match the current
target. The [partial authentication report](reviews/20261105-anchor270-original-partial-authentication.json)
has SHA-256 `fed1b82a66e787b2b63a0fb81bdaf81dd819e44967fb639a4a411ca45f6e147f`.
The manifest preserves the real cancelled job as the origin of these individual
completed exports. That historical job did not complete the Anchor270 endpoint.

The bounded continuation uses **118 shared prerequisites + 128 authenticated
partial exports + 35 mandatory fresh modules = 281 modules**. The remaining
modules are Cells106–133, Batches010–013, FinitePayment, OriginalAnchor and
Certificate270; they contain 183 new named axiom checks. The unchanged job
limits are 600 seconds per module, one worker, 2048 MiB reserve and 360 minutes.
The separate source graph permits this single-endpoint job to run independently
of the existing Anchor030 job on its own runner.

This checkpoint prepares the Anchor270 run; a new complete receipt is still
required. The three original families `degreeOneMiddle`, `degreeTwoThree` and
`degreeFourToFortyfive` remain open. The [remaining-seven evidence map](reviews/20261105-middle-remaining-seven-native-evidence.json)
records historical prefixes and available archives for subsequent original
anchors. Only this Anchor270 prefix has been object-authenticated in this step;
the other six native-log counts are not current object or endpoint proof claims.

'''
    put(RG + 'README.md', readme.replace(marker, section + marker).encode())
    rows = []
    for p in sorted(p for p in PATCH.rglob('*') if p.is_file()):
        value = p.read_bytes()
        rows.append(dict(path=str(p.relative_to(PATCH)), bytes=len(value), sha256=sha(value),
            git_blob_sha=hashlib.sha1(b'blob ' + str(len(value)).encode() + b'\0' + value).hexdigest()))
    result = dict(repository='RhudeJJJJ/formal-conjectures',
        parent_commit='5aed41513a76d7d22be5087091e796587353bbf5',
        branch='rg-middle-anchor270-partial-resume-20261105',
        runtime_files=[path for path, _ in runtime], original_lean_sources_modified=False,
        file_count=len(rows), total_bytes=sum(r['bytes'] for r in rows), files=rows)
    (BASE / 'anchor270_publication/inventory.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('branch','file_count','total_bytes','original_lean_sources_modified')}))


if __name__ == '__main__':
    main()
