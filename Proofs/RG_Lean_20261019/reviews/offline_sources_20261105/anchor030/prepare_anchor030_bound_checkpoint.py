#!/usr/bin/env python3
"""Preserve the fixed authenticator and genuinely observed active native job.

This source-only checkpoint does not alter runtime or Lean files, execute an
authenticator, or read a ZIP. The already running workflow remains on its own SHA.
"""
from pathlib import Path
import hashlib
import json

BASE = Path(__file__).resolve().parent
PATCH = BASE / 'bound_checkpoint/patch'
RG = 'Proofs/RG_Lean_20261019/'
REV = RG + 'reviews/'


def put(path, raw):
    p = PATCH / path
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(raw)


def main():
    checker = BASE / 'ci_review/candidate/authenticate_anchor030_continuation.py'
    assert hashlib.sha256(checker.read_bytes()).hexdigest() == 'e1b2d0306494ded22526d78e20e0b7940be2078ed9eaafd7f4879766c8e654cf'
    binding = BASE / 'ci_review/candidate/continuation_binding.json'
    assert hashlib.sha256(binding.read_bytes()).hexdigest() == '3946d265c550efadb154bc913cadf073d4492f2f98a4afa18361735962c015aa'
    values = json.loads(binding.read_bytes())
    assert (values['run'], values['job'], values['attempt'], values['head_sha']) == (
        42052127520, 127330696809, 1, '415f1d8bbc3a065b81adea9ac3b74fd27fc66265')
    files = {
        'ci_review/candidate/authenticate_anchor030_continuation.py':
            'offline_sources_20261105/anchor030/authenticate_anchor030_continuation.py',
        'ci_review/candidate/continuation_binding.json': '20261105-anchor030-fixed-native-binding.json',
        'ci_review/candidate/bound_fixed_input_preflight.json': '20261105-anchor030-bound-fixed-input-preflight.json',
        'ci_review/candidate/authenticator_freeze_review.json': '20261105-anchor030-authenticator-freeze-review.json',
        'source_scope/continuation_checker_readonly_review.json': '20261105-anchor030-completion-checker-independent-review.json',
        'source_scope/bound_native_binding_review.json': '20261105-anchor030-native-binding-independent-review.json',
        'ci_review/candidate/candidate_validation.json': '20261105-anchor030-runtime-candidate-validation.json',
        'ci_review/ci_integration_review.json': '20261105-anchor030-ci-integration-review.json',
        'ci_review/current_origin/source_inventory.json': '20261105-anchor030-current-helper-inventory.json',
        'ci_review/current_origin/source_capture.json': 'offline_sources_20261105/anchor030/current_helper_source_capture.json',
        'publication/independent_publication_review.json': '20261105-anchor030-publication-independent-review.json',
        'publication/inventory.json': '20261105-anchor030-original-publication-inventory.json',
        'publication/published_state.json': '20261105-anchor030-original-publication-readback.json',
        'source_scope/availability/native_catalog_capture.json': 'native_20261105/anchor030_prerequisites/catalogs.json',
        'ci_review/candidate/native_progress/progress.json': '20261105-anchor030-active-native-state.json',
        'ci_review/candidate/native_progress/run.json': 'native_20261105/anchor030_continuation_initial/run.json',
        'ci_review/candidate/native_progress/jobs.json': 'native_20261105/anchor030_continuation_initial/jobs.json',
        'prior_evidence/native/run39999831483.json': 'native_20261105/middle_residual_historical/run.json',
        'prior_evidence/native/run39999831483_jobs.json': 'native_20261105/middle_residual_historical/jobs.json',
        'prior_evidence/native/run39999831483_artifacts.json': 'native_20261105/middle_residual_historical/artifacts.json',
        'prior_evidence/native/run39999831483_job120572732381.log': 'native_20261105/middle_residual_historical/job.log',
        'source_scope/MIDDLE_SOURCE_SCOPE_20261105.md': '20261105-middle-source-scope.md',
        'source_scope/middle_anchor_index.json': '20261105-middle-original-anchor-index.json',
        'prepare_anchor030_bound_checkpoint.py': 'offline_sources_20261105/anchor030/prepare_anchor030_bound_checkpoint.py',
    }
    for source, destination in files.items():
        put(REV + destination, (BASE / source).read_bytes())
    readme = (BASE / 'publication/patch' / RG / 'README.md').read_bytes().decode()
    old = '''This checkpoint prepares the continuation; its complete new kernel receipt is
still required. `degreeOneMiddle`, `degreeTwoThree` and `degreeFourToFortyfive`
remain the three open original families. The current Middle dependency audit
'''
    new = '''The [new native continuation 42052127520](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/42052127520/job/127330696809)
is running as attempt 1 on workflow head `415f1d8bbc3a065b81adea9ac3b74fd27fc66265`.
Both restoration steps and the mandatory frontier preflight succeeded. The
kernel step began on 5 November at **16:11:31 CET**. Its final result, completed
fresh-export count and complete result archive have not yet been observed.
The [native status capture](reviews/20261105-anchor030-active-native-state.json)
records this distinction explicitly.

The [fixed completion authenticator](reviews/offline_sources_20261105/anchor030/authenticate_anchor030_continuation.py),
SHA-256 `e1b2d0306494ded22526d78e20e0b7940be2078ed9eaafd7f4879766c8e654cf`,
is bound to the actual new run and job by the [separate native binding](reviews/20261105-anchor030-fixed-native-binding.json),
SHA-256 `3946d265c550efadb154bc913cadf073d4492f2f98a4afa18361735962c015aa`.
Its fixed-input check and independent review passed. Actual completion mode has
not run; it requires all 72 new exports, 383 new ordered named profiles, the
complete 281-module receipt, the exact 501-member result archive and successful
native/resource completion. This documentation checkpoint does not alter the
running workflow, restore plan, manifests or any Lean source.

The complete new kernel receipt is still required. `degreeOneMiddle`,
`degreeTwoThree` and `degreeFourToFortyfive` remain the three open original
families. The current Middle dependency audit
'''
    assert readme.count(old) == 1
    put(RG + 'README.md', readme.replace(old, new).encode())
    rows = []
    for p in sorted(p for p in PATCH.rglob('*') if p.is_file()):
        raw = p.read_bytes()
        path = str(p.relative_to(PATCH))
        assert path.startswith(RG) and not path.endswith('.lean')
        rows.append(dict(path=path, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest(),
                         git_blob_sha=hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()))
    inventory = dict(repository='RhudeJJJJ/formal-conjectures',
        parent_commit='415f1d8bbc3a065b81adea9ac3b74fd27fc66265',
        branch='rg-middle-anchor030-partial-resume-20261105',
        running_workflow_head='415f1d8bbc3a065b81adea9ac3b74fd27fc66265',
        runtime_files_modified=False, lean_sources_modified=False,
        complete_actual_anchor030_claim=False, remaining_original_families=3,
        file_count=len(rows), total_bytes=sum(r['bytes'] for r in rows), files=rows)
    (BASE / 'bound_checkpoint/inventory.json').write_text(json.dumps(inventory, indent=2) + '\n')
    print(json.dumps({k: inventory[k] for k in ('file_count','total_bytes','runtime_files_modified','lean_sources_modified')}))


if __name__ == '__main__':
    main()
