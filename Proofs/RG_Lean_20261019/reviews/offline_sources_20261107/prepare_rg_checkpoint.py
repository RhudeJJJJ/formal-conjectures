#!/usr/bin/env python3
"""Package the actual Anchor030 completion and the bound Anchor270 continuation.

This only copies evidence and builds a fresh-export manifest. It does not run
Lean, create a kernel receipt, or relabel inherited exports as fresh results.
"""
import hashlib
import json
import pathlib
import shutil

WORK = pathlib.Path('/workspace/scratch/9f79fa0e9941')
OLD = pathlib.Path('/workspace/scratch/406169dbc070/rg_resume_20261105')
OUT = WORK / 'checkpoint/patch'
REV = OUT / 'Proofs/RG_Lean_20261019/reviews'
ACTUAL = OLD / 'middle_next/ci_review/candidate/actual'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


def copy(src, dst):
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)


def main():
    report_path = ACTUAL / 'anchor030_continuation_authentication.json'
    assert sha(report_path) == '4548ffb0a0b99c6ceed6bc283a2c4611bd4784fb541c16e36b942b1050d06400'
    report = json.loads(report_path.read_text())
    assert report['status'] == 'ACTUAL_ORIGINAL_ANCHOR030_CONTINUATION_KERNEL_CLOSURE_AUTHENTICATED'
    audit = report['archive_audit']
    assert audit['completed_fresh_count'] == 72 and audit['actual_named_axiom_profiles'] == 383
    assert audit['required_prior_rows_observed'] == 209 and audit['full_original_receipt_validated']
    assert report['full_degree_one_middle_family_claim'] is False and report['global_rg_claim'] is False
    review = WORK / 'anchor030_review/independent_review.json'
    assert sha(review) == 'eb9bd5904bfb4046a5c50795c302945c0afa4007570c54e4e6404a4c3c56aa5e'
    assert json.loads(review.read_text())['endpoint_claim_supported'] is True

    # Retain the already reviewed Anchor270 origin package; runtime files are
    # already in the parent commit and are not changed by this checkpoint.
    prior = OLD / 'middle_followup_1105c/anchor270_publication/patch'
    for src in sorted((prior / 'Proofs/RG_Lean_20261019/reviews').rglob('*')):
        if src.is_file():
            copy(src, OUT / src.relative_to(prior))
    copy(report_path, REV / '20261107-anchor030-complete-authentication.json')
    copy(review, REV / '20261107-anchor030-independent-review.json')
    copy(WORK / 'anchor030_review/fresh_module_byte_checks.json',
         REV / '20261107-anchor030-fresh-module-byte-checks.json')
    copy(WORK / 'anchor030_review/review_actual_anchor030.py',
         REV / 'offline_sources_20261107/review_actual_anchor030.py')
    for name in ('run.json', 'jobs.json', 'artifacts.json', 'job.log'):
        copy(ACTUAL / name, REV / 'native_20261107/anchor030_complete' / name)
    for name in ('continuation_binding_run42345329502.json', 'current_state_20261107.json',
                 'initial_run_jobs_20261107.json', 'artifact_availability_20261107.json'):
        copy(WORK / 'anchor270/native' / name,
             REV / 'native_20261107/anchor270_continuation' / name)
    checker = OLD / 'middle_followup_1105c/native_evidence/anchor270_candidate/authenticate_anchor270_continuation.py'
    copy(checker, REV / 'offline_sources_20261107/authenticate_anchor270_continuation.py')
    copy(WORK / 'anchor270/launch_candidate.json', REV / '20261107-anchor270-launch-validation.json')

    fresh = {name: item['row'] for name, item in audit['modules'].items()}
    assert len(fresh) == 72
    assert all(row['mode'] == 'FRESH_KERNEL_EXPORT' and 'origin' not in row for row in fresh.values())
    manifest = dict(
        repository=report['repository'], run=report['run'], job=report['job'],
        source_commit=report['source_commit'], artifact_id=report['artifact']['id'],
        artifact_sha256=report['artifact']['digest'].removeprefix('sha256:'),
        kind='AUTHENTICATED_FRESH_KERNEL_EXPORTS', lean_version='4.33.1',
        mathlib='0df444a360eaa60ab8c11dca51a86af692955474', modules=fresh,
        origin_context=dict(
            actual_fresh_modules=72, actual_job_conclusion='success', actual_run_conclusion='success',
            authenticated_report_sha256=sha(report_path), complete_endpoint_receipt_present=True,
            kernel_receipt_created_by_this_packager=False,
            manifest_scope='Only actual fresh objects physically exported by this artifact; no prior row relabelled as fresh',
            named_axiom_profiles=383, receipt_sha256=audit['receipt_sha256'],
            run_attempt=1, workflow_event='push'))
    write_json(OUT / 'ci/rg_middle_anchor030_run42052127520_prior_exports.json', manifest)

    residual_base = WORK / 'residual'
    residual_report_path = residual_base / 'actual/completion_authentication.json'
    assert sha(residual_report_path) == '7ecebecdf5005875929208ff8bfb5c80d63bc16b8a964326a2511e8a8cc34034'
    residual_report = json.loads(residual_report_path.read_text())
    assert residual_report['status'] == 'ACTUAL_ORIGINAL_RESIDUAL_LIST_ASSEMBLY_AUTHENTICATED'
    assert (residual_report['required_modules'], residual_report['prior_modules'],
            residual_report['fresh_modules'], residual_report['named_axiom_profiles']) == (39,31,8,28)
    copy(residual_report_path, REV / '20261107-residual-list-assembly-authentication.json')
    for name in ('run.json','jobs.json','artifacts.json','job.log'):
        copy(residual_base / 'actual' / name, REV / 'native_20261107/residual_list_assembly' / name)
    for name in ('authenticate_completion.py','completion_binding.json','fixed_source_graph.json',
                 'fixed_source_inventory.json','expected_prior_rows.json','actual_restore_and_frontier.json'):
        copy(residual_base / name, REV / 'offline_sources_20261107/residual_list_assembly' / name)
    residual_fresh = {name: item['row'] for name,item in residual_report['modules'].items()}
    assert len(residual_fresh) == 8
    residual_manifest = dict(
        repository=residual_report['repository'],run=residual_report['run'],job=residual_report['job'],
        source_commit=residual_report['head_sha'],artifact_id=residual_report['artifact']['id'],
        artifact_sha256=residual_report['artifact']['digest'].removeprefix('sha256:'),
        kind='AUTHENTICATED_FRESH_KERNEL_EXPORTS',lean_version='4.33.1',
        mathlib='0df444a360eaa60ab8c11dca51a86af692955474',modules=residual_fresh,
        origin_context=dict(actual_job_conclusion='success',actual_run_conclusion='success',
            authenticated_report_sha256=sha(residual_report_path),complete_endpoint_receipt_present=True,
            actual_fresh_modules=8,named_axiom_profiles=28,receipt_sha256=residual_report['receipt_sha256'],
            kernel_receipt_created_by_this_packager=False,
            manifest_scope='Only actual fresh objects physically exported by this artifact; no prior row relabelled as fresh'))
    checked_residual_manifest = json.loads((residual_base/'fresh_prior_exports.json').read_text())
    assert checked_residual_manifest['modules'] == residual_fresh
    for key in ('repository','run','job','source_commit','artifact_id','artifact_sha256','lean_version','mathlib'):
        assert checked_residual_manifest[key] == residual_manifest[key]
    copy(residual_base/'fresh_prior_exports.json',
         OUT/'ci/rg_middle_residual_list_assembly_run42345489172_prior_exports.json')
    unused = OUT/'ci/rg_middle_residual_list_run42345489172_prior_exports.json'
    if unused.exists():
        unused.unlink()

    readme = (prior / 'Proofs/RG_Lean_20261019/README.md').read_text()
    old_status = 'Status at 15:31 CET on 5 November 2026: **the original `degreeOneLarge` family is kernel-verified; three original input families remain open, and no full Lean proof has been submitted**.'
    assert readme.count(old_status) == 1
    readme = readme.replace(old_status, 'Status on 7 November 2026: **the original `degreeOneLarge` family and original Anchor029/Anchor030 certificates are kernel-verified; three original input families remain open, and no full Lean proof has been submitted**.')
    readme = readme.replace('## Original Anchor270 continuation — 5 November 2026', '## Original Anchor270 continuation — 7 November 2026')
    readme = readme.replace('of the existing Anchor030 job on its own runner.', 'of the completed Anchor030 work on its own runner.')
    readme = readme.replace('## Original Anchor030 continuation — 5 November 2026', '## Original Anchor030 completion — 7 November 2026')
    readme = readme.replace('The next bounded original target is `MiddleOriginalAnchorCertificate030.certificate`.', 'The completed original target is `MiddleOriginalAnchorCertificate030.certificate`.')
    start = readme.index('The [new native continuation 42052127520]')
    end = readme.index('\n## Verified degree-one large-order family', start)
    readme = readme[:start] + '''The [native continuation 42052127520](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/42052127520/job/127330696809)
completed successfully on 5 November at **20:32:48 CET**. On 7 November the
unchanged, previously frozen completion checker was executed against the complete
actual archive and terminal native metadata. It returned exit 0. The
[complete authentication report](reviews/20261107-anchor030-complete-authentication.json)
and [independent byte review](reviews/20261107-anchor030-independent-review.json)
establish this exact original endpoint.

The complete receipt covers **281 modules: 209 source-bound prior exports and
72 fresh original exports**. The full 3,645,182-byte archive has 501 members;
all 281 source files and their recursive dependency hashes match the pinned
target. All 72 fresh compiled objects were hashed, totaling 9,925,536 bytes.
The actual logs contain all 383 new ordered named axiom profiles; with the
preserved 455 historical profiles, all 838 original profiles are covered.
They use only `propext`, `Classical.choice`, and `Quot.sound`.

The successful native run retains workflow head
`415f1d8bbc3a065b81adea9ac3b74fd27fc66265`; the original source identity remains
`eec9bfa2996116bb5f83fc2b6d83d015b5786c6b`. Its actual artifact is `13447525826`,
SHA-256 `a48e29915be99a0ed998b9512760beec1979520518322cd3d7aa6aca1d65fed9`.
The new [fresh-export manifest](../../ci/rg_middle_anchor030_run42052127520_prior_exports.json)
contains only the 72 objects physically exported by this successful job. The
91 historical partial exports retain their cancelled producer origin.

Anchor030 is one certificate of `degreeOneMiddle`; its success does not close
the full family. `degreeOneMiddle`, `degreeTwoThree`, and
`degreeFourToFortyfive` remain open. The Middle scope consists of 680 analytic
anchors, 39 order-coverage modules, and 25 finite-residual certificate batches.
The historical 3,880-module residual join has a preserved success log, but
its result archive is no longer listed; its objects are being recovered.
''' + readme[end:]
    marker = 'This checkpoint prepares the Anchor270 run; a new complete receipt is still\nrequired.'
    assert readme.count(marker) == 1
    readme = readme.replace(marker, '''The [actual Anchor270 continuation 42345329502](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/42345329502/job/128321707343)
started on 7 November at workflow head `12d2d0ddecb59686244f7eb14c42687ec2b456e9`.
Its fixed checker is separately bound to the actual run and job. Completion is
still pending; this checkpoint does not count it as a proved endpoint.''')
    marker = '## Original Anchor270 continuation'
    pos = readme.index(marker)
    readme = readme[:pos] + '''## Residual finite list assembly recovered — 7 November 2026

The [new original ListAssembly run](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/42345489172/job/128322194549)
completed successfully and passed its fixed archive authenticator. The exact
39-module receipt consists of 31 restored prerequisites and eight fresh modules,
with all 28 ordered named axiom profiles using only standard Lean axioms.
All 13,348,232 fresh compiled-object bytes were checked against the recorded
hashes. The [authentication report](reviews/20261107-residual-list-assembly-authentication.json)
binds the source closure, native success, full artifact, and receipt.

This closes the generic theorem
`DegreeOneMiddleResidualFiniteListAssembly.of_batches`: for an arbitrary
predicate on keys, proofs for all 25 listed batches imply the predicate for
every key in the complete list. It does not supply those 25 concrete certificate
proofs. The list has 1,232 keys. Core/parameter coverage, actual-tree transport,
and the concrete residual certificates remain separate components.

''' + readme[pos:]
    (OUT / 'Proofs/RG_Lean_20261019/README.md').write_text(readme)

    state = dict(
        schema='rg_formalization_checkpoint_20261107_v1',
        completed_original_families=['degreeOneSmall','degreeOneLarge','degreeGeFourSmall','degreeGeFortysix'],
        remaining_original_families=['degreeOneMiddle','degreeTwoThree','degreeFourToFortyfive'],
        remaining_original_family_count=3, global_rg_lean_proof_complete=False,
        anchor030=dict(status='COMPLETE_AUTHENTICATED', run=report['run'], job=report['job'],
            workflow_head=report['source_commit'], required_modules=281, fresh_modules=72,
            prior_modules=209, new_named_axiom_profiles=383,
            authentication_report_sha256=sha(report_path), independent_review_sha256=sha(review)),
        anchor270=dict(status='RUNNING_COMPLETION_NOT_CLAIMED', run=42345329502, job=128321707343,
            workflow_head='12d2d0ddecb59686244f7eb14c42687ec2b456e9', required_modules=281,
            prior_modules=246, fresh_modules=35, new_named_axiom_profiles=183),
        residual_list_assembly=dict(status='COMPLETE_AUTHENTICATED', run=42345489172,
            job=128322194549, workflow_head='9db7ac27d50f0b0c8f4d90d5bc27398f374f06ca',
            required_modules=39, prior_modules=31, fresh_modules=8, new_named_axiom_profiles=28,
            authentication_report_sha256=sha(residual_report_path),
            scope='Generic assembly from 25 batch hypotheses; not the concrete residual certificates'),
        original_lean_source_changes=0, upstream_full_proof_submission=False)
    write_json(REV / '20261107-formalization-status.json', state)
    copy(pathlib.Path(__file__), REV / 'offline_sources_20261107/prepare_rg_checkpoint.py')
    files=[]
    for path in sorted(OUT.rglob('*')):
        if path.is_file():
            raw=path.read_bytes()
            files.append(dict(path=path.relative_to(OUT).as_posix(), bytes=len(raw), sha256=sha(path),
                              git_blob_sha1=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()))
    write_json(WORK / 'checkpoint/inventory.json', dict(files=files, file_count=len(files),
               bytes=sum(row['bytes'] for row in files), lean_source_changes=0))
    print(json.dumps(dict(files=len(files),bytes=sum(row['bytes'] for row in files),
                         output=str(OUT),anchor030='COMPLETE_AUTHENTICATED',remaining_families=3)))


if __name__ == '__main__':
    main()
