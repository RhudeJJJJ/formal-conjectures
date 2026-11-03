"""Audit the actual Ge46 kernel exports without recompiling or reexporting them.

The failed proof job retains its real conclusion. Its 63 completed exports keep
their original archive and provenance; a separate audit may only certify the
complete 178-module receipt after restoring all objects with zero fresh work.
"""
import argparse, hashlib, io, json, os, pathlib, re, shutil, subprocess, sys, zipfile

from rg_ge46_checked_rows_control import (ROOT, SOURCE, BUILD, PIN, LC, ALLOWED,
    ENDPOINT, CURRENT_ACCEPTED_PROFILE_METADATA, bound, load_spec, current_scope,
    check_receipt, validate_current_accepted_profiles)
from rg_collect_exact_d1_reproductions import GitHub, identity, records_from_log
from rg_github_artifacts import fetch_archive
from module_outputs import output_members

AUDIT_SPEC = 'ci/rg_ge46_zero_fresh_audit_20261103_spec.json'
AUDIT_SHA = '8df0d7923386cd3845d93ca8f05affcbb33d13a80c58ff071ef26f2458bb0c0b'
KIND = 'GE46_COMPILED_OBJECTS_WITH_SEPARATE_ZERO_FRESH_METADATA_AUDIT'
ORIGIN_KEYS = ('repository', 'run', 'job', 'source_commit', 'artifact_id', 'artifact_sha256')
OLD_ORIGIN = dict(repository='RhudeJJJJ/formal-conjectures', run=41706475942,
    job=126182927540, source_commit='1ec3794cd015edc12bfda7aa45389af73cc9ab3b',
    artifact_id=13270535981,
    artifact_sha256='f9df291a80a27e7244893aac72a4afcec323c6818f5ba4e8ca6ac5ff98dd4d54')
EVIDENCE = SOURCE / 'build/ge46_zero_fresh_audit'
STATUS = 'ALL178_GE46_IDENTITIES_REVALIDATED_WITH_ZERO_FRESH_KERNEL_EXPORTS'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def dump(value):
    return (json.dumps(value, indent=2) + '\n').encode()


def load_context():
    audit = bound(AUDIT_SPEC, AUDIT_SHA)
    assert audit['kind'] == 'EXACT_GE46_ZERO_FRESH_METADATA_AUDIT'
    assert audit['failed_kernel_origin'] == OLD_ORIGIN
    assert audit['endpoint'] == ENDPOINT and audit['required_module_count'] == 178
    assert (audit['fresh_module_count'], audit['workers'], audit['module_timeout'],
            audit['memory_reserve_mib']) == (0, 1, 1200, 2048)
    spec, historical = load_spec()
    assert bound(**dict(relative=audit['corrected_spec']['path'],
                        digest=audit['corrected_spec']['sha256'])) == spec
    proof = bound(audit['proof_manifest']['path'], audit['proof_manifest']['sha256'])
    assert {k:proof[k] for k in ORIGIN_KEYS} == OLD_ORIGIN
    assert set(proof['modules']) == set(spec['stages']['final']['fresh_modules'])
    assert len(proof['modules']) == 63
    assert proof['origin_context']['job_conclusion'] == 'failure'
    assert proof['origin_context']['metadata_audit_complete'] is False
    assert proof['origin_context']['original_degree_ge46_endpoint_complete'] is False
    base = bound(spec['base_manifest'], spec['base_manifest_sha256'])
    partial = bound(spec['partial_manifest'], spec['partial_manifest_sha256'])
    parents = {key:bound(value['path'], value['sha256'])
               for key,value in audit['parent_manifests'].items()}
    assert set(parents) == set(spec['stages']['final']['prerequisites'])
    assert len(parents) == 26
    return dict(audit=audit, spec=spec, historical=historical, proof=proof,
                base=base, partial=partial, parents=parents)


def restored_row(manifest, row, capsule=False):
    if capsule:
        assert manifest['kind'] == 'INDEPENDENTLY_AUDITED_COMPLETE_SCOPE_CAPSULE'
        origin = row['origin'] if row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT' else {
            k:manifest[k] for k in ORIGIN_KEYS}
        return dict(row, mode='PRIOR_VERIFIED_JOB_EXPORT', origin=origin,
            transport_capsule={k:manifest[k] for k in ORIGIN_KEYS if k != 'repository'})
    assert row['mode'] == 'FRESH_KERNEL_EXPORT'
    origin = {k:manifest[k] for k in ORIGIN_KEYS}
    if 'origin_context' in manifest:
        origin['context'] = manifest['origin_context']
    return dict(row, mode='PRIOR_VERIFIED_JOB_EXPORT', origin=origin)


def expected_records(context):
    """Replicate the existing restorers' exact origins, never invent fresh ones."""
    spec, base, partial = context['spec'], context['base'], context['partial']
    expected = {n:restored_row(base,r,True) for n,r in base['modules'].items()}
    for manifest in [partial] + [context['parents'][key]
            for key in spec['stages']['final']['prerequisites']] + [context['proof']]:
        for name,row in manifest['modules'].items():
            if name in expected:
                assert identity(name,expected[name]) == identity(name,row)
            else:
                expected[name] = restored_row(manifest,row)
    required = set(spec['stages']['final']['required_modules'])
    assert required <= set(expected) and len(required) == 178
    return {n:expected[n] for n in sorted(required)}


def open_checked_archive(raw, digest, maximum=1024**3):
    assert len(raw) <= maximum and sha(raw) == digest
    archive = zipfile.ZipFile(io.BytesIO(raw))
    assert len(archive.namelist()) == len(set(archive.namelist())) <= 4096
    for info in archive.infolist():
        p = pathlib.PurePosixPath(info.filename)
        assert not p.is_absolute() and '..' not in p.parts
        assert (info.external_attr >> 16) & 0o170000 != 0o120000
    return archive


def check_original_job(audit, job, run, artifact):
    assert run['id'] == OLD_ORIGIN['run'] and run['head_sha'] == OLD_ORIGIN['source_commit']
    assert run['path'] == audit['failed_workflow_path']
    assert run['head_branch'] == 'rg-degree-one-large-20261103'
    assert job['id'] == OLD_ORIGIN['job'] and job['run_id'] == OLD_ORIGIN['run']
    assert job['head_sha'] == OLD_ORIGIN['source_commit'] and job['name'] == audit['failed_job_name']
    assert job['status'] == 'completed' and job['conclusion'] == 'failure'
    assert job['run_attempt'] == 1
    for name, conclusion in ((audit['successful_kernel_step'],'success'),
                             (audit['failed_metadata_step'],'failure')):
        steps = [s for s in job['steps'] if s['name'] == name]
        assert len(steps) == 1 and steps[0]['conclusion'] == conclusion
    assert artifact['id'] == OLD_ORIGIN['artifact_id']
    assert artifact['name'] == audit['failed_archive_name']
    assert artifact['size_in_bytes'] == audit['failed_archive_bytes']
    assert not artifact['expired'] and artifact['workflow_run']['id'] == OLD_ORIGIN['run']
    assert artifact['workflow_run']['head_sha'] == OLD_ORIGIN['source_commit']
    assert artifact['digest'] == 'sha256:' + OLD_ORIGIN['artifact_sha256']


def authenticate_original(context, archive, logged):
    audit, spec, historical = (context[k] for k in ('audit','spec','historical'))
    raw = archive.read('receipt.json')
    assert sha(raw) == audit['original_receipt_sha256']
    fresh, logical, _ = check_receipt(spec,historical,spec['stages']['final'],raw,
        archive.read,archive.open,lambda n:archive.getinfo(n).file_size,
        lambda n:archive.read(n+'.log'))
    assert fresh == context['proof']['modules'] == logged
    assert logical == audit['original_kernel_raw_output_bytes']
    assert {n[:-5] for n in archive.namelist()
            if n.startswith('Proofs.') and n.endswith('.json')} == set(fresh)
    for name,row in fresh.items():
        text = archive.read(name+'.log').decode('utf-8')
        assert not re.search(r'\b(error|warning)(?:\([^\n]*?\))?:',text)
        profiles = [sorted(set(x.strip() for x in p.split(',') if x.strip()))
            for p in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',text)]
        profiles += [[] for _ in re.findall('does not depend on any axioms',text)]
        assert profiles == row['axiom_profiles']
    resource = json.loads(archive.read('resource_observer.json'))
    assert resource['status'] == 'VERIFIER_COMPLETED' and resource['exit_code'] == 0
    assert resource['mathlib_and_lean_flags_unchanged'] is True
    original = json.loads(raw)
    expected = expected_records(context)
    assert set(original['modules']) == set(expected)
    for name,row in original['modules'].items():
        assert identity(name,row) == identity(name,expected[name])
        if row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT':
            assert {k:row['origin'][k] for k in ORIGIN_KEYS} == {
                k:expected[name]['origin'][k] for k in ORIGIN_KEYS}
        else:
            assert row['mode'] == 'FRESH_KERNEL_EXPORT'
            assert {k:expected[name]['origin'][k] for k in ORIGIN_KEYS} == OLD_ORIGIN
    diagnostics = json.loads(archive.read('diagnostics_records.json'))['modules']
    records = {r['module']:r for r in diagnostics}
    assert len(records) == len(diagnostics)
    assert all(records[n] == r for n,r in original['modules'].items())
    named = {n:validate_current_accepted_profiles(spec,historical,n,fresh[n],
                lambda name:archive.read(name+'.log'))
             for n in CURRENT_ACCEPTED_PROFILE_METADATA['modules']}
    return raw, named


def check_zero_receipt(context, raw, original_raw, read_record=None,
                       open_member=None, member_size=None):
    audit, spec = context['audit'], context['spec']
    assert sha(original_raw) == audit['original_receipt_sha256']
    original, receipt = json.loads(original_raw), json.loads(raw)
    assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE'
    assert receipt['endpoints'] == [ENDPOINT]
    assert receipt['mathlib'] == PIN and receipt['leancert'] == LC
    assert receipt['lean'] == original['lean'] and 'version 4.33.1,' in receipt['lean']
    expected = expected_records(context)
    assert set(receipt['modules']) == set(expected) == set(original['modules'])
    logical = 0
    for name,row in receipt['modules'].items():
        assert row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'
        assert row == expected[name], ('Changed prior record or original origin', name)
        assert identity(name,row) == identity(name,original['modules'][name])
        assert row['source_sha256'] == spec['source_graph'][name]['source_sha256']
        assert row['source_closure_sha256'] == spec['source_graph'][name]['source_closure_sha256']
        assert row['axiom_profiles'] and all(set(p) <= ALLOWED for p in row['axiom_profiles'])
        if read_record is not None:
            assert json.loads(read_record(name+'.json')) == row
        if open_member is not None:
            assert member_size is not None
            for relative,digest,size in output_members(name,row):
                actual_size = member_size(relative)
                assert size is None or size == actual_size
                with open_member(relative) as stream:
                    assert hashlib.file_digest(stream,'sha256').hexdigest() == digest
                logical += actual_size
    assert logical <= 8*1024**3
    assert not [n for n,r in receipt['modules'].items() if r['mode']=='FRESH_KERNEL_EXPORT']
    return logical


def local_file(relative):
    p = pathlib.PurePosixPath(relative)
    assert not p.is_absolute() and '..' not in p.parts
    actual = BUILD / p
    assert actual.resolve().is_relative_to(BUILD.resolve())
    return actual


def restore(context):
    audit, spec = context['audit'], context['spec']
    api = GitHub(OLD_ORIGIN['repository'])
    run = api.get('/actions/runs/' + str(OLD_ORIGIN['run']))
    jobs = api.listing('/actions/runs/' + str(OLD_ORIGIN['run']) + '/jobs?filter=all','jobs')
    artifacts = api.listing('/actions/runs/' + str(OLD_ORIGIN['run']) + '/artifacts','artifacts')
    indexed_jobs, indexed_artifacts = ({j['id']:j for j in jobs},{a['id']:a for a in artifacts})
    check_original_job(audit,indexed_jobs[OLD_ORIGIN['job']],run,indexed_artifacts[OLD_ORIGIN['artifact_id']])
    EVIDENCE.mkdir(parents=True,exist_ok=True)
    seen = set(context['base']['modules']) | set(context['partial']['modules'])
    for key in spec['stages']['final']['prerequisites']:
        manifest, stage = context['parents'][key], spec['stages'][key]
        job, artifact = indexed_jobs[manifest['job']], indexed_artifacts[manifest['artifact_id']]
        assert job['run_id'] == manifest['run'] == OLD_ORIGIN['run']
        assert job['head_sha'] == manifest['source_commit'] == OLD_ORIGIN['source_commit']
        assert job['name'] == stage['job_name'] and job['status'] == 'completed' and job['conclusion'] == 'success'
        steps = [s for s in job['steps'] if s['name'] == stage['required_success_step']]
        assert len(steps) == 1 and steps[0]['conclusion'] == 'success'
        assert artifact['name'] == stage['artifact_name_template'].format(run=manifest['run'],attempt=job['run_attempt'])
        assert artifact['digest'] == 'sha256:' + manifest['artifact_sha256'] and not artifact['expired']
        assert artifact['workflow_run']['id'] == manifest['run']
        assert artifact['workflow_run']['head_sha'] == manifest['source_commit']
        raw = fetch_archive(manifest)
        assert len(raw) == artifact['size_in_bytes']
        with open_checked_archive(raw,manifest['artifact_sha256']) as archive:
            fresh, _, _ = check_receipt(spec,context['historical'],stage,archive.read('receipt.json'),
                archive.read,archive.open,lambda n:archive.getinfo(n).file_size,
                lambda n:archive.read(n+'.log'))
            assert fresh == manifest['modules'] == records_from_log(api.logs(job['id']))
            selected = {n:r for n,r in fresh.items() if n not in seen}
            seen.update(fresh)
        if selected:
            projected = dict(manifest,modules=selected)
            restore_original_zip(projected,raw,key)
    manifest = context['proof']
    raw = fetch_archive(manifest)
    assert len(raw) == audit['failed_archive_bytes']
    with open_checked_archive(raw,manifest['artifact_sha256']) as archive:
        original_raw,named = authenticate_original(context,archive,records_from_log(api.logs(OLD_ORIGIN['job'])))
        (EVIDENCE/'original_completed_kernel_receipt.json').write_bytes(original_raw)
        (EVIDENCE/'current_accepted_named_profiles.json').write_bytes(dump(named))
        for name in CURRENT_ACCEPTED_PROFILE_METADATA['modules']:
            (EVIDENCE/(name+'.log')).write_bytes(archive.read(name+'.log'))
    restore_original_zip(manifest,raw,'original_failed_final')
    expected = expected_records(context)
    for name,row in expected.items():
        assert json.loads(local_file(name+'.json').read_bytes()) == row
    (EVIDENCE/'original_proof_origin.json').write_bytes(dump(dict(
        failed_kernel_origin=OLD_ORIGIN,failed_job_conclusion='failure',
        kernel_step_conclusion='success',metadata_step_conclusion='failure',
        compiled_module_count=63,new_kernel_exports=0,
        original_receipt_sha256=audit['original_receipt_sha256'])))


def restore_original_zip(manifest, raw, key):
    assert shutil.disk_usage(ROOT).free >= 8*1024**3 + 2*len(raw)
    temporary = SOURCE/'build/ge46_zero_fresh_audit_downloads'
    temporary.mkdir(parents=True,exist_ok=True)
    archive_path = temporary/(key+'.zip')
    manifest_path = EVIDENCE/(key+'_prior_exports.json')
    archive_path.write_bytes(raw)
    manifest_path.write_bytes(dump(manifest))
    try:
        subprocess.run([sys.executable,'-B','ci/rg_restore_job_exports.py','--manifest',str(manifest_path),
            '--verified-local-archive',str(archive_path),'--build-directory',str(BUILD)],cwd=ROOT,check=True)
    finally:
        archive_path.unlink()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase',choices=('source','restore','before','verify','after'),required=True)
    args = parser.parse_args()
    context = load_context()
    audit,spec = context['audit'],context['spec']
    hashes,closures = current_scope(spec,spec['stages']['final'])
    assert len(hashes) == 178
    EVIDENCE.mkdir(parents=True,exist_ok=True)
    if args.phase == 'source':
        print(json.dumps(dict(status='EXACT_GE46_SOURCE_AND_COMPOSITE_ORIGIN_BOUND',
            required_modules=178,maximum_fresh_modules=0,failed_kernel_origin=OLD_ORIGIN)),flush=True)
    elif args.phase == 'restore':
        restore(context)
    elif args.phase == 'before':
        # The existing generic helper accepts a minimum bound of one. This
        # sealed audit tightens its observed result to exactly zero before any
        # verifier invocation; it never authorizes that generic one-module cap.
        subprocess.run([sys.executable,'-B','ci/rg_restore_with_kernel_fallback.py',
            '--plan','ci/rg_empty_restore_plan.json','--build-directory',str(BUILD),
            '--endpoint',ENDPOINT,'--max-fresh','1','--preflight-only'],cwd=ROOT,check=True)
        frontier=json.loads(local_file('bounded_kernel_fallback_plan.json').read_bytes())
        assert frontier['required_modules']==178 and frontier['within_bound'] is True
        assert frontier['fresh_modules']==[] and frontier['verified_prior_objects']==178
        (EVIDENCE/'zero_fresh_frontier.json').write_bytes(dump(frontier))
    elif args.phase == 'verify':
        frontier=json.loads((EVIDENCE/'zero_fresh_frontier.json').read_bytes())
        assert frontier['fresh_modules']==[] and frontier['verified_prior_objects']==178
        subprocess.run([sys.executable,'-B','ci/rg_observed_kernel_verify.py','--memory-reserve-mib','2048',
            '--','--mathlib-project',str(ROOT),'--endpoint',ENDPOINT,'--workers','1',
            '--module-timeout','1200','--resume'],cwd=ROOT,check=True)
    else:
        raw=local_file('receipt.json').read_bytes()
        original=(EVIDENCE/'original_completed_kernel_receipt.json').read_bytes()
        logical=check_zero_receipt(context,raw,original,
            lambda n:local_file(n).read_bytes(),lambda n:local_file(n).open('rb'),lambda n:local_file(n).stat().st_size)
        observer=json.loads((SOURCE/'build/fresh_exports/resource_observer.json').read_bytes())
        assert observer['status']=='VERIFIER_COMPLETED' and observer['exit_code']==0
        assert observer['mathlib_and_lean_flags_unchanged'] is True
        checkout=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
        assert checkout==os.environ['GITHUB_SHA']
        report=dict(status=STATUS,kind=KIND,source_commit=checkout,
            workflow_run=int(os.environ['GITHUB_RUN_ID']),workflow_attempt=int(os.environ['GITHUB_RUN_ATTEMPT']),
            workflow_path=audit['audit_workflow_path'],job_name=audit['audit_job_name'],
            required_modules=178,fresh_kernel_exports=0,original_compiled_modules=63,
            failed_kernel_origin=OLD_ORIGIN,original_failed_job_conclusion='failure',
            original_receipt_sha256=audit['original_receipt_sha256'],receipt_sha256=sha(raw),
            audit_spec_sha256=AUDIT_SHA,corrected_metadata_spec_sha256=audit['corrected_spec']['sha256'],
            source_endpoint_sha256=hashes[ENDPOINT],source_endpoint_closure_sha256=closures[ENDPOINT],
            actual_all178_output_bytes_verified=logical,all178_identity_tuples_unchanged=True,
            all178_prior_origin_anchors_preserved=True,prior_records_match_sealed_manifests=True,
            old_objects_reexported_as_fresh=False,
            original_degree_ge46_endpoint_complete=True,whole_degree_one_large_complete=False)
        (EVIDENCE/'receipt.json').write_bytes(raw)
        (EVIDENCE/'resource_observer.json').write_bytes(dump(observer))
        (EVIDENCE/'ge46_zero_fresh_audit.json').write_bytes(dump(report))
        print(json.dumps(report),flush=True)


if __name__ == '__main__':
    main()
