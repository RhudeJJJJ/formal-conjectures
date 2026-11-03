"""Revalidate the actual complete numeric137 batch with no fresh compilation.

The 21 compiled objects keep their actual failed-job origin. This separate
audit restores the complete 95-module scope, checks the actual named profile
logs against all original declarations, and requires exactly zero fresh work.
"""
import argparse, hashlib, io, json, os, pathlib, re, shutil, subprocess, sys, zipfile

import rg_numeric137_decomposed_recovery as decomposition
from rg_collect_exact_d1_reproductions import GitHub, identity, records_from_log
from rg_github_artifacts import fetch_archive
from module_outputs import output_members

ROOT, SOURCE = decomposition.ROOT, decomposition.SOURCES
BUILD = SOURCE / 'build/extension'
EVIDENCE = SOURCE / 'build/numeric137_zero_fresh_audit'
AUDIT_SPEC = 'ci/rg_numeric137_zero_fresh_audit_20261103_spec.json'
AUDIT_SHA = '00efcb5f75bd7f4d30300fa0a116553359744e203497d08ba87a3f95c76bf9d1'
CORRECTED_SHA = '215ae3b2b69a4d7f9f00d694228a45333df0b73e588a6b2f0f61c97b45db4302'
KIND = 'NUMERIC137_COMPILED_OBJECTS_WITH_SEPARATE_ZERO_FRESH_METADATA_AUDIT'
STATUS = 'ALL95_NUMERIC137_IDENTITIES_REVALIDATED_WITH_ZERO_FRESH_KERNEL_EXPORTS'
ORIGIN_KEYS = ('repository','run','job','source_commit','artifact_id','artifact_sha256')
OLD_ORIGIN = dict(repository='RhudeJJJJ/formal-conjectures',run=41709596489,
    job=126173873595,source_commit='ff7f8e64450cba947197417865221d624f5365c8',
    artifact_id=13274071154,
    artifact_sha256='6014d03a98cea6b8285d80ec27f2ec6da4ce930eb76a882deaacf1585a1877c6')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def dump(value):
    return (json.dumps(value,indent=2)+'\n').encode()


def load_context():
    audit = decomposition.bound_file(AUDIT_SPEC,AUDIT_SHA)
    assert audit['kind'] == 'EXACT_NUMERIC137_ZERO_FRESH_METADATA_AUDIT'
    assert audit['failed_kernel_origin'] == OLD_ORIGIN
    assert audit['batch'] == '00_137' and audit['original_endpoints'] == decomposition.ENDPOINTS
    assert (audit['required_module_count'],audit['fresh_module_count'],
            audit['original_compiled_module_count']) == (95,0,21)
    assert (audit['unchanged_historical_numeric_objects'],audit['reorganized_current_source_modules'],
            audit['added_support_module_count'],audit['original_axiom_print_count']) == (9,12,11,313)
    assert (audit['workers'],audit['module_timeout'],audit['memory_reserve_mib']) == (1,1200,2048)
    assert audit['corrected_spec'] == dict(path=decomposition.SPEC,sha256=CORRECTED_SHA)
    spec,plan,original,base,snapshot = decomposition.context(CORRECTED_SHA)
    proof = decomposition.bound_file(audit['proof_manifest']['path'],audit['proof_manifest']['sha256'])
    assert {k:proof[k] for k in ORIGIN_KEYS} == OLD_ORIGIN
    assert set(proof['modules']) == set(spec['modules']) and len(proof['modules']) == 21
    assert proof['origin_context']['job_conclusion'] == 'failure'
    assert proof['origin_context']['metadata_audit_complete'] is False
    assert proof['origin_context']['complete_original_batch_audit_complete'] is False
    assert proof['origin_context']['full_receipt_sha256'] == audit['original_receipt_sha256']
    assert proof['origin_context']['corrected_metadata_spec_sha256'] == CORRECTED_SHA
    return dict(audit=audit,spec=spec,plan=plan,original=original,base=base,snapshot=snapshot,proof=proof)


def expected_records(context):
    """Use the exact existing restorers' record modes and original origins."""
    base,proof,spec = context['base'],context['proof'],context['spec']
    assert base['kind'] == 'INDEPENDENTLY_AUDITED_COMPLETE_SCOPE_CAPSULE'
    records = {}
    for name,row in base['modules'].items():
        origin = row['origin'] if row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT' else {
            k:base[k] for k in ORIGIN_KEYS}
        records[name] = dict(row,mode='PRIOR_VERIFIED_JOB_EXPORT',origin=origin,
            transport_capsule={k:base[k] for k in ORIGIN_KEYS if k != 'repository'})
    for name,row in proof['modules'].items():
        assert name not in records and row['mode'] == 'FRESH_KERNEL_EXPORT'
        records[name] = dict(row,mode='PRIOR_VERIFIED_JOB_EXPORT',
            origin=dict(OLD_ORIGIN,context=proof['origin_context']))
    required = set(spec['required_modules'])
    assert required <= set(records) and len(required) == 95
    return {n:records[n] for n in sorted(required)}


def open_checked_archive(raw):
    assert len(raw) == 190329547 and sha(raw) == OLD_ORIGIN['artifact_sha256']
    archive = zipfile.ZipFile(io.BytesIO(raw))
    assert len(archive.namelist()) == len(set(archive.namelist())) == 68
    for info in archive.infolist():
        p = pathlib.PurePosixPath(info.filename)
        assert not p.is_absolute() and '..' not in p.parts
        assert (info.external_attr >> 16) & 0o170000 != 0o120000
    return archive


def check_original_job(audit,job,run,artifact):
    assert run['id'] == OLD_ORIGIN['run'] and run['head_sha'] == OLD_ORIGIN['source_commit']
    assert run['path'] == audit['failed_workflow_path']
    assert run['head_branch'] == 'rg-degree-one-large-20261103'
    assert job['id'] == OLD_ORIGIN['job'] and job['run_id'] == OLD_ORIGIN['run']
    assert job['head_sha'] == OLD_ORIGIN['source_commit'] and job['name'] == audit['failed_job_name']
    assert job['status'] == 'completed' and job['conclusion'] == 'failure' and job['run_attempt'] == 1
    for name,conclusion in ((audit['successful_kernel_step'],'success'),
                            (audit['failed_metadata_step'],'failure')):
        steps = [s for s in job['steps'] if s['name'] == name]
        assert len(steps) == 1 and steps[0]['conclusion'] == conclusion
    assert artifact['id'] == OLD_ORIGIN['artifact_id'] and not artifact['expired']
    assert artifact['name'] == audit['failed_archive_name']
    assert artifact['size_in_bytes'] == audit['failed_archive_bytes']
    assert artifact['workflow_run']['id'] == OLD_ORIGIN['run']
    assert artifact['workflow_run']['head_sha'] == OLD_ORIGIN['source_commit']
    assert artifact['digest'] == 'sha256:' + OLD_ORIGIN['artifact_sha256']


def authenticate_original(context,archive,logged):
    """Read every compiled object and the real named logs from the old ZIP."""
    audit,spec,original,base,snapshot,proof = (context[k] for k in
        ('audit','spec','original','base','snapshot','proof'))
    raw = archive.read('receipt.json')
    assert sha(raw) == audit['original_receipt_sha256']
    receipt = json.loads(raw)
    assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints'] == decomposition.ENDPOINTS
    assert receipt['mathlib'] == decomposition.PIN and receipt['leancert'] == decomposition.LC
    assert 'version 4.33.1,' in receipt['lean']
    assert set(receipt['modules']) == set(spec['required_modules']) and len(receipt['modules']) == 95
    fresh = {n:r for n,r in receipt['modules'].items() if r['mode'] == 'FRESH_KERNEL_EXPORT'}
    assert fresh == proof['modules'] == logged and set(fresh) == set(spec['modules'])
    assert {n[:-5] for n in archive.namelist() if n.startswith('Proofs.') and n.endswith('.json')} == set(fresh)
    diagnostics = json.loads(archive.read('diagnostics_records.json'))['modules']
    records = {r['module']:r for r in diagnostics}
    assert len(records) == len(diagnostics)
    expected = expected_records(context)
    logical = 0
    for name,row in receipt['modules'].items():
        assert row['module'] == name and records[name] == row
        assert row['source_sha256'] == spec['required_source_sha256'][name]
        assert row['source_closure_sha256'] == spec['required_source_closure_sha256'][name]
        assert row['axiom_profiles'] and all(set(p) <= decomposition.ALLOWED for p in row['axiom_profiles'])
        assert identity(name,row) == identity(name,expected[name])
        if name not in fresh:
            assert row == expected[name], ('Changed original prior record or provenance',name)
            continue
        assert json.loads(archive.read(name+'.json')) == row
        if name not in decomposition.NEW:
            assert identity(name,row) == identity(name,original[name])
        else:
            assert len(row['axiom_profiles']) == spec['modules'][name]['axiom_profile_count']
        text = archive.read(name+'.log').decode('utf-8')
        assert not re.search(r'\b(error|warning)(?:\([^\n]*?\))?:',text)
        profiles = [sorted(set(x.strip() for x in p.split(',') if x.strip()))
                    for p in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',text)]
        profiles += [[] for _ in re.findall('does not depend on any axioms',text)]
        assert profiles == row['axiom_profiles']
        for relative,digest,size in output_members(name,row):
            actual_size = archive.getinfo(relative).file_size
            assert size is None or size == actual_size
            with archive.open(relative) as stream:
                assert hashlib.file_digest(stream,'sha256').hexdigest() == digest
            logical += actual_size
    assert logical == audit['original_kernel_raw_output_bytes']
    named = decomposition.validate_named_split_axioms(spec,original,snapshot,receipt['modules'],
                                                      lambda n:archive.read(n+'.log'))
    observer = json.loads(archive.read('resource_observer.json'))
    assert observer['status'] == 'VERIFIER_COMPLETED' and observer['exit_code'] == 0
    assert observer['mathlib_and_lean_flags_unchanged'] is True
    return raw,named


def check_zero_receipt(context,raw,original_raw,read_record=None,open_member=None,member_size=None):
    audit,spec = context['audit'],context['spec']
    assert sha(original_raw) == audit['original_receipt_sha256']
    original,receipt = json.loads(original_raw),json.loads(raw)
    assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE'
    assert receipt['endpoints'] == decomposition.ENDPOINTS
    assert receipt['mathlib'] == decomposition.PIN and receipt['leancert'] == decomposition.LC
    assert receipt['lean'] == original['lean'] and 'version 4.33.1,' in receipt['lean']
    expected = expected_records(context)
    assert set(receipt['modules']) == set(expected) == set(original['modules'])
    logical = 0
    for name,row in receipt['modules'].items():
        assert row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'
        assert row == expected[name], ('Changed original identity or provenance',name)
        assert identity(name,row) == identity(name,original['modules'][name])
        assert row['source_sha256'] == spec['required_source_sha256'][name]
        assert row['source_closure_sha256'] == spec['required_source_closure_sha256'][name]
        assert row['axiom_profiles'] and all(set(p) <= decomposition.ALLOWED for p in row['axiom_profiles'])
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
    assert logical <= 4*1024**3
    assert not [n for n,r in receipt['modules'].items() if r['mode'] == 'FRESH_KERNEL_EXPORT']
    return logical


def local_file(relative):
    p = pathlib.PurePosixPath(relative)
    assert not p.is_absolute() and '..' not in p.parts
    actual = BUILD/p
    assert actual.resolve().is_relative_to(BUILD.resolve())
    return actual


def restore(context):
    audit = context['audit']
    api = GitHub(OLD_ORIGIN['repository'])
    run = api.get('/actions/runs/'+str(OLD_ORIGIN['run']))
    jobs = api.listing('/actions/runs/'+str(OLD_ORIGIN['run'])+'/jobs?filter=all','jobs')
    artifacts = api.listing('/actions/runs/'+str(OLD_ORIGIN['run'])+'/artifacts','artifacts')
    selected_jobs = [j for j in jobs if j['id'] == OLD_ORIGIN['job']]
    selected_artifacts = [a for a in artifacts if a['id'] == OLD_ORIGIN['artifact_id']]
    assert len(selected_jobs) == len(selected_artifacts) == 1
    check_original_job(audit,selected_jobs[0],run,selected_artifacts[0])
    log = api.logs(OLD_ORIGIN['job'])
    raw = fetch_archive(context['proof'])
    assert len(raw) == audit['failed_archive_bytes']
    with open_checked_archive(raw) as archive:
        original_raw,named = authenticate_original(context,archive,records_from_log(log))
        (EVIDENCE/'original_completed_kernel_receipt.json').write_bytes(original_raw)
        (EVIDENCE/'numeric137_named_axioms.json').write_bytes(dump(named))
        for name in decomposition.NEW:
            (EVIDENCE/(name+'.log')).write_bytes(archive.read(name+'.log'))
    assert shutil.disk_usage(ROOT).free >= 8*1024**3 + 2*len(raw)
    temporary = SOURCE/'build/numeric137_zero_fresh_downloads'
    temporary.mkdir(parents=True,exist_ok=True)
    archive_path = temporary/'original_failed_compilation.zip'
    manifest_path = EVIDENCE/'original_failed_kernel_prior_exports.json'
    archive_path.write_bytes(raw)
    manifest_path.write_bytes(dump(context['proof']))
    try:
        subprocess.run([sys.executable,'-B','ci/rg_restore_job_exports.py','--manifest',str(manifest_path),
            '--verified-local-archive',str(archive_path),'--build-directory',str(BUILD)],cwd=ROOT,check=True)
    finally:
        archive_path.unlink()
    for name,row in expected_records(context).items():
        assert json.loads(local_file(name+'.json').read_bytes()) == row
    (EVIDENCE/'original_proof_origin.json').write_bytes(dump(dict(
        failed_kernel_origin=OLD_ORIGIN,failed_job_conclusion='failure',kernel_step_conclusion='success',
        metadata_step_conclusion='failure',compiled_module_count=21,new_kernel_exports=0,
        original_receipt_sha256=audit['original_receipt_sha256'])))


def check_frontiers(frontiers):
    assert isinstance(frontiers,list) and len(frontiers) == 10
    assert [f['endpoint'] for f in frontiers] == decomposition.ENDPOINTS
    covered = set()
    for frontier in frontiers:
        hashes,_,_ = decomposition.source_closure(frontier['endpoint'])
        assert frontier['required_modules'] == frontier['verified_prior_objects'] == len(hashes)
        assert frontier['fresh_modules'] == [] and frontier['within_bound'] is True
        covered.update(hashes)
    assert len(covered) == 95
    return covered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase',choices=('source','restore','before','verify','after'),required=True)
    args = parser.parse_args()
    context = load_context()
    audit,spec,original,base,snapshot = (context[k] for k in ('audit','spec','original','base','snapshot'))
    decomposition.preserve_declarations(spec,original,snapshot)
    if args.phase == 'source':
        decomposition.materialize_unchanged(spec,original,snapshot)
        decomposition.preserve_declarations(spec,original,snapshot)
    hashes,closures = decomposition.source_scope(spec,original,base)
    assert len(hashes) == 95
    EVIDENCE.mkdir(parents=True,exist_ok=True)
    if args.phase == 'source':
        print(json.dumps(dict(status='EXACT_NUMERIC137_SOURCE_AND_COMPOSITE_ORIGIN_BOUND',
            required_modules=95,maximum_fresh_modules=0,failed_kernel_origin=OLD_ORIGIN)),flush=True)
    elif args.phase == 'restore':
        restore(context)
    elif args.phase == 'before':
        frontiers = []
        for endpoint in decomposition.ENDPOINTS:
            # The generic helper's minimum cap is one; this audit immediately
            # tightens each observed frontier to zero before verifier use.
            subprocess.run([sys.executable,'-B','ci/rg_restore_with_kernel_fallback.py',
                '--plan','ci/rg_empty_restore_plan.json','--build-directory',str(BUILD),
                '--endpoint',endpoint,'--max-fresh','1','--preflight-only'],cwd=ROOT,check=True)
            frontiers.append(json.loads(local_file('bounded_kernel_fallback_plan.json').read_bytes()))
        assert check_frontiers(frontiers) == set(hashes)
        (EVIDENCE/'zero_fresh_frontiers.json').write_bytes(dump(frontiers))
    elif args.phase == 'verify':
        frontiers = json.loads((EVIDENCE/'zero_fresh_frontiers.json').read_bytes())
        assert check_frontiers(frontiers) == set(hashes)
        for name,row in expected_records(context).items():
            assert json.loads(local_file(name+'.json').read_bytes()) == row
        command = [sys.executable,'-B','ci/rg_observed_kernel_verify.py','--memory-reserve-mib','2048',
                   '--','--mathlib-project',str(ROOT)]
        for endpoint in decomposition.ENDPOINTS:
            command.extend(['--endpoint',endpoint])
        command.extend(['--workers','1','--module-timeout','1200','--resume'])
        subprocess.run(command,cwd=ROOT,check=True)
    else:
        raw = local_file('receipt.json').read_bytes()
        original_raw = (EVIDENCE/'original_completed_kernel_receipt.json').read_bytes()
        logical = check_zero_receipt(context,raw,original_raw,
            lambda n:local_file(n).read_bytes(),lambda n:local_file(n).open('rb'),lambda n:local_file(n).stat().st_size)
        named = decomposition.validate_named_split_axioms(spec,original,snapshot,json.loads(raw)['modules'],
            lambda n:(EVIDENCE/(n+'.log')).read_bytes())
        assert json.loads((EVIDENCE/'numeric137_named_axioms.json').read_bytes()) == named
        observer = json.loads((SOURCE/'build/fresh_exports/resource_observer.json').read_bytes())
        assert observer['status'] == 'VERIFIER_COMPLETED' and observer['exit_code'] == 0
        assert observer['mathlib_and_lean_flags_unchanged'] is True
        checkout = subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
        assert checkout == os.environ['GITHUB_SHA']
        report = dict(status=STATUS,kind=KIND,source_commit=checkout,
            workflow_run=int(os.environ['GITHUB_RUN_ID']),workflow_attempt=int(os.environ['GITHUB_RUN_ATTEMPT']),
            workflow_path=audit['audit_workflow_path'],job_name=audit['audit_job_name'],
            batch='00_137',original_endpoints=decomposition.ENDPOINTS,
            required_modules=95,fresh_kernel_exports=0,original_compiled_modules=21,
            failed_kernel_origin=OLD_ORIGIN,original_failed_job_conclusion='failure',
            original_receipt_sha256=audit['original_receipt_sha256'],receipt_sha256=sha(raw),
            audit_spec_sha256=AUDIT_SHA,corrected_metadata_spec_sha256=CORRECTED_SHA,
            original_plan_sha256=decomposition.ORIGINAL_PLAN_SHA,
            actual_all95_output_bytes_verified=logical,all95_identity_tuples_unchanged=True,
            all95_prior_origin_anchors_preserved=True,prior_records_match_sealed_manifests=True,
            old_objects_reexported_as_fresh=False,original_declarations_preserved_verbatim=True,
            named_original_declarations_verified=313,
            complete_original_axiom_profile_array_preserved=True,
            historical_normalized_profile_sha256=named['historical_normalized_profile_sha256'],
            unchanged_historical_numeric_objects_reproduced=9,
            current_source_exports=sorted(decomposition.NEW),added_support_modules=sorted(decomposition.NEW-{decomposition.NAME}),
            complete_original_batch_audit_complete=True,whole_degree_one_large_complete=False)
        (EVIDENCE/'receipt.json').write_bytes(raw)
        (EVIDENCE/'resource_observer.json').write_bytes(dump(observer))
        (EVIDENCE/'numeric137_zero_fresh_audit.json').write_bytes(dump(report))
        print(json.dumps(report),flush=True)


if __name__ == '__main__':
    main()
