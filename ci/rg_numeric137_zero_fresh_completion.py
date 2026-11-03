"""Bind numeric137's actual compiled objects to a separate successful audit.

The old complete 95-module proof receipt contains 21 fresh exports. Its job
retains its failed metadata conclusion. A later zero-fresh audit can validate
the whole batch, but can never become the origin of those compiled objects.
"""
import io, json, pathlib, re, zipfile

from rg_numeric137_zero_fresh_audit import (ROOT, KIND, STATUS, AUDIT_SPEC, AUDIT_SHA,
    CORRECTED_SHA, OLD_ORIGIN, decomposition, load_context, sha, check_original_job,
    authenticate_original, check_zero_receipt, open_checked_archive, check_frontiers)
from rg_collect_exact_d1_reproductions import records_from_log
from rg_github_artifacts import fetch_archive


def completion_context(item):
    required = {'batch','original_job','original_plan_sha256','run','job','source_commit',
        'artifact_id','artifact_sha256','artifact_name','job_name','required_success_step',
        'completion_kind','completion_spec','compiled_proof_origin'}
    optional = {'workflow_path','key','actual_run_attempt','numeric_replacement',
                'original_manifests','fresh_module_origins'}
    assert required <= set(item) <= required | optional
    assert item['completion_kind'] == KIND and item['batch'] == '00_137'
    assert item['original_job'] == 126095228986
    assert item['original_plan_sha256'] == decomposition.ORIGINAL_PLAN_SHA
    assert item['completion_spec'] == {'path':AUDIT_SPEC,'sha256':AUDIT_SHA}
    assert item['compiled_proof_origin'] == OLD_ORIGIN
    context = load_context()
    audit,spec,original,base,snapshot,plan = (context[k] for k in
        ('audit','spec','original','base','snapshot','plan'))
    decomposition.preserve_declarations(spec,original,snapshot)
    assert item['job_name'] == audit['audit_job_name']
    assert item['required_success_step'] == audit['audit_required_success_step']
    if 'workflow_path' in item:
        assert item['workflow_path'] == audit['audit_workflow_path']
    if 'key' in item:
        assert item['key'] == 'batch00_137'
    if 'original_manifests' in item:
        assert item['original_manifests'] == plan['original_manifests']
    if 'fresh_module_origins' in item:
        assert item['fresh_module_origins'] == plan['fresh_module_origins']
    for key in ('run','job','artifact_id'):
        assert type(item[key]) is int and item[key] > 0 and item[key] != OLD_ORIGIN[key]
    assert item['run'] != 41686621300
    assert re.fullmatch(r'[0-9a-f]{40}',item['source_commit'])
    assert item['source_commit'] not in (OLD_ORIGIN['source_commit'],'aaeaec3cec22467d3f0b83b1761bfb40087bb991')
    assert re.fullmatch(r'[0-9a-f]{64}',item['artifact_sha256'])
    assert item['artifact_sha256'] != OLD_ORIGIN['artifact_sha256']
    if 'actual_run_attempt' in item:
        assert type(item['actual_run_attempt']) is int and item['actual_run_attempt'] > 0
        assert item['artifact_name'] == audit['audit_archive_name_template'].format(
            run=item['run'],attempt=item['actual_run_attempt'])
    else:
        prefix = audit['audit_archive_name_template'].split('{attempt}')[0].format(run=item['run'])
        assert item['artifact_name'].startswith(prefix)
        assert re.fullmatch(r'[1-9][0-9]*',item['artifact_name'][len(prefix):])
    return dict(context,kind=KIND,expected={},prior=context['proof'],
                new_sources=set(decomposition.NEW),original_snapshot=snapshot)


def open_audit_archive(raw,digest):
    assert len(raw) <= 16*1024**2 and sha(raw) == digest
    archive = zipfile.ZipFile(io.BytesIO(raw))
    assert len(archive.namelist()) == len(set(archive.namelist())) <= 128
    for info in archive.infolist():
        p = pathlib.PurePosixPath(info.filename)
        assert not p.is_absolute() and '..' not in p.parts
        assert (info.external_attr >> 16) & 0o170000 != 0o120000
    return archive


def audit_report(context,item,raw,receipt_raw,original_raw,named):
    report = json.loads(raw)
    audit = context['audit']
    assert report['status'] == STATUS and report['kind'] == KIND
    assert report['source_commit'] == item['source_commit']
    assert report['workflow_run'] == item['run'] and report['workflow_attempt'] == item['actual_run_attempt']
    assert report['workflow_path'] == audit['audit_workflow_path'] and report['job_name'] == item['job_name']
    assert report['batch'] == '00_137' and report['original_endpoints'] == decomposition.ENDPOINTS
    assert (report['required_modules'],report['fresh_kernel_exports'],report['original_compiled_modules']) == (95,0,21)
    assert report['failed_kernel_origin'] == OLD_ORIGIN
    assert report['original_failed_job_conclusion'] == 'failure'
    assert report['original_receipt_sha256'] == sha(original_raw) == audit['original_receipt_sha256']
    assert report['receipt_sha256'] == sha(receipt_raw)
    assert report['audit_spec_sha256'] == AUDIT_SHA
    assert report['corrected_metadata_spec_sha256'] == CORRECTED_SHA
    assert report['original_plan_sha256'] == decomposition.ORIGINAL_PLAN_SHA
    assert type(report['actual_all95_output_bytes_verified']) is int
    assert audit['original_kernel_raw_output_bytes'] <= report['actual_all95_output_bytes_verified'] <= 4*1024**3
    for key in ('all95_identity_tuples_unchanged','all95_prior_origin_anchors_preserved',
                'prior_records_match_sealed_manifests','original_declarations_preserved_verbatim',
                'complete_original_axiom_profile_array_preserved','complete_original_batch_audit_complete'):
        assert report[key] is True
    assert report['old_objects_reexported_as_fresh'] is False
    assert report['whole_degree_one_large_complete'] is False
    assert report['named_original_declarations_verified'] == 313
    assert report['historical_normalized_profile_sha256'] == named['historical_normalized_profile_sha256']
    assert report['unchanged_historical_numeric_objects_reproduced'] == 9
    assert report['current_source_exports'] == sorted(decomposition.NEW)
    assert report['added_support_modules'] == sorted(decomposition.NEW-{decomposition.NAME})
    return report


def authenticate_completion(item,artifact,context,fresh,hashes,closures,api):
    assert fresh == {}, 'A zero-fresh audit cannot supply new compiled objects'
    audit,spec = context['audit'],context['spec']
    for name in spec['required_modules']:
        assert hashes[name] == spec['required_source_sha256'][name]
        assert closures[name] == spec['required_source_closure_sha256'][name]
    run = api.get('/actions/runs/'+str(item['run']))
    assert run['id'] == item['run'] and run['head_sha'] == item['source_commit']
    assert run['path'] == audit['audit_workflow_path'] and run['head_branch'] == 'rg-degree-one-large-20261103'
    job = api.get('/actions/jobs/'+str(item['job']))
    assert job['id'] == item['job'] and job['run_id'] == item['run']
    assert job['head_sha'] == item['source_commit'] and job['name'] == item['job_name']
    assert job['status'] == 'completed' and job['conclusion'] == 'success'
    assert job['run_attempt'] == item['actual_run_attempt']
    steps = [s for s in job['steps'] if s['name'] == item['required_success_step']]
    assert len(steps) == 1 and steps[0]['conclusion'] == 'success'
    assert artifact['id'] == item['artifact_id'] and artifact['name'] == item['artifact_name']
    assert artifact['digest'] == 'sha256:'+item['artifact_sha256'] and not artifact['expired']
    assert artifact['workflow_run']['id'] == item['run'] and artifact['workflow_run']['head_sha'] == item['source_commit']
    assert artifact['size_in_bytes'] <= 16*1024**2

    original_run = api.get('/actions/runs/'+str(OLD_ORIGIN['run']))
    original_job = api.get('/actions/jobs/'+str(OLD_ORIGIN['job']))
    original_artifact = api.get('/actions/artifacts/'+str(OLD_ORIGIN['artifact_id']))
    check_original_job(audit,original_job,original_run,original_artifact)
    original_zip = fetch_archive(context['proof'])
    assert len(original_zip) == audit['failed_archive_bytes']
    with open_checked_archive(original_zip) as old:
        original_raw,named = authenticate_original(context,old,records_from_log(api.logs(OLD_ORIGIN['job'])))
        logs = {n:old.read(n+'.log') for n in decomposition.NEW}

    audit_origin = {k:item[k] for k in ('run','job','source_commit','artifact_id','artifact_sha256')}
    audit_origin['repository'] = OLD_ORIGIN['repository']
    audit_zip = fetch_archive(audit_origin)
    assert len(audit_zip) == artifact['size_in_bytes']
    with open_audit_archive(audit_zip,item['artifact_sha256']) as new:
        assert not any(n.endswith(('.olean','.ilean','.server','.private','.zip')) for n in new.namelist())
        assert not any(n.startswith('Proofs.') and n.endswith('.json') for n in new.namelist())
        assert new.read('original_completed_kernel_receipt.json') == original_raw
        receipt_raw = new.read('receipt.json')
        check_zero_receipt(context,receipt_raw,original_raw)
        assert json.loads(new.read('numeric137_named_axioms.json')) == named
        for name,log in logs.items():
            assert new.read(name+'.log') == log
        resource = json.loads(new.read('resource_observer.json'))
        assert resource['status'] == 'VERIFIER_COMPLETED' and resource['exit_code'] == 0
        assert resource['mathlib_and_lean_flags_unchanged'] is True
        frontiers = json.loads(new.read('zero_fresh_frontiers.json'))
        assert check_frontiers(frontiers) == set(spec['required_modules'])
        observed = audit_report(context,item,new.read('numeric137_zero_fresh_audit.json'),
            receipt_raw,original_raw,named)
        assert json.loads(new.read('original_failed_kernel_prior_exports.json')) == context['proof']
        origin = json.loads(new.read('original_proof_origin.json'))
        assert origin == dict(failed_kernel_origin=OLD_ORIGIN,failed_job_conclusion='failure',
            kernel_step_conclusion='success',metadata_step_conclusion='failure',
            compiled_module_count=21,new_kernel_exports=0,original_receipt_sha256=audit['original_receipt_sha256'])
    return context['proof']['modules'], dict(kind=KIND,required_modules=95,
        original_endpoints=10,original_compiled_objects=21,audit_fresh_exports=0,
        original_failed_kernel_origin=OLD_ORIGIN,successful_audit_origin=audit_origin,
        original_receipt_sha256=audit['original_receipt_sha256'],audit_receipt_sha256=sha(receipt_raw),
        audit_spec_sha256=AUDIT_SHA,original_failed_job_conclusion='failure',
        old_objects_reexported_as_fresh=False,
        named_original_declarations_verified=313,complete_original_axiom_profile_array_preserved=True,
        current_source_exports=sorted(decomposition.NEW),
        additional_current_numeric_support_modules=sorted(decomposition.NEW-{decomposition.NAME}),
        actual_all95_output_bytes_verified=observed['actual_all95_output_bytes_verified'])
