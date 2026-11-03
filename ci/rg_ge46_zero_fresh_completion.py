"""Collect Ge46 through an actual failed proof origin and a separate audit.

The audit supplies no new proof objects. All 63 compiled exports keep their
original failed-job archive, while the successful audit checks their complete
178-module endpoint. Both real job statuses and both artifacts are mandatory.
"""
import json, pathlib, re

from rg_ge46_zero_fresh_audit import (ROOT, ENDPOINT, KIND, AUDIT_SPEC, AUDIT_SHA,
    OLD_ORIGIN, STATUS, CURRENT_ACCEPTED_PROFILE_METADATA, load_context, sha,
    check_original_job, authenticate_original, check_zero_receipt, open_checked_archive)
from rg_collect_exact_d1_reproductions import records_from_log
from rg_github_artifacts import fetch_archive


def completion_context(item):
    required = {'key','expected_kind','audit_spec','compiled_proof_origin','run',
        'job','source_commit','artifact_id','artifact_sha256','artifact_name',
        'job_name','required_success_step'}
    assert set(item) in (required, required | {'actual_run_attempt'})
    assert item['key'] == 'ge46_final_zero_fresh_audit' and item['expected_kind'] == KIND
    assert item['audit_spec'] == {'path':AUDIT_SPEC,'sha256':AUDIT_SHA}
    assert item['compiled_proof_origin'] == OLD_ORIGIN
    context = load_context()
    audit = context['audit']
    assert item['job_name'] == audit['audit_job_name']
    assert item['required_success_step'] == audit['required_success_step']
    for key in ('run','job','artifact_id'):
        assert type(item[key]) is int and item[key] > 0 and item[key] != OLD_ORIGIN[key]
    assert re.fullmatch(r'[0-9a-f]{40}',item['source_commit'])
    assert item['source_commit'] != OLD_ORIGIN['source_commit']
    assert re.fullmatch(r'[0-9a-f]{64}',item['artifact_sha256'])
    assert item['artifact_sha256'] != OLD_ORIGIN['artifact_sha256']
    if 'actual_run_attempt' in item:
        assert type(item['actual_run_attempt']) is int and item['actual_run_attempt'] > 0
        assert item['artifact_name'] == audit['artifact_name_template'].format(
            run=item['run'],attempt=item['actual_run_attempt'])
    else:
        prefix=audit['artifact_name_template'].split('{attempt}')[0].format(run=item['run'])
        assert item['artifact_name'].startswith(prefix)
        assert re.fullmatch(r'[1-9][0-9]*',item['artifact_name'][len(prefix):])
    return context


def audit_report(context,item,raw,receipt_raw,original_raw,hashes,closures):
    """Validate the complete zero-fresh evidence, never synthesize exports."""
    report=json.loads(raw)
    audit=context['audit']
    assert report['status']==STATUS and report['kind']==KIND
    assert report['source_commit']==item['source_commit']
    assert report['workflow_run']==item['run'] and report['workflow_attempt']==item['actual_run_attempt']
    assert report['workflow_path']==audit['audit_workflow_path'] and report['job_name']==item['job_name']
    assert report['required_modules']==178 and report['fresh_kernel_exports']==0
    assert report['original_compiled_modules']==63
    assert report['failed_kernel_origin']==OLD_ORIGIN
    assert report['original_failed_job_conclusion']=='failure'
    assert report['original_receipt_sha256']==sha(original_raw)==audit['original_receipt_sha256']
    assert report['receipt_sha256']==sha(receipt_raw)
    assert report['audit_spec_sha256']==AUDIT_SHA
    assert report['corrected_metadata_spec_sha256']==audit['corrected_spec']['sha256']
    assert report['source_endpoint_sha256']==hashes[ENDPOINT]
    assert report['source_endpoint_closure_sha256']==closures[ENDPOINT]
    assert type(report['actual_all178_output_bytes_verified']) is int
    assert audit['original_kernel_raw_output_bytes'] <= report['actual_all178_output_bytes_verified'] <= 8*1024**3
    for key in ('all178_identity_tuples_unchanged','all178_prior_origin_anchors_preserved',
                'prior_records_match_sealed_manifests',
                'original_degree_ge46_endpoint_complete'):
        assert report[key] is True
    assert report['old_objects_reexported_as_fresh'] is False
    assert report['whole_degree_one_large_complete'] is False
    return report


def authenticate_completion(item,artifact,context,fresh,hashes,closures,api):
    assert fresh == {}, 'A zero-fresh audit cannot supply fresh kernel exports'
    audit,spec=context['audit'],context['spec']
    for name,expected in spec['source_graph'].items():
        assert hashes[name]==expected['source_sha256']
        assert closures[name]==expected['source_closure_sha256']
    current_run=api.get('/actions/runs/'+str(item['run']))
    assert current_run['id']==item['run'] and current_run['head_sha']==item['source_commit']
    assert current_run['path']==audit['audit_workflow_path']
    assert current_run['head_branch']=='rg-degree-one-large-20261103'
    current_job=api.get('/actions/jobs/'+str(item['job']))
    assert current_job['id']==item['job'] and current_job['run_id']==item['run']
    assert current_job['head_sha']==item['source_commit'] and current_job['name']==item['job_name']
    assert current_job['status']=='completed' and current_job['conclusion']=='success'
    assert current_job['run_attempt']==item['actual_run_attempt']
    steps=[s for s in current_job['steps'] if s['name']==item['required_success_step']]
    assert len(steps)==1 and steps[0]['conclusion']=='success'
    assert artifact['id']==item['artifact_id'] and artifact['name']==item['artifact_name']
    assert artifact['digest']=='sha256:'+item['artifact_sha256'] and not artifact['expired']
    assert artifact['workflow_run']['id']==item['run'] and artifact['workflow_run']['head_sha']==item['source_commit']
    assert artifact['size_in_bytes']<=16*1024**2

    original_run=api.get('/actions/runs/'+str(OLD_ORIGIN['run']))
    original_job=api.get('/actions/jobs/'+str(OLD_ORIGIN['job']))
    original_artifact=api.get('/actions/artifacts/'+str(OLD_ORIGIN['artifact_id']))
    check_original_job(audit,original_job,original_run,original_artifact)
    original_zip=fetch_archive(context['proof'])
    assert len(original_zip)==audit['failed_archive_bytes']
    with open_checked_archive(original_zip,OLD_ORIGIN['artifact_sha256']) as old:
        original_raw,named=authenticate_original(context,old,records_from_log(api.logs(OLD_ORIGIN['job'])))
        actual_logs={n:old.read(n+'.log') for n in CURRENT_ACCEPTED_PROFILE_METADATA['modules']}
    audit_manifest={k:item[k] for k in ('run','job','source_commit','artifact_id','artifact_sha256')}
    audit_manifest['repository']=OLD_ORIGIN['repository']
    audit_zip=fetch_archive(audit_manifest)
    assert len(audit_zip)==artifact['size_in_bytes']
    with open_checked_archive(audit_zip,item['artifact_sha256'],16*1024**2) as new:
        assert not any(n.endswith(('.olean','.ilean','.server','.private','.zip')) for n in new.namelist())
        assert not any(n.startswith('Proofs.') and n.endswith('.json') for n in new.namelist())
        assert new.read('original_completed_kernel_receipt.json')==original_raw
        receipt_raw=new.read('receipt.json')
        check_zero_receipt(context,receipt_raw,original_raw)
        assert json.loads(new.read('current_accepted_named_profiles.json'))==named
        for name,log in actual_logs.items():assert new.read(name+'.log')==log
        resource=json.loads(new.read('resource_observer.json'))
        assert resource['status']=='VERIFIER_COMPLETED' and resource['exit_code']==0
        assert resource['mathlib_and_lean_flags_unchanged'] is True
        frontier=json.loads(new.read('zero_fresh_frontier.json'))
        assert frontier['fresh_modules']==[] and frontier['required_modules']==178
        assert frontier['verified_prior_objects']==178 and frontier['within_bound'] is True
        observed=audit_report(context,item,new.read('ge46_zero_fresh_audit.json'),
            receipt_raw,original_raw,hashes,closures)
        old_manifest=json.loads(new.read('original_failed_final_prior_exports.json'))
        assert old_manifest==context['proof']
        origin=json.loads(new.read('original_proof_origin.json'))
        assert origin==dict(failed_kernel_origin=OLD_ORIGIN,failed_job_conclusion='failure',
            kernel_step_conclusion='success',metadata_step_conclusion='failure',
            compiled_module_count=63,new_kernel_exports=0,
            original_receipt_sha256=audit['original_receipt_sha256'])
    return context['proof']['modules'], dict(kind=KIND,required_modules=178,
        original_compiled_objects=63,audit_fresh_exports=0,
        original_failed_kernel_origin=OLD_ORIGIN,successful_audit_origin=audit_manifest,
        original_receipt_sha256=audit['original_receipt_sha256'],audit_receipt_sha256=sha(receipt_raw),
        audit_spec_sha256=AUDIT_SHA,original_failed_job_conclusion='failure',
        old_objects_reexported_as_fresh=False,
        actual_all178_output_bytes_verified=observed['actual_all178_output_bytes_verified'])
