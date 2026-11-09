#!/usr/bin/env python3
"""Post-run archive authentication, not a new Lean execution.

Download only fixed successful producers. Stream-check fresh objects and bind
all sources, ordered axiom profiles and reused origins. Distinguish locally
rehashing fresh objects from the producer's validation of reused objects.
"""
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import urllib.request
import zipfile

ROOT=Path(__file__).resolve().parent.parent
OUT=ROOT/'rg_completion_audit_20261109'
REPO='RhudeJJJJ/formal-conjectures'
ORIGINAL='15d45e8d3ed3bacaf3afe7d85488a42f08302d76'
INV_SHA='22c745d4fdb281e8cc2172ffcc3b975005da4fb4777e9021e85f46bbc9a665e0'
MATHLIB='0df444a360eaa60ab8c11dca51a86af692955474'
LEANCERT='621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED={'propext','Classical.choice','Quot.sound'}
NAMED=re.compile(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
BATCH_HEAD='da50fcb4764d92a7fc4eb6f31ee727697ac561f6'
BATCH_RUN=42640095601
# label, run, job, artifact, archive bytes, SHA256, workflow head
TARGETS=[
 ('001',BATCH_RUN,129238619067,13691863491,267264878,'b6127c8ceed0306c4a1cfac7e90d959621ba6edb79f9a0a7e487cf8f30e4eca3',BATCH_HEAD),
 ('002',BATCH_RUN,129238619177,13690264897,284689307,'8e23422142af46479ef914ed29e9ed45f995242ef30f01479a8173551b4a4190',BATCH_HEAD),
 ('003',BATCH_RUN,129238619071,13692398461,274463400,'8bce886fcfb8e2db3d68b10ea32c39c2644b710bb438e6fc162545b9feb507aa',BATCH_HEAD),
 ('004',BATCH_RUN,129238618579,13692913410,324163154,'6e33e7e1ba2cc4a52ddcaa83d0040177ed89be0492ebc5ad77bada08b7366746',BATCH_HEAD),
 ('005',BATCH_RUN,129238619267,13695445951,326674140,'db48f37d1d3f5b544ccfb6db8b140acff53c15b680eae39e974b2350754427ad',BATCH_HEAD),
 ('006',BATCH_RUN,129238619240,13695166921,343975888,'bc470000bbd2c45de3f5106b428993d839bccb0bcabb920f728cbb5f6c2e5dfc',BATCH_HEAD),
 ('008',BATCH_RUN,129238619059,13695345148,336620465,'41c412d0a93b40215821af1dd9de9ebc0b852d8daa982059c19066b1e4c9312e',BATCH_HEAD),
 ('024',42644500373,129253983079,13689000052,25996857,'c53eb547c8772552b8304cadf837be5e1c2c4a06eab905a5527f743fc0b00567','bf7d97a3bab575bafca3890c932ab5fecb006f0d'),
 ('case0493',42673973938,129351274543,13699936774,8379312,'595ada35c0ead01c51cd9690c86432c21e4482f05f18760ac3e6a5d92406ac61','7055056815ad29380647a306b9e547f3200c0342'),
]

def sha(raw):return hashlib.sha256(raw).hexdigest()
def api(path):
    request=urllib.request.Request('https://api.github.com/repos/'+REPO+'/'+path,
        headers={'Authorization':'Bearer '+os.environ['GITHUB_TOKEN'],
                 'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28'})
    with urllib.request.urlopen(request,timeout=180) as response:return json.load(response)
def dump(path,value):path.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def original(relative):
    return subprocess.check_output(['git','show',ORIGINAL+':'+relative],cwd=ROOT)

def ordered_names(raw):
    text=raw.decode();namespaces=re.findall(r'^namespace\s+(\S+)\s*$',text,re.M)
    assert len(namespaces)==1
    tokens=re.findall(r'^\s*#print\s+axioms\s+(\S+)\s*$',text,re.M)
    assert tokens and len(tokens)==len(set(tokens))
    return [t[7:] if t.startswith('_root_.') else t if t.startswith(namespaces[0]+'.')
            else namespaces[0]+'.'+t for t in tokens]

def download(target):
    label,run_id,job_id,artifact_id,size,digest,head=target
    directory=OUT/label;directory.mkdir(parents=True,exist_ok=True)
    run=api(f'actions/runs/{run_id}');job=api(f'actions/jobs/{job_id}')
    artifact=api(f'actions/artifacts/{artifact_id}')
    assert run['head_sha']==head and job['run_id']==run_id
    assert job['status']=='completed' and job['conclusion']=='success'
    assert all(step['conclusion']=='success' for step in job['steps']),label
    # The matrix run may contain other unsuccessful jobs. Bind this exact job.
    assert artifact['id']==artifact_id and not artifact['expired']
    assert artifact['size_in_bytes']==size and artifact['digest']=='sha256:'+digest
    assert artifact['workflow_run']['id']==run_id and artifact['workflow_run']['head_sha']==head
    dump(directory/'native_run.json',run);dump(directory/'native_job.json',job)
    dump(directory/'native_artifact.json',artifact)
    url=f'https://api.github.com/repos/{REPO}/actions/artifacts/{artifact_id}/zip'
    request=urllib.request.Request(url,headers={'Authorization':'Bearer '+os.environ['GITHUB_TOKEN']})
    archive=ROOT/('rg-audit-'+label+'.zip');h=hashlib.sha256();count=0
    with urllib.request.urlopen(request,timeout=180) as response, archive.open('wb') as stream:
        while chunk:=response.read(1024*1024):h.update(chunk);count+=len(chunk);stream.write(chunk)
    assert count==size and h.hexdigest()==digest
    return directory,archive

def audit(target):
    label,run_id,job_id,artifact_id,size,digest,head=target
    directory,archive=download(target)
    with zipfile.ZipFile(archive) as z:
        members=z.namelist();assert len(members)==len(set(members))
        assert all(not p.startswith('/') and '..' not in Path(p).parts for p in members)
        def read(path):return z.read(path)
        def load(path):return json.loads(read(path))
        invraw=read('frozen_validation/rg_middle_residual_batch_inventory_20261109.json')
        assert sha(invraw)==INV_SHA
        inv=json.loads(invraw);priors=inv['expected_prior_rows']
        is_case=label=='case0493'
        if is_case:
            generator=ROOT/'ci/rg_middle_case0493_split_20261109.py'
            assert generator.read_bytes()==read('frozen_validation/'+generator.name)
            g=load_module('case_generator',generator)
            candidates,expected_sources,evidence,_=g.plan(invraw,original)
            assert load('generated_source/generated_source_manifest.json')==evidence
            row=dict(endpoint=evidence['endpoint'],source_sha256=evidence['source_sha256'],
                source_closure_sha256=evidence['source_closure_sha256'],fresh_modules=evidence['fresh_modules'],
                ordered_axiom_names=evidence['ordered_axiom_names'],source_count=50,prior_count=45,
                fresh_count=5,fresh_axiom_print_count=51,key_count=1)
        else:
            original_row=next(r for r in inv['batches'] if r['index']==label);row=original_row
            if label=='024':
                manifest=load('frozen_validation/rg_middle_residual_batch024_split_inventory_20261109.json')
                assert manifest['original_inventory_sha256']==INV_SHA
                assert manifest['expected_prior_rows']==priors
                row=manifest['batches'][0];assert row['index']=='024'
        receipt=load('receipt.json');diagnostics=load('diagnostics_records.json')['modules']
        records={r['module']:r for r in diagnostics};assert len(records)==len(diagnostics)
        fresh=set(row['fresh_modules'])
        assert set(records)==set(priors)|fresh
        assert all(records[name]==record for name,record in priors.items())
        assert receipt['scope']=='EXPLICIT_EXTENSION_CLOSURE' and receipt['endpoints']==[row['endpoint']]
        assert receipt['mathlib']==MATHLIB and receipt['leancert']==LEANCERT
        assert 'version 4.33.1,' in receipt['lean']
        assert receipt['global_rg']=='NOT_PROVED' and receipt['complete_submission']=='NOT_SUBMITTED'
        assert set(receipt['modules'])==set(row['source_closure_sha256'])
        sources={};dependencies={};closures={}
        for relative,expected in row['source_sha256'].items():
            raw=read('generated_source/'+relative);assert sha(raw)==expected,relative
            name=relative.removeprefix('Proofs/RG_Lean_20261019/').removesuffix('.lean').replace('/','.')
            sources[name]=raw
            assert not re.search(rb'\b(sorry|admit|native_decide)\b|^\s*axiom\s',raw,re.M)
            dependencies[name]=sorted(set(re.findall(r'^\s*(?:public\s+)?import\s+(Proofs\.[\w.]+)\s*$',raw.decode(),re.M)))
            if is_case:assert raw==expected_sources[name]
            elif label!='024':assert raw==original(relative)
        def visit(name):
            if name in closures:return
            for dep in dependencies[name]:visit(dep)
            closures[name]=sha(json.dumps([name,sha(sources[name]),MATHLIB,LEANCERT,
                [(dep,closures[dep]) for dep in dependencies[name]]],separators=(',',':')).encode())
        visit(row['endpoint']);assert closures==row['source_closure_sha256']
        assert len(sources)==row['source_count']
        output_module=load_module('outputs',ROOT/'Proofs/RG_Lean_20261019/module_outputs.py')
        fresh_bytes=0;objects=[];printed={}
        for name,record in receipt['modules'].items():
            assert record==records[name] and record['module']==name
            assert record['source_sha256']==sha(sources[name]) and record['source_closure_sha256']==closures[name]
            assert record['axiom_profiles'] and all(set(p)<=ALLOWED for p in record['axiom_profiles'])
            assert (record['mode']=='FRESH_KERNEL_EXPORT')==(name in fresh)
            if name not in fresh:continue
            assert 'origin' not in record and 'transport_capsule' not in record
            assert load(name+'.json')==record
            assert type(record['seconds']) in (int,float) and math.isfinite(record['seconds']) and record['seconds']>=0
            for relative,expected,expected_size in output_module.output_members(name,record):
                with z.open(relative) as stream:actual=hashlib.file_digest(stream,'sha256').hexdigest()
                assert actual==expected,relative
                actual_size=z.getinfo(relative).file_size
                assert expected_size is None or actual_size==expected_size
                fresh_bytes+=actual_size;objects.append(dict(path=relative,sha256=actual,bytes=actual_size))
            log=read(name+'.log').decode()
            assert not re.search(r'\b(error|warning)(?:\([^\n]*?\))?:',log)
            matches=list(NAMED.finditer(log));expected_names=ordered_names(sources[name])
            assert expected_names==row['ordered_axiom_names'][name]
            assert [match[1] for match in matches]==expected_names
            profiles=[sorted(set(a.strip() for a in (m[2] or '').split(',') if a.strip())) for m in matches]
            assert all(set(p)<=ALLOWED for p in profiles)
            grouped=[p for m,p in zip(matches,profiles) if m[2] is not None]
            grouped += [p for m,p in zip(matches,profiles) if m[2] is None]
            assert grouped==record['axiom_profiles'];printed[name]=expected_names
        assert len(fresh)==row['fresh_count']
        assert sum(map(len,printed.values()))==row['fresh_axiom_print_count']
        keys_source=sources['Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteKeysData'].decode()
        def keys_of(index):
            body,=re.findall(r'^def keys'+index+r' : List Key := \[(.*?)\]$',keys_source,re.M)
            return [tuple(map(int,t)) for t in re.findall(r'⟨(\d+),(\d+),(\d+),(\d+)⟩',body)]
        keys=[(10,10,2,2)] if is_case else keys_of(label)
        assert len(keys)==row['key_count'] and len(set(keys))==len(keys)
        if is_case:
            assert keys[0] in keys_of('009')
            native_check=load('case0493_validation.json')
            assert native_check['status']=='FRESH_KERNEL_RECEIPT_CHECKED'
        if label=='024':
            gen=load_module('old_split',ROOT/'ci/rg_middle_residual_sample_split_20261109.py')
            for name,raw in sources.items():
                relative='Proofs/RG_Lean_20261019/'+name.replace('.','/')+'.lean'
                old=original(relative)
                assert sha(old)==original_row['source_sha256'][relative]
                if name in row['changed_source_modules']:
                    candidate,preservation=gen.split_source(old,name.split('Spectrum')[-1])
                    assert candidate==raw and preservation==row['source_preservation'][name]
                else:assert raw==old
        resource=load('resource_observer.json')
        assert resource['status']=='VERIFIER_COMPLETED' and resource['exit_code']==0
        assert resource['mathlib_and_lean_flags_unchanged'] is True
        assert resource['samples'] and all(s['available_bytes']>=2048*1024**2 for s in resource['samples'] if s['lean_processes'])
        report=dict(schema='rg_independent_post_run_archive_audit_v1',status='PASS',label=label,
            run=run_id,job=job_id,artifact=artifact_id,workflow_head=head,archive_sha256=digest,
            archive_bytes=size,archive_members=len(members),endpoint=row['endpoint'],source_modules=len(sources),
            fresh_modules=len(fresh),required_prior_modules=row['prior_count'],all_prior_records=len(priors),
            fresh_object_bytes=fresh_bytes,ordered_named_axiom_profiles=sum(map(len,printed.values())),
            only_standard_axioms=True,keys=keys,key_count=len(keys),object_checks=objects,
            endpoint_source_closure_sha256=closures[row['endpoint']],maximum_aggregate_lean_rss=resource['maximum_aggregate_lean_rss'],
            module_seconds={name:records[name]['seconds'] for name in sorted(fresh)},
            original_propositions_and_numerical_data_preserved=True,prior_object_bytes_rehashed_by_this_audit=False,
            prior_records_match_frozen_actual_origins=True,native_producer_receipt_validation_pass=True,
            audit_is_not_new_kernel_execution=True,whole_batch009_complete=False,
            complete_middle_family=False,global_rg_complete=False)
        dump(directory/'authentication.json',report)
        dump(directory/'fresh_native_records.json',{name:records[name] for name in sorted(fresh)})
        dump(directory/'named_axiom_profiles.json',printed)
        # Retain the newly proved source texts, without redistributing fonts or opaque binaries.
        if is_case:
            for name,raw in sources.items():
                target=directory/'sources'/(name.replace('.','/')+'.lean')
                target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
        baseline=keys_of('000')
        print('ARCHIVE_AUDIT_PASS '+json.dumps({k:report[k] for k in ('label','key_count','fresh_modules','ordered_named_axiom_profiles')}),flush=True)
    archive.unlink()
    return report,baseline

def main():
    OUT.mkdir(exist_ok=True)
    reports=[];baseline=None
    # Authenticate the new proof first, then the already-completed batch producers.
    for target in [TARGETS[-1],TARGETS[-2]]+TARGETS[:-2]:
        report,old=audit(target);reports.append(report)
        assert baseline is None or baseline==old
        baseline=old
    assert len(baseline)==52 and len(set(baseline))==52
    union=set(baseline)
    for report in reports:
        keys={tuple(k) for k in report['keys']}
        assert not (union&keys),report['label']
        union.update(keys)
    assert len(union)==433
    summary=dict(status='PASS',new_original_case0493_kernel_verified=True,
        previously_authenticated_batch000_keys=52,newly_audited_completed_batch_keys=380,
        newly_implemented_and_kernel_verified_keys=1,authenticated_key_union=433,total_residual_keys=1232,
        outstanding_residual_keys=799,whole_batch009_complete=False,
        complete_original_families=['degreeOneSmall','degreeOneLarge','degreeGeFourSmall','degreeGeFortysix'],
        remaining_original_families=['degreeOneMiddle','degreeTwoThree','degreeFourToFortyfive'],
        complete_middle_family=False,global_rg_complete=False,full_upstream_proof_submitted=False,
        reports=[dict(label=r['label'],sha256=sha((OUT/r['label']/'authentication.json').read_bytes())) for r in reports])
    dump(OUT/'summary.json',summary)
    print('RG_COMPLETION_AUDIT_PASS '+json.dumps(summary),flush=True)

if __name__=='__main__':main()
