"""Complete three exact original batches while preserving authenticated priors.

Every batch retains all ten original endpoints. Already checked modules keep
their failed-job archive origins; only the sealed remainder is fresh. A full
successful receipt and all ten historical output identities are mandatory.
"""
import argparse, hashlib, json, os, pathlib, re, subprocess, sys
from rg_original_d1_numeric_reproduction import load_plan
from rg_plan_exact_degree_one_large import source_closure

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCES = ROOT / 'Proofs/RG_Lean_20261019'
BUILD = SOURCES / 'build/extension'
EXPORTS = SOURCES / 'build/fresh_exports'
sys.path.insert(0, str(SOURCES))
from module_outputs import output_members

PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED = {'propext','Classical.choice','Quot.sound'}
NUMERIC = 'ci/rg_d1_required_numeric_batches_20261103.json'
NUMERIC_SHA = 'f47334108b563ae5e20f15fc07b2e4589f6d6e7f49e308bfdb8b4301e689e18e'
ORIGINAL_RUN = 41686621300
ORIGINAL_COMMIT = 'aaeaec3cec22467d3f0b83b1761bfb40087bb991'
PARTIALS = {
    '00_139': dict(job=126095234749, artifact_id=13271197315,
        artifact_sha256='0082ee00e4b104ff4e392f65fcb0462fb17d1325071b07fa028fdb680248a38f',
        indices=[1390,1391,1392,1393]),
    '00_156': dict(job=126095228744, artifact_id=13265702201,
        artifact_sha256='2d3fe3a3cad629c02a85b735460e4e4f6fb49ad60e9664b4fd4e4001daf6254d',
        indices=[1560,1561,1562,1563,1564,1565]),
    '00_164': dict(job=126095228779, artifact_id=13266625964,
        artifact_sha256='45cc7a292bab0958bc264895d97b62d9b192c46b29718f29e80fb178bf640a03',
        indices=[1640,1641,1642,1644]),
}


def sha(raw): return hashlib.sha256(raw).hexdigest()


def bound(relative, digest):
    path = pathlib.PurePosixPath(relative)
    assert path.is_relative_to('ci') and '..' not in path.parts
    raw = (ROOT / path).read_bytes()
    assert sha(raw) == digest, ('Changed sealed original input', relative)
    return json.loads(raw)


def identity(name, row):
    return (row['source_sha256'],row['source_closure_sha256'],row['output_sha256'],
            row['axiom_profiles'],tuple(sorted(output_members(name,row))))


def partial_origin(manifest):
    origin = {k:manifest[k] for k in ('repository','run','job','source_commit','artifact_id','artifact_sha256')}
    origin['context'] = manifest['origin_context']
    return origin


def load_remainder(batch):
    assert batch in PARTIALS
    path = ROOT / 'ci/rg_d1_numeric_remainder_20261103' / ('batch'+batch+'.json')
    spec = json.loads(path.read_bytes())
    assert spec['kind'] == 'EXACT_ORIGINAL_NUMERIC_REMAINDER_WITH_AUTHENTICATED_PARTIAL_PRIORS'
    assert spec['batch'] == batch
    assert (spec['workers'],spec['module_timeout'],spec['memory_reserve_mib']) == (1,1200,2048)
    assert spec['required_module_count'] == 84
    assert spec['original_numeric_spec'] == NUMERIC and spec['original_numeric_spec_sha256'] == NUMERIC_SHA
    numeric = bound(NUMERIC,NUMERIC_SHA)
    original = next(row for row in numeric['jobs'] if row['batch']==batch)
    assert spec['original_plan'] == original['plan']
    assert spec['original_plan_sha256'] == original['plan_sha256']
    bound(original['plan'],original['plan_sha256'])
    plan, expected = load_plan(ROOT / original['plan'])
    assert plan['scope'] == 'original00_leaves' and plan['workers'] == 2
    assert len(plan['endpoints']) == len(expected) == 10
    assert spec['endpoints'] == plan['endpoints']
    partial = bound(spec['partial_manifest'],spec['partial_manifest_sha256'])
    known = PARTIALS[batch]
    assert partial['repository'] == 'RhudeJJJJ/formal-conjectures'
    assert partial['run'] == ORIGINAL_RUN and partial['source_commit'] == ORIGINAL_COMMIT
    for key in ('job','artifact_id','artifact_sha256'):
        assert partial[key] == known[key]
    assert partial['mathlib'] == PIN and partial['lean_version'] == '4.33.1'
    context = partial['origin_context']
    assert context['kind'] == 'AUTHENTICATED_ORIGINAL_NUMERIC_PARTIAL_EXPORTS_FROM_FAILED_JOB'
    assert context['workflow_job_conclusion'] == 'failure' and context['endpoint_complete'] is False
    assert context['archived_full_scope_receipt_available'] is False
    assert context['original_batch'] == batch
    assert context['original_plan'] == original['plan']
    assert context['original_plan_sha256'] == original['plan_sha256']
    prior = {f'Proofs.RadenkovicGutmanD1Long00Leaf{i:05d}' for i in known['indices']}
    assert set(partial['modules']) == prior == set(spec['prior_original_modules'])
    assert len(spec['prior_original_modules']) == len(prior)
    fresh = set(expected) - prior
    assert sorted(fresh) == spec['fresh_modules']
    assert len(fresh) == spec['fresh_module_count'] == (4 if batch=='00_156' else 6)
    assert prior | fresh == set(expected) and not prior & fresh
    for name,row in partial['modules'].items():
        assert row['module'] == name and row['mode'] == 'FRESH_KERNEL_EXPORT'
        assert identity(name,row) == identity(name,expected[name])
    return spec, plan, expected, partial


def current_scope(spec, plan, expected):
    hashes, closures = {}, {}
    for endpoint in plan['endpoints']:
        h,_,c = source_closure(endpoint)
        hashes.update(h); closures.update(c)
    assert len(hashes) == spec['required_module_count'] == 84
    base = bound(plan['base_manifest'],plan['base_manifest_sha256'])
    assert set(hashes)-set(base['modules']) == set(expected)
    for name,row in expected.items():
        assert hashes[name] == row['source_sha256']
        assert closures[name] == row['source_closure_sha256']
    return hashes,closures


def local_path(relative):
    p = pathlib.PurePosixPath(relative)
    assert not p.is_absolute() and '..' not in p.parts
    full = BUILD / p
    assert full.resolve().is_relative_to(BUILD.resolve())
    return full


def complete_receipt(spec, plan, expected, partial, hashes, closures, raw,
                     read_record, open_member, member_size):
    receipt = json.loads(raw)
    assert receipt['scope'] == 'EXPLICIT_EXTENSION_CLOSURE'
    assert receipt['endpoints'] == plan['endpoints'] == spec['endpoints']
    assert receipt['mathlib'] == PIN and receipt['leancert'] == LC
    assert 'version 4.33.1,' in receipt['lean']
    assert set(receipt['modules']) == set(hashes) == set(closures)
    assert len(receipt['modules']) == 84
    actual_fresh = {n for n,r in receipt['modules'].items() if r['mode']=='FRESH_KERNEL_EXPORT'}
    assert actual_fresh == set(spec['fresh_modules'])
    for name,row in receipt['modules'].items():
        assert row['module'] == name
        assert (row['source_sha256'],row['source_closure_sha256']) == (hashes[name],closures[name])
        assert row['mode'] in ('FRESH_KERNEL_EXPORT','PRIOR_VERIFIED_JOB_EXPORT')
        assert row['axiom_profiles'] or name.startswith('LeanCert.')
        assert all(set(p)<=ALLOWED for p in row['axiom_profiles'])
    logical = 0
    for name,old in expected.items():
        row = receipt['modules'][name]
        assert row == json.loads(read_record(name+'.json'))
        assert identity(name,row) == identity(name,old), ('Original complete-batch identity differs',name)
        if name in partial['modules']:
            assert row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'
            assert row['origin'] == partial_origin(partial), ('Partial original origin was changed',name)
        else:
            assert row['mode'] == 'FRESH_KERNEL_EXPORT'
        for relative,digest,size in output_members(name,row):
            p = pathlib.PurePosixPath(relative)
            assert not p.is_absolute() and '..' not in p.parts
            actual_size = member_size(relative)
            assert size is None or size == actual_size
            with open_member(relative) as stream:
                assert hashlib.file_digest(stream,'sha256').hexdigest() == digest, (name,relative)
            logical += actual_size
    assert logical <= 8*1024**3
    return receipt, logical


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--batch',choices=sorted(PARTIALS),required=True)
    parser.add_argument('--phase',choices=('source','restore','before','kernel','after'),required=True)
    args = parser.parse_args()
    spec,plan,expected,partial = load_remainder(args.batch)
    hashes,closures = current_scope(spec,plan,expected)
    EXPORTS.mkdir(parents=True,exist_ok=True)
    if args.phase=='source':
        print(json.dumps(dict(status='FULL_ORIGINAL_SOURCE_SCOPE_AND_PARTIAL_ORIGINS_BOUND_NOT_KERNEL_PROOF',
            batch=args.batch,required_modules=84,original_endpoints=10,
            prior_original_modules=len(partial['modules']),expected_fresh_modules=spec['fresh_modules'])),flush=True)
    elif args.phase=='restore':
        subprocess.run([sys.executable,'-B','ci/rg_restore_complete_scope.py',
            '--manifest',plan['base_manifest'],'--build-directory',str(BUILD)],cwd=ROOT,check=True)
        subprocess.run([sys.executable,'-B','ci/rg_restore_job_exports.py',
            '--manifest',spec['partial_manifest'],'--build-directory',str(BUILD)],cwd=ROOT,check=True)
    elif args.phase=='before':
        observed=set()
        for endpoint in plan['endpoints']:
            subprocess.run([sys.executable,'-B','ci/rg_restore_with_kernel_fallback.py',
                '--plan','ci/rg_empty_restore_plan.json','--build-directory',str(BUILD),
                '--endpoint',endpoint,'--max-fresh',str(spec['fresh_module_count']),'--preflight-only'],cwd=ROOT,check=True)
            frontier=json.loads((BUILD/'bounded_kernel_fallback_plan.json').read_bytes())
            assert set(frontier['fresh_modules']) <= set(spec['fresh_modules'])
            observed.update(frontier['fresh_modules'])
        assert observed==set(spec['fresh_modules'])
        for name in partial['modules']:
            row=json.loads((BUILD/(name+'.json')).read_bytes())
            assert row['mode']=='PRIOR_VERIFIED_JOB_EXPORT' and row['origin']==partial_origin(partial)
            assert identity(name,row)==identity(name,expected[name])
        print(json.dumps(dict(status='EXACT_ORIGINAL_REMAINDER_FRONTIER_NO_NEW_KERNEL_PROOF',
            batch=args.batch,original_endpoints=plan['endpoints'],fresh_modules=sorted(observed),
            authenticated_original_prior_modules=sorted(partial['modules']))),flush=True)
    elif args.phase=='kernel':
        command=[sys.executable,'-B','ci/rg_observed_kernel_verify.py','--memory-reserve-mib','2048',
                 '--','--mathlib-project',str(ROOT)]
        for endpoint in plan['endpoints']:command.extend(['--endpoint',endpoint])
        command.extend(['--workers','1','--module-timeout','1200','--resume'])
        subprocess.run(command,cwd=ROOT,check=True)
    else:
        raw=(BUILD/'receipt.json').read_bytes()
        receipt,logical=complete_receipt(spec,plan,expected,partial,hashes,closures,raw,
            lambda p:local_path(p).read_bytes(),lambda p:local_path(p).open('rb'),
            lambda p:local_path(p).stat().st_size)
        checkout=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
        assert checkout==os.environ['GITHUB_SHA']
        report=dict(status='COMPLETE_ORIGINAL_NUMERIC_BATCH_VERIFIED_WITH_PRESERVED_PARTIAL_ORIGINS',
            batch=args.batch,required_modules=len(receipt['modules']),original_endpoints=plan['endpoints'],
            original_plan=spec['original_plan'],original_plan_sha256=spec['original_plan_sha256'],
            prior_original_modules=sorted(partial['modules']),fresh_modules=spec['fresh_modules'],
            partial_original_origin=partial_origin(partial),partial_manifest_sha256=spec['partial_manifest_sha256'],
            source_commit=checkout,workflow_run=int(os.environ['GITHUB_RUN_ID']),
            workflow_attempt=int(os.environ['GITHUB_RUN_ATTEMPT']),receipt_sha256=sha(raw),
            all_ten_original_output_identities_verified=True,verified_output_bytes=logical,
            old_failed_job_status='UNCHANGED_FAILURE',prior_records_relabelled_as_fresh=False,
            whole_degree_one_large='NOT_ESTABLISHED_BY_THIS_BATCH')
        (EXPORTS/'original_numeric_complete_recovery.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report),flush=True)


if __name__=='__main__':main()
