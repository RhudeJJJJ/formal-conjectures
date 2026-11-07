#!/usr/bin/env python3
"""Independent bounded byte/receipt review; never calls the completion checker."""
from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import hashlib
import json
import re
import zipfile

BASE = Path('/workspace/scratch/406169dbc070/rg_resume_20261105/middle_next')
ACTUAL = BASE / 'ci_review/candidate/actual'
OUT = Path(__file__).resolve().parent
ENDPOINT = 'Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate030'
REPORT_SHA = '4548ffb0a0b99c6ceed6bc283a2c4611bd4784fb541c16e36b942b1050d06400'
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def without_comments(code):
    depth = 0
    result = []
    i = 0
    while i < len(code):
        if code[i:i+2] == '/-':
            depth += 1
            result.append('  ')
            i += 2
        elif depth and code[i:i+2] == '-/':
            depth -= 1
            result.append('  ')
            i += 2
        elif not depth and code[i:i+2] == '--':
            end = code.find('\n', i)
            if end < 0:
                end = len(code)
            result.append(' ' * (end - i))
            i = end
        else:
            result.append(code[i] if not depth or code[i] == '\n' else ' ')
            i += 1
    assert depth == 0
    return ''.join(result)

def source_profiles(code):
    namespaces = re.findall(r'^namespace ([\w.]+)\s*$', code, re.M)
    assert len(namespaces) <= 1
    result = []
    for name in re.findall(r'^#print axioms ([\w.]+)\s*$', code, re.M):
        if name.startswith('Gebendorfer.'):
            result.append(name)
        else:
            assert namespaces, name
            result.append(namespaces[0] + '.' + name)
    return result

report_bytes = (ACTUAL / 'anchor030_continuation_authentication.json').read_bytes()
assert sha(report_bytes) == REPORT_SHA
report = json.loads(report_bytes)
assert report['status'] == 'ACTUAL_ORIGINAL_ANCHOR030_CONTINUATION_KERNEL_CLOSURE_AUTHENTICATED'
assert report['full_original_endpoint_success_authenticated'] is True
assert report['full_degree_one_middle_family_claim'] is False
assert report['global_rg_claim'] is False
assert report['run'] == 42052127520 and report['job'] == 127330696809
for name, digest in report['native_capture_sha256'].items():
    assert sha((ACTUAL / name).read_bytes()) == digest, name
run = json.loads((ACTUAL / 'run.json').read_bytes())
jobs = json.loads((ACTUAL / 'jobs.json').read_bytes())
job = next(j for j in jobs['jobs'] if j['id'] == report['job'])
assert run['id'] == report['run'] and run['conclusion'] == 'success'
assert job['run_id'] == run['id'] and job['conclusion'] == 'success'
assert run['head_sha'] == job['head_sha'] == report['source_commit']
assert job['name'] == report['external_fixed_binding']['job_name']
assert all(step['conclusion'] == 'success' for step in job['steps'])
artifact_bytes = (ACTUAL / 'artifact.zip').read_bytes()
assert 'sha256:' + sha(artifact_bytes) == report['artifact']['digest']
assert len(artifact_bytes) == report['artifact']['size_in_bytes']
graph_bytes = (BASE / 'source_scope/anchor030_source_graph.json').read_bytes()
assert sha(graph_bytes) == report['current_original_source_graph_sha256']
graph = json.loads(graph_bytes)
audit = report['archive_audit']
profile_pattern = re.compile(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", re.S)

with zipfile.ZipFile(ACTUAL / 'artifact.zip') as archive:
    names = archive.namelist()
    assert len(names) == len(set(names)) == 501
    assert archive.testzip() is None
    receipt_bytes = archive.read('receipt.json')
    assert sha(receipt_bytes) == audit['receipt_sha256']
    receipt = json.loads(receipt_bytes)
    assert receipt['endpoints'] == [ENDPOINT]
    assert receipt['mathlib'] == PIN and receipt['leancert'] == LC
    assert receipt['global_rg'] == 'NOT_PROVED' and receipt['complete_submission'] == 'NOT_SUBMITTED'
    modules = receipt['modules']
    assert len(modules) == 281
    assert Counter(row['mode'] for row in modules.values()) == {'PRIOR_VERIFIED_JOB_EXPORT': 209, 'FRESH_KERNEL_EXPORT': 72}
    fresh = {name: row for name, row in modules.items() if row['mode'] == 'FRESH_KERNEL_EXPORT'}
    prior = {name: row for name, row in modules.items() if row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT'}
    assert set(fresh) == set(audit['modules']) == set(audit['completed_fresh_modules'])
    diagnostics = json.loads(archive.read('diagnostics_records.json'))['modules']
    assert len(diagnostics) == 524 and len({r['module'] for r in diagnostics}) == 524
    diagnostic_rows = {r['module']: r for r in diagnostics}
    assert Counter(row['mode'] for row in diagnostics) == {'PRIOR_VERIFIED_JOB_EXPORT': 452, 'FRESH_KERNEL_EXPORT': 72}
    assert all(row == diagnostic_rows[name] for name, row in modules.items())
    source_manifest = json.loads(archive.read('generated_source/generated_source_manifest.json'))
    assert source_manifest['endpoint'] == ENDPOINT and source_manifest['anchor_index'] == 30
    code, deps, source_hashes = {}, {}, {}
    for name, row in modules.items():
        assert row['module'] == name
        path = 'Proofs/RG_Lean_20261019/' + name.replace('.', '/') + '.lean'
        raw = archive.read('generated_source/' + path)
        digest = sha(raw)
        assert digest == row['source_sha256'] == source_manifest['source_sha256'][path] == graph['source_sha256'][name]
        source_hashes[name] = digest
        code[name] = without_comments(raw.decode())
        assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s', code[name], re.M), name
        deps[name] = sorted(set(re.findall(r'^\s*(?:public\s+)?import\s+((?:Proofs|LeanCert)\.[\w.]+)\s*$', code[name], re.M)))
        assert deps[name] == graph['source_dependencies'][name]
        assert row['axiom_profiles'] and all(set(p) <= ALLOWED for p in row['axiom_profiles'])
        if row['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT':
            assert row['origin']['repository'] == 'RhudeJJJJ/formal-conjectures'
            assert all(row['origin'][k] for k in ['run','job','source_commit','artifact_id','artifact_sha256'])
    assert len(source_manifest['source_sha256']) == 281
    closures, active = {}, set()
    def closure(name):
        if name not in closures:
            assert name not in active and name in modules
            active.add(name)
            payload = [name, source_hashes[name], PIN, LC, [(d, closure(d)) for d in deps[name]]]
            closures[name] = sha(json.dumps(payload, separators=(',', ':')).encode())
            active.remove(name)
        return closures[name]
    closure(ENDPOINT)
    assert set(closures) == set(modules)
    assert all(closures[n] == modules[n]['source_closure_sha256'] == graph['source_closure_sha256'][n] for n in modules)
    bytes_read = profiles_read = 0
    reviewed_fresh = []
    for name, row in sorted(fresh.items()):
        object_bytes = archive.read(name.replace('.', '/') + '.olean')
        log_bytes = archive.read(name + '.log')
        record = json.loads(archive.read(name + '.json'))
        evidence = audit['modules'][name]
        assert sha(object_bytes) == row['output_sha256']
        assert len(object_bytes) == evidence['output_bytes']
        assert record == row == evidence['row']
        assert sha(log_bytes) == evidence['log_sha256']
        log = log_bytes.decode()
        assert not re.search(r'\b(error|warning)(?:\([^\n]*?\))?:', log)
        parsed = [(decl, sorted(x.strip() for x in axes.split(',') if x.strip())) for decl, axes in profile_pattern.findall(log)]
        assert [decl for decl, _ in parsed] == source_profiles(code[name])
        assert [axes for _, axes in parsed] == row['axiom_profiles']
        assert [{'declaration': decl, 'axioms': axes} for decl, axes in parsed] == evidence['named_axiom_profiles']
        assert all(set(axes) <= ALLOWED for _, axes in parsed)
        bytes_read += len(object_bytes)
        profiles_read += len(parsed)
        reviewed_fresh.append({'module': name, 'object_sha256': sha(object_bytes), 'object_bytes': len(object_bytes), 'log_sha256': sha(log_bytes), 'named_profiles': len(parsed)})
    assert (bytes_read, profiles_read) == (9925536, 383)
    inherited = report['inherited_completed_producer_modules']
    assert len(inherited) == 91
    assert set(inherited) <= set(prior)
    for name, evidence in inherited.items():
        row = prior[name]
        assert row['origin']['run'] == 40714530693 and row['origin']['job'] == 122908481894
        assert row['origin']['artifact_id'] == 12872778035
        assert row['origin']['context']['whole_job_conclusion'] == 'cancelled'
        source_row = evidence['row']
        assert all(row[k] == source_row[k] for k in ['source_sha256','source_closure_sha256','output_sha256','axiom_profiles'])
        assert len(source_profiles(code[name])) == len(row['axiom_profiles'])
    inherited_profile_count = sum(len(prior[name]['axiom_profiles']) for name in inherited)
    assert inherited_profile_count == 455
    own = set(inherited) | set(fresh)
    assert len(own) == 163
    assert sum(len(source_profiles(code[n])) for n in own) == 838
    expected_members = {'diagnostics_records.json','receipt.json','resource_observer.json','generated_source/generated_source_manifest.json'}
    expected_members |= {'generated_source/Proofs/RG_Lean_20261019/' + n.replace('.', '/') + '.lean' for n in modules}
    expected_members |= {n.replace('.', '/') + '.olean' for n in fresh}
    expected_members |= {n + suffix for n in fresh for suffix in ['.json','.log']}
    assert set(names) == expected_members
    endpoint_record = fresh[ENDPOINT]
    endpoint_source = code[ENDPOINT]
    assert '⟨52,9,39,(3824018983001674635847799415612737/32624163332060752803334972325527552)⟩' in endpoint_source
    assert 'theorem certificate : MiddleOriginalAnchorPredicate.Proved anchor := by' in endpoint_source
    assert 'WideAnchor030OriginalAnchor.actual_bound C u hd hn' in endpoint_source
    assert 'WideAnchor030OriginalAnchor.actual_bound_swapped C u hd hn' in endpoint_source

result = {
    'status': 'PASS_INDEPENDENT_ACTUAL_ANCHOR030_BYTE_AND_RECEIPT_REVIEW',
    'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
    'repository': 'RhudeJJJJ/formal-conjectures', 'run': report['run'], 'job': report['job'],
    'workflow_head': report['source_commit'], 'endpoint': ENDPOINT,
    'authentication_report_sha256': REPORT_SHA, 'artifact_sha256': sha(artifact_bytes),
    'artifact_bytes': len(artifact_bytes), 'archive_members_read_and_crc_checked': len(names),
    'receipt_sha256': sha(receipt_bytes),
    'receipt_partition': {'required': 281, 'prior': 209, 'fresh': 72},
    'diagnostic_partition': {'total': 524, 'prior': 452, 'fresh': 72, 'outside_endpoint_scope': 243},
    'actual_source_files_hashed': 281, 'actual_recursive_source_closures_recomputed': 281,
    'actual_fresh_compiled_objects_hashed': 72, 'actual_fresh_object_bytes_read': bytes_read,
    'actual_fresh_named_profiles_read': profiles_read, 'inherited_original_profiles': inherited_profile_count,
    'original_named_profiles_combined': 838, 'all_fresh_named_profiles_match_source_order': True,
    'all_axiom_sets_are_standard': True, 'native_run_and_job_success_verified': True,
    'fresh_endpoint_record': endpoint_record,
    'fresh_endpoint_profile': audit['modules'][ENDPOINT]['named_axiom_profiles'],
    'inherited_91_cancelled_producer_origins_preserved': True,
    'endpoint_claim_supported': True, 'full_degree_one_middle_claim': False,
    'global_rg_claim': False, 'remaining_original_families': 3,
    'completion_authenticator_executions_by_reviewer': 0,
    'Lean_or_lake_executions_by_reviewer': 0,
    'prior_object_archives_reread_by_reviewer': False,
    'review_scope': 'Read actual fresh ZIP bytes, native captures, all endpoint receipt rows, original source graph and frozen root report; inherited object authentication remains the frozen producer/native restore evidence.',
    'findings': [],
}
fresh_check_bytes = (json.dumps(reviewed_fresh, indent=2, sort_keys=True) + '\n').encode()
(OUT / 'fresh_module_byte_checks.json').write_bytes(fresh_check_bytes)
result['fresh_module_byte_checks_sha256'] = sha(fresh_check_bytes)
(OUT / 'independent_review.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps({k: result[k] for k in ['status','run','job','receipt_partition','actual_fresh_compiled_objects_hashed','actual_fresh_object_bytes_read','actual_fresh_named_profiles_read','original_named_profiles_combined','endpoint_claim_supported']}))
