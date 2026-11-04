"""Prepare a local numeric replacement contract from frozen actual API evidence.

This program performs no network or remote mutations. It binds all 349 original
plans, complete paginated API captures and five already authenticated repairs.
The default --seal requires complete metadata coverage. The separate
--seal-alternatives mode requires all 195 actual alternatives and concrete
observations for the other 154 original jobs, whose pending states stay pending.
Every prepared contract remains an input to the collector's complete archive
authentication; it is not a kernel receipt or a main-family closure claim.
"""
import argparse
import collections
import hashlib
import json
import math
import os
import pathlib
import re
import sys
import tempfile

REPOSITORY = 'RhudeJJJJ/formal-conjectures'
BRANCH = 'rg-degree-one-large-20261103'
MASTER_RUN = 41686621300
MASTER_HEAD = 'aaeaec3cec22467d3f0b83b1761bfb40087bb991'
REFERENCE_RUN = 41708676694
REFERENCE_HEAD = 'c2e2f145a77c2c2c65349085283f5ca2db7aa814'
SPEC = 'ci/rg_d1_required_numeric_batches_20261103.json'
SPEC_SHA = 'f47334108b563ae5e20f15fc07b2e4589f6d6e7f49e308bfdb8b4301e689e18e'
ORIGIN = 'ci/rg_d1_numeric_run41686621300_20261103.json'
ORIGIN_SHA = '9e4fbdfaf1f57b59453b5501e270e4d15b87a06bddcafd719ac882bd026980c7'
REGISTRY = 'ci/rg_d1_original_reference_bytes_20261103.json'
REGISTRY_SHA = 'a04e5e612ce5e927a9f121a03b2786224b84736e64cee1974eaaa8c603693dc9'
STEP = 'Require exact historical output identities'
REFERENCE_COMPLETION = 'EXACT_REGISTERED_REFERENCE_BATCH_COMPLETION'
THREE_WAVE_TWO_COMPLETION = 'EXACT_REGISTERED_THREE_WAVE_TWO_BATCH_COMPLETION'
PARTIAL = 'ORIGINAL_PARTIAL_PRIORS_WITH_FRESH_REMAINDER'
ZERO = 'NUMERIC137_COMPILED_OBJECTS_WITH_SEPARATE_ZERO_FRESH_METADATA_AUDIT'
ZERO_ITEM = 'ci/rg_numeric137_20261103_zero_fresh_prerequisite.json'
ZERO_ITEM_SHA = '695ca13cd739d41840ca5877525b765bec84e8cf5b2713ce1bb089024b9bc85b'
MATRICES = {
    'master': (MASTER_RUN, MASTER_HEAD,
        '.github/workflows/rg-d1-numeric-and-final-20261103.yml',
        'original-numeric-', 'plan', 'rg-d1-original-numeric-{run}-1-{batch}'),
    'reference': (REFERENCE_RUN, REFERENCE_HEAD,
        '.github/workflows/rg-d1-long-reference-recovery-20261103.yml',
        'reproduce-original-long-', 'Bind all 186 exact original long batch plans',
        'rg-d1-long-reference-recovery-20261103-{run}-1-{batch}'),
}
# Each tuple is an observed successful fixed origin, not a future placeholder.
REPAIRS = {
    '00_137': (41727434809, 126235797085, '69e96d8a50fca2c84498275cbe7364205d14239e',
        13274084950, '8ff2317bdb8d91e53e893c8c1c07bfbfc600e1514b66d298bd092dc766c4a4ad',
        '1dca83d36273fb2643080add5dda86d89f63e9a7f40640e810562810353d16f7'),
    '00_139': (41725665566, 126229651606, '8a7e69b6e50976dceac355964299ce3bf40bf257',
        13279016964, 'd7a9cca21c2490f5d6d3e779e7415464c457f2156b84888861ddac3a1557d5aa',
        '7a3c2e583b6717d85a421492eadaf756c23c708a0e0633ff34c846b14f1f4bc6'),
    '00_147': (41692349895, 126113875433, 'e3bee2bbf80ae020437f127c9400b201c69927fa',
        13269479099, 'dbf57876f2eb83f19f89efcf6b2e202afd4aa897ff904ebf3d23d792e1f97f06',
        '48b1f6354b2c5aac6712aa0df3f49d40232215b0e9a15673ff1438c215d57b4d'),
    '00_156': (41711724404, 126181209594, '8efa08e1a271255d98e2a1ebdab6b461d46c10d6',
        13272042804, '9d41cfa398dcd9b53031deaf60ce045056b359411fefbe0038275950b322e49a',
        '359fcae1afd9f440618690b2731a8ad6fdaa673f1f3b7c3e294dacd517ee3f7e'),
    '00_164': (41711724404, 126181209194, '8efa08e1a271255d98e2a1ebdab6b461d46c10d6',
        13274151889, '33e6ff9e403c0d2b2542ad02e204d7a189456667b88fa6bdaabd408292749cce',
        '487eaf5e033e7cd967f44739cd745bd00c17a68eb02f15bbe37decc68f84eedd'),
}
REMAINDER_SPECS = {
    '00_139': '18a46b10ebaff7640f068ae35001eafdba401c90265cbf1634fa0221a9fed922',
    '00_156': '23cd16f29c7ed1501e973a64ae9696f48c8eede0d26b638fadb3d080e175707c',
    '00_164': '0be737163dbafd7901cc7096e45e2113ddc2eb4caf5245e880e75f98577140e2',
}
# This is deliberately not a successful origin. Registration of a later success
# requires its actual run, job, head, archive and authenticated report.
PENDING_REPAIRS = {
    '00_166': {
        'original_job': 126095241107,
        'completion_spec': {
            'path': 'ci/rg_d1_numeric_remainder_20261103/batch00_166.json',
            'sha256': 'd8aeaa83a3ff9496203b2b2c442a66589a3f907b154643a677a8281f871c60a5'},
        'workflow_path': '.github/workflows/rg-d1-numeric166-partial-remainder-20261104.yml',
        'job_name': 'Complete original numeric remainder 00_166',
        'actual_run': 41740037248,
        'actual_job': 126278963245,
        'source_commit': 'e916d412087b10298ffe03e0e488ca43790be17d',
        'successful_origin_registered': False,
    },
}

# This source-preserving repair is prepared, but has no registered successful
# origin. The four actual kernel archives and their zero-fresh join must pass
# authentication before a later reviewed entry can join REPAIRS.
PREPARED_DECLARATION_SPLITS = {
    '00_166': {
        'completion_kind': 'NUMERIC166_COMPILED_OBJECTS_WITH_SEPARATE_ZERO_FRESH_BATCH_JOIN',
        'completion_spec': {
            'path': 'ci/rg_d1_numeric166_decomposed_20261104_spec.json',
            'sha256': '0ddb0d67758c7627ddc7fae947a7100bcb94c9ea6b26ab3f9c13fef33f7d8f8c'},
        'original_job': 126095241107,
        'workflow_path': '.github/workflows/rg-d1-numeric166-decomposed-recovery-20261104.yml',
        'job_name': 'Join complete original numeric166 batch',
        'required_success_step': 'Require full original batch and all preserved origins',
        'successful_origin_registered': False,
    },
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def check(condition, detail):
    if not condition:
        raise ValueError(detail)


def positive(value):
    return type(value) is int and value > 0


def bound(root, relative, digest, size=None):
    path = pathlib.PurePosixPath(relative)
    check(not path.is_absolute() and '..' not in path.parts, ('Unsafe input path', relative))
    full = root / path
    check(full.resolve().is_relative_to(root.resolve()), ('Escaping input path', relative))
    raw = full.read_bytes()
    check(sha(raw) == digest and (size is None or len(raw) == size), ('Changed input', relative))
    return json.loads(raw), raw


def evidence_file(root, ref):
    check(set(ref) == {'path', 'sha256', 'bytes'}, 'Malformed evidence binding')
    check(re.fullmatch(r'[0-9a-f]{64}', ref['sha256']) is not None, 'Malformed evidence digest')
    check(positive(ref['bytes']), 'Malformed evidence length')
    return bound(root, ref['path'], ref['sha256'], ref['bytes'])[0]


def pages(root, refs, member):
    check(isinstance(refs, list) and 1 <= len(refs) <= 100, 'Missing or excessive pagination')
    rows, total = [], None
    for index, ref in enumerate(refs):
        page = evidence_file(root, ref)
        count = page['total_count']
        check(type(count) is int and count >= 0, 'Invalid total_count')
        if total is None:
            total = count
        check(count == total, 'Live pagination totals changed; capture all pages again')
        current = page[member]
        check(isinstance(current, list), 'Malformed paginated member')
        check(len(current) == min(100, max(0, total - index * 100)), 'Missing or partial page')
        rows.extend(current)
    check(len(refs) == max(1, math.ceil(total / 100)) and len(rows) == total,
          'Incomplete pagination')
    ids = [r['id'] for r in rows]
    check(all(positive(i) for i in ids) and len(ids) == len(set(ids)), 'Duplicate or invalid IDs')
    return rows


def validate_run(run, run_id, head, workflow):
    check(run['id'] == run_id and run['head_sha'] == head, 'Wrong actual run/head')
    check(run['path'] == workflow and run['head_branch'] == BRANCH, 'Wrong workflow/branch')
    check(type(run['run_attempt']) is int and run['run_attempt'] == 1, 'Changed run attempt')
    check(run['repository']['full_name'] == REPOSITORY, 'Wrong run repository')


def validate_job(job, run_id, head):
    check(positive(job['id']) and job['run_id'] == run_id and job['head_sha'] == head,
          'Wrong actual job origin')
    check(type(job['run_attempt']) is int and job['run_attempt'] == 1, 'Changed job attempt')
    check(job['head_branch'] == BRANCH, 'Wrong job branch')
    check(job['status'] in ('queued', 'waiting', 'in_progress', 'completed'), 'Unknown job status')


def succeeded(job, step):
    if job['status'] != 'completed' or job['conclusion'] != 'success':
        return False
    matches = [s for s in job['steps'] if s['name'] == step]
    check(len(matches) == 1 and matches[0]['status'] == 'completed'
          and matches[0]['conclusion'] == 'success', 'Missing exact successful identity step')
    return True


def validate_artifact(artifact, run_id, head, name):
    check(positive(artifact['id']) and artifact['name'] == name, 'Wrong artifact name/id')
    check(artifact['workflow_run']['id'] == run_id
          and artifact['workflow_run']['head_sha'] == head, 'Wrong artifact origin')
    check(artifact['workflow_run']['head_branch'] == BRANCH, 'Wrong artifact branch')
    check(artifact['expired'] is False, 'Expired artifact')
    check(positive(artifact['size_in_bytes']) and artifact['size_in_bytes'] <= 1024**3,
          'Unexpected artifact size')
    check(re.fullmatch(r'sha256:[0-9a-f]{64}', artifact['digest']) is not None,
          'Missing actual artifact digest')


def validate_non_numeric_names(key, names):
    plan_name = MATRICES[key][4]
    check(names.count(plan_name) == 1 and len(names) == len(set(names)),
          'Missing or duplicate matrix plan job')
    if key == 'master':
        # jobs.final exists in the immutable master workflow. Its actual result
        # never supplies numeric batch coverage, including a skipped result.
        check(set(names) <= {plan_name, 'final'}, 'Unknown master side job')
    else:
        check(names == [plan_name], 'Unexpected reference matrix side job')


def matrix(root, bundle, key, allowed):
    run_id, head, workflow, prefix, plan_name, template = MATRICES[key]
    refs = bundle['matrices'][key]
    check(set(refs) == {'run', 'jobs', 'artifacts'}, 'Malformed matrix evidence')
    run = evidence_file(root, refs['run'])
    validate_run(run, run_id, head, workflow)
    jobs = pages(root, refs['jobs'], 'jobs')
    artifacts = pages(root, refs['artifacts'], 'artifacts')
    named, plans = {}, []
    for job in jobs:
        validate_job(job, run_id, head)
        if not job['name'].startswith(prefix):
            plans.append(job)
            continue
        batch = job['name'][len(prefix):]
        check(batch in allowed and batch not in named, ('Unknown or duplicate batch job', batch))
        named[batch] = job
    validate_non_numeric_names(key, [j['name'] for j in plans])
    artifact_names = collections.defaultdict(list)
    for artifact in artifacts:
        check(artifact['workflow_run']['id'] == run_id
              and artifact['workflow_run']['head_sha'] == head, 'Mixed artifact pagination')
        artifact_names[artifact['name']].append(artifact)
    successful, absent_artifacts = {}, []
    for batch, job in named.items():
        if not succeeded(job, STEP):
            continue
        expected = template.format(run=run_id, batch=batch)
        matches = artifact_names[expected]
        check(len(matches) <= 1, ('Ambiguous actual artifact', expected))
        if not matches:
            absent_artifacts.append(batch)
            continue
        artifact = matches[0]
        validate_artifact(artifact, run_id, head, expected)
        successful[batch] = (job, artifact)
    return dict(run=run, jobs=named, success=successful, missing_artifacts=absent_artifacts,
                actual_job_count=len(jobs), actual_artifact_count=len(artifacts),
                non_numeric_jobs=[{k:j[k] for k in ('id','name','status','conclusion')} for j in plans])


def reference_binding(batch, plans, old_jobs, late):
    old = old_jobs.get(batch)
    if old is None:
        check(batch in late, ('No actual original job outside allowed late wave two', batch))
        check(plans[batch]['wave'] == 2, 'Invalid late original batch')
    return {'provenance_kind': REFERENCE_COMPLETION, 'original_job_observation': {
        'run': MASTER_RUN, 'source_commit': MASTER_HEAD, 'run_attempt': 1,
        'job_name': 'original-numeric-' + batch, 'job': old['id'] if old else None,
        'status': old['status'] if old else 'not_created',
        'conclusion': old['conclusion'] if old else None}}


def make_item(batch, plan, job, artifact, workflow, binding, step=STEP):
    return dict(batch=batch, original_plan_sha256=plan['plan_sha256'],
        run=job['run_id'], job=job['id'], source_commit=job['head_sha'],
        artifact_id=artifact['id'], artifact_sha256=artifact['digest'].removeprefix('sha256:'),
        artifact_name=artifact['name'], job_name=job['name'], workflow_path=workflow,
        required_success_step=step, **binding)


def repair(checkout, evidence_root, refs, batch, plan, original_job):
    check(set(refs) == {'run', 'job', 'artifact', 'authentication_report'}, 'Malformed repair evidence')
    run, job, artifact, report = (evidence_file(evidence_root, refs[k]) for k in
        ('run', 'job', 'artifact', 'authentication_report'))
    run_id, job_id, head, artifact_id, digest, auth_sha = REPAIRS[batch]
    check(refs['authentication_report']['sha256'] == auth_sha, 'Changed authenticated repair report')
    check(job['id'] == job_id and artifact['id'] == artifact_id
          and artifact['digest'] == 'sha256:' + digest, 'Unregistered repair origin')
    if batch == '00_137':
        item = bound(checkout, ZERO_ITEM, ZERO_ITEM_SHA)[0]
        workflow, name, step = (item[k] for k in ('workflow_path', 'job_name', 'required_success_step'))
        expected_name = 'rg-d1-numeric137-zero-fresh-audit-20261103-' + str(run_id) + '-1'
    elif batch == '00_147':
        workflow = '.github/workflows/rg-d1-numeric147-serial-recovery-20261103.yml'
        name = 'Restore original numeric00_147 with one worker'
        step = STEP
        expected_name = 'rg-d1-original-numeric-serial-00_147-' + str(run_id) + '-1'
    else:
        workflow = ('.github/workflows/rg-d1-numeric139-partial-remainder-20261103.yml'
            if batch == '00_139' else '.github/workflows/rg-d1-numeric-partial-remainders-20261103.yml')
        name = 'Complete original numeric remainder ' + batch
        step = STEP
        expected_name = 'rg-d1-original-numeric-remainder-20261103-' + str(run_id) + '-1-' + batch
    validate_run(run, run_id, head, workflow)
    validate_job(job, run_id, head)
    check(job['name'] == name and succeeded(job, step), 'Repair is not actually successful')
    validate_artifact(artifact, run_id, head, expected_name)
    check(original_job['status'] == 'completed' and original_job['conclusion'] in ('failure', 'timed_out'),
          'Original failed-job provenance changed')
    constructed = make_item(batch, plan, job, artifact, workflow,
                            {'original_job': original_job['id']}, step)
    if batch == '00_137':
        for key, value in constructed.items():
            check(item[key] == value, ('Changed published numeric137 origin', key))
        check(report['successful_audit_origin'] == {k:item[k] for k in
              ('run', 'job', 'source_commit', 'artifact_id', 'artifact_sha256')}, 'Changed audit report origin')
        return item
    item = constructed
    for key in ('run', 'job', 'source_commit', 'artifact_id', 'artifact_sha256'):
        check(report[key] == item[key], 'Changed repair report origin')
    if batch in REMAINDER_SPECS:
        relative = 'ci/rg_d1_numeric_remainder_20261103/batch' + batch + '.json'
        spec = bound(checkout, relative, REMAINDER_SPECS[batch])[0]
        check(spec['original_plan_sha256'] == plan['plan_sha256'], 'Changed remainder plan')
        check((spec['workers'], spec['module_timeout'], spec['memory_reserve_mib']) == (1, 1200, 2048),
              'Changed remainder guards')
        item.update(completion_kind=PARTIAL,
            completion_spec={'path':relative, 'sha256':REMAINDER_SPECS[batch]})
    return item


def registered_completion(checkout, evidence_root, refs, batch, plan, old, entry, spec_raw, origin):
    """Recheck frozen actual API evidence against an independently authenticated registry."""
    check(set(refs) == {'run','job','artifact','authentication_report'}, 'Malformed registered completion evidence')
    run, job, artifact, report = (evidence_file(evidence_root, refs[k]) for k in
        ('run','job','artifact','authentication_report'))
    item = dict(entry['item'])
    check(batch == item['batch'] and plan['plan_sha256'] == item['original_plan_sha256'],
          'Changed registered completion plan')
    auth = entry['authentication_report']
    check(refs['authentication_report']['sha256'] == auth['sha256']
          and refs['authentication_report']['bytes'] == auth['bytes'], 'Changed registered authentication report')
    validate_run(run, item['run'], item['source_commit'], item['workflow_path'])
    validate_job(job, item['run'], item['source_commit'])
    check(job['id'] == item['job'] and job['name'] == item['job_name']
          and succeeded(job, item['required_success_step']), 'Registered job is not actually successful')
    validate_artifact(artifact, item['run'], item['source_commit'], item['artifact_name'])
    check(artifact['id'] == item['artifact_id']
          and artifact['digest'] == 'sha256:' + item['artifact_sha256'], 'Changed registered archive')
    for key in ('run','job','source_commit','artifact_id','artifact_sha256','original_plan_sha256'):
        check(report[key] == item[key], 'Changed registered authentication report origin')
    if batch == '00_166':
        for key in ('run','job','artifact'):
            check(refs[key]['sha256'] == report['recorded_api_evidence_sha256'][key+'_metadata.json'],
                  'Numeric166 API evidence differs from its complete archive authentication')
        check(old is not None and old['id'] == item['original_job'] == 126095241107,
              'Missing exact failed numeric166 original')
        check(old['run_id'] == MASTER_RUN and old['head_sha'] == MASTER_HEAD,
              'Changed failed numeric166 original origin')
        check(old['status'] == 'completed' and old['conclusion'] in ('failure','timed_out'),
              'Numeric166 repair requires its actual failed original')
    else:
        for key in ('run','job','artifact'):
            check(refs[key]['sha256'] == report[key+'_metadata_sha256'],
                  'Three-batch API evidence differs from its complete archive authentication')
        from rg_actual_numeric_completions import original_observation, three_binding
        check(item['provenance_kind'] == THREE_WAVE_TWO_COMPLETION, 'Unknown registered provenance')
        item['original_job_observation'] = original_observation(batch, old)
        three_binding(item, spec_raw, origin, checkout)
    return item


def prepare(checkout, evidence_root, bundle, evidence_sha, alternatives_only=False):
    check(bundle['kind'] == 'FROZEN_ACTUAL_D1_NUMERIC_API_EVIDENCE', 'Wrong evidence kind')
    check(bundle['repository'] == REPOSITORY, 'Wrong evidence repository')
    check(set(bundle['matrices']) == set(MATRICES), 'Missing actual matrix')
    check(set(bundle['repairs']) <= set(REPAIRS), 'Unregistered future repair origin')
    check(set(bundle.get('pending_repairs', {})) <= set(PENDING_REPAIRS), 'Unknown pending repair')
    spec, spec_raw = bound(checkout, SPEC, SPEC_SHA)
    origin, _ = bound(checkout, ORIGIN, ORIGIN_SHA)
    registry, registry_raw = bound(checkout, REGISTRY, REGISTRY_SHA)
    check(spec['kind'] == 'EXACT_MISSING_D1_ORIGINAL_NUMERIC_BATCHES', 'Wrong original scope')
    check(spec['mathlib'] == '0df444a360eaa60ab8c11dca51a86af692955474'
          and spec['leancert'] == '621a43d7cf21f87872392a01e874f2f1dbddc926'
          and spec['lean_version'] == '4.33.1', 'Changed fixed toolchain')
    plans = {r['batch']:r for r in spec['jobs']}
    check(len(plans) == len(spec['jobs']) == 349, 'Incomplete original 349-plan universe')
    for batch, row in plans.items():
        plan = bound(checkout, row['plan'], row['plan_sha256'])[0]
        check(plan['kind'] == 'EXACT_ORIGINAL_D1_NUMERIC_REPRODUCTION', 'Changed original plan kind')
        check((plan['workers'], plan['module_timeout'], plan['memory_reserve_mib']) == (2, 1200, 2048),
              ('Changed original guards', batch))
    bound(checkout, spec['head_plan'], spec['head_plan_sha256'])
    for batch, pending in PREPARED_DECLARATION_SPLITS.items():
        fixed = pending['completion_spec']
        split = bound(checkout, fixed['path'], fixed['sha256'])[0]
        check(split['kind'] == 'SOURCE_PRESERVING_NUMERIC166_FULL_BATCH_WITH_PRESERVED_PARTIAL_ORIGINS',
              'Changed prepared declaration split')
        check(split['batch_id'] == batch and split['original_plan_sha256'] == plans[batch]['plan_sha256'],
              'Changed prepared split scope')
        check((split['workers'], split['module_timeout'], split['memory_reserve_mib'],
               split['max_parallel_leaf_jobs']) == (1, 1200, 2048, 2), 'Changed prepared split guards')
        check(split['original_numeric_module_count'] == 10
              and split['required_module_count'] == 160 and split['fresh_module_count'] == 80,
              'Changed prepared split module counts')
        check(split['source_reorganized_original_modules'] ==
              [f'Proofs.RadenkovicGutmanD1Long00Leaf{i:05d}' for i in range(1666, 1670)],
              'Changed prepared split endpoint names')
        check(split['original_declarations_preserved_verbatim'] is True
              and split['proof_bodies_changed'] is False, 'Changed prepared split proof scope')
    for batch, pending in PENDING_REPAIRS.items():
        fixed = pending['completion_spec']
        remainder = bound(checkout, fixed['path'], fixed['sha256'])[0]
        check(remainder['batch'] == batch and remainder['original_plan_sha256'] == plans[batch]['plan_sha256'],
              'Changed prepared remainder scope')
        check((remainder['workers'], remainder['module_timeout'], remainder['memory_reserve_mib']) == (1, 1200, 2048),
              'Changed prepared remainder guards')
    pending_observations = {}
    for batch, entry in bundle.get('pending_repairs', {}).items():
        fixed = PENDING_REPAIRS[batch]
        actual = evidence_file(evidence_root, entry['metadata'])
        run, job = actual['run'], actual['job']
        validate_run(run, fixed['actual_run'], fixed['source_commit'], fixed['workflow_path'])
        validate_job(job, fixed['actual_run'], fixed['source_commit'])
        check(job['id'] == fixed['actual_job'] and job['name'] == fixed['job_name'], 'Wrong pending repair job')
        pending_observations[batch] = dict(fixed, observed_job_status=job['status'],
            observed_job_conclusion=job['conclusion'], actual_metadata_sha256=entry['metadata']['sha256'],
            metadata_readback_at=entry['readback_at'], complete_batch_success_claimed=False)
    references = set(registry['affected_numeric_batches'])
    check(len(references) == len(registry['affected_numeric_batches']) == 186
          and references <= set(plans), 'Changed reference matrix scope')
    late = references & {b for b,r in plans.items() if r['wave'] == 2}
    check(len(late) == 90, 'Changed narrowly allowed late original jobs')
    master = matrix(evidence_root, bundle, 'master', set(plans))
    reference = matrix(evidence_root, bundle, 'reference', references)
    for batch, pending in PENDING_REPAIRS.items():
        if batch in master['jobs']:
            check(master['jobs'][batch]['id'] == pending['original_job'], 'Changed prepared original job')
    check(set(reference['jobs']) == references, 'Reference matrix capture omits registered jobs')
    candidates, repair_success, registered_success = {}, {}, {}
    for batch, refs in bundle['repairs'].items():
        check(batch in master['jobs'], 'Missing actual old repair job')
        item = repair(checkout, evidence_root, refs, batch, plans[batch], master['jobs'][batch])
        candidates[batch] = repair_success[batch] = item
    if bundle.get('registered_completions'):
        from rg_actual_numeric_completions import context as registered_context
        registration = registered_context(checkout)
        check(set(bundle['registered_completions']) <= registration['jobs'].keys(),
              'Unknown actual registered completion')
        for batch, refs in bundle['registered_completions'].items():
            check(batch not in candidates, 'Duplicate registered completion origin')
            item = registered_completion(checkout, evidence_root, refs, batch, plans[batch],
                master['jobs'].get(batch), registration['jobs'][batch], spec_raw, origin)
            candidates[batch] = registered_success[batch] = item
            if batch == '00_166':
                repair_success[batch] = item
    selected, batch_status, binding_wait = {}, [], []
    for batch, plan in sorted(plans.items()):
        old = master['jobs'].get(batch)
        row = {'batch':batch, 'original_plan_sha256':plan['plan_sha256'],
               'original_job':old['id'] if old else None,
               'original_status':old['status'] if old else 'not_created',
               'original_conclusion':old['conclusion'] if old else None,
               'selected_successful_origin':None}
        if alternatives_only and batch in candidates:
            # Candidates have already passed their exact registered-origin
            # validation. Keep the fixed alternative even if its master
            # duplicate succeeds while the remaining jobs are still pending.
            selected[batch] = 'repair' if batch in repair_success else 'registered_alternative'
        elif batch in master['success'] and not (alternatives_only and batch in reference['success']):
            check(batch not in repair_success, 'Fixed failed repair origin also claimed successful')
            selected[batch] = 'master'
            if batch in registered_success:
                del candidates[batch]
        elif batch in repair_success:
            selected[batch] = 'repair'
        elif batch in reference['success']:
            selected[batch] = 'reference'
            job, artifact = reference['success'][batch]
            candidates[batch] = make_item(batch, plan, job, artifact, MATRICES['reference'][2],
                                          reference_binding(batch, plans, master['jobs'], late))
        elif batch in registered_success:
            selected[batch] = 'registered_alternative'
        if batch in selected:
            row['selected_successful_origin'] = selected[batch]
        if batch in candidates:
            item = candidates[batch]
            row['replacement_job'] = item['job']
            row['replacement_artifact_id'] = item['artifact_id']
            row['uses_registered_late_original_lookup'] = 'original_job_lookup' in item
            if item.get('provenance_kind') in {REFERENCE_COMPLETION, THREE_WAVE_TWO_COMPLETION}:
                row['provenance_kind'] = item['provenance_kind']
                row['original_job_observation'] = item['original_job_observation']
            elif old and not (old['status'] == 'completed' and old['conclusion'] in ('failure', 'timed_out')):
                binding_wait.append(batch)
        batch_status.append(row)
    missing = sorted(set(plans) - set(selected))
    late_lookups = sorted(b for b,item in candidates.items() if 'original_job_lookup' in item)
    reference_completions = sorted(b for b,item in candidates.items()
        if item.get('provenance_kind') == REFERENCE_COMPLETION)
    reference_originals_not_created = sorted(b for b in reference_completions
        if candidates[b]['original_job_observation']['status'] == 'not_created')
    ready = not missing and not binding_wait
    failures = sorted(b for b,j in master['jobs'].items()
        if j['status'] == 'completed' and j['conclusion'] in ('failure', 'timed_out')
        and b not in selected)
    report = dict(kind='ACTUAL_NUMERIC_COVERAGE_REPORT_NOT_KERNEL_RECEIPT',
        repository=REPOSITORY, observed_at=bundle['observed_at'], evidence_sha256=evidence_sha,
        artifact_observation_end=bundle.get('artifact_observation_end'),
        original_numeric_run=MASTER_RUN, original_numeric_source_commit=MASTER_HEAD,
        original_spec_sha256=SPEC_SHA, original_batch_plans_verified=349, head_plan_verified=True,
        reference_registry_sha256=REGISTRY_SHA, registered_reference_batches=186,
        actual_matrix_jobs={k:dict(total=m['actual_job_count'], numeric=len(m['jobs']),
            states=dict(collections.Counter(j['conclusion'] if j['status']=='completed' else j['status']
                for j in m['jobs'].values())), artifacts=m['actual_artifact_count'],
            successful_jobs_without_artifacts=m['missing_artifacts'],
            non_numeric_jobs_excluded_from_coverage=m['non_numeric_jobs'])
            for k,m in [('master',master), ('reference',reference)]},
        distinct_successful_complete_batch_origins=len(selected), planned_batches=349,
        selected_origin_counts=dict(collections.Counter(selected.values())),
        missing_successful_batches=missing, missing_successful_batch_count=len(missing),
        unhandled_observed_failures=failures, original_job_bindings_still_pending=binding_wait,
        observed_failed_numeric_jobs={key:[dict(batch=b, job=j['id'], conclusion=j['conclusion'])
            for b,j in sorted(value['jobs'].items())
            if j['status']=='completed' and j['conclusion'] in ('failure','timed_out')]
            for key,value in [('master',master),('reference',reference)]},
        permitted_original_job_lookups_requiring_runtime_resolution=late_lookups,
        all_selected_original_job_ids_are_concrete=not late_lookups and not reference_originals_not_created,
        exact_registered_reference_completions=reference_completions,
        reference_completion_original_jobs_not_created=reference_originals_not_created,
        collector_must_validate_failed_original_jobs_for_repairs=True,
        collector_must_reobserve_reference_original_jobs_without_failure_requirement=True,
        known_repairs_awaiting_actual_success=pending_observations,
        prepared_declaration_splits_not_counted_as_success=PREPARED_DECLARATION_SPLITS,
        pending_repairs_missing_actual_metadata=sorted(set(PENDING_REPAIRS)-set(pending_observations)),
        registered_repairs_missing_evidence=sorted(set(REPAIRS)-set(bundle['repairs'])),
        successful_replacement_candidate_count=len(candidates),
        contract_ready=ready, sealed_contract_written=False,
        contract_readiness_accepts_only_fixed_registered_reference_completions=True,
        complete_numeric_metadata_coverage=len(selected)==349,
        archive_authentication_still_required=True, whole_degree_one_large_complete=False,
        remaining_open_original_families=4, batch_states=batch_status)
    contract = dict(kind='SEALED_SUCCESSFUL_NUMERIC_BATCH_COMPLETIONS_WITH_EXPLICIT_SOURCE_REORGANIZATION'
        if '00_137' in candidates else 'SEALED_SUCCESSFUL_ORIGINAL_NUMERIC_BATCH_REPLACEMENTS',
        repository=REPOSITORY, numeric_run=MASTER_RUN, numeric_source_commit=MASTER_HEAD,
        numeric_spec_sha256=SPEC_SHA, replacements=[candidates[b] for b in sorted(candidates)])
    if bundle.get('registered_completions'):
        from rg_actual_numeric_completions import REGISTRY as ACTUAL_REGISTRY, REGISTRY_SHA as ACTUAL_SHA
        three_completions = sorted(b for b,item in candidates.items()
            if item.get('provenance_kind') == THREE_WAVE_TWO_COMPLETION)
        absent_three_originals = sorted(b for b in three_completions
            if candidates[b]['original_job_observation']['status'] == 'not_created')
        report.update(actual_completion_registry={'path':ACTUAL_REGISTRY,'sha256':ACTUAL_SHA},
            registered_completions_missing_evidence=sorted(registration['jobs'].keys()-registered_success.keys()),
            actual_registered_completion_batches=sorted(registered_success),
            exact_registered_three_wave_two_completions=three_completions,
            three_completion_original_jobs_not_created=absent_three_originals,
            collector_must_reobserve_three_wave_two_original_jobs_without_failure_requirement=True,
            contract_readiness_accepts_only_fixed_reference186_and_three_wave_two_completions=True)
        del report['contract_readiness_accepts_only_fixed_registered_reference_completions']
        report['all_selected_original_job_ids_are_concrete'] = (
            report['all_selected_original_job_ids_are_concrete'] and not absent_three_originals)
        if '00_166' in registered_success:
            report['superseded_serial_attempt_observations'] = pending_observations
            report['known_repairs_awaiting_actual_success'] = {
                b:v for b,v in pending_observations.items() if b not in registered_success}
            report['prepared_declaration_splits_not_counted_as_success'] = {
                b:v for b,v in PREPARED_DECLARATION_SPLITS.items() if b not in registered_success}
            report['actually_registered_declaration_splits'] = {'00_166':registered_success['00_166']}
    if alternatives_only:
        from rg_numeric_alternative_coverage import assess
        alternative_report, annotation = assess(spec_raw, registry_raw, candidates, master,
            binding_wait, evidence_sha, bundle['observed_at'])
        report.update(alternative_report)
        report['requested_sealing_mode'] = 'ACTUAL_ALTERNATIVES_ONLY'
        if annotation is not None:
            contract['coverage_at_sealing'] = annotation
    return report, contract, spec_raw, origin


def atomic_json(path, value, exclusive=False, validate=None):
    path.parent.mkdir(parents=True, exist_ok=True)
    raw = (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix=path.name+'.incomplete-', delete=False) as out:
            temporary = pathlib.Path(out.name)
            out.write(raw)
            out.flush()
            os.fsync(out.fileno())
        check(temporary.read_bytes() == raw and json.loads(temporary.read_bytes()) == value,
              'Incomplete atomic JSON readback')
        if validate:
            validate(temporary)
        if exclusive:
            os.link(temporary, path)
            temporary.unlink()
        else:
            temporary.replace(path)
        temporary = None
        check(path.read_bytes() == raw and json.loads(path.read_bytes()) == value, 'Final JSON readback failed')
        return sha(raw)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkout', type=pathlib.Path, required=True)
    parser.add_argument('--evidence-root', type=pathlib.Path, required=True)
    parser.add_argument('--evidence', type=pathlib.Path, required=True)
    parser.add_argument('--evidence-sha256', required=True)
    parser.add_argument('--report', type=pathlib.Path, required=True)
    sealing = parser.add_mutually_exclusive_group()
    sealing.add_argument('--seal', type=pathlib.Path,
        help='Create a new contract only after complete coverage and collector validation; never overwrite')
    sealing.add_argument('--seal-alternatives', type=pathlib.Path,
        help='Seal all 195 actual alternatives while explicitly preserving pending original coverage')
    args = parser.parse_args()
    raw = args.evidence.read_bytes()
    check(sha(raw) == args.evidence_sha256, 'Changed frozen evidence index')
    report, contract, spec_raw, origin = prepare(args.checkout.resolve(), args.evidence_root.resolve(),
        json.loads(raw), sha(raw), alternatives_only=args.seal_alternatives is not None)
    atomic_json(args.report, report)
    seal_path = args.seal_alternatives or args.seal
    if seal_path:
        ready = (report['alternative_contract_ready'] if args.seal_alternatives
                 else report['contract_ready'])
        if not ready:
            print(json.dumps({'status':'PENDING_NO_CONTRACT_WRITTEN',
                'complete_batches':report['distinct_successful_complete_batch_origins'],
                'missing_batches':report['missing_successful_batch_count'],
                'pending_existing_original_bindings':len(report['original_job_bindings_still_pending']),
                'missing_required_alternatives':report.get('missing_required_alternative_batches'),
                'unsafe_original_coverage':report.get('unsafe_original_coverage'),
                'permitted_original_lookups_pending':len(
                    report['permitted_original_job_lookups_requiring_runtime_resolution'])}))
            return 2
        # Reuse the published scope/typed-completion validator. No candidate can
        # override a plan, invent an original job, or bypass a compiled origin.
        sys.path.insert(0, str(args.checkout.resolve() / 'ci'))
        from rg_collect_exact_d1_reproductions import sealed_numeric_replacements
        def validate(path):
            replacements, _ = sealed_numeric_replacements(path, spec_raw, origin, REPOSITORY)
            check(set(replacements) == {r['batch'] for r in contract['replacements']}, 'Collector mismatch')
        digest = atomic_json(seal_path, contract, exclusive=True, validate=validate)
        report.update(sealed_contract_written=True, sealed_contract_sha256=digest)
        atomic_json(args.report, report)
    status = 'PENDING'
    if args.seal_alternatives and report['alternative_contract_ready']:
        status = ('ACTUAL_ALTERNATIVES_SEALED_PENDING_ORIGINAL_COVERAGE'
            if report['pending_original_coverage']
            else 'ACTUAL_ALTERNATIVES_SEALED_FOR_COMPLETE_ARCHIVE_AUTHENTICATION')
    elif report['contract_ready']:
        status = ('NUMERIC_CONTRACT_READY_AWAITING_ORIGINAL_JOB_LOOKUPS'
            if report['permitted_original_job_lookups_requiring_runtime_resolution']
            else 'NUMERIC_CONTRACT_READY_FOR_ARCHIVE_AUTHENTICATION')
    print(json.dumps({'status':status,
        'complete_batches':report['distinct_successful_complete_batch_origins'],
        'planned_batches':349, 'sealed_contract_written':report['sealed_contract_written'],
        'pending_original_coverage':report.get('pending_original_coverage'),
        'permitted_original_lookups_pending':len(
            report['permitted_original_job_lookups_requiring_runtime_resolution']),
        'whole_degree_one_large_complete':False}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
