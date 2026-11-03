"""Exercise the preparer's gates using only the frozen actual 23:37 evidence.

Mutated copies are rejection controls, never candidate successful origins.
No artificial full-coverage positive contract is constructed.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile

DEFAULT_ROOT = pathlib.Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--checkout', type=pathlib.Path, default=DEFAULT_ROOT)
parser.add_argument('--evidence-root', type=pathlib.Path, default=DEFAULT_ROOT)
parser.add_argument('--output', type=pathlib.Path,
    default=DEFAULT_ROOT/'ci/rg_numeric_replacement_preparer_20261104_validation.json')
args = parser.parse_args()
ROOT = args.evidence_root.resolve()
CHECKOUT = args.checkout.resolve()
SCRIPT = pathlib.Path(__file__).resolve().with_name('rg_prepare_numeric_replacements.py')
EVIDENCE = ROOT / 'ci/rg_numeric_replacement_evidence_20261104/index.json'
EVIDENCE_SHA = '39c2cceb645117e98f530e2c68ef9cdec9005d1074379de0cbf350e43d17bc6e'
spec = importlib.util.spec_from_file_location('numeric_preparer', SCRIPT)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
bundle = json.loads(EVIDENCE.read_bytes())
assert m.sha(EVIDENCE.read_bytes()) == EVIDENCE_SHA
results = []


def add(name, details=None):
    results.append(dict(name=name, status='passed', details=details))


def execute(b=bundle, checkout=CHECKOUT, evidence_root=ROOT):
    return m.prepare(checkout, evidence_root, b, EVIDENCE_SHA)


report, contract, _, _ = execute()
assert report['distinct_successful_complete_batch_origins'] == 180
assert report['selected_origin_counts'] == {'master':52, 'reference':123, 'repair':5}
assert len(report['batch_states']) == 349 and report['missing_successful_batch_count'] == 169
assert report['unhandled_observed_failures'] == ['00_166']
assert len(report['original_job_bindings_still_pending']) == 96
assert len(report['permitted_original_job_lookups_requiring_runtime_resolution']) == 27
assert report['all_selected_original_job_ids_are_concrete'] is False
assert not report['contract_ready'] and not report['sealed_contract_written']
assert report['known_repairs_awaiting_actual_success']['00_166']['successful_origin_registered'] is False
assert report['known_repairs_awaiting_actual_success']['00_166']['actual_run'] == 41740037248
assert report['known_repairs_awaiting_actual_success']['00_166']['actual_job'] == 126278963245
assert report['known_repairs_awaiting_actual_success']['00_166']['observed_job_status'] == 'in_progress'
assert len(contract['replacements']) == 128
assert '00_166' not in {i['batch'] for i in contract['replacements']}
add('actual_349_plan_capture_has_exact_180_distinct_origins_and_no_166_success')

# Only names are tested here. No future final-job ID or successful origin is
# fabricated to exercise the immutable master's optional nonnumeric final job.
for names,label in [(['plan'],'master_plan_only_allowed'),
                    (['plan','final'],'master_plan_and_optional_final_allowed')]:
    m.validate_non_numeric_names('master',names)
    add(label)
for key,names,label in [
    ('master',['plan','final','final'],'duplicate_master_final_rejected'),
    ('master',['plan','unknown'],'unknown_master_side_job_rejected'),
    ('master',['final'],'missing_master_plan_rejected'),
    ('reference',[m.MATRICES['reference'][4],'final'],'reference_extra_final_rejected')]:
    try:
        m.validate_non_numeric_names(key,names)
    except ValueError:
        add(label)
    else:
        raise AssertionError(label)


def all_refs(value):
    if isinstance(value, dict):
        if set(value) == {'path','sha256','bytes'}:
            yield value
        else:
            for v in value.values():
                yield from all_refs(v)
    elif isinstance(value, list):
        for v in value:
            yield from all_refs(v)


def rejected(name, mutate):
    with tempfile.TemporaryDirectory() as directory:
        temp = pathlib.Path(directory)
        b = copy.deepcopy(bundle)
        for ref in all_refs(b):
            target = temp / ref['path']
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / ref['path'], target)
        mutate(b, temp)
        try:
            execute(b, evidence_root=temp)
        except (ValueError, KeyError, FileNotFoundError) as error:
            add(name, str(error)[:180])
        else:
            raise AssertionError('Rejected-control unexpectedly accepted: ' + name)


def rewrite(root, ref, change):
    p = root / ref['path']
    value = json.loads(p.read_bytes())
    change(value)
    raw = (json.dumps(value) + '\n').encode()
    p.write_bytes(raw)
    ref.update(sha256=m.sha(raw), bytes=len(raw))


rejected('missing_master_page_rejected', lambda b,t: b['matrices']['master']['jobs'].pop())
rejected('changed_pagination_total_rejected', lambda b,t: rewrite(t,b['matrices']['reference']['jobs'][1],
    lambda j:j.update(total_count=j['total_count']+1)))
rejected('duplicate_actual_job_id_rejected', lambda b,t: rewrite(t,b['matrices']['master']['jobs'][0],
    lambda j:j['jobs'][1].update(id=j['jobs'][0]['id'])))
rejected('wrong_reference_head_rejected', lambda b,t: rewrite(t,b['matrices']['reference']['run'],
    lambda j:j.update(head_sha=m.MASTER_HEAD)))
rejected('wrong_reference_attempt_rejected', lambda b,t: rewrite(t,b['matrices']['reference']['jobs'][0],
    lambda j:j['jobs'][0].update(run_attempt=2)))


def remove_required_step(b,t):
    ref = b['matrices']['reference']['jobs'][0]
    def change(j):
        job = next(x for x in j['jobs'] if x['conclusion']=='success' and x['name'].startswith('reproduce-original-long-'))
        job['steps'] = [s for s in job['steps'] if s['name'] != m.STEP]
    rewrite(t, ref, change)
rejected('successful_job_without_exact_identity_step_rejected', remove_required_step)
rejected('wrong_repair_job_id_rejected', lambda b,t: rewrite(t,b['repairs']['00_139']['job'],
    lambda j:j.update(id=m.REPAIRS['00_156'][1])))
rejected('wrong_repair_job_conclusion_rejected', lambda b,t: rewrite(t,b['repairs']['00_139']['job'],
    lambda j:j.update(conclusion='failure')))
rejected('wrong_repair_archive_digest_rejected', lambda b,t: rewrite(t,b['repairs']['00_139']['artifact'],
    lambda j:j.update(digest='sha256:'+m.REPAIRS['00_156'][4])))
rejected('future_166_origin_registration_rejected', lambda b,t:b['repairs'].update({'00_166':b['repairs']['00_139']}))
rejected('wrong_pending_166_job_rejected', lambda b,t: rewrite(t,b['pending_repairs']['00_166']['metadata'],
    lambda j:j['job'].update(id=m.REPAIRS['00_139'][1])))
rejected('changed_authentication_report_rejected', lambda b,t: rewrite(t,b['repairs']['00_139']['authentication_report'],
    lambda j:j.update(required_modules=83)))


def duplicate_artifact_name(b,t):
    ref = b['matrices']['reference']['artifacts'][0]
    actual = m.evidence_file(ROOT, bundle['matrices']['reference']['jobs'][0])['jobs']
    name = next(j['name'].removeprefix('reproduce-original-long-') for j in actual
                if j['conclusion']=='success' and j['name'].startswith('reproduce-original-long-'))
    expected = m.MATRICES['reference'][5].format(run=m.REFERENCE_RUN,batch=name)
    def change(j):
        other = next(a for a in j['artifacts'] if a['name'] != expected)
        other['name'] = expected
    rewrite(t,ref,change)
rejected('ambiguous_successful_artifact_name_rejected', duplicate_artifact_name)
rejected('wrong_artifact_origin_rejected', lambda b,t: rewrite(t,b['matrices']['reference']['artifacts'][0],
    lambda j:j['artifacts'][0]['workflow_run'].update(head_sha=m.MASTER_HEAD)))


for relative,label in [
    ('ci/rg_d1_required_numeric_batches_20261103/batch00_139.json','changed_original_plan_rejected'),
    (m.SPEC,'changed_master_spec_rejected'),
    (m.ZERO_ITEM,'changed_zero_fresh_composite_origin_rejected'),
    (m.PENDING_REPAIRS['00_166']['completion_spec']['path'],'changed_pending_166_scope_rejected')]:
    with tempfile.TemporaryDirectory() as directory:
        checkout = pathlib.Path(directory) / 'checkout'
        numeric = json.loads((CHECKOUT/m.SPEC).read_bytes())
        paths = [m.SPEC,m.ORIGIN,m.REGISTRY,m.ZERO_ITEM,numeric['head_plan']]
        paths += [row['plan'] for row in numeric['jobs']]
        paths += ['ci/rg_d1_numeric_remainder_20261103/batch'+batch+'.json'
                  for batch in m.REMAINDER_SPECS]
        paths += [row['completion_spec']['path'] for row in m.PENDING_REPAIRS.values()]
        for relative_source in paths:
            target = checkout/relative_source
            target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(CHECKOUT/relative_source,target)
        p = checkout / relative
        p.write_bytes(p.read_bytes()+b'\n')
        try:
            execute(checkout=checkout)
        except ValueError as error:
            add(label,str(error)[:180])
        else:
            raise AssertionError(label)


spec_value = json.loads((CHECKOUT / m.SPEC).read_bytes())
plans = {p['batch']:p for p in spec_value['jobs']}
registry = json.loads((CHECKOUT / m.REGISTRY).read_bytes())
late = set(registry['affected_numeric_batches']) & {b for b,p in plans.items() if p['wave']==2}
outside = next(b for b in registry['affected_numeric_batches'] if b not in late)
try:
    m.old_binding(outside,plans,{},late)
except ValueError:
    add('unknown_original_job_outside_90_registered_wave_two_cases_rejected')
else:
    raise AssertionError('Unregistered original-job lookup accepted')
inside = next(iter(late))
lookup = m.old_binding(inside,plans,{},late)
assert set(lookup) == {'original_job_lookup'}
assert lookup['original_job_lookup']['job_name'] == 'original-numeric-'+inside
assert 'original_job' not in lookup
add('allowed_late_lookup_preserves_name_without_inventing_job_id')


with tempfile.TemporaryDirectory() as directory:
    temp = pathlib.Path(directory)
    output, pending = temp/'contract.json',temp/'report.json'
    command = [sys.executable,'-B',str(SCRIPT),'--checkout',str(CHECKOUT),
        '--evidence-root',str(ROOT),'--evidence',str(EVIDENCE),
        '--evidence-sha256',EVIDENCE_SHA,'--report',str(pending),'--seal',str(output)]
    result = subprocess.run(command,capture_output=True,text=True)
    assert result.returncode == 2, result.stderr
    assert not output.exists()
    observed = json.loads(pending.read_bytes())
    assert observed['distinct_successful_complete_batch_origins'] == 180
    assert observed['sealed_contract_written'] is False
    assert not list(temp.glob('*.incomplete-*'))
    add('requested_seal_hard_blocked_with_exit_2_and_no_partial_contract',result.stdout.strip())
    # Wrong inventory must fail before any report or contract can be written.
    pending.unlink()
    command[command.index(EVIDENCE_SHA)] = '0'*64
    bad = subprocess.run(command,capture_output=True,text=True)
    assert bad.returncode != 0 and not pending.exists() and not output.exists()
    add('wrong_frozen_evidence_sha_rejected_before_output')
    output.write_bytes(b'preserve-existing-file\n')
    try:
        m.atomic_json(output,{'no':'replacement'},exclusive=True)
    except FileExistsError:
        pass
    else:
        raise AssertionError('Exclusive sealed output overwrote existing file')
    assert output.read_bytes() == b'preserve-existing-file\n'
    assert not list(temp.glob('*.incomplete-*'))
    add('exclusive_atomic_output_preserves_existing_file')

result = dict(status='ACTUAL_PENDING_PATH_AND_REJECTION_CONTROLS_PASSED',
    builder_sha256=m.sha(SCRIPT.read_bytes()),evidence_sha256=EVIDENCE_SHA,
    source_spec_sha256=m.SPEC_SHA, tests=len(results), results=results,
    actual_successful_batch_origins=180,total_original_batches=349,
    successful_full_contract_positive_path_tested=False,
    reason='Complete actual 349-batch coverage does not yet exist; no synthetic successful contract was made.',
    remote_mutations=False,whole_degree_one_large_complete=False)
m.atomic_json(args.output,result)
print(json.dumps({k:result[k] for k in ['status','builder_sha256','tests','actual_successful_batch_origins']}))
