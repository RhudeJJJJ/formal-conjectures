"""Describe a fixed alternatives-only seal without claiming numeric completion.

The 195 alternatives must still pass the collector's concrete-origin validator.
The other 154 original jobs may be pending at seal time, but every one must be
an actually observed job in the fixed master run. Runtime collection requires
all 349 successful jobs and the unchanged source/archive/object checks.
"""
import hashlib
import json
import re

REPOSITORY = 'RhudeJJJJ/formal-conjectures'
RUN = 41686621300
HEAD = 'aaeaec3cec22467d3f0b83b1761bfb40087bb991'
BRANCH = 'rg-degree-one-large-20261103'
SPEC_SHA = 'f47334108b563ae5e20f15fc07b2e4589f6d6e7f49e308bfdb8b4301e689e18e'
REGISTRY = 'ci/rg_d1_original_reference_bytes_20261103.json'
REGISTRY_SHA = 'a04e5e612ce5e927a9f121a03b2786224b84736e64cee1974eaaa8c603693dc9'
KIND = 'ACTUAL_ALTERNATIVES_ONLY_WITH_OBSERVED_ORIGINAL_COVERAGE'
FIXED_OTHER_ALTERNATIVES = {
    '00_137', '00_139', '00_147', '00_156', '00_164', '00_166',
    '00_129', '10_044', '30_013',
}
PENDING = {'queued', 'waiting', 'in_progress'}


def scope(spec_raw, registry_raw):
    assert hashlib.sha256(spec_raw).hexdigest() == SPEC_SHA
    assert hashlib.sha256(registry_raw).hexdigest() == REGISTRY_SHA
    spec, registry = json.loads(spec_raw), json.loads(registry_raw)
    plans = {r['batch']: r for r in spec['jobs']}
    assert len(plans) == len(spec['jobs']) == 349
    references = set(registry['affected_numeric_batches'])
    assert len(references) == len(registry['affected_numeric_batches']) == 186
    assert not references & FIXED_OTHER_ALTERNATIVES
    alternatives = references | FIXED_OTHER_ALTERNATIVES
    assert alternatives <= plans.keys() and len(alternatives) == 195
    originals = set(plans) - alternatives
    assert len(originals) == 154
    assert all(plans[b]['wave'] == 1 for b in originals)
    return plans, alternatives, originals


def original_observation(batch, plan, job):
    assert type(job['id']) is int and job['id'] > 0
    assert job['run_id'] == RUN and job['head_sha'] == HEAD
    assert type(job['run_attempt']) is int and job['run_attempt'] == 1
    assert job['head_branch'] == BRANCH and job['name'] == 'original-numeric-' + batch
    return dict(batch=batch, original_plan_sha256=plan['plan_sha256'],
        run=RUN, source_commit=HEAD, run_attempt=1, job=job['id'],
        job_name=job['name'], status=job['status'], conclusion=job['conclusion'])


def assess(spec_raw, registry_raw, candidates, master, binding_wait,
           evidence_sha256, observed_at):
    plans, alternatives, originals = scope(spec_raw, registry_raw)
    assert re.fullmatch(r'[0-9a-f]{64}', evidence_sha256)
    observed, pending, unsafe = {}, [], []
    for batch in sorted(originals):
        job = master['jobs'].get(batch)
        if job is None:
            unsafe.append(dict(batch=batch, reason='ORIGINAL_JOB_NOT_CREATED'))
            continue
        row = original_observation(batch, plans[batch], job)
        if batch in master['success']:
            assert row['status'] == 'completed' and row['conclusion'] == 'success'
        elif row['status'] in PENDING and row['conclusion'] is None:
            pending.append(batch)
        else:
            unsafe.append(dict(batch=batch, job=row['job'], status=row['status'],
                conclusion=row['conclusion'], reason='NO_SUCCESSFUL_OR_PENDING_ORIGINAL_JOB'))
        observed[batch] = row
    missing = sorted(alternatives - candidates.keys())
    extra = sorted(candidates.keys() - alternatives)
    ready = not missing and not extra and not unsafe and not binding_wait
    report = dict(alternative_contract_ready=ready,
        alternative_batches_required=195, original_batches_required_at_collection=154,
        missing_required_alternative_batches=missing, unexpected_alternative_batches=extra,
        pending_original_coverage=pending, unsafe_original_coverage=unsafe,
        original_jobs_observed_at_sealing=observed,
        full_numeric_successes_required_at_collection=349)
    annotation = None
    if ready:
        annotation = dict(kind=KIND, evidence_sha256=evidence_sha256,
            observed_at=observed_at, alternative_batches=sorted(alternatives),
            original_jobs=observed, pending_original_coverage=pending,
            complete_numeric_metadata_coverage=not pending,
            required_successful_batches_at_collection=349,
            complete_archive_authentication_still_required=True,
            whole_degree_one_large_complete=False)
        validate(annotation, spec_raw, registry_raw, candidates)
    return report, annotation


def validate(annotation, spec_raw, registry_raw, replacements):
    plans, alternatives, originals = scope(spec_raw, registry_raw)
    assert set(annotation) == {'kind', 'evidence_sha256', 'observed_at',
        'alternative_batches', 'original_jobs', 'pending_original_coverage',
        'complete_numeric_metadata_coverage', 'required_successful_batches_at_collection',
        'complete_archive_authentication_still_required', 'whole_degree_one_large_complete'}
    assert annotation['kind'] == KIND
    assert re.fullmatch(r'[0-9a-f]{64}', annotation['evidence_sha256'])
    assert isinstance(annotation['observed_at'], str) and annotation['observed_at']
    assert annotation['alternative_batches'] == sorted(alternatives)
    assert set(replacements) == alternatives
    rows = annotation['original_jobs']
    assert set(rows) == originals
    pending, ids = [], set()
    for batch, row in sorted(rows.items()):
        assert set(row) == {'batch', 'original_plan_sha256', 'run', 'source_commit',
            'run_attempt', 'job', 'job_name', 'status', 'conclusion'}
        assert row['batch'] == batch and row['original_plan_sha256'] == plans[batch]['plan_sha256']
        assert type(row['run']) is int and row['run'] == RUN
        assert row['source_commit'] == HEAD
        assert type(row['run_attempt']) is int and row['run_attempt'] == 1
        assert type(row['job']) is int and row['job'] > 0 and row['job'] not in ids
        ids.add(row['job'])
        assert row['job_name'] == 'original-numeric-' + batch
        if row['status'] in PENDING:
            assert row['conclusion'] is None
            pending.append(batch)
        else:
            assert row['status'] == 'completed' and row['conclusion'] == 'success'
    assert annotation['pending_original_coverage'] == pending
    assert annotation['complete_numeric_metadata_coverage'] is (not pending)
    assert type(annotation['required_successful_batches_at_collection']) is int
    assert annotation['required_successful_batches_at_collection'] == 349
    assert annotation['complete_archive_authentication_still_required'] is True
    assert annotation['whole_degree_one_large_complete'] is False
    return rows


def require_observed_original_success(observed, job):
    """Pending at seal time never substitutes for success at collection time."""
    assert job['id'] == observed['job']
    assert job['run_id'] == observed['run'] == RUN
    assert job['head_sha'] == observed['source_commit'] == HEAD
    assert job['run_attempt'] == observed['run_attempt'] == 1
    assert job['name'] == observed['job_name'] and job['head_branch'] == BRANCH
    assert job['status'] == 'completed' and job['conclusion'] == 'success'
