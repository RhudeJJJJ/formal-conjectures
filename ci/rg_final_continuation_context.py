"""Validate the fixed checkout and sealed inputs of the exact-run callback.

The callback is installed on default main, so GITHUB_SHA describes the
workflow's artifact origin. It is never substituted for the reviewed proof
source commit or overwritten to mimic the checkout.
"""
import hashlib, json, os, pathlib, re, subprocess, urllib.request

ROOT = pathlib.Path(__file__).resolve().parents[1]
REPOSITORY = 'RhudeJJJJ/formal-conjectures'
NUMERIC_RUN = 41686621300
NUMERIC_SHA = 'aaeaec3cec22467d3f0b83b1761bfb40087bb991'
NUMERIC_WORKFLOW = '.github/workflows/rg-d1-numeric-and-final-20261103.yml'
NUMERIC_NAME = 'RG bounded original D1 numeric reconstruction and automatic family join'
BRANCH = 'rg-degree-one-large-20261103'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def validate_numeric_run(run):
    assert type(run['id']) is int and run['id'] == NUMERIC_RUN
    assert run['head_sha'] == NUMERIC_SHA
    assert run['head_branch'] == BRANCH and run['path'] == NUMERIC_WORKFLOW
    assert run['name'] == NUMERIC_NAME and run['status'] == 'completed'
    assert type(run['run_attempt']) is int and run['run_attempt'] == 1
    assert run['repository']['full_name'] == REPOSITORY


def get_numeric_run():
    from rg_github_rate_limit import api_open
    request = urllib.request.Request(
        'https://api.github.com/repos/' + REPOSITORY + '/actions/runs/' + str(NUMERIC_RUN),
        headers={'Authorization': 'Bearer ' + os.environ['GITHUB_TOKEN'],
            'Accept': 'application/vnd.github+json', 'X-GitHub-Api-Version': '2022-11-28'},
        method='GET')
    with api_open(request) as response:
        return json.load(response)


def validate_context():
    descriptor = json.loads(os.environ['RG_FINAL_CONTINUATION_DESCRIPTOR'])
    assert descriptor['kind'] == 'SEALED_EXACT_NUMERIC_RUN_FINAL_CALLBACK'
    assert descriptor['repository'] == os.environ['GITHUB_REPOSITORY'] == REPOSITORY
    assert descriptor['numeric_run'] == NUMERIC_RUN
    assert descriptor['numeric_source_commit'] == NUMERIC_SHA
    assert descriptor['numeric_workflow_path'] == NUMERIC_WORKFLOW
    assert descriptor['numeric_branch'] == BRANCH
    assert type(descriptor['numeric_run_attempt']) is int and descriptor['numeric_run_attempt'] == 1
    assert descriptor['callback_default_branch'] == 'main'
    proof_commit = descriptor['proof_source_commit']
    assert re.fullmatch(r'[0-9a-f]{40}', proof_commit)
    checked_commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    assert checked_commit == proof_commit, ('Fixed reviewed checkout differs', checked_commit, proof_commit)
    assert re.fullmatch(r'[0-9a-f]{40}', os.environ['GITHUB_SHA'])
    assert os.environ['GITHUB_REF'] == 'refs/heads/main'
    event = json.loads(pathlib.Path(os.environ['GITHUB_EVENT_PATH']).read_bytes())
    assert event['repository']['full_name'] == REPOSITORY
    if os.environ['GITHUB_EVENT_NAME'] == 'workflow_run':
        assert event['action'] == 'completed'
        validate_numeric_run(event['workflow_run'])
        entrypoint = 'PINNED_MASTER_COMPLETION_EVENT'
    else:
        assert os.environ['GITHUB_EVENT_NAME'] == 'workflow_dispatch'
        assert event.get('inputs') in ({}, None), 'Manual replay accepts no origin overrides'
        entrypoint = 'PINNED_COMPLETED_MASTER_MANUAL_REPLAY'
    # A read-only live observation closes the install/completion race. Manual
    # replay cannot run early, select another master, or bypass an upstream job.
    run = get_numeric_run()
    validate_numeric_run(run)
    if os.environ['GITHUB_EVENT_NAME'] == 'workflow_run':
        assert event['workflow_run']['conclusion'] == run['conclusion']
    # The old overall run may fail: every individual numeric batch, including
    # an explicitly sealed successful replacement, is checked by the collector.
    files = descriptor['bound_files']
    assert set(files) == {
        'ci/rg_d1_required_numeric_batches_20261103.json',
        'ci/rg_d1_numeric_run41686621300_20261103.json',
        'ci/rg_d1_20261103_verified_continuation_contract.json',
        'ci/rg_d1_20261103_verified_numeric_replacements.json',
        'ci/rg_current_final_source_binding_20261103.json',
    }
    for relative, digest in files.items():
        assert re.fullmatch(r'[0-9a-f]{64}', digest)
        assert sha((ROOT / relative).read_bytes()) == digest, relative
    report = dict(descriptor,
        workflow_head_commit=os.environ['GITHUB_SHA'],
        workflow_event=os.environ['GITHUB_EVENT_NAME'],
        callback_run=int(os.environ['GITHUB_RUN_ID']),
        callback_run_attempt=int(os.environ['GITHUB_RUN_ATTEMPT']),
        entrypoint=entrypoint,
        upstream_run_attempt=run['run_attempt'],
        upstream_status=run['status'],
        upstream_conclusion=run['conclusion'],
        status='EXACT_CALLBACK_CONTEXT_ONLY_NO_NEW_KERNEL_PROOF')
    return report


if __name__ == '__main__':
    report = validate_context()
    out = ROOT / 'Proofs/RG_Lean_20261019/build/final_continuation_context.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report), flush=True)
