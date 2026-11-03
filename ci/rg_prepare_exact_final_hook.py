"""Generate a default-main callback only after real final inputs are sealed.

This writes local reviewable files. It never publishes, dispatches, edits main,
or accepts unresolved prerequisite origins. The reviewed task commit must
already contain the bound contracts and final-continuation helpers.
"""
import argparse, hashlib, json, pathlib, re

REPOSITORY = 'RhudeJJJJ/formal-conjectures'
RUN = 41686621300
NUMERIC_SHA = 'aaeaec3cec22467d3f0b83b1761bfb40087bb991'
NAME = 'RG bounded original D1 numeric reconstruction and automatic family join'
PATH = '.github/workflows/rg-d1-numeric-and-final-20261103.yml'
BRANCH = 'rg-degree-one-large-20261103'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def sealed_job(item):
    assert all(isinstance(item[k], int) and item[k] > 0 for k in ('run', 'job', 'artifact_id'))
    assert re.fullmatch(r'[0-9a-f]{40}', item['source_commit'])
    assert re.fullmatch(r'[0-9a-f]{64}', item['artifact_sha256'])
    assert item['artifact_name'] and item['required_success_step']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--proof-source-commit', required=True)
    p.add_argument('--numeric-spec', type=pathlib.Path, required=True)
    p.add_argument('--numeric-origin', type=pathlib.Path, required=True)
    p.add_argument('--auxiliary-contract', type=pathlib.Path, required=True)
    p.add_argument('--numeric-replacements', type=pathlib.Path, required=True)
    p.add_argument('--continuation-workflow', type=pathlib.Path, required=True)
    p.add_argument('--output-root', type=pathlib.Path, required=True)
    a = p.parse_args()
    assert re.fullmatch(r'[0-9a-f]{40}', a.proof_source_commit) and set(a.proof_source_commit) != {'0'}
    paths = {
        'ci/rg_d1_required_numeric_batches_20261103.json': a.numeric_spec,
        'ci/rg_d1_numeric_run41686621300_20261103.json': a.numeric_origin,
        'ci/rg_d1_20261103_verified_continuation_contract.json': a.auxiliary_contract,
        'ci/rg_d1_20261103_verified_numeric_replacements.json': a.numeric_replacements,
    }
    loaded = {relative: (path.read_bytes(), json.loads(path.read_bytes())) for relative, path in paths.items()}
    spec_raw, spec = loaded['ci/rg_d1_required_numeric_batches_20261103.json']
    _, origin = loaded['ci/rg_d1_numeric_run41686621300_20261103.json']
    _, contract = loaded['ci/rg_d1_20261103_verified_continuation_contract.json']
    _, replacements = loaded['ci/rg_d1_20261103_verified_numeric_replacements.json']
    assert spec['kind'] == 'EXACT_MISSING_D1_ORIGINAL_NUMERIC_BATCHES' and len(spec['jobs']) == 349
    assert origin['kind'] == 'PINNED_ORIGINAL_NUMERIC_RUN_FOR_FINAL_ONLY_CONTINUATION'
    assert origin['repository'] == REPOSITORY and origin['run'] == RUN and origin['source_commit'] == NUMERIC_SHA
    assert origin['workflow_path'] == PATH and origin['branch'] == BRANCH
    assert origin['numeric_spec_sha256'] == sha(spec_raw)
    assert contract['kind'] == 'SEALED_D1_COMPLETION_PREREQUISITES'
    for key in ('source_endpoint_sha256', 'source_endpoint_closure_sha256'):
        assert origin[key] == contract[key] == spec[key]
    for item in contract['jobs']:
        assert 'workflow_path' not in item, 'All auxiliary jobs must have actual pinned origins'
        sealed_job(item)
    assert replacements['kind'] == 'SEALED_SUCCESSFUL_ORIGINAL_NUMERIC_BATCH_REPLACEMENTS'
    assert replacements['repository'] == REPOSITORY and replacements['numeric_run'] == RUN
    assert replacements['numeric_source_commit'] == NUMERIC_SHA
    assert replacements['numeric_spec_sha256'] == sha(spec_raw)
    assert replacements['replacements']
    batches = {b['batch']: b for b in spec['jobs']}
    seen = set()
    for item in replacements['replacements']:
        sealed_job(item)
        assert item['batch'] in batches and item['batch'] not in seen
        seen.add(item['batch'])
        assert item['original_plan_sha256'] == batches[item['batch']]['plan_sha256']
        assert item['run'] != RUN and item['original_job'] > 0
    descriptor = dict(kind='SEALED_EXACT_NUMERIC_RUN_FINAL_CALLBACK', repository=REPOSITORY,
        numeric_run=RUN, numeric_source_commit=NUMERIC_SHA, numeric_workflow_path=PATH,
        numeric_branch=BRANCH, proof_source_commit=a.proof_source_commit,
        bound_files={relative: sha(raw) for relative, (raw, _) in loaded.items()})
    original = a.continuation_workflow.read_text()
    assert original.count('\njobs:\n') == 1
    body = original.split('\njobs:\n', 1)[1]
    old_if = "    if: github.repository == 'RhudeJJJJ/formal-conjectures'\n"
    condition = (
        "    if: >-\n"
        "      github.repository == 'RhudeJJJJ/formal-conjectures' &&\n"
        "      github.event.workflow_run.id == 41686621300 &&\n"
        "      github.event.workflow_run.head_sha == 'aaeaec3cec22467d3f0b83b1761bfb40087bb991' &&\n"
        "      github.event.workflow_run.head_branch == 'rg-degree-one-large-20261103' &&\n"
        "      github.event.workflow_run.path == '.github/workflows/rg-d1-numeric-and-final-20261103.yml'\n")
    assert body.count(old_if) == 1
    body = body.replace(old_if, condition, 1)
    timeout = '    timeout-minutes: 360\n'
    assert body.count(timeout) == 1
    encoded = json.dumps(descriptor, separators=(',', ':'))
    assert "'" not in encoded
    body = body.replace(timeout, timeout + "    env:\n      RG_FINAL_CONTINUATION_DESCRIPTOR: '" + encoded + "'\n", 1)
    checkout = '        with:\n          persist-credentials: false\n'
    assert body.count(checkout) == 1
    body = body.replace(checkout, '        with:\n          ref: ' + a.proof_source_commit + '\n          persist-credentials: false\n', 1)
    reserve = '      - name: Reserve actual host space without touching proof inputs\n'
    assert body.count(reserve) == 1
    body = body.replace(reserve,
        '      - name: Require the exact callback event, reviewed checkout and sealed input hashes\n'
        '        run: python3 -B ci/rg_final_continuation_context.py\n' + reserve, 1)
    evidence = '            Proofs/RG_Lean_20261019/build/exact_degree_one_plan.json\n'
    assert body.count(evidence) == 1
    body = body.replace(evidence, '            Proofs/RG_Lean_20261019/build/final_continuation_context.json\n' + evidence, 1)
    body = body.replace('rg-degree-one-large-continuation-final-', 'rg-degree-one-large-exact-hook-final-')
    header = (
        'name: RG exact run41686621300 final family callback\n'
        '# Install only on default main after publishing the fixed reviewed task commit.\n'
        '# No numeric certificates are recompiled; all successful origins stay sealed.\n'
        'on:\n  workflow_run:\n    workflows: ["' + NAME + '"]\n'
        '    types: [completed]\n    branches: [' + BRANCH + ']\n'
        'permissions:\n  contents: read\n  actions: read\n'
        'concurrency:\n  group: rg-degree-one-large-final-41686621300\n  cancel-in-progress: false\n'
        'jobs:\n')
    workflow = a.output_root / '.github/workflows/rg-degree-one-large-exact-run-final-hook-20261103.yml'
    workflow.parent.mkdir(parents=True, exist_ok=True)
    workflow.write_text(header + body)
    descriptor_path = a.output_root / 'ci/rg_d1_exact_final_callback_20261103.json'
    descriptor_path.parent.mkdir(parents=True, exist_ok=True)
    descriptor_path.write_text(json.dumps(descriptor, indent=2) + '\n')
    print(json.dumps(dict(status='LOCAL_REVIEWABLE_CALLBACK_ONLY_NO_PUBLICATION_OR_KERNEL_PROOF',
        proof_source_commit=a.proof_source_commit, workflow=str(workflow),
        workflow_sha256=sha(workflow.read_bytes()), descriptor=str(descriptor_path),
        descriptor_sha256=sha(descriptor_path.read_bytes()))), flush=True)


if __name__ == '__main__':
    main()
