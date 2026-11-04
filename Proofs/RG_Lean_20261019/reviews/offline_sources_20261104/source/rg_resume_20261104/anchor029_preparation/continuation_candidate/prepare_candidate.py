#!/usr/bin/env python3
"""Derive a local continuation from frozen authenticated evidence and source text.

No archive read, object restoration, Lean invocation, authenticator rerun, network
access, CI invocation or remote mutation is performed by this preparation.
"""
import ast
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREP = HERE.parent
PRODUCER = PREP / 'original_anchor029_candidate'
AUTH_SHA = 'd5189d1fb0493e394d65054c29f1a4ac3a934e84d2e8873172bb758207312783'
GRAPH_SHA = 'f48e155c412d5e75a8a2980851506c48e69985a4b4c2c6ba3ea985af27d93540'
OLD_WORKFLOW = '.github/workflows/rg-middle-anchor029-original-recovery-20261104.yml'
OLD_WORKFLOW_SHA = '6676ba35ed497f7479d0021a75714af3ab1c1e98086dab171ff2bc5cfd8c1fe2'
OLD_PLAN = 'ci/rg_middle_anchor029_generic_recovered_restore_plan_20261104.json'
OLD_PLAN_SHA = 'fe37ffe775fcc06a969c72349249df46c3fbc051316ffdd699ba30472391177b'
NEW_WORKFLOW = '.github/workflows/rg-middle-anchor029-partial-resume-20261104.yml'
NEW_PLAN = 'ci/rg_middle_anchor029_partial_resume_restore_plan_20261104.json'
NEW_MANIFEST = 'ci/rg_middle_anchor029_run41826563525_partial_prior_exports.json'
BRANCH = 'rg-middle-anchor029-partial-resume-20261104'
ENDPOINT = 'Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate029'
ALLOWED = {'Classical.choice', 'Quot.sound', 'propext'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def bound(path, expected):
    data = path.read_bytes()
    assert sha(data) == expected, str(path)
    return json.loads(data)


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def git_blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def named_checks(code):
    # Resolve exactly the namespace/section forms in these fixed source files.
    stack, namespace, names = [], '', []
    for line in code.splitlines():
        line = line.strip()
        match = re.fullmatch(r'namespace\s+([\w.]+)', line)
        if match:
            name = match[1]
            stack.append((name, namespace))
            namespace = namespace + '.' + name if namespace else name
            continue
        match = re.fullmatch(r'(?:noncomputable\s+)?section(?:\s+([\w.]+))?', line)
        if match:
            stack.append((match[1], namespace))
            continue
        match = re.fullmatch(r'end(?:\s+([\w.]+))?', line)
        if match:
            assert stack
            name, previous = stack.pop()
            assert match[1] is None or match[1] == name
            namespace = previous
            continue
        match = re.fullmatch(r'#print\s+axioms\s+([\w.]+)', line)
        if match:
            name = match[1]
            if name.startswith('_root_.'):
                name = name.removeprefix('_root_.')
            elif not name.startswith('Gebendorfer.'):
                assert namespace
                name = namespace + '.' + name
            names.append(name)
    assert not stack and not namespace
    return names


def main():
    auth_path = PRODUCER / 'actual/original_anchor029_authentication.json'
    auth = bound(auth_path, AUTH_SHA)
    assert auth['status'] == 'ACTUAL_TERMINAL_FAILURE_PARTIAL_ARCHIVE_EVIDENCE_AUTHENTICATED'
    assert auth['repository'] == 'RhudeJJJJ/formal-conjectures'
    assert (auth['run'], auth['job'], auth['run_attempt']) == (41826563525, 126562666235, 1)
    assert auth['source_commit'] == '5b7bd43a9f3ca170b19450dd4f34fe9d12bbba90'
    assert auth['native_run_conclusion'] == auth['native_job_conclusion'] == 'cancelled'
    assert auth['native_identity_authenticated']
    assert not auth['proof_rows_synthesized'] and not auth['production_receipt_created_by_authenticator']
    assert not auth['full_original_endpoint_success_authenticated']
    assert not auth['anchor029_certificate_claim'] and not auth['full_degree_one_middle_family_claim']
    assert auth['family_count_change_from_this_anchor_run'] == 0
    artifact = auth['artifact']
    assert artifact['id'] == 13351145439 and artifact['size_in_bytes'] == 5122551
    assert artifact['digest'] == 'sha256:11c263c3f06adca05f4810ed1d410221f6e2d4b1a479dcf8b731f435d5b98fd5'
    audit = auth['archive_audit']
    assert audit['complete_281_original_source_bundle'] and audit['actual_recursive_closure_recomputed']
    assert audit['actual_original_source_files_checked'] == 281
    assert audit['completed_fresh_count'] == len(audit['modules']) == 108
    assert audit['actual_fresh_output_bytes'] == 15631024
    assert audit['actual_named_axiom_profiles'] == 545
    assert audit['required_prior_rows_observed'] == 118
    assert audit['additional_diagnostic_prior_rows_observed'] == 243
    assert not audit['full_original_receipt_validated'] and audit['receipt_sha256'] is None

    graph = bound(PREP / 'static_source_closure/source_graph.json', GRAPH_SHA)
    assert auth['current_original_source_graph_sha256'] == GRAPH_SHA
    fixed = auth['fixed_input_sha256']
    inventory = bound(PREP / 'static_source_closure/source_inventory.json',
                      fixed['static_source_closure/source_inventory.json'])
    metadata = bound(PREP / 'static_source_closure/metadata_and_parser_source_capture.json',
                     fixed['static_source_closure/metadata_and_parser_source_capture.json'])
    initial = bound(PREP / 'generic_recovered_plan_source_capture.json',
                    fixed['generic_recovered_plan_source_capture.json'])
    files = {}
    for row in metadata['files'] + initial['manifests']:
        raw = row['content'].encode()
        assert git_blob(raw) == row['git_blob_sha']
        assert row['path'] not in files or files[row['path']] == raw
        files[row['path']] = raw
    parser_path = 'Proofs/RG_Lean_20261019/verify.py'
    functions = [node for node in ast.parse(files[parser_path]).body
                 if isinstance(node, ast.FunctionDef) and node.name == 'without_comments']
    assert len(functions) == 1
    parser_scope = {'re': re}
    # Only the pinned pure comment/string parser is evaluated, never a verifier.
    exec(compile(ast.Module(body=functions, type_ignores=[]), parser_path, 'exec'), parser_scope)
    without_comments = parser_scope['without_comments']
    sources = {}
    for capture in inventory['capture_files']:
        data = bound(PREP / capture['path'], capture['sha256'])
        for row in data['sources']:
            raw = row['content'].encode()
            assert git_blob(raw) == row['git_blob_sha']
            assert row['module'] not in sources or sources[row['module']] == raw
            sources[row['module']] = raw
    assert len(sources) == len(graph['source_sha256']) == 281
    assert set(sources) == set(graph['source_sha256'])
    for name, raw in sources.items():
        assert sha(raw) == graph['source_sha256'][name]

    old_plan = bound(PRODUCER / 'patch' / OLD_PLAN, OLD_PLAN_SHA)
    base_manifest = 'ci/rg_reusable_analytic_kernel_base_complete_scope_capsule.json'
    offered = {}
    for path in [base_manifest, *old_plan]:
        manifest = json.loads(files[path])
        for name, row in manifest['modules'].items():
            assert name not in offered
            offered[name] = row
    old_prior = set(offered) & set(sources)
    original_fresh = set(sources) - old_prior
    assert len(offered) == 361 and len(old_prior) == 118 and len(original_fresh) == 163

    checks = {name: named_checks(without_comments(sources[name].decode()))
              for name in sorted(original_fresh)}
    assert all(checks.values()) and sum(map(len, checks.values())) == 838
    actual = audit['modules']
    completed = set(actual)
    assert completed == set(audit['completed_fresh_modules']) and completed <= original_fresh
    assert not completed & set(offered)
    rows = {}
    for name in sorted(completed):
        item = actual[name]
        row = item['row']
        assert row['module'] == name and row['mode'] == 'FRESH_KERNEL_EXPORT'
        assert 'origin' not in row and 'transport_capsule' not in row and not row.get('additional_outputs')
        assert row['source_sha256'] == graph['source_sha256'][name]
        assert row['source_closure_sha256'] == graph['source_closure_sha256'][name]
        assert [p['declaration'] for p in item['named_axiom_profiles']] == checks[name]
        assert all(set(p['axioms']) <= ALLOWED for p in item['named_axiom_profiles'])
        assert all(set(p) <= ALLOWED for p in row['axiom_profiles'])
        assert set(graph['source_dependencies'][name]) <= old_prior | completed
        rows[name] = row
    remaining = original_fresh - completed
    assert len(remaining) == 55 and len(old_prior | completed) == 226
    assert sum(len(checks[n]) for n in completed) == 545
    assert sum(len(checks[n]) for n in remaining) == 293
    cells = sorted(n for n in remaining if re.search(r'WideAnchor029Cell\d{3}$', n))
    batches = sorted(n for n in remaining if re.search(r'WideAnchor029Batch\d{3}$', n))
    final_heads = sorted(remaining - set(cells) - set(batches))
    prefix = 'Proofs.RadenkovicGutmanWideAnchor029'
    assert cells == [prefix + f'Cell{i:03}' for i in range(88, 134)]
    assert batches == [prefix + f'Batch{i:03}' for i in range(8, 14)]
    assert final_heads == sorted([prefix + 'FinitePayment', prefix + 'OriginalAnchor', ENDPOINT])

    partial = dict(repository=auth['repository'], run=auth['run'], job=auth['job'],
        source_commit=auth['source_commit'], artifact_id=artifact['id'],
        artifact_sha256=artifact['digest'].removeprefix('sha256:'),
        lean_version='4.33.1', mathlib='0df444a360eaa60ab8c11dca51a86af692955474',
        origin_context=dict(scope='INDIVIDUAL_COMPLETED_KERNEL_EXPORTS_ONLY',
            whole_job_conclusion='cancelled', completed_endpoint_receipt=False,
            full_original_log_sha256=auth['native_job_log_sha256'],
            authenticated_partial_archive_report_sha256=AUTH_SHA,
            completed_fresh_modules=108, completed_named_axiom_profiles=545), modules=rows)
    patch = HERE / 'patch'
    dump(patch / NEW_MANIFEST, partial)
    # Keep all four historical plan references and their order; append one new origin.
    (patch / NEW_PLAN).write_text(json.dumps([*old_plan, NEW_MANIFEST], indent=2) + '\n')

    old_workflow = (PRODUCER / 'patch' / OLD_WORKFLOW).read_bytes()
    assert sha(old_workflow) == OLD_WORKFLOW_SHA
    changes = [
        ('name: RG original Anchor029 with recovered generic prerequisites',
         'name: RG original Anchor029 continuation from authenticated partial exports'),
        ('    branches: [rg-middle-anchor029-original-recovery-20261104]',
         f'    branches: [{BRANCH}]'),
        (f"    paths: ['{OLD_WORKFLOW}', '{OLD_PLAN}']",
         f"    paths: ['{NEW_WORKFLOW}', '{NEW_PLAN}', '{NEW_MANIFEST}']"),
        (f'            plan: {OLD_PLAN}', f'            plan: {NEW_PLAN}'),
        ('            max_fresh: 163', '            max_fresh: 55'),
        ('          name: rg-middle-anchor029-original-recovery-20261104-exports-${{ github.run_id }}-${{ strategy.job-index }}',
         '          name: rg-middle-anchor029-partial-resume-20261104-exports-${{ github.run_id }}-${{ strategy.job-index }}'),
    ]
    new_workflow = old_workflow.decode()
    for before, after in changes:
        assert new_workflow.count(before) == 1
        new_workflow = new_workflow.replace(before, after, 1)
    reconstructed = new_workflow
    for before, after in reversed(changes):
        assert reconstructed.count(after) == 1
        reconstructed = reconstructed.replace(after, before, 1)
    assert reconstructed.encode() == old_workflow
    target = patch / NEW_WORKFLOW
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(new_workflow)

    bindings = {}
    for name in sorted(original_fresh):
        row = dict(source_sha256=graph['source_sha256'][name],
                   source_closure_sha256=graph['source_closure_sha256'][name],
                   expected_named_axiom_checks=checks[name])
        if name in completed:
            row.update(status='AUTHENTICATED_COMPLETED_EXPORT_FROM_CANCELLED_PRODUCER',
                       output_sha256=actual[name]['row']['output_sha256'],
                       module_log_sha256=actual[name]['log_sha256'],
                       authenticated_named_axiom_profiles=actual[name]['named_axiom_profiles'])
        else:
            row.update(status='REQUIRES_FUTURE_FRESH_KERNEL_EXPORT',
                       local_dependencies=graph['source_dependencies'][name])
        bindings[name] = row
    scope = dict(kind='AUTHENTICATED_PRIOR_AND_SOURCE_ONLY_CONTINUATION_PLAN',
        endpoint=ENDPOINT, original_source_graph_sha256=GRAPH_SHA,
        producer_authentication_report_sha256=AUTH_SHA,
        source_identity_commit=auth['reviewed_original_source_identity_commit'],
        required_modules=281, original_prior_modules=118, newly_authenticated_prior_modules=108,
        predicted_required_prior_modules=226, predicted_fresh_modules=55,
        original_named_axiom_checks=838, inherited_named_axiom_checks=545,
        remaining_named_axiom_checks=293, original_prior_module_names=sorted(old_prior),
        completed_producer_module_names=sorted(completed), remaining_module_names=sorted(remaining),
        remaining_categories=dict(cells=cells, batches=batches, final_heads=final_heads),
        original_fresh_module_bindings=bindings,
        actual_continuation_preflight_performed=False, actual_continuation_kernel_run_performed=False,
        full_original_endpoint_success_claimed=False, middle_family_success_claimed=False,
        global_rg_success_claimed=False)
    dump(HERE / 'continuation_scope.json', scope)

    production = []
    for path in [NEW_WORKFLOW, NEW_PLAN, NEW_MANIFEST]:
        data = (patch / path).read_bytes()
        production.append(dict(path=path, bytes=len(data), sha256=sha(data), git_blob_sha=git_blob(data)))
    inventory_report = dict(kind='LOCAL_PUBLICATION_CANDIDATE_NOT_A_CI_RESULT',
        proposed_branch=BRANCH, publication_base_commit_requires_root_confirmation=True,
        original_source_identity_commit=auth['reviewed_original_source_identity_commit'],
        producer_source_commit=auth['source_commit'], exact_production_paths=[r['path'] for r in production],
        files=production, historical_files_modified=[], lean_sources_modified=[],
        producer_authentication_report_sha256=AUTH_SHA,
        continuation_scope_sha256=sha((HERE / 'continuation_scope.json').read_bytes()),
        prepare_script_sha256=sha(Path(__file__).read_bytes()),
        limits=dict(workers=1, module_timeout_seconds=600, memory_reserve_mib=2048,
                    job_timeout_minutes=360, max_fresh=55, source_bundle_modules=281,
                    artifact_retention_days=90))
    dump(HERE / 'publication_inventory.json', inventory_report)
    review = dict(kind='CONTINUATION_DESIGN_AND_LOCAL_DERIVATION_REVIEW',
        producer_evidence=auth_path.as_posix(), producer_evidence_sha256=AUTH_SHA,
        minimal_production_change='Exactly three new files: one partial prior manifest, one appended plan, one isolated workflow.',
        unchanged='All Lean sources, endpoint, original four manifest references, original origins, restore/verifier code, strict compiler flags, workers, memory reserve, per-module and job limits, and retention behavior.',
        authenticated_partial_rows_copied_verbatim_as_json_values=True,
        partial_origin_remains_cancelled=True, completed_producer_receipt_claimed=False,
        original_workflow_reconstructs_byte_for_byte_after_reversing_six_declared_line_changes=True,
        predicted_frontier=dict(required=281, prior=226, fresh=55),
        profile_conservation=dict(original=838, authenticated=545, remaining=293,
            binding='Exact ordered declaration lists per original module; repeated checks in different modules remain separate.'),
        required_postrun_gates=[
            'A separately frozen continuation authenticator must bind the new native run/job/commit and full artifact digest.',
            'Require all 281 original source bytes and recursive closure identities unchanged.',
            'For complete success require native success and an actual complete 281-module receipt with exact 226 PRIOR plus 55 FRESH modes.',
            'The 108 producer rows must retain the cancelled producer origin and original output/profile identities; prior origins of the old 118 remain unchanged.',
            'Bind all 838 original named checks per module: 545 from this frozen partial authentication, 293 from the 55 new actual module logs.',
            'Check new archive rows, module logs, actual output bytes, complete original source bundle and receipt; never synthesize a receipt.',
            'An original Anchor029 endpoint success must not be described as a completed degreeOneMiddle family or global RG theorem.'
        ],
        dependencies=[
            'The existing base capsule and original four manifest archives remain required; the new plan adds the genuine producer archive once.',
            'The production restorer will verify archive digest and original exact records/objects, then the unchanged preflight/verifier will recheck current source/closure/object identities.',
            'The tight max_fresh=55 rejects any additional missing required prior; transport availability is not a proof substitute.',
            'The 360-minute job cap remains unchanged; 55 modules alone do not guarantee completion within that cap.',
            'Root must select/confirm the publication base, freeze the postrun verifier, review the candidate and perform any remote publication.'
        ],
        no_artifact_zip_reads=True, no_authenticator_rerun=True, no_object_restore=True,
        no_lean_execution=True, no_remote_reads_or_writes=True, no_ci_started=True,
        original_anchor029_proved=False, middle_family_proved=False, global_rg_proved=False)
    dump(HERE / 'continuation_review.json', review)
    print(json.dumps(dict(inventory_path=str(HERE / 'publication_inventory.json'),
        inventory_sha256=sha((HERE / 'publication_inventory.json').read_bytes()),
        scope_sha256=sha((HERE / 'continuation_scope.json').read_bytes()),
        review_sha256=sha((HERE / 'continuation_review.json').read_bytes()), production_files=production), indent=2))


if __name__ == '__main__':
    main()
