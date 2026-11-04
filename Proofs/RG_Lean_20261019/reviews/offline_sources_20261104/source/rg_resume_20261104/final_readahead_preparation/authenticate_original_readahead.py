#!/usr/bin/env python3
"""Authenticate only the actual completed original RG owned-readahead continuation.

Preparation only: fixed native run/job/commit identifiers must be bound before use.

This program is offline. It accepts native API captures, the native completed
job log, and the two complete artifact ZIPs. It never creates a kernel receipt
and writes a success report only after every actual-evidence check succeeds.
"""
import argparse
import ast
import collections
import datetime
import runpy
import types
import hashlib
import json
import math
import pathlib
import re
import sys
import zipfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
BASE = ROOT / 'integration_validation'
REPOSITORY = 'RhudeJJJJ/formal-conjectures'
RUN = None  # Bind only after the actual native run exists.
JOB = None  # Bind only after the actual native job exists.
COMMIT = None  # Bind to the actual published continuation commit.
ORIGINAL_PROOF_SOURCE = '10aa67f5f16e8ad00b30ac21332791b008b69cfe'
ORIGINAL_PROOF_RUN = 41800448987
BRANCH = 'rg-degree-one-large-20261103'
WORKFLOW = '.github/workflows/rg-degree-one-large-join-repair-20261104.yml'
WORKFLOW_SHA = '7147154b7091f5459bb35b78c5a837be2bc5505f88927a035c19e489aaf2ff56'
GRAPH_SHA = 'f0e3699070738db4ae272e3adbaf21ef20779082b93e55c1c269842284e8259a'
PROJECTION_SHA = 'f30016a879e80f98d3047ceb404fe088d6d92111e177c4844056cd725498c226'
PREVIOUS_PLAN_SHA = '29e2cf80c90d550da3b6b29b96a9ecd9b745f41c77f5febf78547ae222bd33e2'
DECLARATIONS_SHA = 'c224b1efc499184cdb2bc45b33378239e3e2c3370738daabd8ec9830e937f07e'
NUMERIC_AUDIT_SHA = '899704d2d7169578abee66e68e63b7166239df4c60fbbe5ccb85e5c3878c24b6'
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LC = '621a43d7cf21f87872392a01e874f2f1dbddc926'
ENDPOINT = 'Proofs.RadenkovicGutmanRemainingThreeAssembly'
FINAL = {
    'Proofs.RadenkovicGutmanD1OriginalSharedBothLong',
    'Proofs.RadenkovicGutmanOriginalDegreeOneLarge',
    ENDPOINT,
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
REMAINING = ['degreeOneMiddle', 'degreeTwoThree', 'degreeFourToFortyfive']
BUILD = 'Proofs/RG_Lean_20261019/build/'
RUNTIME = 'ci/rg_d1_20261103_runtime_reconstructed_exports/'
ORIGIN_KEYS = ('repository', 'run', 'job', 'source_commit', 'artifact_id', 'artifact_sha256')
BASE_SHA = {
    'ci/rg_callback_partial_completion.py': '8872cd2515892ab1acf963e48e19162a98225582ba2b6e2579fc732576821b2b',
    'ci/rg_exact_final_source_binding.py': '1d459d526e2c2f2832111fb021d99e9f9ad45f5bc629c1fdcfb33cb694b867a8',
    'ci/rg_exact_numeric_completion.py': '52c9bf602ede0e8913d444fdf03ba1f5bf2bdd9f8f0e17f270bd8407ca0fe539',
    'ci/rg_collect_exact_d1_reproductions.py': '90938b2c9aba656c89287f724f78932fe9e625abb27543abd0d5a906bfc9c761',
    'ci/rg_plan_exact_degree_one_large.py': '9fc72a8644fd66e5045e7d1b3f45c6e8cb71f1bba70d8dc9c17f6173294bf874',
    'Proofs/RG_Lean_20261019/module_outputs.py': '394954aaa39ccb0be1bf124a35091f4cad9b04e5f35e1a34ac84052b8bf779cd',
    'ci/rg_current_final_source_binding_20261103.json': '48a083f8050264c03af22483d793e75bf9f8990793e91f0a46e3e9b25f7f0bbc',
    'ci/rg_d1_20261103_verified_continuation_contract.json': '845467fbdc2106eae11a4e3384a767ec31179c3911e0329b4d6c9934e4df3b70',
    'ci/rg_d1_20261103_verified_numeric_replacements.json': '72c52956c9c6f77228317ba623851953ca3151a3ae7ded9d929ac1251899049d',
    'ci/rg_d1_required_numeric_batches_20261103.json': 'f47334108b563ae5e20f15fc07b2e4589f6d6e7f49e308bfdb8b4301e689e18e',
    'ci/rg_d1_numeric_run41686621300_20261103.json': '9e4fbdfaf1f57b59453b5501e270e4d15b87a06bddcafd719ac882bd026980c7',
    'ci/rg_d1_callback41771586873_partial_prior_exports_20261104.json': '5261abd7410fbd6f10b786d60c03d7606f5143127c9d5900e39fb668218bc32b',
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def file_sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        assert key not in result, ('Repeated JSON key', key)
        result[key] = value
    return result


def decode(raw):
    return json.loads(raw, object_pairs_hook=unique_object)



# Preparation remains locked: none of these bindings supplies a native run.
PARENT_ORIGINAL_AUTHENTICATOR_SHA = '0c01acb3884573c3e8e571d1bd6cd02936e47f072786a8379093732ca0189023'
READAHEAD_GATE_SOURCE_SHA = 'bcdf299c53d1d3fe8ec5be20fc4fa9b2e9d4bc52db001e5627de45d6edc5ef11'
TRANSPORT_PARSER_SOURCE_SHA = '47b9b7affcac54c4c68745ae5f3c5c3d30ad456b5d333beebd767626fddddf1f'
READAHEAD_HELPER_SHA = 'be321bc881d77668d5e00731b7c1ba11a24154426ae98bcecdd5abf867f903f2'
DIO_HELPER_SHA = 'f37830c0db07c77e865907b5f0d67d272c6963f46aeff81487a7438f33d33b1a'
NATIVE_ROOT = pathlib.PurePosixPath('/home/runner/work/formal-conjectures/formal-conjectures')
NATIVE_PRODUCTION_BUILD = NATIVE_ROOT / BUILD.rstrip('/')
READAHEAD_ENABLE_STEP = 'Set only the new owned final Btrfs filesystem readahead to zero'
READAHEAD_CHECK_STEP = 'Confirm the owned final filesystem readahead stayed zero after preflight'
FINAL_KERNEL_STEP = 'Check final class, full family, and three-field assembly'
CODE_FILES = {
    WORKFLOW: (WORKFLOW_SHA, '6496e2230b6878d881d0b094414dc010f91d125d'),
    'ci/rg_enable_final_owned_proofstore_direct_io_20261104.py': (
        DIO_HELPER_SHA, '059b5fd863fcc14285d9f3791c3b5341064e387f'),
    'ci/rg_final_owned_proofstore_readahead_20261104.py': (
        READAHEAD_HELPER_SHA, 'ed715804b09f2812898be0d6acb93a4eb434462a'),
    'ci/rg_github_artifacts.py': (
        'db9221ee4aa24f77082c98f33588b987531fc77f9f93c49111d31ad12363b0ef',
        '0d6b0ca19ca8b1717621559b426a0a7b0b9d9520'),
}
# This is the same duplicate-key-rejecting decoder under the copied pure
# diagnostic gate's name; no frozen diagnostic module or constants are changed.
decode_json = decode


def bind_prepared_gate_sources():
    assert type(RUN) is int and RUN > 0, 'Actual production run has not been bound'
    assert type(JOB) is int and JOB > 0, 'Actual production job has not been bound'
    assert isinstance(COMMIT, str) and re.fullmatch(r'[0-9a-f]{40}', COMMIT), 'Actual production commit has not been bound'
    parents = {
        'original_production_authenticator': (ROOT / 'final_direct_io_candidate/authenticate_original_direct_io.py', PARENT_ORIGINAL_AUTHENTICATOR_SHA),
        'reviewed_readahead_gate_source': (ROOT / 'bothlong_phase_probe/authenticate_readahead_run.py', READAHEAD_GATE_SOURCE_SHA),
        'reviewed_transport_parser_source': (ROOT / 'bothlong_phase_probe/authenticate_mmap_transport_retry_run.py', TRANSPORT_PARSER_SOURCE_SHA),
    }
    source_bindings = {}
    for key, (path, digest) in parents.items():
        raw = path.read_bytes()
        assert sha(raw) == digest
        source_bindings[key] = dict(path=str(path), sha256=digest, bytes=len(raw))
    runtime = {}
    for relative, (digest, blob) in CODE_FILES.items():
        raw = (ROOT / 'final_readahead_preparation/patch' / relative).read_bytes()
        assert sha(raw) == digest
        assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == blob
        runtime[relative] = dict(sha256=digest, git_blob_sha1=blob, bytes=len(raw))
    return dict(parent_and_gate_sources=source_bindings, runtime_code_bindings=runtime,
                authenticator_sha256=file_sha(pathlib.Path(__file__)),
                frozen_diagnostic_constants_overwritten=False,
                native_context_simulated=False, native_paths_materialized=False,
                transport_events_used_as_restore_success=False)

def bound_json(path, digest):
    raw = path.read_bytes()
    assert sha(raw) == digest, ('Changed fixed input', str(path))
    return decode(raw)


def production():
    for relative, digest in BASE_SHA.items():
        assert file_sha(BASE / relative) == digest, ('Changed production dependency', relative)
    sys.path.insert(0, str(BASE / 'ci'))
    sys.path.insert(0, str(BASE / 'Proofs/RG_Lean_20261019'))
    import rg_callback_partial_completion as partial
    from rg_exact_final_source_binding import binding_metadata
    from rg_collect_exact_d1_reproductions import records_from_log
    from module_outputs import output_members
    assert partial.FINAL == FINAL
    binding, summary = binding_metadata(
        (BASE / 'ci/rg_current_final_source_binding_20261103.json').read_bytes(),
        (BASE / 'ci/rg_d1_required_numeric_batches_20261103.json').read_bytes(),
        (BASE / 'ci/rg_d1_numeric_run41686621300_20261103.json').read_bytes())
    return partial, summary, records_from_log, output_members


def expected_declarations(graph):
    expected = bound_json(ROOT / 'final_scope_review/expected_final_declarations.json', DECLARATIONS_SHA)
    assert expected['repository'] == REPOSITORY and expected['actual_candidate_commit'] == ORIGINAL_PROOF_SOURCE
    assert expected['actual_run_for_later_authentication'] == ORIGINAL_PROOF_RUN
    assert expected['expected_named_profiles_total'] == 11
    rows = {r['module']: r for r in expected['modules']}
    assert len(expected['modules']) == len(rows) == 3 and set(rows) == FINAL
    for name, row in rows.items():
        raw = (ROOT / 'final_scope_review/exact_candidate' / row['path']).read_bytes()
        assert len(raw) == row['bytes']
        assert sha(raw) == row['source_sha256'] == graph['source_sha256'][name]
        blob = b'blob ' + str(len(raw)).encode() + b'\0' + raw
        assert hashlib.sha1(blob).hexdigest() == row['git_blob_sha']
        assert row['raw_module_log'] == name + '.log'
        assert len(row['expected_axiom_declarations_in_source_order']) == row['expected_named_profile_count']
    assert sum(r['expected_named_profile_count'] for r in rows.values()) == 11
    return rows


def native_metadata(directory):
    assert type(RUN) is int and RUN > 0, 'Actual continuation run has not been bound'
    assert type(JOB) is int and JOB > 0, 'Actual continuation job has not been bound'
    assert isinstance(COMMIT, str) and re.fullmatch(r'[0-9a-f]{40}', COMMIT), 'Actual continuation commit has not been bound'
    run = decode((directory / 'run.json').read_bytes())
    jobs = decode((directory / 'jobs.json').read_bytes())
    artifacts = decode((directory / 'artifacts.json').read_bytes())
    assert run['id'] == RUN and run['run_attempt'] == 1
    assert run['repository']['full_name'] == REPOSITORY
    assert run['head_sha'] == COMMIT and run['head_branch'] == BRANCH
    assert run['event'] == 'push' and run['path'] == WORKFLOW
    assert run['status'] == 'completed' and run['conclusion'] == 'success'
    assert jobs['total_count'] == len(jobs['jobs']) == 1
    job = jobs['jobs'][0]
    assert job['id'] == JOB and job['run_id'] == RUN and job['run_attempt'] == 1
    assert job['head_sha'] == COMMIT and job['head_branch'] == BRANCH and job['name'] == 'check'
    assert job['status'] == 'completed' and job['conclusion'] == 'success'
    assert job['completed_at'] is not None
    workflow = ROOT / 'final_readahead_preparation/patch' / WORKFLOW
    assert file_sha(workflow) == WORKFLOW_SHA
    required_steps = re.findall(r'^      - name: (.+)$', workflow.read_text(), re.M)
    steps = {step['name']: step for step in job['steps']}
    assert len(steps) == len(job['steps'])
    for name in required_steps:
        assert steps[name]['status'] == 'completed' and steps[name]['conclusion'] == 'success', name
    assert not any(step['conclusion'] in {'failure', 'cancelled', 'timed_out', 'action_required'} for step in job['steps'])
    assert artifacts['total_count'] == len(artifacts['artifacts']) == 2
    by_name = {a['name']: a for a in artifacts['artifacts']}
    assert len(by_name) == 2
    names = {
        'fresh': f'rg-degree-one-large-join-repair-20261104-{RUN}-1',
        'evidence': f'rg-degree-one-large-join-repair-20261104-evidence-{RUN}-1',
    }
    assert set(by_name) == set(names.values())
    result = {}
    for kind, name in names.items():
        artifact = by_name[name]
        assert type(artifact['id']) is int and artifact['id'] > 0
        assert artifact['expired'] is False
        assert artifact['workflow_run']['id'] == RUN
        assert artifact['workflow_run']['head_sha'] == COMMIT
        assert artifact['workflow_run']['head_branch'] == BRANCH
        assert artifact['workflow_run']['repository_id'] == artifact['workflow_run']['head_repository_id'] == 1416044648
        assert re.fullmatch(r'sha256:[0-9a-f]{64}', artifact['digest'])
        path = directory / (kind + '.zip')
        assert path.stat().st_size == artifact['size_in_bytes'] and 0 < path.stat().st_size <= 1024**3
        assert file_sha(path) == artifact['digest'][7:], ('Changed complete artifact ZIP', kind)
        result[kind] = artifact
    return run, job, result


def open_zip(path):
    archive = zipfile.ZipFile(path)
    names = archive.namelist()
    assert len(names) == len(set(names)) <= 4096
    for name in names:
        part = pathlib.PurePosixPath(name)
        assert not part.is_absolute() and '..' not in part.parts and '\\' not in name
    return archive


def member_json(archive, name):
    assert archive.getinfo(name).file_size <= 512 * 1024**2
    return decode(archive.read(name))


def row_table(rows):
    if isinstance(rows, dict):
        assert all(name == row['module'] for name, row in rows.items())
        return rows
    assert isinstance(rows, list)
    result = {row['module']: row for row in rows}
    assert len(result) == len(rows)
    return result


def collection_evidence(evidence, summary):
    collection = member_json(evidence, RUNTIME + 'collection.json')
    assert collection['kind'] == 'EXACT_RECONSTRUCTION_MANIFEST_COLLECTION'
    assert collection['current_source_binding'] == summary
    assert collection['kernel_proof'] == 'NO_NEW_KERNEL_RUN_IN_COLLECTOR'
    assert collection['final_archive_and_source_closure_checks'] == 'MANDATORY'
    numeric = bound_json(ROOT / 'numeric_audit/all349_current_metadata_audit.json', NUMERIC_AUDIT_SHA)
    contract = decode((BASE / 'ci/rg_d1_20261103_verified_continuation_contract.json').read_bytes())
    spec = decode((BASE / 'ci/rg_d1_required_numeric_batches_20261103.json').read_bytes())
    numeric_rows = {r['batch']: r for r in numeric['selected_origins']}
    assert len(numeric_rows) == len(spec['jobs']) == 349
    expected = {
        'batch' + batch: dict(run=row['run'], job=row['job'], artifact_id=row['artifact']['id'])
        for batch, row in numeric_rows.items()
    }
    assert len(contract['jobs']) == 69
    for item in contract['jobs']:
        assert item['key'] not in expected
        expected[item['key']] = {k: item[k] for k in ('run', 'job', 'artifact_id')}
    reports = {r['key']: r for r in collection['reports']}
    assert len(reports) == len(collection['reports']) == 418 and set(reports) == set(expected)
    for key, origin in expected.items():
        assert all(reports[key][k] == value for k, value in origin.items()), ('Changed collected origin', key)
    binding = decode((BASE / 'ci/rg_current_final_source_binding_20261103.json').read_bytes())
    support = set()
    for split in binding['numeric_source_reorganizations']:
        raw = (BASE / split['spec']).read_bytes()
        assert sha(raw) == split['spec_sha256']
        support.update(set(decode(raw)['new_source_exports']) - set(split['original_modules']))
    assert len(support) == 87 and set(collection['additional_current_numeric_support_modules']) == support
    required = set(spec['scheduled_numeric_modules']) | set(contract['required_collected_modules']) | support
    assert collection['modules'] == len(required) == 5758
    return dict(numeric_batches=349, auxiliary_origins=69, collected_modules=5758, numeric_supports=87)


def restored_rows(evidence, plan, rows, output_members):
    # The old actual callback authenticated this exact plan and its complete
    # restoration before compiling any of its four partial exports. Its fixed
    # bytes bind unchanged static manifest selections absent from the local
    # partial checkout. New runtime manifests must be present in the new ZIP.
    previous = bound_json(ROOT / 'final_audit/previous_actual_callback_plan.json', PREVIOUS_PLAN_SHA)
    previous_rows = {}
    for group in previous['selected_archives']:
        descriptor = {key: group[key] for key in (*ORIGIN_KEYS, 'mathlib', 'lean_version')}
        for name, selected in group['selected_modules'].items():
            assert name not in previous_rows
            previous_rows[name] = (descriptor, group['manifests'][selected['manifest']], selected)
    assert len(previous_rows) == 33652
    del previous
    seen, archive_ids, total_bytes = set(), set(), 0
    last_cumulative = 0
    for group in plan['selected_archives']:
        assert group['artifact_id'] not in archive_ids
        archive_ids.add(group['artifact_id'])
        assert group['availability']['available'] is True
        manifests = {}
        for relative, expected in group['manifests'].items():
            path = pathlib.PurePosixPath(relative)
            assert path.is_relative_to('ci') and '..' not in path.parts
            if relative in evidence.namelist():
                raw = evidence.read(relative)
            elif relative.startswith(RUNTIME):
                raise AssertionError(('Missing actual runtime manifest', relative))
            elif (BASE / relative).is_file():
                raw = (BASE / relative).read_bytes()
            else:
                # Every selected row must match the previously authenticated
                # archive descriptor, manifest digest and full original row.
                descriptor = {key: group[key] for key in (*ORIGIN_KEYS, 'mathlib', 'lean_version')}
                selected_rows = {n: s for n, s in group['selected_modules'].items() if s['manifest'] == relative}
                assert selected_rows
                for name, selected in selected_rows.items():
                    assert previous_rows[name] == (descriptor, expected, selected), ('Changed static archived selection', name)
                manifests[relative] = None
                continue
            assert sha(raw) == expected['sha256'], ('Changed selected manifest', relative)
            manifest = decode(raw)
            for key in (*ORIGIN_KEYS, 'mathlib', 'lean_version'):
                assert manifest[key] == group[key]
            assert manifest['mathlib'] == PIN and manifest['lean_version'] == '4.33.1'
            assert expected['capsule'] == (manifest.get('kind') == 'INDEPENDENTLY_AUDITED_COMPLETE_SCOPE_CAPSULE')
            manifests[relative] = manifest
        chosen = group['selected_modules']
        assert chosen and not seen.intersection(chosen)
        for name, selected in chosen.items():
            manifest = manifests[selected['manifest']]
            old = selected['row']
            assert old['module'] == name
            if manifest is not None:
                assert manifest['modules'][name] == old
            capsule = group['manifests'][selected['manifest']]['capsule']
            assert old['source_sha256'] == plan['source_sha256'][name]
            assert old['source_closure_sha256'] == plan['source_closure_sha256'][name]
            if old['mode'] == 'PRIOR_VERIFIED_JOB_EXPORT':
                assert capsule is True
                origin = old['origin']
            else:
                assert old['mode'] == 'FRESH_KERNEL_EXPORT'
                origin = {key: group[key] for key in ORIGIN_KEYS}
            expected = dict(old, mode='PRIOR_VERIFIED_JOB_EXPORT', origin=origin)
            if capsule:
                expected['transport_capsule'] = {key: group[key] for key in ORIGIN_KEYS if key != 'repository'}
            assert rows[name] == expected, ('Final receipt changed a selected prior row or origin', name)
            list(output_members(name, rows[name]))
        seen.update(chosen)
        roundtrip = member_json(evidence, f'rg-proofstore-roundtrip-reports/{group["artifact_id"]}.json')
        assert roundtrip['status'] == 'EXACT_ORIGINAL_MEMBERS_RESTORED_AND_READ_BACK_THROUGH_COMPRESSION'
        assert roundtrip['artifact_id'] == group['artifact_id'] and roundtrip['artifact_sha256'] == group['artifact_sha256']
        assert roundtrip['modules'] == len(chosen)
        assert roundtrip['all_declared_sidecars_preserved'] is True and roundtrip['fresh_kernel_compilations'] == 0
        assert type(roundtrip['logical_member_bytes']) is int and roundtrip['logical_member_bytes'] > 0
        total_bytes += roundtrip['logical_member_bytes']
        assert roundtrip['cumulative_logical_member_bytes'] == total_bytes > last_cumulative
        last_cumulative = total_bytes
    assert seen == set(plan['source_sha256']) - FINAL and len(seen) == 33656
    actual_reports = {name for name in evidence.namelist() if name.startswith('rg-proofstore-roundtrip-reports/') and name.endswith('.json')}
    assert actual_reports == {f'rg-proofstore-roundtrip-reports/{artifact}.json' for artifact in archive_ids}
    return dict(restored_modules=len(seen), restored_archives=len(archive_ids), recorded_readback_bytes=total_bytes)


def named_profiles(raw, expected, row):
    text = raw.decode('utf-8')
    assert not re.search(r'\b(error|warning)(?:\([^\n]*?\))?:', text)
    pattern = r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)"
    matches = list(re.finditer(pattern, text, re.S))
    assert [match.group(1) for match in matches] == expected['expected_axiom_declarations_in_source_order']
    profiles = [sorted(set(x.strip() for x in match.group(2).split(',') if x.strip())) if match.group(2) is not None else [] for match in matches]
    assert all(set(profile) <= ALLOWED for profile in profiles)
    # The unchanged verifier records nonempty-print lines before empty prints.
    grouped = [profiles[i] for i, m in enumerate(matches) if m.group(2) is not None]
    grouped += [profiles[i] for i, m in enumerate(matches) if m.group(2) is None]
    assert grouped == row['axiom_profiles']
    assert len(matches) == expected['expected_named_profile_count']
    return dict(zip(expected['expected_axiom_declarations_in_source_order'], profiles))


def fresh_outputs(fresh, rows, declarations, logged, output_members):
    expected_rows = {name: rows[name] for name in FINAL}
    assert logged == expected_rows, 'Actual job-log fresh exports differ from the complete receipt'
    archived = {name[:-5] for name in fresh.namelist() if name.startswith('Proofs.') and name.endswith('.json')}
    assert archived == FINAL
    results, members, logical = {}, set(), 0
    for name in sorted(FINAL):
        row = rows[name]
        assert member_json(fresh, name + '.json') == row
        log = fresh.read(name + '.log')
        named = named_profiles(log, declarations[name], row)
        verified = []
        for relative, digest, size in output_members(name, row):
            assert relative not in members
            member = fresh.getinfo(relative)
            assert size is None or member.file_size == size
            with fresh.open(relative) as stream:
                assert hashlib.file_digest(stream, 'sha256').hexdigest() == digest
            members.add(relative)
            logical += member.file_size
            verified.append(dict(path=relative, sha256=digest, bytes=member.file_size))
        results[name] = dict(row=row, module_log_sha256=sha(log), named_axiom_profiles=named, verified_output_members=verified)
    actual_members = {n for n in fresh.namelist() if n.endswith(('.olean', '.olean.server', '.olean.private', '.ir'))}
    assert actual_members == members
    assert sum(len(r['named_axiom_profiles']) for r in results.values()) == 11
    return results, logical


def authenticate_direct_io(archive):
    """Check recorded commands and actual state, with the pinned pure validators."""
    import runpy
    helper_path = ROOT / 'final_readahead_preparation/patch/ci/rg_enable_final_owned_proofstore_direct_io_20261104.py'
    assert sha(helper_path.read_bytes()) == 'f37830c0db07c77e865907b5f0d67d272c6963f46aeff81487a7438f33d33b1a'
    helper = runpy.run_path(str(helper_path))
    direct_raw = archive.read('rg-proofstore-direct-io.json')
    direct = decode(direct_raw)
    setup_raw = archive.read('rg-proofstore-setup.json')
    setup = decode(setup_raw)
    assert direct['status'] == 'OWNED_PROOFSTORE_LOOP_DIRECT_IO_ENABLED'
    assert direct['native_run_id'] == str(RUN) and direct['native_run_attempt'] == '1'
    assert direct['native_workflow_source_commit'] == COMMIT
    assert direct['setup_report_sha256'] == sha(setup_raw)
    for key in ('proof_export_claim', 'resource_limits_changed',
                'filesystem_recreated_or_remounted', 'swap_configuration_changed'):
        assert direct[key] is False
    image, mount = pathlib.Path(direct['image']), pathlib.Path(direct['mount'])
    assert str(image) == setup['image'] and str(mount) == setup['mount']
    assert image.name == 'rg-ephemeral-proofstore.btrfs'
    assert image.is_absolute() and image.is_relative_to('/home/runner/work')
    assert mount == image.parent / 'Proofs/RG_Lean_20261019/build/extension'
    assert setup['logical_image_bytes'] == 256 * 1024**3
    before, after = direct['before'], direct['after']
    for state in (before, after):
        identity, row = state['image_identity'], state['loop']
        assert identity['size'] == setup['logical_image_bytes']
        helper['validate_mount'](state['mount'], setup, mount)
        assert re.fullmatch(r'7:[0-9]+', row['maj:min'])
        helper['validate_loop'](row, image, identity, state['mount']['source'], row['maj:min'])
        helper['validate_sector_compatibility'](row, state['backing_block'])
        assert type(state['sysfs_dio']) is int and state['sysfs_dio'] in (0, 1)
        assert bool(state['sysfs_dio']) == row['dio']
    assert before['image_identity'] == after['image_identity']
    for key in ('mount', 'mount_stat_device', 'backing_block', 'backing_filesystem'):
        assert before[key] == after[key]
    for key in helper['LOOP_IMMUTABLE']:
        assert before['loop'][key] == after['loop'][key]
    assert after['loop']['dio'] is True and after['sysfs_dio'] == 1
    assert direct['dio_flag_changed'] == (before['loop']['dio'] is False)
    loop = before['loop']['name']
    find_mount = ['findmnt', '--json', '--target', str(mount), '--output', helper['MOUNT_COLUMNS']]
    find_image = ['findmnt', '--json', '--target', str(image), '--output', helper['MOUNT_COLUMNS']]
    read_loop = ['sudo', '-n', '--', 'losetup', '--list', '--json', '--output', helper['LOOP_COLUMNS'], '--', loop]
    expected_commands = [
        ['uname', '--release'], ['losetup', '--version'], find_mount, read_loop, find_image,
        ['sudo', '-n', '--', 'losetup', '--direct-io=on', '--', loop],
        find_mount, read_loop, find_image]
    commands = direct['commands']
    assert [row['argv'] for row in commands] == expected_commands
    assert all(row['returncode'] == 0 for row in commands)
    assert commands[0]['stdout'].strip() == direct['kernel_release']
    assert commands[1]['stdout'].strip() == direct['util_linux_version']
    for offset, state in ((2, before), (6, after)):
        for index, key, target in ((offset, 'filesystems', 'mount'),
                                   (offset + 1, 'loopdevices', 'loop'),
                                   (offset + 2, 'filesystems', 'backing_filesystem')):
            assert helper['single_row'](decode(commands[index]['stdout']), key) == state[target]
    return dict(report_sha256=sha(direct_raw), setup_report_sha256=sha(setup_raw),
                before_enabled=before['loop']['dio'], after_enabled=after['loop']['dio'],
                flag_changed=direct['dio_flag_changed'], effective_sysfs_after=after['sysfs_dio'],
                loop=loop, image_identity=after['image_identity'],
                backing_filesystem=after['backing_filesystem'], backing_block=after['backing_block'],
                kernel_release=direct['kernel_release'], util_linux_version=direct['util_linux_version'],
                only_owned_loop_dio_mutation=True, original_sources_and_guards_unchanged=True,
                lower_filesystem_cache_behavior_measured_directly=False)


def resource_evidence(fresh, evidence):
    resource = member_json(fresh, 'resource_observer.json')
    assert resource['status'] == 'VERIFIER_COMPLETED' and resource['exit_code'] == 0
    assert resource['mathlib_and_lean_flags_unchanged'] is True
    assert resource['samples'] and math.isfinite(resource['seconds']) and resource['seconds'] > 0
    minimum = min(sample['available_bytes'] for sample in resource['samples'])
    sample_maximum = max(sample['aggregate_lean_rss'] for sample in resource['samples'])
    maximum = resource['maximum_aggregate_lean_rss']
    # The observer updates its maximum every second and retains samples only
    # every ten seconds. A peak between stored samples is still an actual peak.
    assert type(maximum) is int and maximum >= 0
    assert all(type(sample['aggregate_lean_rss']) is int and sample['aggregate_lean_rss'] >= 0
               for sample in resource['samples'])
    assert minimum > 2048 * 1024**2
    assert maximum >= sample_maximum
    host = member_json(evidence, 'rg-proofstore-kernel-reserve.json')
    assert host['status'] == 'OWNED_KERNEL_GROUP_ENDED' and host['exit_code'] == 0
    assert host['host_reserve_stop'] is False and host['foreign_processes_signalled'] == 0
    setup = member_json(evidence, 'rg-proofstore-setup.json')
    assert setup['status'] == 'NEW_EPHEMERAL_COMPRESSED_PROOFSTORE_MOUNTED'
    assert setup['logical_image_bytes'] == 256 * 1024**3
    assert setup['filesystem']['fstype'] == 'btrfs' and 'compress=zstd:6' in setup['filesystem']['options']
    assert setup['local_changes'] == setup['existing_sources_or_archives_deleted'] == 0
    assert setup['mathematical_checks_changed'] is False
    direct_io = authenticate_direct_io(evidence)
    return dict(status=resource['status'], exit_code=0, seconds=resource['seconds'],
        direct_io_evidence=direct_io,
        maximum_aggregate_lean_rss=maximum, minimum_observed_available_bytes=minimum,
        maximum_persisted_sample_lean_rss=sample_maximum,
        memory_reserve_bytes=2048 * 1024**2, host=host,
        resource_observer_sha256=sha(fresh.read('resource_observer.json')))



def pure_readahead_validators():
    """Load only pinned pure definitions; never import the native RA module."""
    helper_path = ROOT / 'final_readahead_preparation/patch/ci/rg_final_owned_proofstore_readahead_20261104.py'
    helper_raw = helper_path.read_bytes()
    assert sha(helper_raw) == READAHEAD_HELPER_SHA
    dio_path = ROOT / 'final_readahead_preparation/patch/ci/rg_enable_final_owned_proofstore_direct_io_20261104.py'
    assert sha(dio_path.read_bytes()) == DIO_HELPER_SHA
    # The original DIO module has definitions and an inert __main__ guard only.
    # Its native main/observe/capture functions are not called by this loader.
    dio = types.SimpleNamespace(**runpy.run_path(str(dio_path)))
    tree = ast.parse(helper_raw, filename=str(helper_path))
    pure_names = ('parse_blkid', 'select_owned_loop', 'validate_sysfs_binding',
                  'validate_inputs', 'validate_transition', 'validate_enable_report')
    definitions = [node for node in tree.body
                   if isinstance(node, ast.FunctionDef) and node.name in pure_names]
    assert [node.name for node in definitions] == list(pure_names)
    constants = {}
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            name = node.targets[0].id
            if name in ('UUID_PATTERN', 'NATIVE_KEYS', 'IDENTITY_KEYS'):
                constants[name] = ast.literal_eval(node.value)
    assert set(constants) == {'UUID_PATTERN', 'NATIVE_KEYS', 'IDENTITY_KEYS'}
    namespace = dict(re=re, pathlib=pathlib, dio=dio, require=dio.require, **constants)
    # No imports, assignments with effects, decorators, main or observe are
    # selected from the native helper. Only these six reviewed definitions run.
    assert all(not node.decorator_list for node in definitions)
    exec(compile(ast.Module(body=definitions, type_ignores=[]), str(helper_path), 'exec'), namespace)
    return namespace, dio


def native_recorded_path(value):
    """Validate spelling only; an original /home/runner or /sys path stays data."""
    assert isinstance(value, str)
    path = pathlib.PurePosixPath(value)
    assert path.is_absolute() and '..' not in path.parts and str(path) == value
    return path


def recorded_sysfs_identity(value):
    assert set(value) == {'device', 'inode'}
    assert isinstance(value['device'], str) and re.fullmatch(r'[0-9]+:[0-9]+', value['device'])
    assert type(value['inode']) is int and value['inode'] > 0


def recorded_readahead_attribute(value, expected_path, expected_resolved=None, *, has_value):
    assert set(value) == {'path', 'resolved_path', 'identity'} | ({'value_kib'} if has_value else set())
    assert value['path'] == expected_path
    native_recorded_path(value['path'])
    resolved = native_recorded_path(value['resolved_path'])
    assert resolved.is_relative_to('/sys/devices') and resolved.name == 'read_ahead_kb'
    if expected_resolved is not None:
        assert value['resolved_path'] == expected_resolved
    recorded_sysfs_identity(value['identity'])
    if has_value:
        assert type(value['value_kib']) is int and value['value_kib'] >= 0


def authenticate_readahead_observation(state, commands, setup, direct, validators, dio):
    """Validate one retained state against exact read-only command outputs."""
    assert set(state) == set(validators['IDENTITY_KEYS']) | {
        'read_ahead_kib', 'other_device_readahead', 'mount_empty'}
    image = NATIVE_ROOT / 'rg-ephemeral-proofstore.btrfs'
    mount = NATIVE_PRODUCTION_BUILD / 'extension'
    for key in ('image_identity', 'mount', 'mount_stat_device', 'loop', 'sysfs_dio',
                'backing_block', 'backing_filesystem'):
        assert state[key] == direct['after'][key], key
    identity, loop = state['image_identity'], state['loop']
    assert identity['size'] == 256 * 1024**3
    assert type(state['sysfs_dio']) is int and state['sysfs_dio'] == 1 and loop['dio'] is True
    assert type(state['mount_empty']) is bool
    assert type(state['read_ahead_kib']) is int and state['read_ahead_kib'] >= 0
    expected_commands = [
        ['sudo', '-n', '--', 'findmnt', '--json', '--target', str(mount),
         '--output', dio.MOUNT_COLUMNS + ',UUID'],
        ['sudo', '-n', '--', 'losetup', '--list', '--json', '--output', dio.LOOP_COLUMNS],
        ['findmnt', '--json', '--target', str(image), '--output', dio.MOUNT_COLUMNS],
        ['sudo', '-n', '--', 'blkid', '--probe', '--output', 'export', '--', loop['name']]]
    assert [row['argv'] for row in commands] == expected_commands
    for row in commands:
        assert set(row) == {'argv', 'returncode', 'stdout', 'stderr'}
        assert type(row['returncode']) is int and row['returncode'] == 0
        assert isinstance(row['stdout'], str) and isinstance(row['stderr'], str)
    mount_record = dio.single_row(decode_json(commands[0]['stdout']), 'filesystems')
    dio.validate_mount(mount_record, setup, mount)
    assert {key.lower(): mount_record[key.lower()] for key in dio.MOUNT_COLUMNS.split(',')} == state['mount']
    assert mount_record['uuid'] == state['filesystem_uuid']
    selected_loop = validators['select_owned_loop'](decode_json(commands[1]['stdout']), identity)
    assert selected_loop == loop
    dio.validate_loop(loop, image, identity, state['mount']['source'], loop['maj:min'])
    assert dio.single_row(decode_json(commands[2]['stdout']), 'filesystems') == state['backing_filesystem']
    blkid = validators['parse_blkid'](commands[3]['stdout'])
    loop_sysfs = '/sys/devices/virtual/block/' + pathlib.PurePosixPath(loop['name']).name
    validators['validate_sysfs_binding'](
        state['filesystem_uuid'], blkid, loop['name'], loop['maj:min'], loop_sysfs,
        state['filesystem_sysfs'], state['filesystem_device_links'], state['bdi_link'], state['resolved_bdi'])
    recorded_sysfs_identity(state['filesystem_sysfs_identity'])
    recorded_sysfs_identity(state['resolved_bdi_identity'])
    recorded_readahead_attribute(state['readahead_file'],
        state['bdi_link'] + '/read_ahead_kb', state['resolved_bdi'] + '/read_ahead_kb', has_value=False)
    backing = state['backing_block']
    assert backing['status'] == 'READ_FROM_SYSFS'
    assert backing['image_device'] == identity['device']
    assert backing['sysfs'] == '/sys/dev/block/' + identity['device']
    assert native_recorded_path(backing['resolved_sysfs']).is_relative_to('/sys/devices')
    sector_path = native_recorded_path(backing['logical_sector_source'])
    assert sector_path.is_relative_to('/sys/devices') and sector_path.name == 'logical_block_size'
    assert sector_path.parent.name == 'queue'
    dio.validate_sector_compatibility(loop, backing)
    other = state['other_device_readahead']
    assert set(other) == {'loop_queue', 'backing_queue'}
    recorded_readahead_attribute(other['loop_queue'], loop_sysfs + '/queue/read_ahead_kb', has_value=True)
    recorded_readahead_attribute(other['backing_queue'], str(sector_path.parent / 'read_ahead_kb'), has_value=True)
    assert all(row['resolved_path'] != state['readahead_file']['resolved_path'] for row in other.values())
    return dict(filesystem_uuid=state['filesystem_uuid'],
                filesystem_device_links=state['filesystem_device_links'], bdi_link=state['bdi_link'],
                resolved_bdi=state['resolved_bdi'], readahead_file=state['readahead_file'],
                read_ahead_kib=state['read_ahead_kib'], other_device_readahead=other,
                effective_loop_direct_io=state['sysfs_dio'], mount_empty=state['mount_empty'])


def authenticate_readahead_step_order(steps):
    names = ('Create a new bounded logical proofstore without formatting an existing disk',
             'Require direct I/O only for the new owned final proofstore loop',
             READAHEAD_ENABLE_STEP,
             'Authenticate and read back every selected original object and sidecar',
             'Require exactly the three remaining fresh final modules',
             READAHEAD_CHECK_STEP, FINAL_KERNEL_STEP)
    records = []
    for name in names:
        row = steps[name]
        assert row['status'] == 'completed'
        if name != FINAL_KERNEL_STEP:
            assert row['conclusion'] == 'success', name
        else:
            assert row['conclusion'] in ('success', 'failure')
        assert type(row['number']) is int and row['number'] > 0
        start, end = row['started_at'], row['completed_at']
        assert isinstance(start, str) and isinstance(end, str)
        assert start.endswith('Z') and end.endswith('Z')
        first = datetime.datetime.fromisoformat(start)
        last = datetime.datetime.fromisoformat(end)
        assert first.tzinfo is not None and last.tzinfo is not None and first <= last
        if records:
            assert records[-1]['number'] + 1 == row['number']
            assert datetime.datetime.fromisoformat(records[-1]['completed_at']) <= first
        records.append(dict(name=name, number=row['number'], conclusion=row['conclusion'],
                            started_at=start, completed_at=end))
    return records


def authenticate_readahead(archive, steps, capture_directory):
    validators, dio = pure_readahead_validators()
    setup_raw = archive.read('rg-proofstore-setup.json')
    direct_raw = archive.read('rg-proofstore-direct-io.json')
    enable_raw = archive.read('rg-proofstore-readahead-enable.json')
    check_raw = archive.read('rg-proofstore-readahead-check.json')
    setup, direct, enabled, checked = map(decode_json, (setup_raw, direct_raw, enable_raw, check_raw))
    image = NATIVE_ROOT / 'rg-ephemeral-proofstore.btrfs'
    mount = NATIVE_PRODUCTION_BUILD / 'extension'
    context = dict(native_run_id=str(RUN), native_run_attempt='1', native_workflow_source_commit=COMMIT)
    validators['validate_inputs'](setup, sha(setup_raw), direct, context, image, mount)
    binding = dict(context, setup_report_sha256=sha(setup_raw), dio_report_sha256=sha(direct_raw),
                   dio_helper_sha256=DIO_HELPER_SHA, helper_sha256=READAHEAD_HELPER_SHA,
                   kernel_release=direct['kernel_release'], image=str(image), mount=str(mount))
    assert enabled['binding'] == checked['binding'] == binding
    common_keys = {'status', 'phase', 'commands', 'units', 'proof_export_claim',
                   'resource_limits_changed', 'swap_configuration_changed',
                   'filesystem_recreated_or_remounted', 'only_permitted_mutation',
                   'interpretation_limit', 'binding'}
    assert set(enabled) == common_keys | {'before', 'after', 'mutation'}
    assert set(checked) == common_keys | {'observed', 'enable_report_sha256'}
    assert enabled['status'] == 'OWNED_PROOFSTORE_READAHEAD_ZERO_ENABLED' and enabled['phase'] == 'enable'
    assert checked['status'] == 'OWNED_PROOFSTORE_READAHEAD_ZERO_CONFIRMED' and checked['phase'] == 'check'
    assert checked['enable_report_sha256'] == sha(enable_raw)
    for report in (enabled, checked):
        for key in ('proof_export_claim', 'resource_limits_changed', 'swap_configuration_changed',
                    'filesystem_recreated_or_remounted'):
            assert report[key] is False
        assert report['units'] == 'read_ahead_kb is KiB (1024 bytes)'
        assert report['only_permitted_mutation'] == 'one owned Btrfs filesystem BDI read_ahead_kb: positive -> 0'
        assert report['interpretation_limit'] == 'Compressed extents may still be read in full; this is a bounded hypothesis test.'
        uname = report['commands'][0]
        assert set(uname) == {'argv', 'returncode', 'stdout', 'stderr'}
        assert uname['argv'] == ['uname', '--release']
        assert type(uname['returncode']) is int and uname['returncode'] == 0
        assert isinstance(uname['stdout'], str) and isinstance(uname['stderr'], str)
        assert uname['stdout'].strip() == binding['kernel_release']
    assert len(enabled['commands']) == 9 and len(checked['commands']) == 5
    before = authenticate_readahead_observation(enabled['before'], enabled['commands'][1:5], setup, direct, validators, dio)
    after = authenticate_readahead_observation(enabled['after'], enabled['commands'][5:9], setup, direct, validators, dio)
    current = authenticate_readahead_observation(checked['observed'], checked['commands'][1:5], setup, direct, validators, dio)
    validators['validate_transition'](enabled['before'], enabled['after'])
    validators['validate_enable_report'](enabled, binding, checked['observed'])
    # The helper permits either emptiness on check; this completed full-restore
    # path additionally requires the native observation to be nonempty.
    assert checked['observed']['mount_empty'] is False
    assert type(enabled['mutation']['returncode']) is int and enabled['mutation']['returncode'] == 0
    # Both command arrays are now exactly their fixed read-only allowlists.
    # The only recorded mutation is the one separate, fully bound tee record.
    order = authenticate_readahead_step_order(steps)
    (capture_directory / 'rg-proofstore-readahead-enable.json').write_bytes(enable_raw)
    (capture_directory / 'rg-proofstore-readahead-check.json').write_bytes(check_raw)
    return dict(status='ACTUAL_OWNED_BTRFS_READAHEAD_ENABLE_AND_READ_ONLY_CHECK_AUTHENTICATED',
        native_run_id=RUN, native_job_id=JOB, native_run_attempt=1, source_commit=COMMIT,
        helper_sha256=READAHEAD_HELPER_SHA, dio_helper_sha256=DIO_HELPER_SHA,
        setup_report_sha256=sha(setup_raw), dio_report_sha256=sha(direct_raw),
        enable_report_sha256=sha(enable_raw), check_report_sha256=sha(check_raw),
        immutable_native_binding=binding, before=before, after=after, observed_before_kernel=current,
        positive_to_zero_transition=True, check_read_only=True,
        actual_native_enable_and_check_passed=True, recorded_mutation_count=1,
        sole_mutation=enabled['mutation'], other_device_readahead_unchanged=True,
        effective_loop_dio_unchanged=True, native_step_order=order,
        original_runtime_sysfs_observations_not_reread_locally=True,
        native_paths_used_only_as_data=True, native_context_observe_and_main_executed_offline=False,
        pure_validator_names=['parse_blkid', 'select_owned_loop', 'validate_sysfs_binding',
                              'validate_inputs', 'validate_transition', 'validate_enable_report'],
        interpretation_limit='Actual per-filesystem policy changed before restore and remained zero after preflight. This is an end-to-end policy observation, not an isolated Lean-only A/B measurement, a proof export, or a unique causal attribution. Demand faults, compressed-extent reads and other kernel paths remain possible.')


def checked_number(value, minimum=0):
    assert type(value) in (int, float) and math.isfinite(value) and value >= minimum
    return value


def transport_retry_observations(job_log_raw):
    """Parse only actual structured records; no download success is emitted.

    The pinned helper does not emit an artifact ID or a successful-GET event.
    A retry decision is not proof that a later GET began or succeeded. Multiple
    records can refer to one HTTP response; counts below count log records.
    Printed GitHub log timestamps remain data, not monotonic retry timings.
    """
    events = []
    decisions, service_codes = collections.Counter(), collections.Counter()
    statuses = collections.Counter()
    relevant = re.compile(rb'"status"\s*:\s*"(?:SIGNED_ARCHIVE_HTTP_503|WAITING_FOR_SIGNED_ARCHIVE_SERVICE)"')
    stamp_pattern = re.compile(rb'[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}(?:\.[0-9]+)?Z')
    base_keys = {'status', 'attempt', 'maximum_attempts', 'retry_start_window_seconds',
                 'service_error_code', 'has_retry_after', 'has_retry_after_ms_generic',
                 'has_retry_after_ms', 'decision'}
    for line_number, raw_line in enumerate(job_log_raw.splitlines(keepends=True), 1):
        line = raw_line.rstrip(b'\r\n')
        timestamp, separator, payload = line.partition(b' ')
        if not payload.startswith(b'{') or not relevant.search(payload):
            continue
        assert separator and stamp_pattern.fullmatch(timestamp), 'Unbound transport log timestamp'
        event = decode_json(payload)
        assert isinstance(event, dict)
        status = event['status']
        assert status in ('SIGNED_ARCHIVE_HTTP_503', 'WAITING_FOR_SIGNED_ARCHIVE_SERVICE')
        if status == 'WAITING_FOR_SIGNED_ARCHIVE_SERVICE':
            assert set(event) == {'status', 'remaining_seconds', 'no_request_during_wait'}
            assert checked_number(event['remaining_seconds']) <= 600
            assert event['no_request_during_wait'] is True
        else:
            assert type(event['attempt']) is int and 1 <= event['attempt'] <= 4
            decision = event['decision']
            if decision == 'STOP_RETRY_WINDOW_ELAPSED_DURING_REDIRECT':
                assert set(event) == {'status', 'attempt', 'decision'}
                assert event['attempt'] >= 2
            else:
                assert event['maximum_attempts'] == 4 and type(event['maximum_attempts']) is int
                assert event['retry_start_window_seconds'] == 600 and type(event['retry_start_window_seconds']) is int
                for key in ('has_retry_after', 'has_retry_after_ms_generic', 'has_retry_after_ms'):
                    assert type(event[key]) is bool
                code = event['service_error_code']
                assert code is None or (isinstance(code, str) and code.isascii()
                    and code.isalnum() and len(code) <= 128)
                if code is not None:
                    service_codes[code] += 1
                if decision == 'RETRY_SAME_ARTIFACT_WITH_FRESH_REDIRECT_AFTER_WAIT':
                    assert event['attempt'] < 4
                    assert set(event) == base_keys | {'wait_seconds', 'documented_service_wait_seconds'}
                    service_wait = checked_number(event['documented_service_wait_seconds'])
                    wait = checked_number(event['wait_seconds'])
                    assert wait == max(float((30, 60, 120)[event['attempt'] - 1]), service_wait)
                    assert wait <= 600
                elif decision == 'STOP_SERVICE_WAIT_EXCEEDS_RETRY_WINDOW':
                    assert event['attempt'] < 4
                    assert set(event) == base_keys | {'requested_wait_seconds'}
                    assert checked_number(event['requested_wait_seconds']) >= (30, 60, 120)[event['attempt'] - 1]
                else:
                    assert decision in ('STOP_ATTEMPTS_EXHAUSTED', 'STOP_INVALID_SERVICE_RETRY_HEADER',
                                        'STOP_RETRY_START_WINDOW_ELAPSED')
                    assert set(event) == base_keys
                    if decision == 'STOP_ATTEMPTS_EXHAUSTED':
                        assert event['attempt'] == 4
                    else:
                        assert event['attempt'] < 4
            decisions[decision] += 1
        statuses[status] += 1
        events.append(dict(job_log_line=line_number, printed_github_log_timestamp_utc=timestamp.decode('ascii'),
            raw_log_line_sha256=sha(raw_line), event=event))
    return dict(status='ACTUAL_STRUCTURED_TRANSPORT_LOG_RECORDS_PARSED',
        job_log_sha256=sha(job_log_raw), transport_helper_sha256=CODE_FILES['ci/rg_github_artifacts.py'][0],
        event_records=events, event_record_count=len(events), status_record_counts=dict(sorted(statuses.items())),
        decision_record_counts=dict(sorted(decisions.items())), service_error_code_record_counts=dict(sorted(service_codes.items())),
        retry_decision_records=decisions.get('RETRY_SAME_ARTIFACT_WITH_FRESH_REDIRECT_AFTER_WAIT', 0),
        successful_retry_requests=None, distinct_http_503_responses=None,
        per_artifact_retry_attribution_possible=False, retry_success_inferred_from_restore_success=False,
        events_are_actual_log_records_not_independent_network_observations=True,
        printed_log_timestamps_are_not_measured_retry_durations=True,
        request_urls_tokens_and_error_bodies_reproduced=False,
        interpretation_limit='No transport records means none of these structured records was observed. The helper emits no successful-GET record or artifact ID; retry decisions and wait records do not count successful retries. Full original archive/source/receipt/trace checks remain separate and mandatory.')


def authenticate(directory):
    gate_sources = bind_prepared_gate_sources()
    partial, summary, records_from_log, output_members = production()
    graph = bound_json(ROOT / 'projected_source_graph.json', GRAPH_SHA)
    projection = bound_json(ROOT / 'source_projection.json', PROJECTION_SHA)
    assert projection['actual_prior_plan_sha256'] == PREVIOUS_PLAN_SHA
    assert projection['required_modules'] == 33659
    assert projection['source_changed'] == ['Proofs.RadenkovicGutmanD1OriginalSharedBothLong']
    assert set(projection['closure_changed']) == FINAL
    assert projection['current_endpoint_closure_sha256'] == graph['source_closure_sha256'][ENDPOINT]
    assert projection['current_binding_sha256'] == BASE_SHA['ci/rg_current_final_source_binding_20261103.json']
    assert projection['auxiliary_contract_sha256'] == BASE_SHA['ci/rg_d1_20261103_verified_continuation_contract.json']
    assert set(graph) == {'source_sha256', 'source_dependencies', 'source_closure_sha256'}
    assert all(len(graph[key]) == 33659 for key in graph)
    declarations = expected_declarations(graph)
    run, job, artifacts = native_metadata(directory)
    native_log = (directory / 'job.log').read_bytes()
    transport_events = transport_retry_observations(native_log)
    logged = records_from_log(native_log)
    with open_zip(directory / 'fresh.zip') as fresh, open_zip(directory / 'evidence.zip') as evidence:
        plan_raw = evidence.read(BUILD + 'exact_degree_one_plan.json')
        plan = decode(plan_raw)
        assert plan['kind'] == 'EXACT_SOURCE_BOUND_COMPRESSED_RESTORE_PLAN'
        assert plan['endpoint'] == ENDPOINT and plan['required_modules'] == 33659
        assert len(plan['selected_archives']) == 767
        assert (plan['mathlib'], plan['leancert'], plan['lean_version']) == (PIN, LC, '4.33.1')
        for key in graph:
            assert plan[key] == graph[key], ('Changed complete current source graph', key)
        assert plan['current_source_binding'] == summary
        partial.validate_selected_origins(plan)
        audit_raw = evidence.read(BUILD + 'final_partial_authentication.json')
        assert sha(audit_raw) == plan['final_partial_authentication_sha256']
        audit = decode(audit_raw)
        assert audit['status'] == 'FOUR_FIXED_CALLBACK_PARTIAL_EXPORTS_AUTHENTICATED'
        assert audit['manifest_sha256'] == partial.MANIFEST_SHA
        assert audit['preserved_origin'] == partial.origin()
        assert audit['proof_source_commit'] == partial.PROOF_SOURCE and audit['workflow_head_commit'] == partial.WORKFLOW_HEAD
        assert audit['original_run_conclusion'] == audit['original_job_conclusion'] == 'failure'
        assert audit['complete_final_receipt_present'] is False and audit['partial_objects_relabelled_as_fresh'] is False
        assert audit['actual_output_bytes_verified'] == 12963144
        assert set(audit['partial_modules']) == partial.PARTIAL and set(audit['required_fresh_modules']) == FINAL
        assert audit['current_source_changes'] == ['Proofs.RadenkovicGutmanD1OriginalSharedBothLong']
        assert set(audit['current_closure_changes']) == FINAL
        reuse = plan['final_partial_reuse']
        assert reuse == dict(kind='EXACT_FOUR_CALLBACK_PRIORS_FOR_THREE_FINAL_KERNEL_EXPORTS',
            manifest=partial.MANIFEST, manifest_sha256=partial.MANIFEST_SHA,
            preserved_origin=partial.origin(), proof_source_commit=partial.PROOF_SOURCE,
            partial_modules=sorted(partial.PARTIAL), required_fresh_modules=sorted(FINAL),
            original_failed_job_unchanged=True, partial_objects_relabelled_as_fresh=False)
        preflight = member_json(evidence, BUILD + 'extension/bounded_kernel_fallback_plan.json')
        assert preflight['status'] == 'EXACT_FRONTIER_REQUIRES_MANDATORY_FRESH_KERNEL_EXPORTS'
        assert preflight['endpoint'] == ENDPOINT and preflight['required_modules'] == 33659
        assert preflight['verified_prior_objects'] == 33656 and preflight['max_fresh'] == 3
        assert preflight['within_bound'] is True and set(preflight['fresh_modules']) == FINAL
        receipt_raw = fresh.read('receipt.json')
        receipt = decode(receipt_raw)
        preserved = partial.validate_final_receipt(receipt, graph['source_sha256'], graph['source_closure_sha256'])
        rows = receipt['modules']
        assert isinstance(rows, dict) and len(rows) == 33659
        assert receipt['global_rg'] == 'NOT_PROVED' and receipt['complete_submission'] == 'NOT_SUBMITTED'
        for name, row in rows.items():
            assert row['module'] == name
            assert row['source_sha256'] == graph['source_sha256'][name]
            assert row['source_closure_sha256'] == graph['source_closure_sha256'][name]
            assert row['mode'] == ('FRESH_KERNEL_EXPORT' if name in FINAL else 'PRIOR_VERIFIED_JOB_EXPORT')
            assert row['axiom_profiles'] or name.startswith('LeanCert.')
            assert all(set(profile) <= ALLOWED for profile in row['axiom_profiles'])
            list(output_members(name, row))
        assert row_table(member_json(fresh, 'diagnostics_records.json')['modules']) == rows
        coverage = collection_evidence(evidence, summary)
        restoration = restored_rows(evidence, plan, rows, output_members)
        modules, logical = fresh_outputs(fresh, rows, declarations, logged, output_members)
        milestone_raw = evidence.read(BUILD + 'degree_one_large_verified_milestone.json')
        assert milestone_raw == fresh.read('verified_proof_origin_and_milestone.json')
        milestone = decode(milestone_raw)
        assert milestone['status'] == 'KERNEL_VERIFIED_DEGREE_ONE_LARGE_AND_THREE_REMAINING_ORIGINAL_FAMILIES'
        assert milestone['repository'] == REPOSITORY
        assert milestone['source_commit'] == milestone['proof_source_commit'] == milestone['workflow_head_commit'] == COMMIT
        assert milestone['run'] == RUN and milestone['run_attempt'] == 1 and milestone['workflow_event'] == 'push'
        assert 'exact_callback_context' not in milestone
        assert milestone['endpoint'] == ENDPOINT and milestone['required_modules'] == 33659
        assert milestone['source_endpoint_sha256'] == graph['source_sha256'][ENDPOINT]
        assert milestone['source_endpoint_closure_sha256'] == graph['source_closure_sha256'][ENDPOINT]
        assert milestone['receipt_sha256'] == sha(receipt_raw)
        assert milestone['authenticated_restore_plan_sha256'] == sha(plan_raw)
        assert set(milestone['new_final_modules']) == FINAL
        assert set(milestone['reconstructed_historical_heads']) == partial.HEADS
        assert set(milestone['rechecked_current_original_intervals']) == partial.INTERVALS
        assert milestone['remaining_main_family_count'] == 3 and milestone['remaining_original_main_families'] == REMAINING
        assert milestone['global_rg'] == 'THREE_EXPLICIT_ORIGINAL_FORMAL_INPUT_OBLIGATIONS_REMAIN'
        assert milestone['current_source_binding'] == summary
        assert milestone['authenticated_prior_final_modules'] == dict(reuse, **preserved)
        assert milestone['fresh_axiom_profiles'] == {name: rows[name]['axiom_profiles'] for name in FINAL}
        resources = resource_evidence(fresh, evidence)
        steps = {step['name']: step for step in job['steps']}
        readahead_policy = authenticate_readahead(evidence, steps, directory)
    inputs = ['run.json', 'jobs.json', 'artifacts.json', 'job.log', 'fresh.zip', 'evidence.zip']
    return dict(status='ACTUAL_EXACT_DEGREE_ONE_LARGE_KERNEL_RECEIPT_AUTHENTICATED_THREE_FAMILIES_REMAIN',
        repository=REPOSITORY, run=RUN, job=JOB, source_commit=COMMIT, run_attempt=1, workflow_event='push',
        unchanged_original_proof_source_commit=ORIGINAL_PROOF_SOURCE,
        native_run_conclusion=run['conclusion'], native_job_conclusion=job['conclusion'],
        artifacts={kind: {k: item[k] for k in ('id', 'name', 'digest', 'size_in_bytes')} for kind, item in artifacts.items()},
        required_modules=33659, restored_modules=33656, fresh_modules=sorted(FINAL),
        fixed_callback_priors=preserved, receipt_sha256=sha(receipt_raw), plan_sha256=sha(plan_raw),
        source_graph_sha256=GRAPH_SHA, source_projection_sha256=PROJECTION_SHA,
        prior_actual_callback_plan_sha256=PREVIOUS_PLAN_SHA,
        source_endpoint_sha256=graph['source_sha256'][ENDPOINT], source_endpoint_closure_sha256=graph['source_closure_sha256'][ENDPOINT],
        milestone_sha256=sha(milestone_raw), partial_authentication_sha256=sha(audit_raw),
        collected_prerequisite_coverage=coverage, complete_restoration_evidence=restoration,
        fresh_output_bytes_verified=logical, named_axiom_profiles_checked=11, modules=modules,
        resource_evidence=resources, remaining_original_main_families=REMAINING, remaining_main_family_count=3,
        global_rg='THREE_EXPLICIT_ORIGINAL_FORMAL_INPUT_OBLIGATIONS_REMAIN',
        full_global_rg_proof_claim=False, kernel_receipt_created_by_authenticator=False,
        production_helper_sha256=BASE_SHA['ci/rg_callback_partial_completion.py'],
        expected_declarations_sha256=DECLARATIONS_SHA,
        new_gate_sources=gate_sources, readahead_policy=readahead_policy,
        transport_retry_observations=transport_events,
        native_inputs={name: dict(bytes=(directory / name).stat().st_size, sha256=file_sha(directory / name)) for name in inputs})


def main():
    if not __debug__:
        raise RuntimeError('Original production authentication must not disable evidence assertions')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence-directory', type=pathlib.Path, required=True)
    parser.add_argument('--output', type=pathlib.Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists(), 'Refusing to leave or overwrite an earlier success report; choose a new output path'
    report = authenticate(args.evidence_directory.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x', encoding='utf-8') as stream:
        stream.write(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps({key: report[key] for key in ('status', 'run', 'job', 'required_modules', 'restored_modules', 'fresh_modules', 'named_axiom_profiles_checked', 'remaining_main_family_count')}, indent=2))
    print('authentication_report_sha256', file_sha(args.output))


if __name__ == '__main__':
    main()
