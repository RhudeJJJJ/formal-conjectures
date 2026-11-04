"""Offline authentication of the fixed direct-I/O diagnostic; never a proof receipt.

Run only after the actual native metadata, job log and diagnostic.zip have been
captured under direct_io_actual. This does not run Lean or restore proof objects.
"""
import hashlib
import json
import pathlib
import re
import zipfile

HERE = pathlib.Path(__file__).resolve().parent
ACTUAL = HERE / 'direct_io_actual'
RUN = 41833843857
JOB = 126587565934
COMMIT = '3d33148521b26f541335b3f7c764632dfa415a80'
PREFIX = 'Proofs/RG_Lean_20261019/build/bothlong_phase_probe/'
ORIGINAL = 'Proofs.RadenkovicGutmanD1OriginalSharedBothLong'
PROBE = ORIGINAL + 'PhaseProbe'
SPEC_SHA = 'd789066587ab434e4e11455d5ac5dc7ebebf4ced1f52fd9a6c9bda7d77c718b0'
ORIGINAL_SHA = '01d60858da8d95431e0240e6c7dbf2c657111fe34dbf3a3e5a115f90797edc06'
PLAN_SHA = '11ff7db7f88e1e3aa1722796a5002cc9bb29263cb7343df851a12e699b94cd44'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read_json(path):
    return json.loads(path.read_bytes())


def named_axioms(text):
    result = []
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, text, re.S):
        axioms = sorted(set(a.strip() for a in (match[2] or '').split(',') if a.strip()))
        assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}
        result.append(dict(declaration=match[1], axioms=axioms))
    return result


def markers(raw, expected):
    rows = [line.split('\t') for line in raw.decode().splitlines()]
    assert all(len(row) == 3 and row[0] == 'RG_PHASE' and row[1].isdigit() for row in rows)
    stamps = [int(row[1]) for row in rows]
    labels = [row[2] for row in rows]
    assert stamps == sorted(stamps) and labels == expected[:len(labels)]
    return stamps, labels


def authenticate_direct_io(archive):
    """Check recorded commands and actual state, with the pinned pure validators."""
    import runpy
    helper_path = HERE / 'direct_io_candidate/patch/ci/rg_enable_owned_proofstore_direct_io_20261104.py'
    assert sha(helper_path.read_bytes()) == '96211dac3452504564d33b7e2d90bdbc59597fa07eb953fc26fc6e4a56add5af'
    helper = runpy.run_path(str(helper_path))
    direct_raw = archive.read('rg-proofstore-direct-io.json')
    direct = json.loads(direct_raw)
    setup_raw = archive.read('rg-proofstore-setup.json')
    setup = json.loads(setup_raw)
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
            assert helper['single_row'](json.loads(commands[index]['stdout']), key) == state[target]
    (ACTUAL / 'direct_io_setup.json').write_bytes(direct_raw)
    return dict(report_sha256=sha(direct_raw), setup_report_sha256=sha(setup_raw),
                before_enabled=before['loop']['dio'], after_enabled=after['loop']['dio'],
                flag_changed=direct['dio_flag_changed'], effective_sysfs_after=after['sysfs_dio'],
                loop=loop, image_identity=after['image_identity'],
                backing_filesystem=after['backing_filesystem'], backing_block=after['backing_block'],
                kernel_release=direct['kernel_release'], util_linux_version=direct['util_linux_version'],
                only_owned_loop_dio_mutation=True, original_sources_and_guards_unchanged=True,
                lower_filesystem_cache_behavior_measured_directly=False)


def resource_summary(resource):
    rows = []
    skipped = 0
    for sample in resource['samples']:
        details = sample.get('process_diagnostics', {})
        for item in details.get('lean_processes', []):
            process = item['process']
            if process.get('same_process_identity_across_reads') is not True:
                skipped += 1
                continue
            if any(process[key]['status'] != 'READ' for key in ('stat_before', 'stat_after', 'status', 'io')):
                skipped += 1
                continue
            memory = process['status'].get('bytes', {})
            if any(type(memory.get(key)) is not int for key in ('VmSwap', 'RssAnon', 'RssFile', 'VmRSS', 'VmSize')):
                skipped += 1
                continue
            rows.append(dict(seconds=sample['seconds'], pid=process['pid'],
                start_time_ticks=process['stat_before']['values']['start_time_ticks'],
                ticks_per_second=details['clock_ticks_per_second'],
                memory=process['status']['bytes'], io=process['io']['counters'],
                stat=process['stat_after']['values']))
    result = dict(valid_identity_consistent_lean_samples=len(rows),
                  skipped_partial_or_unbound_process_samples=skipped,
                  one_second_maximum_aggregate_lean_rss=resource['maximum_aggregate_lean_rss'],
                  claims_about_unobserved_process_intervals=False)
    if not rows:
        return result
    identities = {(row['pid'], row['start_time_ticks']) for row in rows}
    assert len(identities) == 1
    result.update(first_sample=rows[0], last_sample=rows[-1],
                  maximum_observed_swap_bytes=max(row['memory']['VmSwap'] for row in rows),
                  maximum_observed_anon_bytes=max(row['memory']['RssAnon'] for row in rows),
                  maximum_observed_file_rss_bytes=max(row['memory']['RssFile'] for row in rows))
    return result


def main():
    run = read_json(ACTUAL / 'run.json')
    jobs = read_json(ACTUAL / 'jobs.json')['jobs']
    assert len(jobs) == 1
    job = jobs[0]
    assert run['id'] == RUN and run['head_sha'] == COMMIT
    assert run['head_branch'] == 'rg-d1-bothlong-phase-probe-20261104'
    assert run['path'] == '.github/workflows/rg-d1-bothlong-phase-probe-20261104.yml'
    assert run['event'] == 'push' and run['run_attempt'] == 1
    assert run['status'] == job['status'] == 'completed'
    assert job['id'] == JOB and job['run_id'] == RUN and job['head_sha'] == COMMIT
    assert job['run_attempt'] == 1 and job['name'] == 'diagnose'
    assert job['conclusion'] == run['conclusion']
    steps = {s['name']: s for s in job['steps']}
    for name in (
        'Require the isolated flushed-marker control before any proof restoration',
        'Authenticate the actual failed run and project only original BothLong imports',
        'Require direct I/O only for the new owned proofstore loop',
        'Authenticate all 444 original archives and read back 25191 projected objects',
        'Require exactly the original BothLong endpoint to remain uncompiled',
        'Retain diagnostic logs and phase observations without proof exports',
    ):
        assert steps[name]['conclusion'] == 'success', name
    artifacts = read_json(ACTUAL / 'artifacts.json')['artifacts']
    assert len(artifacts) == 1
    meta = artifacts[0]
    assert meta['workflow_run']['id'] == RUN
    assert meta['workflow_run']['head_sha'] == COMMIT
    assert meta['name'] == f'rg-bothlong-phase-diagnostic-20261104-{RUN}-1'
    assert meta['expired'] is False
    archive_raw = (ACTUAL / 'diagnostic.zip').read_bytes()
    assert len(archive_raw) == meta['size_in_bytes']
    assert meta['digest'] == 'sha256:' + sha(archive_raw)
    spec_raw = (HERE / 'namespace_repair_patch/ci/rg_bothlong_phase_probe_20261104_spec.json').read_bytes()
    assert sha(spec_raw) == SPEC_SHA
    spec = json.loads(spec_raw)
    with zipfile.ZipFile(ACTUAL / 'diagnostic.zip') as archive:
        names = archive.namelist()
        assert len(names) == len(set(names))
        for name in names:
            path = pathlib.PurePosixPath(name)
            assert not path.is_absolute() and '..' not in path.parts
            assert not name.endswith(('.olean', '.olean.private', '.olean.server'))
            assert not name.endswith('receipt.json')

        def raw(name):
            return archive.read(PREFIX + name)

        def data(name):
            return json.loads(raw(name))

        direct_io = authenticate_direct_io(archive)
        plan_raw = raw('projected_plan.json')
        assert sha(plan_raw) == PLAN_SHA
        assert plan_raw == (HERE / 'validation/actual_projected_plan.json').read_bytes()
        plan = json.loads(plan_raw)
        groups = plan['selected_archives']
        assert len(groups) == 444
        assert plan['required_modules'] == 25192
        total_modules = total_bytes = 0
        for group in groups:
            report = json.loads(archive.read(f"rg-proofstore-roundtrip-reports/{group['artifact_id']}.json"))
            assert report['status'] == 'EXACT_ORIGINAL_MEMBERS_RESTORED_AND_READ_BACK_THROUGH_COMPRESSION'
            assert report['artifact_id'] == group['artifact_id']
            assert report['artifact_sha256'] == group['artifact_sha256']
            assert report['modules'] == len(group['selected_modules'])
            assert report['all_declared_sidecars_preserved'] is True
            assert report['fresh_kernel_compilations'] == 0
            total_modules += report['modules']
            total_bytes += report['logical_member_bytes']
        assert total_modules == 25191 and total_bytes == 97433499160
        preflight = data('original_endpoint_preflight.json')
        assert preflight['required_modules'] == 25192
        assert preflight['verified_prior_objects'] == 25191
        assert preflight['fresh_modules'] == [ORIGINAL]
        assert preflight['max_fresh'] == 1 and preflight['within_bound'] is True
        control = data('control_result.json')
        assert control['source_spec_sha256'] == SPEC_SHA
        assert control['status'] == 'DIAGNOSTIC_MARKER_CONTROL_PASSED'
        assert [r['module'] for r in control['results']] == spec['control_modules_in_compile_order']
        assert all(r['success'] and not r['timeout'] and r['compiler_returncode'] == 0 for r in control['results'])
        assert control['observed_phase_labels'] == spec['control_markers']
        assert control['named_axiom_profiles'] == [dict(declaration='RGDiagnosticMarkerControl.checked', axioms=[])]
        assert control['production_restore_absent_during_control'] is True
        _, control_labels = markers(raw('control_phases.tsv'), spec['control_markers'])
        assert control_labels == spec['control_markers']
        for row in control['results']:
            control_log = raw(row['module'] + '.log')
            assert sha(control_log) == row['log_sha256']
            assert not re.search(rb'\b(error|warning)(?:\([^\n]*?\))?:', control_log)
        assert named_axioms(raw('Proofs.RGDiagnosticMarkerControl.log').decode()) == control['named_axiom_profiles']
        helper_path = pathlib.PurePosixPath(control['import_search_paths'][0])
        assert helper_path.is_absolute()
        assert helper_path.parts[-5:] == ('Proofs', 'RG_Lean_20261019', 'build', 'bothlong_phase_probe', 'helper_objects')
        build_path = helper_path.parent
        assert control['import_search_paths'] == [str(helper_path), str(build_path / 'control_imports')]
        for record in (control, data('probe_result.json')):
            assert record['source_spec_sha256'] == SPEC_SHA
            assert record['strict_flags'] == spec['required_compiler_flags']
            assert record['original_source_sha256'] == ORIGINAL_SHA
            assert record['module_timeout_seconds'] == 900
            assert record['workers'] == 1 and record['memory_reserve_mib'] == 2048
            assert record['production_receipt_created'] is False
            assert record['original_kernel_export_claim'] is False
            assert record['family_closure_claim'] is False
            assert record['probe_output_directory_excluded_from_import_search'] is True
            assert all(pathlib.PurePosixPath(p).name != 'probe_objects' for p in record['import_search_paths'])
        probe = data('probe_result.json')
        assert probe['import_search_paths'][:2] == [str(helper_path), str(build_path.parent / 'extension')]
        assert str(build_path / 'control_imports') not in probe['import_search_paths']
        assert len(probe['results']) == 1 and probe['results'][0]['module'] == PROBE
        result = probe['results'][0]
        log = raw(PROBE + '.log')
        assert sha(log) == result['log_sha256']
        expected = [m['label'] for m in spec['markers']]
        stamps, labels = markers(raw('probe_phases.tsv'), expected)
        assert labels == probe['observed_phase_labels']
        assert probe['last_observed_phase'] == (labels[-1] if labels else None)
        next_label = expected[len(labels)] if len(labels) < len(expected) else None
        profiles_from_log = named_axioms(log.decode())
        expected_names = ['Gebendorfer.RadenkovicGutman.D1OriginalSharedBothLong.' + suffix
                          for suffix in ('all_checked', 'adjacent_checked', 'partition_checked', 'budget_checked', 'normalized_target')]
        assert [p['declaration'] for p in profiles_from_log] == expected_names[:len(profiles_from_log)]
        if result['success']:
            assert not result['timeout'] and result['compiler_returncode'] == 0
            assert labels == expected
            assert not re.search(rb'\b(error|warning)(?:\([^\n]*?\))?:', log)
            assert probe['status'] == 'DIAGNOSTIC_COPY_COMPILER_COMPLETED'
            assert [p['declaration'] for p in profiles_from_log] == expected_names
            assert probe['named_axiom_profiles'] == profiles_from_log
        else:
            assert probe['status'] == 'DIAGNOSTIC_COMPILER_FAILED_OR_TIMED_OUT'
            assert result['timeout'] or result['compiler_returncode'] != 0 or re.search(rb'\b(error|warning)(?:\([^\n]*?\))?:', log)
        expected_conclusion = 'success' if result['success'] else 'failure'
        assert steps['Observe the isolated diagnostic copy with unchanged strict kernel limits']['conclusion'] == expected_conclusion
        assert run['conclusion'] == expected_conclusion
        resource = data('probe_resource_observer.json')
        host = json.loads(archive.read('rg-proofstore-kernel-reserve.json'))
        expected_exit = 0 if result['success'] else 1
        assert resource['status'] == 'VERIFIER_COMPLETED' and resource['exit_code'] == expected_exit
        assert host['status'] == 'OWNED_KERNEL_GROUP_ENDED' and host['exit_code'] == expected_exit
        assert host['host_reserve_stop'] is False
        assert resource['resource_reserve_mib'] == 2048
        assert resource['mathlib_and_lean_flags_unchanged'] is True
        assert resource['observer_created_kernel_receipt'] is False
        assert resource['maximum_aggregate_lean_rss'] >= max(s['aggregate_lean_rss'] for s in resource['samples'])
        assert min(s['available_bytes'] for s in resource['samples']) > 2048 * 1024**2
        assert host['foreign_processes_signalled'] == 0
        extracted = ['control_result.json', 'control_phases.tsv', 'probe_result.json',
                     'probe_phases.tsv', 'probe_resource_observer.json',
                     'probe_host_events.jsonl', 'original_endpoint_preflight.json']
        for name in extracted:
            (ACTUAL / name).write_bytes(raw(name))
        (ACTUAL / 'probe.log').write_bytes(log)
    report = dict(
        status='ACTUAL_DIRECT_IO_DIAGNOSTIC_ARCHIVE_AUTHENTICATED',
        repository='RhudeJJJJ/formal-conjectures', run=RUN, job=JOB, source_commit=COMMIT,
        native_conclusion=run['conclusion'], direct_io=direct_io,
        resource_observations=resource_summary(resource),
        artifact=meta['id'], artifact_bytes=len(archive_raw),
        artifact_sha256=sha(archive_raw), artifact_members=len(names),
        source_projection_byte_identical_to_reviewed_plan=True,
        successful_archive_restores=len(groups), successful_prior_object_readbacks=total_modules,
        selected_logical_object_bytes=total_bytes, actual_original_endpoint_preflight_passed=True,
        actual_three_module_control_passed=True, actual_diagnostic_compiler_result=result,
        phase_markers_written=len(labels), last_observed_phase=probe['last_observed_phase'],
        observed_log_axiom_profiles=profiles_from_log,
        next_unobserved_phase=next_label,
        marker_intervals_seconds=[dict(before=labels[i-1], after=labels[i], seconds=(stamps[i]-stamps[i-1])/1000)
                                  for i in range(1, len(labels))],
        maximum_observed_lean_rss=resource['maximum_aggregate_lean_rss'],
        observer_status=resource['status'], host_guard_stop=host['host_reserve_stop'],
        probe_log_sha256=sha(log), native_job_log_sha256=sha((ACTUAL / 'job.log').read_bytes()),
        production_kernel_receipt_created=False, original_large_family_completed=False,
        production_olean_exports_in_diagnostic_archive=0, remaining_original_input_families=4,
        interpretation_limit='Diagnostic copy only. The last flushed marker bounds observed progress; absence does not identify an individual import or prove a specific resource cause.')
    output = ACTUAL / 'actual_archive_authentication.json'
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
