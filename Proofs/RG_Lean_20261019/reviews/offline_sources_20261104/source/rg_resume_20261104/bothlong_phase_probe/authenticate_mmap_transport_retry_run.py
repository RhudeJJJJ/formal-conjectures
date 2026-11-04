"""Offline authentication of the fixed owned-mmap diagnostic; never a proof receipt.

Run only after the actual native metadata, job log and diagnostic.zip have been
captured under mmap_retry_actual. This does not run Lean, strace, native-context gates,
or restore proof objects. Native runner paths are data, never reconstructed locally.
"""
import collections
import hashlib
import math
import runpy
import stat
import json
import pathlib
import re
import zipfile

HERE = pathlib.Path(__file__).resolve().parent
ACTUAL = HERE / 'mmap_retry_actual'
RUN = 41857856028
JOB = 126671224306
COMMIT = 'f5fa2bc163667ecd2d36ab6133abcffca4f83a0c'
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



# These are native runner path identities, not paths to materialize on this host.
NATIVE_ROOT = pathlib.PurePosixPath('/home/runner/work/formal-conjectures/formal-conjectures')
NATIVE_BUILD = NATIVE_ROOT / PREFIX.rstrip('/')
HELPER_MODULE = 'RGDiagnostic.PhaseMarker'
FIXTURE_MODULE = 'Proofs.RGDiagnosticImportFixture'
CONTROL_MODULE = 'Proofs.RGDiagnosticMarkerControl'
TRACE_FLAGS = ['--kill-on-exit', '-f', '-I', '1', '-yy', '-ttt', '-T',
               '-e', 'trace=mmap,munmap,mremap']
LIFECYCLE_STEP = 'Require owned-tracee lifecycle and actual mmap observation before Lean control'
CONTROL_STEP = 'Require the isolated flushed-marker control before any proof restoration'
PROBE_STEP = 'Observe the isolated diagnostic copy with unchanged strict kernel limits'
CODE_FILES = {
    'ci/rg_bothlong_mmap_trace_20261104.py': (
        'a8799847517d58f12e25f1a6aa67a7a525328baf84b19fddd6c9558a7fdb55ed',
        'e11e23bcb09b974dd19c58e7e2458f4b43fc409d'),
    'ci/rg_bothlong_phase_probe_20261104.py': (
        '4ab98348b61d6570fe4a807daef51a7d8fb292af20697aeadaff219fd10f6f43',
        '144614269b3d78c37efbf11dbb6c8fa07086055f'),
    '.github/workflows/rg-d1-bothlong-phase-probe-20261104.yml': (
        '7acc6c499fbda379bd7a0404637a4221fd1fe1f6b2e97a9cb393d314021f4a2f',
        '893d1378b3d90ce60937bf12cce555138c585355'),
    'ci/rg_github_artifacts.py': (
        'db9221ee4aa24f77082c98f33588b987531fc77f9f93c49111d31ad12363b0ef',
        '0d6b0ca19ca8b1717621559b426a0a7b0b9d9520'),
}
CODE_ROOTS = {
    '.github/workflows/rg-d1-bothlong-phase-probe-20261104.yml': 'transport_retry_candidate/patch',
    'ci/rg_github_artifacts.py': 'transport_retry_candidate/patch',
}
PARENT_AUTHENTICATOR_SHA = '2f586040f635d049b1c1002cf45cc6a77b892e013e5f8e968561a4585a4d97a3'
TRACE_HELPER_SHA = CODE_FILES['ci/rg_bothlong_mmap_trace_20261104.py'][0]
REPOSITORY = 'RhudeJJJJ/formal-conjectures'
REF = 'refs/heads/rg-d1-bothlong-phase-probe-20261104'
NATIVE_IDS = dict(GITHUB_REPOSITORY=REPOSITORY, GITHUB_REF=REF,
    GITHUB_SHA=COMMIT, GITHUB_RUN_ID=str(RUN), GITHUB_RUN_ATTEMPT='1', GITHUB_JOB='diagnose',
    GITHUB_WORKFLOW_REF=REPOSITORY + '/.github/workflows/rg-d1-bothlong-phase-probe-20261104.yml@' + REF)


def unique_json(pairs):
    value = {}
    for key, item in pairs:
        assert key not in value, 'Repeated JSON key: ' + key
        value[key] = item
    return value


def decode_json(raw):
    return json.loads(raw, object_pairs_hook=unique_json)


def checked_number(value, minimum=0):
    assert type(value) in (int, float) and math.isfinite(value) and value >= minimum
    return value


def digest_string(value):
    assert isinstance(value, str) and re.fullmatch(r'[0-9a-f]{64}', value)
    return value


def fixed_code_and_parser():
    bindings = {}
    for relative, (digest, blob) in CODE_FILES.items():
        path = HERE / CODE_ROOTS.get(relative, 'mmap_trace_candidate/patch') / relative
        raw = path.read_bytes()
        assert sha(raw) == digest
        assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == blob
        bindings[relative] = dict(sha256=digest, git_blob_sha1=blob, bytes=len(raw))
    # runpy's default __name__ is not __main__. No helper command, native gate,
    # strace inspection, subprocess, or environment mutation is invoked here.
    parser = runpy.run_path(str(HERE / 'mmap_trace_candidate/patch/ci/rg_bothlong_mmap_trace_20261104.py'))
    assert parser['FLAGS'] == TRACE_FLAGS
    return bindings, parser


def retained_trace(archive, relative):
    assert pathlib.PurePosixPath(relative).name == relative
    local = ACTUAL / 'offline_raw_traces' / relative
    local.parent.mkdir(exist_ok=True)
    raw = archive.read(PREFIX + relative)
    if local.exists():
        assert local.is_file() and not local.is_symlink() and local.read_bytes() == raw
    else:
        with local.open('xb') as stream:
            stream.write(raw)
    return local


def normalized_trace(parser, local, native):
    observed = parser['summarize_trace'](local)
    assert observed['trace_path'] == str(local)
    # Only this one field is normalized. File-descriptor paths inside the raw
    # syscall observations remain exactly the native strings from the ZIP.
    observed['trace_path'] = str(native)
    assert observed['timestamp_kind'] == 'UNIX_WALL_CLOCK_SECONDS'
    assert observed['lean_marker_timestamps_are_separate_monotonic_clock'] is True
    assert observed['main_pid'] is None and observed['main_exit_code'] is None
    assert observed['main_signal'] is None and observed['trace_success_claim'] is False
    assert observed['original_kernel_export_claim'] is False
    assert observed['family_closure_claim'] is False and observed['raw_trace_retained'] is True
    return observed


def mapping_observation(parser, local_trace, native_fixture, size, fixture_sha):
    """Pure replay using archived trace bytes and separately bound native fields.

    The small Python fixture bytes are archived and rehashed separately. The
    diagnostic Lean .olean is deliberately not an artifact; its hash and size
    are recorded by the pinned native controller, and that limitation is kept.
    """
    assert type(size) is int and size > 0
    digest_string(fixture_sha)
    matches = collections.deque(maxlen=parser['TAIL_LIMIT'])
    counts = dict(complete_exact_file_attempts=0, successful_mmaps=0, failed_mmaps=0)

    def observe(call):
        if call['syscall'] == 'mmap' and call['file_path'] == str(native_fixture) and \
                call['length_bytes'] == size and call['offset_bytes'] == 0 and \
                call['outcome'] in ('SUCCESS', 'ERROR'):
            counts['complete_exact_file_attempts'] += 1
            counts['successful_mmaps' if call['outcome'] == 'SUCCESS' else 'failed_mmaps'] += 1
            matches.append(call)

    summary = parser['_read_trace'](local_trace, observe)
    assert counts['complete_exact_file_attempts'] > 0
    return dict(fixture_path=str(native_fixture), fixture_bytes=size, fixture_sha256=fixture_sha,
                trace_bytes=summary['trace_bytes'], trace_sha256=summary['trace_sha256'],
                **counts, last_matching_attempts=list(matches),
                mapping_failure_is_observation_not_lean_failure=True,
                actual_lean_control_success_must_be_checked_separately=True)


def require_identity(value, *, pid=None, start=None, parent=None, group=None, live=False):
    assert value['status'] == 'READ'
    assert type(value['pid']) is int and value['pid'] > 0
    assert type(value['start_time_ticks']) is int and value['start_time_ticks'] >= 0
    for field, expected in (('pid', pid), ('start_time_ticks', start),
                            ('parent_pid', parent), ('process_group', group)):
        if expected is not None:
            assert value[field] == expected
    if live:
        assert value['state'] not in ('Z', 'X', 'x')


def authenticate_lifecycle(archive, parser):
    raw = archive.read(PREFIX + 'mmap_trace_control.json')
    report = decode_json(raw)
    assert report['kind'] == 'FIXED_GITHUB_OWNED_MMAP_LIFECYCLE_CONTROL'
    assert report['status'] == 'GH_OWNED_MMAP_TRACE_CONTROL_PASSED'
    assert report['helper_sha256'] == TRACE_HELPER_SHA
    assert report['native_ids'] == NATIVE_IDS and report['wrapper_flags'] == TRACE_FLAGS
    assert report['production_restore_absent_during_control'] is True
    for field in ('original_kernel_export_claim', 'family_closure_claim', 'limits_changed',
                  'proofstore_modified', 'new_process_group_created'):
        assert report[field] is False
    assert 'error' not in report
    executable = report['strace']
    assert executable['path'] == '/usr/bin/strace'
    assert type(executable['bytes']) is int and executable['bytes'] > 0
    digest_string(executable['sha256'])
    match = re.search(r'\bversion\s+([0-9]+)\.([0-9]+)(?:\.([0-9]+))?', executable['version_stdout'])
    assert match is not None
    assert executable['version'] == [int(match[1]), int(match[2]), int(match[3] or 0)]
    assert tuple(executable['version'][:2]) >= (6, 6) and executable['version_returncode'] == 0
    assert isinstance(executable['version_stderr'], str)
    fixture = report['fixture']
    native_directory = NATIVE_BUILD / 'mmap_trace_fixture'
    assert fixture['directory'] == str(native_directory) and fixture['success'] is True
    assert fixture['process_group_changed'] is False and fixture['tracee_signals_sent'] == []
    assert fixture['fixture_program_sha256'] == sha(parser['FIXTURE_PROGRAM'].encode())
    assert fixture['fixture_self_exit_seconds'] == parser['FIXTURE_SELF_EXIT_SECONDS'] == 15.0
    assert fixture['kill_at_seconds'] == parser['KILL_AT_SECONDS'] == 2.0
    assert fixture['tracee_end_timeout_seconds'] == parser['TRACEE_END_TIMEOUT_SECONDS'] == 3.0
    for field in ('error', 'cleanup_error', 'trace_parse_error', 'tracee_final_cleanup_observation'):
        assert field not in fixture
    expected_files = {'fixture.bin', 'tracee_ready.json', 'fixture.mmap.log',
                      'tracer.stdout.log', 'tracer.stderr.log'}
    assert set(fixture['files']) == expected_files
    present = {n.removeprefix(PREFIX + 'mmap_trace_fixture/') for n in archive.namelist()
               if n.startswith(PREFIX + 'mmap_trace_fixture/') and not n.endswith('/')}
    assert present == expected_files
    files = {}
    for name in sorted(expected_files):
        data = archive.read(PREFIX + 'mmap_trace_fixture/' + name)
        assert fixture['files'][name] == dict(bytes=len(data), sha256=sha(data))
        files[name] = dict(bytes=len(data), sha256=sha(data))
    obj = archive.read(PREFIX + 'mmap_trace_fixture/fixture.bin')
    assert obj == b'R' * parser['FIXTURE_BYTES'] and len(obj) == 4096
    assert fixture['fixture_object'] == dict(path=str(native_directory / 'fixture.bin'),
                                            bytes=len(obj), sha256=sha(obj))
    ready = decode_json(archive.read(PREFIX + 'mmap_trace_fixture/tracee_ready.json'))
    assert ready == fixture['fixture_ready']
    assert ready['fixture_path'] == str(native_directory / 'fixture.bin')
    assert ready['fixture_bytes'] == len(obj)
    context = fixture['proc_namespace_before_spawn']
    assert context['same_pid_namespace'] is True
    for field in ('pid', 'parent_pid', 'process_group'):
        assert type(context['python_' + field]) is int and context['python_' + field] > 0
        assert context['python_' + field] == context['proc_self_' + field]
    tracer, before = fixture['tracer_identity_before'], fixture['tracee_identity_before']
    require_identity(tracer, parent=context['python_pid'], group=context['python_process_group'], live=True)
    assert tracer['pid'] != context['python_pid']
    require_identity(before, pid=ready['pid'], start=ready['start_time_ticks'],
                     parent=tracer['pid'], group=context['python_process_group'], live=True)
    assert before['pid'] not in (tracer['pid'], context['python_pid'])
    assert ready['parent_pid'] == before['parent_pid'] and ready['process_group'] == before['process_group']
    assert fixture['observed_tracee_tracer_pid'] == tracer['pid']
    require_identity(fixture['tracee_identity_immediately_before_kill'], pid=before['pid'],
                     start=before['start_time_ticks'], parent=tracer['pid'],
                     group=before['process_group'], live=True)
    assert fixture['tracee_tracer_pid_immediately_before_kill'] == tracer['pid']
    after = fixture['tracee_identity_after']
    assert after['pid'] == before['pid']
    assert after['status'] == 'GONE' or (after['status'] == 'READ' and
           (after['start_time_ticks'] != before['start_time_ticks'] or after['state'] == 'Z'))
    assert fixture['tracee_ended_after_owned_tracer_kill'] is True
    assert fixture['tracer_signal_sent'] == 'SIGKILL' and fixture['tracer_returncode'] == -9
    times = {k: checked_number(fixture[k]) for k in (
        'ready_at_spawn_elapsed_seconds', 'prekill_at_spawn_elapsed_seconds',
        'tracer_kill_at_spawn_elapsed_seconds', 'tracee_end_observed_spawn_elapsed_seconds',
        'latest_planned_end_observation_spawn_elapsed_seconds')}
    assert times['ready_at_spawn_elapsed_seconds'] <= 5.0
    assert times['ready_at_spawn_elapsed_seconds'] <= times['prekill_at_spawn_elapsed_seconds'] <= \
        times['tracer_kill_at_spawn_elapsed_seconds'] <= times['tracee_end_observed_spawn_elapsed_seconds'] < 14.0
    assert times['tracer_kill_at_spawn_elapsed_seconds'] >= 2.0
    assert times['latest_planned_end_observation_spawn_elapsed_seconds'] == \
        times['prekill_at_spawn_elapsed_seconds'] + 3.0 + 3.0
    assert times['latest_planned_end_observation_spawn_elapsed_seconds'] < 14.0
    assert fixture['earliest_natural_self_exit_spawn_elapsed_seconds'] == 15.0
    assert fixture['self_exit_separation_margin_seconds'] == 1.0
    checked_number(fixture['elapsed_seconds'])
    command = fixture['command']
    separator = command.index('--')
    assert command[:separator + 1] == ['/usr/bin/strace', *TRACE_FLAGS, '-o',
                                     str(native_directory / 'fixture.mmap.log'), '--']
    tail = command[separator + 1:]
    assert len(tail) == 6 and pathlib.PurePosixPath(tail[0]).is_absolute()
    assert pathlib.PurePosixPath(tail[0]).name.startswith('python3')
    assert tail[1:] == ['-I', '-c', parser['FIXTURE_PROGRAM'],
                        str(native_directory / 'fixture.bin'), str(native_directory / 'tracee_ready.json')]
    # The nested raw trace is copied under a local neutral name. No native
    # /home/runner path is created or used as a local filesystem target.
    local = ACTUAL / 'offline_raw_traces' / 'lifecycle.fixture.mmap.log'
    local.parent.mkdir(exist_ok=True)
    trace_raw = archive.read(PREFIX + 'mmap_trace_fixture/fixture.mmap.log')
    if local.exists():
        assert local.is_file() and not local.is_symlink() and local.read_bytes() == trace_raw
    else:
        with local.open('xb') as stream:
            stream.write(trace_raw)
    summary = normalized_trace(parser, local, native_directory / 'fixture.mmap.log')
    assert summary == fixture['trace_summary']
    mapping = mapping_observation(parser, local, native_directory / 'fixture.bin', len(obj), sha(obj))
    assert mapping == fixture['mapping'] and mapping['successful_mmaps'] >= 1
    assert any(m['pid'] == before['pid'] and m['outcome'] == 'SUCCESS'
               for m in mapping['last_matching_attempts'])
    return dict(report_sha256=sha(raw), status='ACTUAL_NATIVE_LIFECYCLE_AND_FILE_MMAP_AUTHENTICATED',
                native_ids=NATIVE_IDS, strace=executable, fixture_files=files,
                tracer_identity=tracer, tracee_identity=before,
                tracee_immediately_before_kill=fixture['tracee_identity_immediately_before_kill'],
                tracee_after_kill=after, actual_timing_seconds=times,
                earliest_natural_exit_seconds=15.0, no_direct_tracee_signals=True,
                mapping=mapping, trace_summary=summary,
                native_path_prefix=str(NATIVE_BUILD), local_raw_trace_path=str(local),
                local_fixture_from_preparation_was_not_a_success=True)


def expected_lean_tail(module, flags):
    source_root = NATIVE_ROOT / 'ci/rg_bothlong_phase_probe_20261104'
    if module == FIXTURE_MODULE:
        source_root /= 'control_imports'
    output_root = NATIVE_BUILD / ('helper_objects' if module == HELPER_MODULE else
                                  'control_imports' if module == FIXTURE_MODULE else 'probe_objects')
    relative = module.replace('.', '/')
    return [*flags, '-R', str(source_root), '-o', str(output_root / (relative + '.olean.pending')),
            str(source_root / (relative + '.lean'))]


def authenticate_invocation(archive, parser, row, phase, spec):
    module = row['module']
    assert module in ({HELPER_MODULE, FIXTURE_MODULE, CONTROL_MODULE} if phase == 'control' else {PROBE})
    assert row['trace_log'] == module + '.mmap.log' and row['trace_report'] == module + '.mmap.json'
    detail_raw = archive.read(PREFIX + row['trace_report'])
    assert sha(detail_raw) == row['trace_report_sha256']
    detail = decode_json(detail_raw)
    assert detail['module'] == module and detail['phase'] == phase
    assert detail['native_run_id'] == str(RUN) and detail['native_run_attempt'] == '1'
    assert detail['native_workflow_source_commit'] == COMMIT
    command = detail['lean_command']
    assert isinstance(command, list) and all(isinstance(a, str) for a in command)
    assert pathlib.PurePosixPath(command[0]).is_absolute() and pathlib.PurePosixPath(command[0]).name == 'lean'
    assert command[1:] == expected_lean_tail(module, spec['required_compiler_flags'])
    execution = ['/usr/bin/strace', *TRACE_FLAGS, '-o', str(NATIVE_BUILD / row['trace_log']), '--', *command]
    assert detail['execution_command'] == execution
    for field in ('tracer_pid', 'tracer_returncode', 'compiler_returncode', 'compiler_returncode_source',
                  'timeout', 'traced_process_seconds'):
        assert detail[field] == row[field]
    assert type(row['tracer_pid']) is int and row['tracer_pid'] > 0
    assert type(row['tracer_returncode']) is int
    assert type(row['timeout']) is bool and type(row['success']) is bool
    checked_number(row['traced_process_seconds'])
    assert checked_number(row['seconds']) >= row['traced_process_seconds']
    assert detail['trace_timestamps'] == 'UNIX_WALL_CLOCK_SECONDS'
    assert detail['host_event_timestamps'] == 'MONOTONIC_NANOSECONDS'
    assert detail['lean_marker_timestamps'] == 'MONOTONIC_MILLISECONDS'
    assert detail['instrumented_timing_is_not_an_untraced_performance_measurement'] is True
    assert detail['production_kernel_export_claim'] is False
    log = archive.read(PREFIX + module + '.log')
    assert sha(log) == row['log_sha256']
    errors = bool(re.search(rb'\b(error|warning)(?:\([^\n]*?\))?:', log))
    assert row['success'] == (not row['timeout'] and row['tracer_returncode'] == 0 and not errors)
    if row['success']:
        assert row['compiler_returncode'] == 0
        assert row['compiler_returncode_source'] == 'STRACE_PROPAGATED_ZERO_STATUS'
        digest_string(row['diagnostic_output_sha256'])
    else:
        assert row['compiler_returncode'] is None and row['diagnostic_output_sha256'] is None
        assert row['compiler_returncode_source'] == 'NOT_OBSERVED_DIRECTLY'
    if row['timeout']:
        assert row['tracer_returncode'] == -9 and row['traced_process_seconds'] >= 900.0
    local = retained_trace(archive, row['trace_log'])
    summary = normalized_trace(parser, local, NATIVE_BUILD / row['trace_log'])
    assert summary == detail['trace_summary'] and summary['trace_sha256'] == row['trace_sha256']
    return dict(module=module, phase=phase, native_lean_command=command,
                native_execution_command=execution, tracer_pid=row['tracer_pid'],
                tracer_returncode=row['tracer_returncode'], compiler_returncode=row['compiler_returncode'],
                compiler_returncode_source=row['compiler_returncode_source'], success=row['success'],
                timeout=row['timeout'], traced_process_seconds=row['traced_process_seconds'],
                raw_trace_sha256=summary['trace_sha256'], raw_trace_bytes=summary['trace_bytes'],
                detail_report_sha256=sha(detail_raw), log_sha256=sha(log), trace_summary=summary,
                diagnostic_output_sha256_recorded_by_native_controller=row['diagnostic_output_sha256'],
                diagnostic_output_bytes_present_in_archive=False, raw_trace_local_path=str(local))


def authenticate_host_events(archive, phase, invocations):
    raw = archive.read(PREFIX + phase + '_host_events.jsonl')
    events = [decode_json(line) for line in raw.splitlines()]
    assert len(events) == 3 * len(invocations)
    stamps = [r['monotonic_ns'] for r in events]
    assert all(type(n) is int and n >= 0 for n in stamps) and stamps == sorted(stamps)
    for index, invocation in enumerate(invocations):
        launch, started, ended = events[index * 3:(index + 1) * 3]
        assert all(r['module'] == invocation['module'] for r in (launch, started, ended))
        assert launch['event'] == 'TRACED_LEAN_LAUNCH_REQUESTED' and launch['timeout_seconds'] == 900
        assert launch['command'] == invocation['native_lean_command']
        assert launch['execution_command'] == invocation['native_execution_command']
        assert started['event'] == 'TRACE_PROCESS_STARTED' and started['tracer_pid'] == invocation['tracer_pid']
        assert ended['event'] == ('TRACE_TIMEOUT' if invocation['timeout'] else 'TRACE_PROCESS_EXITED')
        assert ended['tracer_pid'] == invocation['tracer_pid']
        assert ended['tracer_returncode'] == invocation['tracer_returncode']
        assert ended['seconds'] == invocation['traced_process_seconds']
    return dict(sha256=sha(raw), events=events, clock='MONOTONIC_NANOSECONDS',
                correlated_with_unix_trace_clock=False)


def authenticate_guard(resource, host, phase, expected_exit):
    assert resource['phase'] == phase and resource['scope'] == 'FIXED_BOTHLONG_PHASE_WORKER_ONLY'
    assert resource['status'] == 'VERIFIER_COMPLETED' and resource['exit_code'] == expected_exit
    assert host['status'] == 'OWNED_KERNEL_GROUP_ENDED' and host['exit_code'] == expected_exit
    assert host['host_reserve_stop'] is False and host['foreign_processes_signalled'] == 0
    assert resource['resource_reserve_mib'] == 2048
    assert resource['mathlib_and_lean_flags_unchanged'] is True
    assert resource['observer_created_kernel_receipt'] is False
    assert resource['additional_proc_fields_are_diagnostic_only'] is True
    assert resource['samples']
    assert resource['maximum_aggregate_lean_rss'] >= max(s['aggregate_lean_rss'] for s in resource['samples'])
    assert min(s['available_bytes'] for s in resource['samples']) > 2048 * 1024**2
    return dict(status=resource['status'], exit_code=expected_exit, memory_reserve_mib=2048,
                host_status=host['status'], host_reserve_stop=False, foreign_processes_signalled=0,
                maximum_aggregate_lean_rss=resource['maximum_aggregate_lean_rss'],
                unknown_or_unreadable_cgroup_limits_are_not_claimed_absent=True)


def observed_probe_pid(resource, invocation):
    identities, count = {}, 0
    for sample in resource['samples']:
        for item in sample.get('process_diagnostics', {}).get('lean_processes', []):
            if item.get('module') != PROBE.rsplit('.', 1)[-1] + '.lean':
                continue
            process = item['process']
            if process.get('same_process_identity_across_reads') is not True:
                continue
            before, after = process['stat_before'], process['stat_after']
            if before['status'] != 'READ' or after['status'] != 'READ':
                continue
            first, last = before['values'], after['values']
            assert first['start_time_ticks'] == last['start_time_ticks']
            assert first['parent_pid'] == last['parent_pid'] == invocation['tracer_pid']
            key = (process['pid'], first['start_time_ticks'])
            identities[key] = dict(pid=process['pid'], start_time_ticks=first['start_time_ticks'],
                                   parent_tracer_pid=invocation['tracer_pid'], process_group=last['process_group'])
            count += 1
    assert len(identities) <= 1
    if not identities:
        return dict(status='NO_IDENTITY_BOUND_PROBE_SAMPLE', main_pid=None,
                    observed_sample_count=0, pid_inferred_from_first_trace_line=False)
    value = next(iter(identities.values()))
    assert value['pid'] in invocation['trace_summary']['observed_pids']
    terminal = invocation['trace_summary']['per_pid_terminal'].get(str(value['pid']))
    if invocation['success'] and terminal is not None:
        assert terminal['exit_code'] == 0 and terminal['signal'] is None
    return dict(status='LEAN_PID_BOUND_BY_OBSERVER_START_IDENTITY_AND_PARENT_TRACER',
                **value, observed_sample_count=count, trace_terminal_observation=terminal,
                pid_inferred_from_first_trace_line=False,
                no_unobserved_exit_status_or_timeout_signal_inferred=True)


def common_phase(record, phase, spec, lifecycle_sha):
    assert record['phase'] == phase and 'version 4.33.1,' in record['lean']
    assert record['source_spec_sha256'] == SPEC_SHA
    assert record['strict_flags'] == spec['required_compiler_flags']
    assert record['original_source_sha256'] == ORIGINAL_SHA and record['original_endpoint'] == ORIGINAL
    assert record['diagnostic_endpoint'] == PROBE
    assert record['module_timeout_seconds'] == 900 and record['workers'] == 1
    assert record['memory_reserve_mib'] == 2048
    assert record['mmap_trace_enabled'] is True and record['trace_lifecycle_control_sha256'] == lifecycle_sha
    for field in ('production_receipt_created', 'original_kernel_export_claim', 'family_closure_claim'):
        assert record[field] is False
    assert record['probe_output_directory_excluded_from_import_search'] is True
    assert all(pathlib.PurePosixPath(p).name != 'probe_objects' for p in record['import_search_paths'])


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


def authenticate(report):
    report['stage'] = 'PINNED_SOURCE_AND_PURE_PARSER'
    bindings, parser = fixed_code_and_parser()
    report['code_bindings'] = bindings
    parent_bytes = (HERE / 'authenticate_mmap_run.py').read_bytes()
    assert sha(parent_bytes) == PARENT_AUTHENTICATOR_SHA
    report['inherited_mmap_authenticator_sha256'] = sha(parent_bytes)
    base_bytes = (HERE / 'authenticate_direct_io_run.py').read_bytes()
    assert sha(base_bytes) == '3bc7134af27d46d0a5b904a0f5932152529149cc245be801cd793d2a4c0f31a8'
    report['inherited_direct_io_authenticator_sha256'] = sha(base_bytes)
    spec_raw = (HERE / 'namespace_repair_patch/ci/rg_bothlong_phase_probe_20261104_spec.json').read_bytes()
    assert sha(spec_raw) == SPEC_SHA
    spec = decode_json(spec_raw)
    assert spec['unchanged_limits'] == dict(memory_reserve_mib=2048, module_timeout_seconds=900, workers=1)
    for item in spec['artifacts']:
        source = (HERE / 'namespace_repair_patch/ci/rg_bothlong_phase_probe_20261104' / item['path']).read_bytes()
        assert len(source) == item['bytes'] and sha(source) == item['sha256']
        if item['module'] == PROBE:
            original = b''.join(line for line in source.splitlines(keepends=True)
                if line != b'import RGDiagnostic.PhaseMarker\n'
                and not line.startswith((b'rg_phase ', b'rg_phase_checked ')))
            assert sha(original) == ORIGINAL_SHA
    report['stage'] = 'NATIVE_TERMINAL_METADATA'
    run_raw, jobs_raw = (ACTUAL / 'run.json').read_bytes(), (ACTUAL / 'jobs.json').read_bytes()
    run, jobs_document = decode_json(run_raw), decode_json(jobs_raw)
    jobs = jobs_document['jobs']
    assert len(jobs) == 1 and jobs_document.get('total_count', 1) == 1
    job = jobs[0]
    assert run['id'] == RUN and run['head_sha'] == COMMIT
    assert run['head_branch'] == REF.removeprefix('refs/heads/')
    assert run['path'] == '.github/workflows/rg-d1-bothlong-phase-probe-20261104.yml'
    assert run['event'] == 'push' and run['run_attempt'] == 1
    assert run['repository']['full_name'] == REPOSITORY
    assert run['status'] == job['status'] == 'completed'
    assert job['id'] == JOB and job['run_id'] == RUN and job['head_sha'] == COMMIT
    assert job['run_attempt'] == 1 and job['name'] == 'diagnose'
    assert job['conclusion'] == run['conclusion']
    assert run['conclusion'] in ('success', 'failure', 'cancelled', 'timed_out')
    steps = {s['name']: s for s in job['steps']}
    assert len(steps) == len(job['steps'])
    report.update(native_conclusion=run['conclusion'], native_run_sha256=sha(run_raw),
                  native_jobs_sha256=sha(jobs_raw),
                  native_job_log_sha256=sha((ACTUAL / 'job.log').read_bytes()),
                  unsuccessful_native_steps=[dict(name=s['name'], conclusion=s['conclusion'])
                                             for s in job['steps'] if s['conclusion'] != 'success'])
    report['transport_retry_observations'] = transport_retry_observations((ACTUAL / 'job.log').read_bytes())
    report['stage'] = 'NATIVE_ARTIFACT_AND_ZIP'
    catalog_raw = (ACTUAL / 'artifacts.json').read_bytes()
    catalog = decode_json(catalog_raw)
    assert len(catalog['artifacts']) == 1 and catalog.get('total_count', 1) == 1
    meta = catalog['artifacts'][0]
    assert meta['workflow_run']['id'] == RUN and meta['workflow_run']['head_sha'] == COMMIT
    assert meta['name'] == f'rg-bothlong-phase-diagnostic-20261104-{RUN}-1'
    assert meta['expired'] is False
    archive_raw = (ACTUAL / 'diagnostic.zip').read_bytes()
    assert len(archive_raw) == meta['size_in_bytes'] and meta['digest'] == 'sha256:' + sha(archive_raw)
    report.update(artifact=meta['id'], artifact_bytes=len(archive_raw), artifact_sha256=sha(archive_raw),
                  native_artifact_catalog_sha256=sha(catalog_raw))
    with zipfile.ZipFile(ACTUAL / 'diagnostic.zip') as archive:
        names = archive.namelist()
        assert len(names) == len(set(names))
        for info in archive.infolist():
            path = pathlib.PurePosixPath(info.filename)
            assert not path.is_absolute() and '..' not in path.parts and '\\' not in info.filename
            assert not stat.S_ISLNK(info.external_attr >> 16)
            assert not info.filename.endswith(('.olean', '.olean.private', '.olean.server', 'receipt.json'))
        report['artifact_members'] = len(names)
        report['production_olean_exports_in_diagnostic_archive'] = 0
        assert steps['Retain diagnostic logs and phase observations without proof exports']['conclusion'] == 'success'
        def raw(name):
            return archive.read(PREFIX + name)
        def data(name):
            return decode_json(raw(name))
        report['stage'] = 'ACTUAL_EARLY_LIFECYCLE'
        if PREFIX + 'mmap_trace_control.json' in names:
            early = data('mmap_trace_control.json')
            report['reported_lifecycle_status_before_validation'] = early.get('status')
        assert steps[LIFECYCLE_STEP]['conclusion'] == 'success'
        lifecycle = authenticate_lifecycle(archive, parser)
        report['actual_native_lifecycle'] = lifecycle
        report['stage'] = 'ACTUAL_THREE_LEAN_TRACE_CONTROL'
        assert steps[CONTROL_STEP]['conclusion'] == 'success'
        control = data('control_result.json')
        common_phase(control, 'control', spec, lifecycle['report_sha256'])
        assert control['status'] == 'DIAGNOSTIC_MARKER_CONTROL_PASSED'
        assert [r['module'] for r in control['results']] == spec['control_modules_in_compile_order']
        assert control['production_restore_absent_during_control'] is True
        assert control['import_search_paths'] == [str(NATIVE_BUILD / 'helper_objects'), str(NATIVE_BUILD / 'control_imports')]
        assert all(r['success'] and not r['timeout'] for r in control['results'])
        control_invocations = [authenticate_invocation(archive, parser, r, 'control', spec)
                               for r in control['results']]
        control_events = authenticate_host_events(archive, 'control', control_invocations)
        _, control_labels = markers(raw('control_phases.tsv'), spec['control_markers'])
        assert control_labels == control['observed_phase_labels'] == spec['control_markers']
        assert control['last_observed_phase'] == control_labels[-1]
        assert control['named_axiom_profiles'] == [dict(declaration='RGDiagnosticMarkerControl.checked', axioms=[])]
        assert named_axioms(raw(CONTROL_MODULE + '.log').decode()) == control['named_axiom_profiles']
        mapping = control['control_fixture_mapping']
        fixture_row = control['results'][1]
        assert mapping['fixture_sha256'] == fixture_row['diagnostic_output_sha256']
        actual_mapping = mapping_observation(parser,
            ACTUAL / 'offline_raw_traces' / (CONTROL_MODULE + '.mmap.log'),
            NATIVE_BUILD / 'control_imports/Proofs/RGDiagnosticImportFixture.olean',
            mapping['fixture_bytes'], fixture_row['diagnostic_output_sha256'])
        assert actual_mapping == mapping
        control_guards = authenticate_guard(data('control_resource_observer.json'),
                                            data('control_host_reserve.json'), 'control', 0)
        report.update(actual_three_module_control_passed=True,
                      actual_control_invocations=control_invocations, actual_control_host_events=control_events,
                      actual_control_fixture_mapping=actual_mapping, actual_control_guards=control_guards,
                      diagnostic_fixture_output_hash_is_native_record_not_archived_object_bytes=True)
        report['stage'] = 'UNCHANGED_SOURCE_PROJECTION_DIO_AND_COMPLETE_RESTORE'
        for name in ('Authenticate the actual failed run and project only original BothLong imports',
                     'Require direct I/O only for the new owned proofstore loop',
                     'Authenticate all 444 original archives and read back 25191 projected objects',
                     'Require exactly the original BothLong endpoint to remain uncompiled'):
            assert steps[name]['conclusion'] == 'success', name
        report['direct_io'] = authenticate_direct_io(archive)
        assert report['direct_io']['image_identity']
        direct = decode_json(archive.read('rg-proofstore-direct-io.json'))
        assert direct['image'] == str(NATIVE_ROOT / 'rg-ephemeral-proofstore.btrfs')
        assert direct['mount'] == str(NATIVE_BUILD.parent / 'extension')
        plan_raw = raw('projected_plan.json')
        assert sha(plan_raw) == PLAN_SHA and plan_raw == (HERE / 'validation/actual_projected_plan.json').read_bytes()
        plan = decode_json(plan_raw)
        groups = plan['selected_archives']
        assert len(groups) == 444 and plan['required_modules'] == 25192
        total_modules = total_bytes = 0
        for group in groups:
            restored = decode_json(archive.read(f"rg-proofstore-roundtrip-reports/{group['artifact_id']}.json"))
            assert restored['status'] == 'EXACT_ORIGINAL_MEMBERS_RESTORED_AND_READ_BACK_THROUGH_COMPRESSION'
            assert restored['artifact_id'] == group['artifact_id'] and restored['artifact_sha256'] == group['artifact_sha256']
            assert restored['modules'] == len(group['selected_modules'])
            assert restored['all_declared_sidecars_preserved'] is True and restored['fresh_kernel_compilations'] == 0
            total_modules += restored['modules']
            total_bytes += restored['logical_member_bytes']
        assert total_modules == 25191 and total_bytes == 97433499160
        preflight = data('original_endpoint_preflight.json')
        assert preflight['required_modules'] == 25192 and preflight['verified_prior_objects'] == 25191
        assert preflight['fresh_modules'] == [ORIGINAL]
        assert preflight['max_fresh'] == 1 and preflight['within_bound'] is True
        report.update(source_projection_byte_identical_to_reviewed_plan=True,
                      successful_archive_restores=len(groups), successful_prior_object_readbacks=total_modules,
                      selected_logical_object_bytes=total_bytes, actual_original_endpoint_preflight_passed=True)
        report['stage'] = 'ACTUAL_PROBE_TRACE_AND_PHASES'
        probe = data('probe_result.json')
        common_phase(probe, 'probe', spec, lifecycle['report_sha256'])
        assert probe['production_restore_absent_during_control'] is None and probe['control_fixture_mapping'] is None
        assert probe['import_search_paths'][:2] == [str(NATIVE_BUILD / 'helper_objects'), str(NATIVE_BUILD.parent / 'extension')]
        assert str(NATIVE_BUILD / 'control_imports') not in probe['import_search_paths']
        assert len(probe['results']) == 1 and probe['results'][0]['module'] == PROBE
        result = probe['results'][0]
        invocation = authenticate_invocation(archive, parser, result, 'probe', spec)
        events = authenticate_host_events(archive, 'probe', [invocation])
        expected = [m['label'] for m in spec['markers']]
        stamps, labels = markers(raw('probe_phases.tsv'), expected)
        assert labels == probe['observed_phase_labels']
        assert probe['last_observed_phase'] == (labels[-1] if labels else None)
        log = raw(PROBE + '.log')
        profiles = named_axioms(log.decode())
        expected_names = ['Gebendorfer.RadenkovicGutman.D1OriginalSharedBothLong.' + suffix for suffix in
                          ('all_checked', 'adjacent_checked', 'partition_checked', 'budget_checked', 'normalized_target')]
        assert [p['declaration'] for p in profiles] == expected_names[:len(profiles)]
        if result['success']:
            assert probe['status'] == 'DIAGNOSTIC_COPY_COMPILER_COMPLETED'
            assert labels == expected and [p['declaration'] for p in profiles] == expected_names
            assert probe['named_axiom_profiles'] == profiles
        else:
            assert probe['status'] == 'DIAGNOSTIC_COMPILER_FAILED_OR_TIMED_OUT'
            assert probe['named_axiom_profiles'] == []
        expected_conclusion, expected_exit = ('success', 0) if result['success'] else ('failure', 1)
        assert steps[PROBE_STEP]['conclusion'] == run['conclusion'] == expected_conclusion
        resource = data('probe_resource_observer.json')
        host = decode_json(archive.read('rg-proofstore-kernel-reserve.json'))
        guards = authenticate_guard(resource, host, 'probe', expected_exit)
        report.update(actual_diagnostic_compiler_result=result, actual_probe_invocation=invocation,
                      actual_probe_host_events=events, actual_probe_guards=guards,
                      observed_probe_lean_identity=observed_probe_pid(resource, invocation),
                      resource_observations=resource_summary(resource), phase_markers_written=len(labels),
                      last_observed_phase=probe['last_observed_phase'], observed_log_axiom_profiles=profiles,
                      next_unobserved_phase=expected[len(labels)] if len(labels) < len(expected) else None,
                      marker_intervals_seconds=[dict(before=labels[i-1], after=labels[i],
                                                     seconds=(stamps[i]-stamps[i-1])/1000)
                                               for i in range(1, len(labels))],
                      probe_log_sha256=sha(log))
        for name in ('control_result.json', 'control_phases.tsv', 'control_resource_observer.json',
                     'control_host_reserve.json', 'control_host_events.jsonl', 'probe_result.json',
                     'probe_phases.tsv', 'probe_resource_observer.json', 'probe_host_events.jsonl',
                     'original_endpoint_preflight.json', 'mmap_trace_control.json'):
            (ACTUAL / name).write_bytes(raw(name))
        (ACTUAL / 'probe.log').write_bytes(log)
    report['stage'] = 'COMPLETE_DIAGNOSTIC_EVIDENCE_AUTHENTICATED'
    report['status'] = 'ACTUAL_MMAP_DIAGNOSTIC_ARCHIVE_AUTHENTICATED'


def main():
    if not __debug__:
        raise RuntimeError('Offline authentication must not disable assertions')
    report = dict(status='ACTUAL_MMAP_DIAGNOSTIC_INCOMPLETE_OR_REJECTED',
        repository=REPOSITORY, run=RUN, job=JOB, source_commit=COMMIT,
        production_kernel_receipt_created=False, original_large_family_completed=False,
        original_kernel_export_claim=False, family_closure_claim=False,
        production_olean_exports_in_diagnostic_archive=None, remaining_original_input_families=4,
        offline_native_context_or_strace_identity_executed=False,
        offline_github_environment_spoofed=False, original_runner_paths_materialized_locally=False,
        trace_parser_helper_sha256=TRACE_HELPER_SHA,
        interpretation_limit='Diagnostic copy only. Printed Unix trace-line timestamps are separate from syscall duration and monotonic phase markers. Unresolved calls and unknown main-process/exit identities stay explicit. Tracing adds overhead; an observed last mapping does not prove that mapping caused a stall or identify an unobserved import.')
    try:
        authenticate(report)
    except Exception as error:
        report['error'] = dict(type=type(error).__name__, message=str(error))
    ACTUAL.mkdir(exist_ok=True)
    output = ACTUAL / 'actual_archive_authentication.json'
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report['status'] == 'ACTUAL_MMAP_DIAGNOSTIC_ARCHIVE_AUTHENTICATED' else 2


if __name__ == '__main__':
    raise SystemExit(main())
