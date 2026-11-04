"""Complete offline mmap observations, only after the fixed actual authentication.

This reads retained bytes and writes analysis files. It starts no process, uses
no GitHub environment, and never treats native file paths as local inputs.
The required authentication SHA must be supplied after Root's actual check.
"""
import argparse
import collections
import hashlib
import json
import pathlib
import re
import runpy
import zipfile

HERE = pathlib.Path(__file__).resolve().parent
ACTUAL = HERE / 'mmap_actual'
RUN, JOB = 41848259185, 126637373312
COMMIT = '9362f408f8bdda0f27f8bd547c53927401ca5c50'
ORIGINAL = 'Proofs.RadenkovicGutmanD1OriginalSharedBothLong'
PROBE = ORIGINAL + 'PhaseProbe'
HELPER_SHA = 'a8799847517d58f12e25f1a6aa67a7a525328baf84b19fddd6c9558a7fdb55ed'
PLAN_SHA = '11ff7db7f88e1e3aa1722796a5002cc9bb29263cb7343df851a12e699b94cd44'
PREFIX = 'Proofs/RG_Lean_20261019/build/bothlong_phase_probe/'
NATIVE_ROOT = pathlib.PurePosixPath('/home/runner/work/formal-conjectures/formal-conjectures')
NATIVE_BUILD = NATIVE_ROOT / PREFIX.rstrip('/')
NATIVE_RESTORED = NATIVE_BUILD.parent / 'extension'
LINE_PREFIX = re.compile(r'^\s*(?:\[pid\s+([0-9]+)\]|([0-9]+))\s+([0-9]+\.[0-9]+)\s+(.*)$')


def sha_file(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def unique(pairs):
    value = {}
    for key, item in pairs:
        assert key not in value, 'Repeated JSON key: ' + key
        value[key] = item
    return value


def decode(raw):
    return json.loads(raw, object_pairs_hook=unique)


def emit(stream, row):
    stream.write(json.dumps(row, sort_keys=True, separators=(',', ':')) + '\n')


def file_identity(path):
    return dict(path=str(path), bytes=path.stat().st_size, sha256=sha_file(path))


def address(value):
    if value in ('NULL', '0'):
        return 0
    if isinstance(value, str) and re.fullmatch(r'0x[0-9a-fA-F]+', value):
        return int(value, 16)
    return None


def fresh_counts():
    return dict(attempts=0, successful=0, failed=0, unknown_outcome=0,
                errno_counts={}, requested_lengths_bytes={}, requested_length_sum_bytes=0,
                requested_length_sum_by_outcome_bytes=dict(SUCCESS=0, ERROR=0, UNKNOWN_RETURN=0),
                requested_length_sum_by_errno_bytes={},
                unknown_requested_lengths=0, requested_addresses={}, returned_addresses={},
                successful_address_comparisons=dict(equal=0, unequal=0,
                    unequal_after_null_or_zero_request=0, unequal_after_nonzero_request=0,
                    not_comparable=0), first_trace_line=None, last_trace_line=None)


def increment(table, key):
    table[key] = table.get(key, 0) + 1


def add_call(counts, call):
    counts['attempts'] += 1
    outcome = call['outcome']
    counts[{'SUCCESS': 'successful', 'ERROR': 'failed', 'UNKNOWN_RETURN': 'unknown_outcome'}[outcome]] += 1
    if outcome == 'ERROR':
        increment(counts['errno_counts'], call['errno'])
    length = call['length_bytes']
    if type(length) is int:
        increment(counts['requested_lengths_bytes'], str(length))
        counts['requested_length_sum_bytes'] += length
        counts['requested_length_sum_by_outcome_bytes'][outcome] += length
        if outcome == 'ERROR':
            by_errno = counts['requested_length_sum_by_errno_bytes']
            by_errno[call['errno']] = by_errno.get(call['errno'], 0) + length
    else:
        counts['unknown_requested_lengths'] += 1
    increment(counts['requested_addresses'], call['requested_address'])
    if outcome == 'SUCCESS':
        increment(counts['returned_addresses'], call['result_text'])
        requested, returned = address(call['requested_address']), address(call['result_text'])
        comparisons = counts['successful_address_comparisons']
        if requested is None or returned is None:
            comparisons['not_comparable'] += 1
        elif requested == returned:
            comparisons['equal'] += 1
        else:
            comparisons['unequal'] += 1
            comparisons['unequal_after_null_or_zero_request' if requested == 0
                        else 'unequal_after_nonzero_request'] += 1
    first = dict(line=call['first_line'], pid=call['pid'],
                 printed_wallclock_unix_seconds=call['first_trace_line_wallclock_unix_seconds'])
    last = dict(line=call['last_line'], pid=call['pid'],
                printed_wallclock_unix_seconds=call['last_trace_line_wallclock_unix_seconds'])
    if counts['first_trace_line'] is None or first['line'] < counts['first_trace_line']['line']:
        counts['first_trace_line'] = first
    if counts['last_trace_line'] is None or last['line'] > counts['last_trace_line']['line']:
        counts['last_trace_line'] = last


def selected_modules(plan):
    assert plan['endpoint'] == ORIGINAL and plan['required_modules'] == 25192
    assert plan['fresh_modules'] == [ORIGINAL] and len(plan['selected_archives']) == 444
    selected = {}
    for group in plan['selected_archives']:
        for module, item in group['selected_modules'].items():
            assert module not in selected and module != ORIGINAL
            row = item['row']
            assert row['module'] == module
            assert row['source_sha256'] == plan['source_sha256'][module]
            assert row['source_closure_sha256'] == plan['source_closure_sha256'][module]
            native = str(NATIVE_RESTORED / (module.replace('.', '/') + '.olean'))
            selected[module] = dict(module=module, exact_native_olean_path=native,
                source_sha256=row['source_sha256'], source_closure_sha256=row['source_closure_sha256'],
                original_output_sha256=row['output_sha256'],
                selected_transport_artifact_id=group['artifact_id'],
                selected_transport_artifact_sha256=group['artifact_sha256'])
    assert len(selected) == 25191
    assert set(selected) == set(plan['source_sha256']) - {ORIGINAL}
    assert len({v['exact_native_olean_path'] for v in selected.values()}) == len(selected)
    return selected


def residual_lines(trace, covered_lines, output):
    """Retain every line outside a complete parsed call or recognized metadata.

    This complements the pinned parser's exact counters. A failed resumed-call
    parse can contribute two residual lines; residual-line counts therefore
    must not be relabelled as syscall or parser-error counts.
    """
    counts = collections.Counter()
    first, last = None, None
    with trace.open('rb') as stream, output.open('x') as out:
        for number, raw in enumerate(stream, 1):
            try:
                text = raw.decode().rstrip('\r\n')
            except UnicodeDecodeError:
                category = 'NON_UTF8_LINE'
                emit(out, dict(line=number, category=category, complete_raw_line_hex=raw.hex()))
                counts[category] += 1
                continue
            match = LINE_PREFIX.fullmatch(text)
            if match:
                pid, stamp, body = int(match[1] or match[2]), match[3], match[4]
                observed = dict(line=number, pid=pid, printed_wallclock_unix_seconds=stamp)
                if first is None:
                    first = observed
                last = observed
            else:
                pid, stamp, body = None, None, text
            if number in covered_lines:
                assert match is not None
                continue
            if match and (re.fullmatch(r'\+\+\+ exited with ([0-9]+) \+\+\+', body) or
                          re.fullmatch(r'\+\+\+ killed by ([A-Z][A-Z0-9_]+)(?: \(core dumped\))? \+\+\+', body) or
                          (body.startswith('--- ') and body.endswith(' ---'))):
                continue
            category = ('UNRECOGNIZED_PID_TIMESTAMP' if match is None else
                        'UNFINISHED_WITHOUT_COMPLETE_PARSED_PAIR' if body.endswith('<unfinished ...>') else
                        'RESUMED_WITHOUT_COMPLETE_PARSED_PAIR' if re.match(r'^<\.\.\. (mmap|munmap|mremap) resumed>', body) else
                        'UNPARSED_SYSCALL_OR_OTHER_LINE')
            counts[category] += 1
            emit(out, dict(line=number, category=category, pid=pid,
                           printed_wallclock_unix_seconds=stamp, complete_raw_line_utf8=text))
    return dict(line_counts=dict(sorted(counts.items())), total_residual_lines=sum(counts.values()),
                residual_lines_are_not_syscall_counts=True,
                first_timestamped_trace_line=first, last_timestamped_trace_line=last)


def analyze(authentication_sha256):
    assert re.fullmatch(r'[0-9a-f]{64}', authentication_sha256)
    auth_path = ACTUAL / 'actual_archive_authentication.json'
    assert sha_file(auth_path) == authentication_sha256
    auth = decode(auth_path.read_bytes())
    assert auth['status'] == 'ACTUAL_MMAP_DIAGNOSTIC_ARCHIVE_AUTHENTICATED'
    assert auth['stage'] == 'COMPLETE_DIAGNOSTIC_EVIDENCE_AUTHENTICATED'
    assert (auth['run'], auth['job'], auth['source_commit']) == (RUN, JOB, COMMIT)
    assert auth['trace_parser_helper_sha256'] == HELPER_SHA
    assert auth['code_bindings']['ci/rg_bothlong_mmap_trace_20261104.py']['sha256'] == HELPER_SHA
    assert auth['source_projection_byte_identical_to_reviewed_plan'] is True
    assert auth['successful_archive_restores'] == 444 and auth['successful_prior_object_readbacks'] == 25191
    assert auth['selected_logical_object_bytes'] == 97433499160
    invocation = auth['actual_probe_invocation']
    assert invocation['module'] == PROBE and invocation['phase'] == 'probe'
    trace = ACTUAL / 'offline_raw_traces' / (PROBE + '.mmap.log')
    assert trace.is_file() and not trace.is_symlink()
    assert trace.stat().st_size == invocation['raw_trace_bytes']
    archive_path = ACTUAL / 'diagnostic.zip'
    assert archive_path.stat().st_size == auth['artifact_bytes']
    assert sha_file(archive_path) == auth['artifact_sha256']
    with zipfile.ZipFile(archive_path) as archive:
        plan_raw = archive.read(PREFIX + 'projected_plan.json')
    assert hashlib.sha256(plan_raw).hexdigest() == PLAN_SHA
    modules = selected_modules(decode(plan_raw))
    path_to_module = {row['exact_native_olean_path']: name for name, row in modules.items()}
    helper_path = HERE / 'mmap_trace_candidate/patch/ci/rg_bothlong_mmap_trace_20261104.py'
    assert sha_file(helper_path) == HELPER_SHA
    parser = runpy.run_path(str(helper_path))  # definitions only; never helper main
    output = ACTUAL / ('mmap_full_analysis_' + authentication_sha256[:16])
    output.mkdir(exist_ok=False)
    calls_path = output / 'complete_memory_syscalls.jsonl'
    residual_path = output / 'unpaired_or_unparsed_trace_lines.jsonl'
    paths_path = output / 'exact_file_path_counts.jsonl'
    coverage_path = output / 'selected_original_module_observations.jsonl'
    all_mmaps, selected_mmaps, olean_mmaps = fresh_counts(), fresh_counts(), fresh_counts()
    path_counts, covered_lines = {}, set()
    complete_calls, fixed_flags = collections.Counter(), collections.Counter()
    successful_olean_paths, observed_modules = set(), set()
    file_mmaps = unannotated_file_mmaps = 0
    with calls_path.open('x') as out:
        def observe(call):
            nonlocal file_mmaps, unannotated_file_mmaps
            complete_calls[call['syscall']] += 1
            covered_lines.update((call['first_line'], call['last_line']))
            row = dict(call)
            row['exact_selected_original_module'] = None
            row['exact_olean_file_path'] = False
            if call['syscall'] == 'mmap':
                add_call(all_mmaps, call)
                for flag in ('MAP_FIXED', 'MAP_FIXED_NOREPLACE'):
                    if flag in call['mapping_flags'].split('|'):
                        fixed_flags[flag] += 1
                is_file = call['file_descriptor'] is not None and call['file_descriptor'] >= 0 and \
                    'MAP_ANONYMOUS' not in call['mapping_flags']
                if is_file:
                    file_mmaps += 1
                    path = call['file_path']
                    if path is None:
                        unannotated_file_mmaps += 1
                    else:
                        add_call(path_counts.setdefault(path, fresh_counts()), call)
                        is_olean = path.endswith('.olean')
                        row['exact_olean_file_path'] = is_olean
                        if is_olean:
                            add_call(olean_mmaps, call)
                            if call['outcome'] == 'SUCCESS':
                                successful_olean_paths.add(path)
                        module = path_to_module.get(path)
                        row['exact_selected_original_module'] = module
                        if module is not None:
                            observed_modules.add(module)
                            add_call(selected_mmaps, call)
            emit(out, row)
        summary = parser['_read_trace'](trace, observe)
    assert summary['trace_path'] == str(trace)
    summary['trace_path'] = str(NATIVE_BUILD / (PROBE + '.mmap.log'))
    assert summary == invocation['trace_summary']
    assert summary['trace_sha256'] == invocation['raw_trace_sha256']
    assert sum(complete_calls.values()) == summary['counts']['complete_calls']
    assert all_mmaps['attempts'] == summary['counts']['mmap_total']
    assert all_mmaps['failed'] == summary['counts']['mmap_errors']
    assert file_mmaps == summary['counts']['mmap_file']
    residual = residual_lines(trace, covered_lines, residual_path)
    with paths_path.open('x') as out:
        for path in sorted(path_counts):
            emit(out, dict(exact_native_file_path=path, exact_olean_suffix=path.endswith('.olean'),
                           selected_original_module=path_to_module.get(path),
                           observed_mmap=path_counts[path]))
    with coverage_path.open('x') as out:
        for name in sorted(modules):
            item = modules[name]
            observed = path_counts.get(item['exact_native_olean_path'])
            emit(out, dict(**item,
                observation='COMPLETE_MAPPING_ATTEMPT_OBSERVED' if observed else
                            'NO_COMPLETE_MAPPING_ATTEMPT_FOR_THIS_EXACT_PATH_OBSERVED_IN_THIS_TRACE',
                observed_mmap=observed,
                absence_of_observation_does_not_show_missing_import=True,
                original_object_bytes_not_read_by_this_analysis=True))
    selected_successes = sum(path_counts[modules[n]['exact_native_olean_path']]['successful'] > 0
                             for n in observed_modules)
    result = dict(status='COMPLETE_AUTHENTICATED_RAW_TRACE_OBSERVATIONS_EXPORTED',
        run=RUN, job=JOB, source_commit=COMMIT, authentication_report_sha256=authentication_sha256,
        artifact_sha256=auth['artifact_sha256'], parser_helper_sha256=HELPER_SHA,
        raw_trace=file_identity(trace), raw_trace_retained=True,
        first_timestamped_trace_line=residual['first_timestamped_trace_line'],
        last_timestamped_trace_line=residual['last_timestamped_trace_line'],
        timestamp_interpretation='Printed Unix timestamps by raw line order, not syscall-end measurements and not the monotonic Lean-marker clock.',
        all_complete_memory_syscalls=dict(sorted(complete_calls.items())), all_mmap_observations=all_mmaps,
        exact_olean_path_observations=olean_mmaps,
        complete_file_mapping_attempts=file_mmaps, complete_file_attempts_without_path_annotation=unannotated_file_mmaps,
        distinct_exact_olean_paths=sum(p.endswith('.olean') for p in path_counts),
        distinct_exact_olean_paths_with_successful_mmap=len(successful_olean_paths),
        observed_fixed_flag_counts=dict(sorted(fixed_flags.items())),
        explicit_errno_counts=dict(EEXIST=all_mmaps['errno_counts'].get('EEXIST', 0),
                                   ENOMEM=all_mmaps['errno_counts'].get('ENOMEM', 0)),
        selected_original_modules=dict(projected_plan_sha256=PLAN_SHA, total=25191,
            with_complete_exact_path_mapping_attempt=len(observed_modules),
            without_complete_exact_path_mapping_attempt=25191-len(observed_modules),
            with_at_least_one_successful_mmap=selected_successes,
            without_successful_mmap_observation=25191-selected_successes,
            original_restored_logical_bytes=97433499160, observed_mmap=selected_mmaps),
        pinned_parser_counts=summary['counts'], residual_raw_lines=residual,
        full_raw_call_export_uses_streamed_callback_not_last32=True,
        complete_call_export_order='Parser completion order; each row retains first/last raw line numbers.',
        unparsed_and_unresolved_counts_do_not_authorize_trace_success=True,
        main_pid_not_inferred_from_first_trace_line=True,
        first_observed_trace_pid=summary['first_observed_pid'],
        independently_authenticated_probe_identity=auth['observed_probe_lean_identity'],
        interpretation_limits=[
            'Every complete mmap, munmap and mremap call is exported; unresolved or unparsed lines are retained separately in full, and the original raw trace remains the reference.',
            'An absent exact-path mmap observation is not evidence of a missing import: unresolved calls, alternate native path spelling, inherited mappings or non-mmap reads are not ruled out.',
            'Requested-length sums count repeated attempts, including failures. They are not distinct file bytes, resident memory, read_bytes or successful import totals.',
            'A returned address unequal to a nonzero request is recorded separately from the ordinary null/zero-address request case; no collision or allocation failure is inferred from inequality.',
            'EEXIST and ENOMEM are the errno strings actually printed for complete calls. Their occurrence alone does not prove the cause of a timeout.',
            'The final observed mapping does not identify the cause of a subsequent stall, an unobserved import, or a performance improvement.',
            'Tracing adds overhead; native trace-line timestamps, syscall durations and Lean markers remain separate observations.'],
        outputs={name: file_identity(path) for name, path in (
            ('all_complete_calls', calls_path), ('residual_raw_lines', residual_path),
            ('all_exact_file_paths', paths_path), ('all_selected_modules', coverage_path))},
        subprocesses_started=0, github_environment_spoofed=False, native_paths_used_as_local_files=False,
        original_kernel_export_claim=False, family_closure_claim=False)
    (output / 'analysis.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    return output / 'analysis.json'


def main():
    if not __debug__:
        raise RuntimeError('Analysis must not disable evidence assertions')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--authentication-sha256', required=True)
    args = parser.parse_args()
    result = analyze(args.authentication_sha256)
    print(json.dumps(file_identity(result), sort_keys=True))


if __name__ == '__main__':
    main()
