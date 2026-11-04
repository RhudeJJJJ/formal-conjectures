"""Read Linux resource observations for already identified owned processes.

These diagnostics never set a resource limit, change swap policy, signal a
process, or decide whether a proof passed. Failed and unmapped reads stay
explicit; an empty observation is never reported as absence of a limit.
"""
import os
import pathlib
import re
import time

CGROUP_FILES = ('memory.max', 'memory.high', 'memory.current', 'memory.swap.max',
    'memory.swap.current', 'memory.events', 'memory.events.local', 'memory.stat',
    'memory.pressure', 'cpu.max', 'cpu.stat', 'io.stat')
MEMORY_FIELDS = ('VmSize', 'VmRSS', 'RssAnon', 'RssFile', 'RssShmem', 'VmSwap')
LIMIT_FIELDS = ('Max address space', 'Max data size', 'Max stack size')


def read_text(path, maximum=262144):
    try:
        with path.open('r', encoding='utf-8', errors='replace') as stream:
            value = stream.read(maximum + 1)
        if len(value) > maximum:
            return dict(status='READ_TOO_LARGE', path=str(path), character_limit=maximum)
        return dict(status='READ', path=str(path), text=value)
    except OSError as error:
        return dict(status='READ_ERROR', path=str(path), error_type=type(error).__name__,
                    errno=error.errno)


def proc_stat(pid):
    record = read_text(pathlib.Path('/proc') / str(pid) / 'stat')
    if record['status'] != 'READ':
        return record
    try:
        raw = record.pop('text')
        end = raw.rfind(')')
        assert end >= 0 and int(raw.split('(', 1)[0]) == pid
        fields = raw[end + 2:].split()
        values = dict(state=fields[0], parent_pid=int(fields[1]), process_group=int(fields[2]),
            minor_faults=int(fields[7]), major_faults=int(fields[9]),
            cpu_user_ticks=int(fields[11]), cpu_system_ticks=int(fields[12]),
            threads=int(fields[17]), start_time_ticks=int(fields[19]))
        record['values'] = values
        return record
    except (AssertionError, ValueError, IndexError) as error:
        return dict(status='PARSE_ERROR', path=record['path'], error_type=type(error).__name__)


def proc_status(pid):
    record = read_text(pathlib.Path('/proc') / str(pid) / 'status')
    if record['status'] != 'READ':
        return record
    values = {}
    for line in record.pop('text').splitlines():
        key, separator, value = line.partition(':')
        if not separator or key not in MEMORY_FIELDS:
            continue
        fields = value.split()
        if len(fields) == 2 and fields[0].isdigit() and fields[1] == 'kB':
            values[key] = int(fields[0]) * 1024
        else:
            values[key] = dict(status='UNRECOGNIZED_VALUE', text=value.strip())
    record['bytes'] = values
    record['missing_fields'] = [key for key in MEMORY_FIELDS if key not in values]
    return record


def proc_io(pid):
    record = read_text(pathlib.Path('/proc') / str(pid) / 'io')
    if record['status'] != 'READ':
        return record
    values = {}
    for line in record.pop('text').splitlines():
        key, separator, value = line.partition(':')
        if separator:
            values[key] = int(value) if value.strip().isdigit() else value.strip()
    record['counters'] = values
    return record


def proc_limits(pid):
    record = read_text(pathlib.Path('/proc') / str(pid) / 'limits')
    if record['status'] != 'READ':
        return record
    values = {}
    for line in record.pop('text').splitlines():
        match = re.fullmatch(r'(Max (?:address space|data size|stack size))\s+(\S+)\s+(\S+)\s+(\S+)\s*', line)
        if match:
            values[match[1]] = dict(soft=match[2], hard=match[3], units=match[4])
    record['limits'] = values
    record['missing_fields'] = [key for key in LIMIT_FIELDS if key not in values]
    return record


def kernel_path(value):
    return re.sub(r'\\([0-7]{3})', lambda match: chr(int(match[1], 8)), value)


def cgroup_mounts():
    record = read_text(pathlib.Path('/proc/self/mountinfo'))
    if record['status'] != 'READ':
        return record
    mounts, errors = [], []
    for line in record.pop('text').splitlines():
        left, separator, right = line.partition(' - ')
        if not separator or not right.startswith('cgroup2 '):
            continue
        fields = left.split()
        if len(fields) < 5:
            errors.append('CGROUP2_MOUNTINFO_FIELDS_MISSING')
            continue
        mounts.append(dict(root=kernel_path(fields[3]), mount_point=kernel_path(fields[4])))
    record['mounts'] = mounts
    record['parse_errors'] = errors
    return record


def cgroup_file(path):
    record = read_text(path)
    if record['status'] == 'READ':
        value = record.pop('text').strip()
        if value.isdigit():
            record['value'] = int(value)
        elif value == 'max':
            record['value'] = 'max'
        else:
            record['text'] = value
    return record


def cgroups(pid, mounts):
    record = read_text(pathlib.Path('/proc') / str(pid) / 'cgroup')
    if record['status'] != 'READ':
        return record
    lines = record.pop('text').splitlines()
    record['membership_lines'] = lines
    unified = [line.split(':', 2)[2] for line in lines if line.startswith('0::')]
    record['v2_paths'] = unified
    record['mount_read_status'] = mounts['status']
    record['snapshots'] = []
    if len(unified) != 1 or mounts['status'] != 'READ' or not mounts['mounts']:
        record['mapping_status'] = 'UNIFIED_CGROUP_MAPPING_UNAVAILABLE'
        return record
    relative = pathlib.PurePosixPath(unified[0])
    safe_relative = relative.is_absolute() and '..' not in relative.parts
    record['mapping_status'] = 'CANDIDATES_RECORDED' if safe_relative else 'UNMAPPED_PARENT_COMPONENT_OR_NONABSOLUTE_PATH'
    for mount in mounts['mounts']:
        point, mount_root = pathlib.Path(mount['mount_point']), pathlib.PurePosixPath(mount['root'])
        if not point.is_absolute() or '..' in point.parts:
            continue
        candidates = {}
        if safe_relative:
            if relative.is_relative_to(mount_root):
                leaf = point / relative.relative_to(mount_root)
                candidates.setdefault(str(leaf), []).append('HIERARCHY_RELATIVE_CANDIDATE')
            leaf = point / str(relative).lstrip('/')
            candidates.setdefault(str(leaf), []).append('NAMESPACE_RELATIVE_CANDIDATE')
        else:
            # This visible mount-root snapshot is explicitly not attributed to
            # the process when membership cannot be mapped safely.
            candidates[str(point)] = ['VISIBLE_MOUNT_ROOT_ONLY_PROCESS_MAPPING_UNRESOLVED']
        for value, reasons in candidates.items():
            leaf = pathlib.Path(value)
            assert leaf.is_relative_to(point)
            ancestors, current = [], leaf
            for _ in range(32):
                ancestors.append(dict(path=str(current),
                    files={name: cgroup_file(current / name) for name in CGROUP_FILES}))
                if current == point:
                    break
                current = current.parent
            record['snapshots'].append(dict(mount=mount, candidate_leaf=str(leaf),
                mapping_labels=reasons, ancestors=ancestors,
                reached_visible_mount_root=ancestors[-1]['path'] == str(point)))
    return record


def process_snapshot(pid, mounts):
    assert type(pid) is int and pid > 0
    before = proc_stat(pid)
    result = dict(pid=pid, stat_before=before, status=proc_status(pid), io=proc_io(pid),
                  limits=proc_limits(pid), cgroup=cgroups(pid, mounts))
    after = proc_stat(pid)
    result['stat_after'] = after
    if before['status'] == after['status'] == 'READ':
        result['same_process_identity_across_reads'] = before['values']['start_time_ticks'] == after['values']['start_time_ticks']
    else:
        result['same_process_identity_across_reads'] = 'NOT_ESTABLISHED'
    return result


def snapshot(worker_pid, lean_processes):
    began = time.monotonic()
    mounts = cgroup_mounts()
    result = dict(status='READ_ONLY_OWNED_PROCESS_SNAPSHOT',
        clock_ticks_per_second=os.sysconf('SC_CLK_TCK'), cgroup_mountinfo=mounts,
        worker=process_snapshot(worker_pid, mounts), lean_processes=[])
    for row in lean_processes:
        result['lean_processes'].append(dict(module=row['module'],
            process=process_snapshot(row['pid'], mounts)))
    result['collection_seconds'] = round(time.monotonic() - began, 6)
    result['resource_limits_or_swap_policy_modified'] = False
    return result
