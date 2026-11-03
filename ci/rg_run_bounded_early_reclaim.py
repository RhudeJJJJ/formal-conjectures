"""Run only two sealed original reconstructions in bounded early-reclaim scopes.

The strict verifier, Lean flags, original source/object identities, 1200-second
module timeout (600 for Fast40) and 2048 MiB physical/cgroup reserve remain unchanged. Privilege
is used only for one owned swapfile and one ephemeral systemd scope; the actual
observer, Python verifier and Lean run with the original runner UID/GID.
"""
import argparse
import hashlib
import json
import os
import pathlib
import re
import shutil
import signal
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'Proofs/RG_Lean_20261019/build/fresh_exports'
STATE = OUTPUT / 'early_reclaim_state.json'
TELEMETRY = OUTPUT / 'early_reclaim_cgroup.json'
CONFIG = {
    'ge46': {'spec': 'rg_original_degree_ge46_purge_20261103_spec.json',
             'endpoint': 'Proofs.RadenkovicGutmanOriginalDegreeGeFortysix',
             'fresh': 62, 'partial': 5, 'required': 124, 'timeout': 1200},
    'fast40': {'spec': 'rg_d1_fast40_purge_20261103_spec.json',
               'endpoint': 'Proofs.RadenkovicGutmanD1FastFullBox40',
               'fresh': 7, 'partial': 4, 'required': 84, 'timeout': 600},
}
FAMILY = None
SPEC = None
GIB = 1024 ** 3
HIGH, MAXIMUM, SWAP_MAXIMUM, NEW_SWAP = 11 * GIB, 14 * GIB, 7 * GIB, 4 * GIB
ALLOCATOR = {'MIMALLOC_PURGE_DELAY': '0', 'MIMALLOC_PURGE_EXTEND_DELAY': '0',
             'MIMALLOC_ARENA_PURGE_MULT': '1', 'MIMALLOC_PURGE_DECOMMITS': '1',
             'MIMALLOC_ALLOW_LARGE_OS_PAGES': '0'}
ENVIRONMENT = ('PATH', 'HOME', 'ELAN_HOME', 'LANG', 'LC_ALL', 'TMPDIR', 'USER',
               'LOGNAME', 'GITHUB_WORKSPACE', 'LC_CTYPE', *ALLOCATOR)


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    pending = path.with_suffix(path.suffix + '.pending')
    pending.write_text(json.dumps(value, indent=2) + '\n')
    pending.replace(path)


def memory():
    result = {}
    for line in pathlib.Path('/proc/meminfo').read_text().splitlines():
        fields = line.split()
        if fields[0][:-1] in ('MemTotal', 'MemAvailable', 'SwapTotal', 'SwapFree'):
            result[fields[0][:-1]] = int(fields[1]) * 1024
    return result


def verify_spec():
    raw = SPEC.read_bytes()
    spec = json.loads(raw)
    expected = CONFIG[FAMILY]
    assert spec['endpoint'] == expected['endpoint']
    assert spec['fresh_module_count'] == len(spec['modules']) == expected['fresh']
    assert spec['partial_module_count'] == expected['partial']
    assert spec['required_module_count'] == expected['required']
    assert spec['module_timeout'] == expected['timeout'] and spec['workers'] == 1
    assert spec['memory_reserve_mib'] == 2048 and spec['allocator_environment'] == ALLOCATOR
    assert all(os.environ.get(k) == v for k, v in ALLOCATOR.items())
    return hashlib.sha256(raw).hexdigest()


def command(argv, *, check=True):
    return subprocess.run(argv, check=check, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, timeout=30)


def state_for_cleanup():
    state = json.loads(STATE.read_bytes())
    assert state['kind'] == 'OWNED_SOURCE_BOUND_EARLY_RECLAIM_SCOPE'
    assert state['family'] == FAMILY
    run, attempt, owner = state['run'], state['attempt'], state['controller_pid']
    assert all(isinstance(v, int) and v > 0 for v in (run, attempt, owner))
    assert state['uid'] == os.getuid() > 0 and state['gid'] == os.getgid() > 0
    assert run == int(os.environ['GITHUB_RUN_ID']) and attempt == int(os.environ['GITHUB_RUN_ATTEMPT'])
    assert state['unit'] == f'rg-{FAMILY}-reclaim-{run}-{attempt}-{owner}.scope'
    parent = pathlib.Path(os.environ['RUNNER_TEMP']).resolve()
    path = parent / f'rg-{FAMILY}-reclaim-{run}-{attempt}-{owner}.swap'
    assert state['swapfile'] == str(path) and path.parent == parent
    return state, path


def cleanup():
    if not STATE.exists():
        return
    state, path = state_for_cleanup()
    if state.get('cleanup_complete'):
        return
    # The scope name contains this run, attempt and original controller PID.
    # This never signals a process or unit outside that owned scope.
    if state.get('scope_started'):
        for action in (['kill', '--kill-who=all', '--signal=SIGKILL', state['unit']],
                       ['stop', state['unit']]):
            result = command(['sudo', '-n', '/usr/bin/systemctl', *action], check=False)
            state.setdefault('scope_cleanup', []).append({'action': action[0], 'returncode': result.returncode})
        current = command(['sudo', '-n', '/usr/bin/systemctl', 'show', '--property=ActiveState', '--value', state['unit']], check=False)
        assert current.returncode != 0 or current.stdout.strip() in ('inactive', 'failed', ''), 'Owned scope still active; leave swap intact'
    if state.get('swap_created'):
        assert path.is_file() and not path.is_symlink()
        info = path.stat()
        assert (info.st_dev, info.st_ino) == (state['swap_device'], state['swap_inode'])
        assert info.st_uid in (state['uid'], 0)
        active = {line.split()[0] for line in pathlib.Path('/proc/swaps').read_text().splitlines()[1:]}
        if str(path) in active:
            command(['sudo', '-n', '/sbin/swapoff', '--', str(path)])
        active = {line.split()[0] for line in pathlib.Path('/proc/swaps').read_text().splitlines()[1:]}
        assert str(path) not in active, 'Owned swapfile is still active'
        path.unlink()
    state['cleanup_complete'] = True
    state['memory_after_cleanup'] = memory()
    save(STATE, state)
    print(json.dumps({'status': 'OWNED_ORIGINAL_SCOPE_AND_SWAP_CLEANED', 'unit': state['unit']}), flush=True)


def cgroup_snapshot(folder):
    result = {'monotonic_seconds': round(time.monotonic(), 3), 'host_memory': memory()}
    for key in ('memory.high', 'memory.max', 'memory.current', 'memory.peak',
                'memory.swap.max', 'memory.swap.current', 'memory.swap.peak'):
        path = folder / key
        if path.exists():
            value = path.read_text().strip()
            result[key] = int(value) if value != 'max' else value
    for key in ('memory.events', 'memory.events.local', 'memory.stat'):
        path = folder / key
        if path.exists():
            result[key] = {fields[0]: int(fields[1]) for fields in (line.split() for line in path.read_text().splitlines())}
    assert result['memory.high'] == HIGH and result['memory.max'] == MAXIMUM
    assert result['memory.swap.max'] == SWAP_MAXIMUM
    return result


def worker():
    state = json.loads(STATE.read_bytes())
    assert state['family'] == FAMILY
    assert os.getuid() == state['uid'] > 0 and os.getgid() == state['gid'] > 0
    assert state['spec_sha256'] == verify_spec()
    assert set(os.environ) <= set(ENVIRONMENT), 'Unexpected environment in kernel scope'
    relative = next(line.split(':', 2)[2] for line in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
    folder = (pathlib.Path('/sys/fs/cgroup') / relative.lstrip('/')).resolve()
    assert folder.is_relative_to('/sys/fs/cgroup') and folder.name == state['unit']
    first = cgroup_snapshot(folder)
    assert first['host_memory']['MemAvailable'] >= 2048 * 1024 ** 2
    assert MAXIMUM - first['memory.current'] >= 2048 * 1024 ** 2
    report = {'kind': 'VALIDATED_ORIGINAL_EARLY_RECLAIM_CGROUP', 'unit': state['unit'],
              'uid': os.getuid(), 'gid': os.getgid(), 'spec_sha256': state['spec_sha256'],
              'environment_keys': sorted(os.environ), 'limits': {'memory.high': HIGH,
              'memory.max': MAXIMUM, 'memory.swap.max': SWAP_MAXIMUM},
              'physical_and_cgroup_reserve_mib': 2048, 'kernel_flags_unchanged': True,
              'initial': first, 'samples': []}
    save(TELEMETRY, report)
    print(json.dumps({'status': 'VALIDATED_OWNED_ORIGINAL_CGROUP_BEFORE_KERNEL',
                      'unit': state['unit'], 'uid': os.getuid(), 'gid': os.getgid(),
                      'memory.high': HIGH, 'memory.max': MAXIMUM, 'memory.swap.max': SWAP_MAXIMUM}), flush=True)
    argv = [sys.executable, '-B', str(ROOT / 'ci/rg_observed_kernel_verify.py'),
            '--memory-reserve-mib', '2048', '--', '--mathlib-project', str(ROOT),
            '--endpoint', CONFIG[FAMILY]['endpoint'],
            '--workers', '1', '--module-timeout', str(CONFIG[FAMILY]['timeout']), '--resume']
    proc = subprocess.Popen(argv, cwd=ROOT)
    interrupted = None
    def stop(signum, _frame):
        nonlocal interrupted
        interrupted = signum
        if proc.poll() is None:
            proc.send_signal(signal.SIGTERM)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    try:
        while proc.poll() is None:
            report['samples'].append(cgroup_snapshot(folder))
            save(TELEMETRY, report)
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                if interrupted:
                    break
        code = proc.wait(timeout=30)
    except BaseException:
        if proc.poll() is None:
            proc.terminate()
        raise
    finally:
        report['final'] = cgroup_snapshot(folder)
        report['observer_exit_code'] = proc.poll()
        report['interrupted_signal'] = interrupted
        save(TELEMETRY, report)
    raise SystemExit(code if code >= 0 else 128 - code)


def controller():
    assert os.environ.get('GITHUB_ACTIONS') == 'true'
    assert os.environ.get('RUNNER_ENVIRONMENT') == 'github-hosted'
    assert pathlib.Path(os.environ['GITHUB_WORKSPACE']).resolve() == ROOT
    assert os.getuid() > 0 and os.getgid() > 0
    assert not STATE.exists(), 'Do not reuse a previous owned-resource state'
    run, attempt = int(os.environ['GITHUB_RUN_ID']), int(os.environ['GITHUB_RUN_ATTEMPT'])
    assert run > 0 and attempt > 0
    before = memory()
    assert 0 < before['SwapTotal'] <= 3 * GIB
    assert before['SwapFree'] + NEW_SWAP <= SWAP_MAXIMUM
    parent = pathlib.Path(os.environ['RUNNER_TEMP']).resolve()
    assert parent.is_dir() and shutil.disk_usage(parent).free >= NEW_SWAP + 10 * GIB
    unit = f'rg-{FAMILY}-reclaim-{run}-{attempt}-{os.getpid()}.scope'
    swapfile = parent / f'rg-{FAMILY}-reclaim-{run}-{attempt}-{os.getpid()}.swap'
    state = {'kind': 'OWNED_SOURCE_BOUND_EARLY_RECLAIM_SCOPE', 'run': run, 'attempt': attempt,
             'family': FAMILY, 'controller_pid': os.getpid(), 'uid': os.getuid(), 'gid': os.getgid(),
             'unit': unit, 'swapfile': str(swapfile), 'new_swap_file_bytes': NEW_SWAP,
             'memory_before_setup': before, 'spec_sha256': verify_spec(),
             'swap_created': False, 'scope_started': False, 'cleanup_complete': False}
    save(STATE, state)
    proc = None
    def stop(signum, _frame):
        raise SystemExit(128 + signum)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    try:
        fd = os.open(swapfile, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        info = os.fstat(fd)
        os.close(fd)
        state.update(swap_created=True, swap_device=info.st_dev, swap_inode=info.st_ino)
        save(STATE, state)
        command(['/usr/bin/fallocate', '-l', str(NEW_SWAP), str(swapfile)])
        assert swapfile.stat().st_size == NEW_SWAP
        command(['sudo', '-n', '/usr/bin/chown', '0:0', '--', str(swapfile)])
        assert swapfile.stat().st_uid == 0 and swapfile.stat().st_mode & 0o777 == 0o600
        command(['sudo', '-n', '/sbin/mkswap', '--', str(swapfile)])
        command(['sudo', '-n', '/sbin/swapon', '--', str(swapfile)])
        after = memory()
        assert NEW_SWAP - 1024 ** 2 <= after['SwapTotal'] - before['SwapTotal'] <= NEW_SWAP
        assert after['SwapTotal'] <= SWAP_MAXIMUM
        assert shutil.disk_usage(parent).free >= 10 * GIB
        state['memory_after_swap_setup'] = after
        state['scope_started'] = True
        save(STATE, state)
        environment = {key: os.environ[key] for key in ENVIRONMENT if key in os.environ}
        assert all(key in environment for key in ('PATH', 'HOME', 'GITHUB_WORKSPACE'))
        argv = ['sudo', '-n', '/usr/bin/systemd-run', '--scope', '--quiet', '--unit=' + unit,
                '--property=MemoryHigh=' + str(HIGH), '--property=MemoryMax=' + str(MAXIMUM),
                '--property=MemorySwapMax=' + str(SWAP_MAXIMUM),
                '/usr/bin/setpriv', '--reuid=' + str(state['uid']), '--regid=' + str(state['gid']),
                '--init-groups', '--no-new-privs', '/usr/bin/env', '-i',
                *(key + '=' + value for key, value in sorted(environment.items())),
                sys.executable, '-B', str(pathlib.Path(__file__).resolve()), '--family', FAMILY, '--inside-scope']
        proc = subprocess.Popen(argv, cwd=ROOT)
        code = proc.wait()
        state = json.loads(STATE.read_bytes())
        state['scope_command_exit_code'] = code
        save(STATE, state)
    finally:
        cleanup()
        if proc is not None and proc.poll() is None:
            proc.wait(timeout=30)
    raise SystemExit(code if code >= 0 else 128 - code)


def main():
    global FAMILY, SPEC
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--family', choices=tuple(CONFIG), required=True)
    choice = p.add_mutually_exclusive_group()
    choice.add_argument('--inside-scope', action='store_true')
    choice.add_argument('--cleanup', action='store_true')
    args = p.parse_args()
    FAMILY = args.family
    SPEC = ROOT / 'ci' / CONFIG[FAMILY]['spec']
    if args.inside_scope:
        worker()
    elif args.cleanup:
        cleanup()
    else:
        controller()


if __name__ == '__main__':
    main()
