"""Observe only the fixed control/probe worker, retaining the original guard.

The descendant scan, memory threshold, owned-process-group signals and exit
handling are copied from the pinned original resource observer. Extra /proc
reads are diagnostic only and cannot authorize a kernel success.
"""
import argparse
import json
import os
import pathlib
import signal
import subprocess
import sys
import time
from rg_proc_resource_snapshot_20261104 import snapshot

R = pathlib.Path(__file__).resolve().parents[1]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--phase', choices=('control', 'probe'), required=True)
    ap.add_argument('--memory-reserve-mib', type=int, default=2048)
    a = ap.parse_args()
    assert a.memory_reserve_mib == 2048
    controller = R / 'ci/rg_bothlong_phase_probe_20261104.py'
    assert controller.is_file()
    command = [sys.executable, '-B', str(controller), '--phase', a.phase + '-worker']
    began = time.monotonic()
    samples, maximum_rss, guard, interrupted = [], 0, False, None
    proc = subprocess.Popen(command, cwd=R, start_new_session=True)

    def descendants(pid):
        result = set()
        todo = [pid]
        while todo:
            parent = todo.pop()
            for task in pathlib.Path(f'/proc/{parent}/task').glob('*/children'):
                try:
                    children = list(map(int, task.read_text().split()))
                except (OSError, ValueError):
                    continue
                for child in children:
                    if child not in result:
                        result.add(child)
                        todo.append(child)
        return result

    def observe():
        values = {}
        for line in pathlib.Path('/proc/meminfo').read_text().splitlines():
            fields = line.split()
            if fields[0].rstrip(':') in ['MemTotal', 'MemAvailable', 'SwapFree']:
                values[fields[0].rstrip(':')] = int(fields[1]) * 1024
        available = values.get('MemAvailable')
        cgroups = []
        try:
            rel = next(x.split(':', 2)[2] for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
            folder = pathlib.Path('/sys/fs/cgroup') / rel.lstrip('/')
            while folder.is_relative_to('/sys/fs/cgroup'):
                try:
                    limit = (folder / 'memory.max').read_text().strip()
                    current = int((folder / 'memory.current').read_text())
                    if limit != 'max':
                        remaining = int(limit) - current
                        available = remaining if available is None else min(available, remaining)
                        cgroups.append(dict(limit=int(limit), current=current))
                except (OSError, ValueError):
                    pass
                if folder == pathlib.Path('/sys/fs/cgroup'):
                    break
                folder = folder.parent
        except (OSError, StopIteration):
            pass
        lean = []
        for pid in descendants(proc.pid):
            try:
                cmd = pathlib.Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\0')
                if not cmd or pathlib.Path(os.fsdecode(cmd[0])).name != 'lean':
                    continue
                status = pathlib.Path(f'/proc/{pid}/status').read_text().splitlines()
                rss = next(int(x.split()[1]) * 1024 for x in status if x.startswith('VmRSS:'))
                module = next((pathlib.Path(os.fsdecode(x)).name for x in reversed(cmd) if x.endswith(b'.lean')), None)
                lean.append(dict(pid=pid, rss=rss, module=module))
            except (OSError, ValueError, StopIteration):
                pass
        return dict(seconds=round(time.monotonic() - began, 2), memory=values,
            cgroup_limits=cgroups, available_bytes=available, lean_processes=lean,
            aggregate_lean_rss=sum(x['rss'] for x in lean))

    def stop(signum=None, frame=None):
        nonlocal interrupted
        interrupted = signum
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass

    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    last_log = -30
    while proc.poll() is None:
        sample = observe()
        maximum_rss = max(maximum_rss, sample['aggregate_lean_rss'])
        if sample['seconds'] - last_log >= 10:
            # Never delay an already observed low-memory stop for diagnostics.
            if sample['lean_processes'] and sample['available_bytes'] is not None and sample['available_bytes'] < a.memory_reserve_mib * 1024**2:
                sample['process_diagnostics'] = dict(status='SKIPPED_AT_MEMORY_GUARD')
            else:
                try:
                    sample['process_diagnostics'] = snapshot(proc.pid, sample['lean_processes'])
                except Exception as error:
                    sample['process_diagnostics'] = dict(status='DIAGNOSTIC_READ_ERROR', error_type=type(error).__name__)
            print('RG_KERNEL_RESOURCE_OBSERVATION ' + json.dumps(sample, separators=(',', ':')), file=sys.stderr, flush=True)
            samples.append(sample)
            last_log = sample['seconds']
        if sample['lean_processes'] and sample['available_bytes'] is not None and sample['available_bytes'] < a.memory_reserve_mib * 1024**2:
            guard = True
            print('RG_KERNEL_RESOURCE_GUARD_LOW_MEMORY ' + json.dumps(sample), file=sys.stderr, flush=True)
            stop()
            break
        time.sleep(1)
    try:
        code = proc.wait(timeout=30)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        code = proc.wait()
    result = dict(status='MEMORY_GUARD_STOPPED_OWN_VERIFIER' if guard else 'INTERRUPTED' if interrupted else 'VERIFIER_COMPLETED',
        exit_code=code, maximum_aggregate_lean_rss=maximum_rss,
        seconds=round(time.monotonic() - began, 2), samples=samples,
        mathlib_and_lean_flags_unchanged=True, phase=a.phase,
        scope='FIXED_BOTHLONG_PHASE_WORKER_ONLY', resource_reserve_mib=2048,
        observer_created_kernel_receipt=False, additional_proc_fields_are_diagnostic_only=True)
    dest = R / 'Proofs/RG_Lean_20261019/build/bothlong_phase_probe' / (a.phase + '_resource_observer.json')
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(result, indent=2) + '\n')
    print('RG_KERNEL_RESOURCE_RESULT ' + json.dumps({k: v for k, v in result.items() if k != 'samples'}), file=sys.stderr, flush=True)
    raise SystemExit(86 if guard else 128 + interrupted if interrupted else code if code >= 0 else 128 - code)


if __name__ == '__main__':
    main()
