"""Observe only this verification process; retain kernel rules and bounded memory."""
import argparse,json,os,pathlib,signal,subprocess,sys,time
R=pathlib.Path(__file__).resolve().parent.parent
ap=argparse.ArgumentParser();ap.add_argument('--memory-reserve-mib',type=int,default=2048);ap.add_argument('arguments',nargs=argparse.REMAINDER);a=ap.parse_args()
assert 512<=a.memory_reserve_mib<=4096
args=a.arguments[1:] if a.arguments[:1]==['--'] else a.arguments
assert '--endpoint' in args and '--workers' in args
command=[sys.executable,'-B',str(R/'Proofs/RG_Lean_20261019/verify_extension.py'),*args]
began=time.monotonic();samples=[];maximum_rss=0;guard=False;interrupted=None
proc=subprocess.Popen(command,cwd=R,start_new_session=True)
def descendants(pid):
    result=set();todo=[pid]
    while todo:
        parent=todo.pop()
        for task in pathlib.Path(f'/proc/{parent}/task').glob('*/children'):
            try:children=list(map(int,task.read_text().split()))
            except (OSError,ValueError):continue
            for child in children:
                if child not in result:result.add(child);todo.append(child)
    return result
def observe():
    values={}
    for line in pathlib.Path('/proc/meminfo').read_text().splitlines():
        fields=line.split()
        if fields[0].rstrip(':') in ['MemTotal','MemAvailable','SwapFree']:values[fields[0].rstrip(':')]=int(fields[1])*1024
    available=values.get('MemAvailable');cgroups=[]
    try:
        rel=next(x.split(':',2)[2] for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
        folder=pathlib.Path('/sys/fs/cgroup')/rel.lstrip('/')
        while folder.is_relative_to('/sys/fs/cgroup'):
            try:
                limit=(folder/'memory.max').read_text().strip();current=int((folder/'memory.current').read_text())
                if limit!='max':
                    remaining=int(limit)-current;available=remaining if available is None else min(available,remaining);cgroups.append(dict(limit=int(limit),current=current))
            except (OSError,ValueError):pass
            if folder==pathlib.Path('/sys/fs/cgroup'):break
            folder=folder.parent
    except (OSError,StopIteration):pass
    lean=[]
    for pid in descendants(proc.pid):
        try:
            cmd=pathlib.Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\0')
            if not cmd or pathlib.Path(os.fsdecode(cmd[0])).name!='lean':continue
            status=pathlib.Path(f'/proc/{pid}/status').read_text().splitlines();rss=next(int(x.split()[1])*1024 for x in status if x.startswith('VmRSS:'))
            module=next((pathlib.Path(os.fsdecode(x)).name for x in reversed(cmd) if x.endswith(b'.lean')),None)
            lean.append(dict(pid=pid,rss=rss,module=module))
        except (OSError,ValueError,StopIteration):pass
    return dict(seconds=round(time.monotonic()-began,2),memory=values,cgroup_limits=cgroups,available_bytes=available,lean_processes=lean,aggregate_lean_rss=sum(x['rss'] for x in lean))
def stop(signum=None,frame=None):
    global interrupted
    interrupted=signum
    try:os.killpg(proc.pid,signal.SIGTERM)
    except ProcessLookupError:pass
signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
last_log=-30
while proc.poll() is None:
    sample=observe();maximum_rss=max(maximum_rss,sample['aggregate_lean_rss'])
    if sample['seconds']-last_log>=10:
        print('RG_KERNEL_RESOURCE_OBSERVATION '+json.dumps(sample,separators=(',',':')),file=sys.stderr,flush=True);samples.append(sample);last_log=sample['seconds']
    if sample['lean_processes'] and sample['available_bytes'] is not None and sample['available_bytes']<a.memory_reserve_mib*1024**2:
        guard=True;print('RG_KERNEL_RESOURCE_GUARD_LOW_MEMORY '+json.dumps(sample),file=sys.stderr,flush=True);stop();break
    time.sleep(1)
try:code=proc.wait(timeout=30)
except subprocess.TimeoutExpired:
    try:os.killpg(proc.pid,signal.SIGKILL)
    except ProcessLookupError:pass
    code=proc.wait()
result=dict(status='MEMORY_GUARD_STOPPED_OWN_VERIFIER' if guard else 'INTERRUPTED' if interrupted else 'VERIFIER_COMPLETED',exit_code=code,maximum_aggregate_lean_rss=maximum_rss,seconds=round(time.monotonic()-began,2),samples=samples,mathlib_and_lean_flags_unchanged=True)
dest=R/'Proofs/RG_Lean_20261019/build/fresh_exports/resource_observer.json';dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((json.dumps(result,indent=2)+'\n').encode())
print('RG_KERNEL_RESOURCE_RESULT '+json.dumps({k:v for k,v in result.items() if k!='samples'}),file=sys.stderr,flush=True)
raise SystemExit(86 if guard else 128+interrupted if interrupted else code if code>=0 else 128-code)
