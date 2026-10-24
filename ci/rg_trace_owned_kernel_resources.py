"""Observe one owned foreground kernel group after an unexplained runner shutdown."""
import argparse,json,os,pathlib,shutil,subprocess,time
ap=argparse.ArgumentParser();ap.add_argument('command',nargs=argparse.REMAINDER);a=ap.parse_args()
assert os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('RUNNER_ENVIRONMENT')=='github-hosted' and os.environ.get('RUNNER_OS')=='Linux'
command=a.command[1:] if a.command[:1]==['--'] else a.command
assert command and command[0] in ('python3','python')
proc=subprocess.Popen(command,start_new_session=True)
def observe():
    mem={line.split(':')[0]:int(line.split()[1])*1024 for line in pathlib.Path('/proc/meminfo').read_text().splitlines() if line.split(':')[0] in ['MemTotal','MemAvailable']}
    cgroup={}
    for name in ['memory.max','memory.high','memory.current','memory.events']:
        p=pathlib.Path('/sys/fs/cgroup')/name
        if p.is_file():cgroup[name]=p.read_text().strip()
    rss=0; owned_lean=[]
    for line in subprocess.check_output(['ps','-eo','pid=,pgid=,rss=,comm='],text=True).splitlines():
        pid_s,pgid_s,kib_s,comm=line.split(maxsplit=3)
        pid,pgid,kib=int(pid_s),int(pgid_s),int(kib_s)
        if pgid!=proc.pid:continue
        rss+=kib*1024
        if not comm.lower().startswith('lean'):continue
        details=dict(pid=pid,comm=comm,rss_bytes=kib*1024)
        try:
            d=pathlib.Path('/proc')/str(pid)
            stat=(d/'stat').read_text().rsplit(')',1)[1].split()
            details.update(state=stat[0],minor_faults=int(stat[7]),major_faults=int(stat[9]),
                user_cpu_ticks=int(stat[11]),system_cpu_ticks=int(stat[12]),
                ticks_per_second=os.sysconf('SC_CLK_TCK'),wchan=(d/'wchan').read_text().strip())
            details['io']={k:int(v) for k,v in (line.split(':',1) for line in (d/'io').read_text().splitlines())}
            details['resident_parts']={k:int(v.split()[0])*1024 for k,v in
                (line.split(':',1) for line in (d/'status').read_text().splitlines() if ':' in line)
                if k in ['VmSize','VmRSS','RssAnon','RssFile','RssShmem','VmSwap']}
            maps=(d/'maps').read_text().splitlines()
            oleans=[m.split(maxsplit=5)[-1] for m in maps if '.olean' in m]
            details.update(memory_mappings=len(maps),olean_mappings=len(oleans),last_olean_mappings=oleans[-5:])
        except (OSError,ValueError,IndexError) as error:
            details['observation_error']=repr(error)
        owned_lean.append(details)
    print(json.dumps(dict(status='OWNED_KERNEL_RESOURCE_OBSERVATION',owned_group=proc.pid,group_rss_bytes=rss,owned_lean=owned_lean,host_memory=mem,cgroup_memory=cgroup,host_free_disk_bytes=shutil.disk_usage(os.environ['GITHUB_WORKSPACE']).free,foreign_processes_controlled=0)),flush=True)
observe();next_report=time.monotonic()+30
while proc.poll() is None:
    if time.monotonic()>=next_report:observe();next_report=time.monotonic()+30
    time.sleep(1)
rc=proc.wait();print(json.dumps(dict(status='OWNED_KERNEL_GROUP_ENDED',owned_group=proc.pid,exit_code=rc)),flush=True)
raise SystemExit(rc)
