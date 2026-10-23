"""Observe one owned foreground kernel group after an unexplained runner shutdown."""
import argparse,json,os,pathlib,shutil,subprocess,time
ap=argparse.ArgumentParser();ap.add_argument('command',nargs=argparse.REMAINDER);a=ap.parse_args()
assert os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('RUNNER_ENVIRONMENT')=='github-hosted' and os.environ.get('RUNNER_OS')=='Linux'
command=a.command[1:] if a.command[:1]==['--'] else a.command
assert command and command[0] in ('python3','python')
proc=subprocess.Popen(command,start_new_session=True)
def observe():
    mem={line.split(':')[0]:int(line.split()[1])*1024 for line in pathlib.Path('/proc/meminfo').read_text().splitlines() if line.split(':')[0] in ['MemTotal','MemAvailable']}
    rss=0
    for line in subprocess.check_output(['ps','-eo','pgid=,rss='],text=True).splitlines():
        pgid,kib=map(int,line.split())
        if pgid==proc.pid:rss+=kib*1024
    print(json.dumps(dict(status='OWNED_KERNEL_RESOURCE_OBSERVATION',owned_group=proc.pid,group_rss_bytes=rss,host_memory=mem,host_free_disk_bytes=shutil.disk_usage(os.environ['GITHUB_WORKSPACE']).free,foreign_processes_controlled=0)),flush=True)
observe();next_report=time.monotonic()+30
while proc.poll() is None:
    if time.monotonic()>=next_report:observe();next_report=time.monotonic()+30
    time.sleep(1)
rc=proc.wait();print(json.dumps(dict(status='OWNED_KERNEL_GROUP_ENDED',owned_group=proc.pid,exit_code=rc)),flush=True)
raise SystemExit(rc)
