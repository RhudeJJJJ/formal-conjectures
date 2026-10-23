"""Monitor only the process group started here; leave every other process alone."""
import argparse,json,os,pathlib,shutil,signal,subprocess,time
ap=argparse.ArgumentParser();ap.add_argument('command',nargs=argparse.REMAINDER);a=ap.parse_args()
assert os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('RUNNER_ENVIRONMENT')=='github-hosted'
host=pathlib.Path(os.environ['RG_PROOFSTORE_HOST_PATH']).resolve()
assert host==pathlib.Path(os.environ['GITHUB_WORKSPACE']).resolve()
command=a.command[1:] if a.command[:1]==['--'] else a.command
assert command and command[0] in ('python3','python')
assert shutil.disk_usage(host).free>=10*1024**3
proc=subprocess.Popen(command,start_new_session=True);lowest=shutil.disk_usage(host).free;stopped=False
while proc.poll() is None:
    free=shutil.disk_usage(host).free;lowest=min(lowest,free)
    if free<8*1024**3:
        print(json.dumps(dict(status='OWNED_KERNEL_GROUP_STOPPED_AT_HOST_RESERVE',owned_pid=proc.pid,host_free_bytes=free)),flush=True)
        os.killpg(proc.pid,signal.SIGTERM);stopped=True
        try:proc.wait(timeout=10)
        except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL)
        break
    time.sleep(1)
rc=proc.wait();report=dict(status='OWNED_KERNEL_GROUP_ENDED',exit_code=rc,host_reserve_stop=stopped,lowest_observed_host_free_bytes=lowest,owned_pid=proc.pid,foreign_processes_signalled=0)
(host/'rg-proofstore-kernel-reserve.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
raise SystemExit(1 if stopped else rc)
