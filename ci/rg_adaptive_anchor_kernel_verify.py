"""Use the proved two-worker anchor profile, with one measured-memory fallback."""
import argparse,json,pathlib,re,shutil,subprocess,sys
R=pathlib.Path(__file__).resolve().parent.parent;S=R/'Proofs/RG_Lean_20261019'
ap=argparse.ArgumentParser();ap.add_argument('--endpoint',required=True);ap.add_argument('--mathlib-project',type=pathlib.Path,required=True);a=ap.parse_args()
assert re.fullmatch(r'Proofs\.RadenkovicGutmanWideAnchor\d{3}OriginalAnchor',a.endpoint)
fresh=S/'build/fresh_exports';fresh.mkdir(parents=True,exist_ok=True)
attempts=[]
for workers in [2,1]:
    report=fresh/'resource_observer.json'
    if report.exists():
        retained=fresh/'resource_observer_workers2.json'
        assert workers==1 and retained.is_file() and retained.read_bytes()==report.read_bytes()
        report.unlink()
    command=[sys.executable,'-B',str(R/'ci/rg_observed_kernel_verify.py'),'--memory-reserve-mib','2048','--','--mathlib-project',str(a.mathlib_project),'--endpoint',a.endpoint,'--workers',str(workers),'--module-timeout','600','--resume']
    result=subprocess.run(command,cwd=R)
    assert report.is_file(),'The resource observer must retain its actual outcome'
    observed=json.loads(report.read_bytes());copy=fresh/f'resource_observer_workers{workers}.json';shutil.copyfile(report,copy)
    attempts.append(dict(workers=workers,exit_code=result.returncode,resource_status=observed['status']))
    (fresh/'adaptive_worker_attempts.json').write_bytes((json.dumps(dict(endpoint=a.endpoint,attempts=attempts,all_lean_flags_and_proof_sources_unchanged=True),indent=2)+'\n').encode())
    if result.returncode!=86:
        if result.returncode==0:assert observed['status']=='VERIFIER_COMPLETED' and observed['exit_code']==0
        raise SystemExit(result.returncode)
    assert observed['status']=='MEMORY_GUARD_STOPPED_OWN_VERIFIER'
    if workers==1:raise SystemExit(86)
    print('RETRY_ONLY_AFTER_MEASURED_MEMORY_GUARD_WITH_ONE_WORKER_SAME_KERNEL_RULES_AND_VERIFIED_COMPLETED_EXPORTS',flush=True)
