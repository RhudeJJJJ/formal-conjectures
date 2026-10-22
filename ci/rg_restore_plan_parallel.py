"""Restore disjoint source-bound prerequisite manifests with bounded concurrency."""
import argparse,concurrent.futures,json,pathlib,subprocess,sys
ap=argparse.ArgumentParser();ap.add_argument('--plan',type=pathlib.Path,required=True)
ap.add_argument('--build-directory',type=pathlib.Path,required=True)
ap.add_argument('--workers',type=int,default=2);a=ap.parse_args()
assert 1<=a.workers<=2
paths=json.loads(a.plan.read_text());assert 0<len(paths)<=2000
seen=set()
for value in paths:
    p=pathlib.Path(value);assert p.is_relative_to('ci') and '..' not in p.parts
    modules=set(json.loads(p.read_text())['modules']);assert not seen&modules,value
    seen|=modules
def restore(value):
    result=subprocess.run([sys.executable,'-B','ci/rg_restore_job_exports.py',
        '--manifest',value,'--build-directory',str(a.build_directory)],
        stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    return value,result
failures=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:
    futures=[pool.submit(restore,p) for p in paths]
    for number,future in enumerate(concurrent.futures.as_completed(futures),1):
        value,result=future.result()
        print(result.stdout.decode('utf-8'),end='',flush=True)
        print(json.dumps({'prerequisite_manifests_finished':number,'total':len(paths),
                          'manifest':value,'exit_code':result.returncode}),flush=True)
        if result.returncode:failures.append(value)
if failures:raise SystemExit('PREREQUISITE_RESTORE_FAILED '+json.dumps(failures))
