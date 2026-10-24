#!/usr/bin/env python3
"""Recheck local fusion, all-arm degree-two/three, degree-four/five all-arm and conditional global results.
Binary checkpoints are optional.
Default: fresh kernel exports. --resume reuses content- and dependency-checked
exports from this verifier. --reuse-binaries explicitly restores the optional
pinned compiler checkpoints supplied with this partial formalization.
"""
import argparse, concurrent.futures, hashlib, json, os, pathlib, re, shutil, subprocess, sys, time, zlib
from verify import without_comments
ROOT=pathlib.Path(__file__).resolve().parent
PIN='0df444a360eaa60ab8c11dca51a86af692955474'
LC='621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def digest(data):return hashlib.sha256(data).hexdigest()
from module_outputs import check_additional_outputs, remove_pending_outputs, finalize_outputs

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--mathlib-project',type=pathlib.Path,required=True)
 ap.add_argument('--lean-bin-directory',type=pathlib.Path,help='Use an installed toolchain directly, without Lake environment discovery')
 ap.add_argument('--build-directory',type=pathlib.Path,help='Separate exports for an independent verification closure')
 ap.add_argument('--endpoint',action='append',help='Explicit module head; recursively check its closure')
 ap.add_argument('--workers',type=int,default=2)
 ap.add_argument('--module-timeout',type=int,default=7200)
 ap.add_argument('--resume',action='store_true')
 ap.add_argument('--profile',action='store_true',help='Report compiler timings without changing source or proof checks')
 ap.add_argument('--reuse-binaries',action='store_true')
 ap.add_argument('--print-receipt',action='store_true',help='Emit the completed receipt for CI collection')
 a=ap.parse_args();assert 1<=a.workers<=8
 project=a.mathlib_project.resolve();dep=project if (project/'Mathlib').is_dir() else project/'.lake/packages/mathlib'
 def run(cmd,cwd=project,env=None):return subprocess.check_output(cmd,cwd=cwd,env=env,text=True,stderr=subprocess.STDOUT).strip()
 assert run(['git','rev-parse','HEAD'],cwd=dep)==PIN,'Mathlib pin mismatch'
 up=json.loads((ROOT/'ThirdParty/LeanCert/UPSTREAM.json').read_text());assert up['commit']==LC
 for p,h in up['source_sha256'].items():assert digest((ROOT/'ThirdParty/LeanCert'/p).read_bytes())==h,p
 if a.lean_bin_directory:
  package_dir=project/'.lake/packages'
  libraries=[project/'.lake/build/lib/lean']
  libraries.extend(p/'.lake/build/lib/lean' for p in sorted(package_dir.iterdir()) if p.is_dir())
  settings={'PATH':str(a.lean_bin_directory.resolve())+os.pathsep+os.environ['PATH'],
            'LEAN_PATH':os.pathsep.join(str(p.resolve()) for p in libraries)}
 else:
  settings=json.loads(run(['lake','env',sys.executable,'-c',"import os,json;print(json.dumps({k:os.environ[k] for k in ('PATH','LEAN_PATH')}))"]))
 env=os.environ.copy();env.update(settings)
 paths=[str((project/p).resolve()) if not pathlib.Path(p).is_absolute() else p for p in env['LEAN_PATH'].split(os.pathsep) if p]
 lean=shutil.which('lean',path=env['PATH']);assert lean
 version=run([lean,'--version'],ROOT,env);assert 'version 4.33.1,' in version,version
 build=a.build_directory.resolve() if a.build_directory else ROOT/'build/extension'
 if build.exists() and not a.resume:shutil.rmtree(build)
 build.mkdir(parents=True,exist_ok=True)
 env['LEAN_PATH']=os.pathsep.join([str(build),*paths])
 ends=a.endpoint or json.loads((ROOT/'SHORT_ARM_ENDPOINTS.json').read_text());sources={};deps={};hashes={};closure={}
 def visit(n):
  if n in sources:return
  p=(ROOT/'ThirdParty/LeanCert' if n.startswith('LeanCert.') else ROOT)/(n.replace('.','/')+'.lean')
  code=without_comments(p.read_text());assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s',code,re.M),n
  sources[n]=p;hashes[n]=digest(p.read_bytes())
  deps[n]=set(re.findall(r'^\s*(?:public\s+)?import\s+((?:Proofs|LeanCert)\.[\w.]+)\s*$',code,re.M))
  for d in sorted(deps[n]):visit(d)
 def ch(n):
  if n not in closure:closure[n]=digest(json.dumps([n,hashes[n],PIN,LC,[(d,ch(d)) for d in sorted(deps[n])]],separators=(',',':')).encode())
  return closure[n]
 for n in ends:visit(n)
 for n in sources:ch(n)
 if not a.endpoint:assert set(sources)==set(json.loads((ROOT/'SHORT_ARM_MODULES.json').read_text())),'Scope manifest mismatch'
 records={}
 if a.reuse_binaries:
  man=json.loads((ROOT/'BINARY_CACHE/manifest.json').read_text());assert man['mathlib']==PIN and man['leancert']==LC
  assert man['lean']==version and man['lean_binary_sha256']==digest(pathlib.Path(lean).read_bytes()),'Compiler checkpoint mismatch'
  for row in man['objects']:
   n=row['module']
   if n not in sources:continue
   assert not row.get('additional_outputs'),'Use source-bound archive restoration for module-system sidecars'
   assert row['source_sha256']==hashes[n] and row['source_closure_sha256']==closure[n],n
   assert all(set(p)<=ALLOWED for p in row['axiom_profiles']),n
   data=(ROOT/row['compressed_path']).read_bytes();assert digest(data)==row['compressed_sha256'],n
   data=zlib.decompress(data);assert len(data)==row['output_bytes'] and digest(data)==row['output_sha256'],n
   out=build/(n.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
   tmp=out.with_suffix('.olean.pending');tmp.write_bytes(data);tmp.replace(out)
   rec=dict(module=n,source_sha256=hashes[n],source_closure_sha256=closure[n],output_sha256=row['output_sha256'],axiom_profiles=row['axiom_profiles'],mode='PINNED_CHECKPOINT',seconds=0)
   (build/(n+'.json')).write_text(json.dumps(rec,indent=2)+'\n')
 def compile_one(n):
  p=sources[n];assert digest(p.read_bytes())==hashes[n],'Source changed during run: '+n
  out=build/(n.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
  rp=build/(n+'.json')
  if rp.exists() and out.exists():
   r=json.loads(rp.read_text())
   if r['source_sha256']==hashes[n] and r['source_closure_sha256']==closure[n] and r['output_sha256']==digest(out.read_bytes()):
    check_additional_outputs(out,r)
    assert all(set(p)<=ALLOWED for p in r['axiom_profiles']),n
    assert r['axiom_profiles'] or n.startswith('LeanCert.'),'Missing resumed axiom profile: '+n
    return n,r
  log=build/(n+'.log');tmp=out.with_suffix('.olean.pending');remove_pending_outputs(tmp);start=time.monotonic()
  cmd=[lean,'-j1','-DElab.async=false','-DwarningAsError=true']
  if a.profile:cmd+=['-Dprofiler=true','-Dprofiler.threshold=100']
  cmd+=['-R',str(ROOT/'ThirdParty/LeanCert')] if n.startswith('LeanCert.') else ['-DautoImplicit=false','-DrelaxedAutoImplicit=false']
  cmd+=['-o',str(tmp),str(p)]
  with log.open('w') as f:
   try:r=subprocess.run(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=a.module_timeout)
   except subprocess.TimeoutExpired:remove_pending_outputs(tmp);raise RuntimeError('Timeout: '+n)
  text=log.read_text()
  if r.returncode or re.search(r'\b(error|warning)(?:\([^\n]*?\))?:',text):remove_pending_outputs(tmp);raise RuntimeError(text)
  profiles=[sorted(set(x.strip() for x in s.split(',') if x.strip())) for s in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',text)]
  profiles += [[] for _ in re.findall('does not depend on any axioms',text)]
  assert all(set(p)<=ALLOWED for p in profiles),n
  assert profiles or n.startswith('LeanCert.'),'Missing axiom profile: '+n
  assert digest(p.read_bytes())==hashes[n],'Source changed during run: '+n
  additional_outputs=finalize_outputs(tmp,out)
  row=dict(module=n,source_sha256=hashes[n],source_closure_sha256=closure[n],output_sha256=digest(out.read_bytes()),axiom_profiles=profiles,mode='FRESH_KERNEL_EXPORT',seconds=round(time.monotonic()-start,3))
  if additional_outputs:row['additional_outputs']=additional_outputs
  rp.write_text(json.dumps(row,indent=2)+'\n');return n,row
 done=set();running={};started=time.monotonic()
 with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:
  while len(done)<len(sources):
   ready=[n for n in sorted(sources) if n not in done and n not in running.values() and deps[n]<=done]
   for n in ready[:a.workers-len(running)]:running[pool.submit(compile_one,n)]=n
   assert running,'Cyclic module graph'
   finished,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
   for f in finished:
    n,row=f.result();del running[f];done.add(n);records[n]=row
    print('PASS',n,row['mode'],row['seconds'],flush=True)
    print('COMPLETED_MODULE_JSON '+json.dumps(row,separators=(',',':')),flush=True)
 report=dict(lean=version,mathlib=PIN,leancert=LC,global_rg='NOT_PROVED',complete_submission='NOT_SUBMITTED',scope='EXPLICIT_EXTENSION_CLOSURE' if a.endpoint else 'ALL_ARM_DEGREES_TWO_THREE_FOUR_FIVE_AND_CONDITIONAL_GLOBAL_REDUCTION',endpoints=ends,modules=records,wall_seconds=round(time.monotonic()-started,3))
 (build/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
 print('PASS_EXTENSION_SCOPE' if a.endpoint else 'PASS_SHORT_ARM_SCOPE',len(done),'MODULES; GLOBAL RG NOT_PROVED',flush=True)
 if a.print_receipt:print('RECEIPT_JSON '+json.dumps(report,separators=(',',':')),flush=True)
if __name__=='__main__':main()
