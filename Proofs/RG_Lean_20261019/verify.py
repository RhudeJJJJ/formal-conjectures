#!/usr/bin/env python3
"""Rebuild the exact RG closure and pinned, restricted LeanCert sources."""
import argparse, hashlib, json, os, pathlib, re, shutil, subprocess, time
ROOT=pathlib.Path(__file__).resolve().parent
PIN='0df444a360eaa60ab8c11dca51a86af692955474'
LEANCERT_PIN='621a43d7cf21f87872392a01e874f2f1dbddc926'
ALLOWED={'propext','Classical.choice','Quot.sound'}

def run(cmd,cwd,env=None):
    return subprocess.check_output(cmd,cwd=cwd,env=env,text=True,stderr=subprocess.STDOUT)

def without_comments(s):
    """Preserve newlines while removing Lean nested comments and strings."""
    out=[];i=0;depth=0;quoted=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
            elif s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif quoted:
            if s[i]=='\\':out.extend('  ');i+=2
            elif s[i]=='"':quoted=False;out.append(' ');i+=1
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i)
            if j<0:j=len(s)
            out.extend(' '*(j-i));i=j
        elif s[i]=='"':quoted=True;out.append(' ');i+=1
        else:out.append(s[i]);i+=1
    assert depth==0 and not quoted,'Unterminated Lean comment or string'
    return ''.join(out)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--mathlib-project',type=pathlib.Path)
    ap.add_argument('--module-timeout',type=int,default=7200)
    ap.add_argument('--resume',action='store_true',help='Resume a checked prefix with unchanged source hashes')
    args=ap.parse_args()
    if (ROOT/'SHA256SUMS').exists():
        for line in (ROOT/'SHA256SUMS').read_text().splitlines():
            sha,rel=line.split('  ',1)
            assert hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==sha,rel
    modules=json.loads((ROOT/'MODULES.json').read_text())
    upstream=json.loads((ROOT/'ThirdParty/LeanCert/UPSTREAM.json').read_text())
    vmods=json.loads((ROOT/'LEANCERT_MODULES.json').read_text())
    assert upstream['commit']==LEANCERT_PIN
    vendor=ROOT/'ThirdParty/LeanCert'
    for rel,sha in upstream['source_sha256'].items():
        assert hashlib.sha256((vendor/rel).read_bytes()).hexdigest()==sha,rel
    files=[(m,vendor/(m.replace('.','/')+'.lean'),'LeanCert') for m in vmods]
    files += [('Proofs.'+m,ROOT/'Proofs'/(m+'.lean'),'RG') for m in modules]
    assert len(files)==len(set(m for m,_,_ in files))
    provided=set(m for m,_,_ in files);seen=set()
    for m,source,kind in files:
        code=without_comments(source.read_text())
        assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s',code,re.M),m
        imports=re.findall(r'^\s*(?:public\s+)?import\s+((?:Proofs|LeanCert)\.[\w.]+)\s*$',code,re.M)
        assert set(imports)<=seen,(m,'Non-topological or missing source imports',imports)
        seen.add(m)
    project=args.mathlib_project.resolve() if args.mathlib_project else ROOT
    if args.mathlib_project is None:
        subprocess.run(['lake','update'],cwd=ROOT,check=True)
        imports=sorted({i for _,source,_ in files for i in
            re.findall(r'^\s*(?:public\s+)?import\s+(Mathlib\.[\w.]+)\s*$',source.read_text(),re.M)})
        subprocess.run(['lake','exe','cache','get',*imports],cwd=ROOT,check=True)
    dep=project/'.lake/packages/mathlib'
    assert run(['git','rev-parse','HEAD'],dep).strip()==PIN,'Mathlib pin mismatch'
    query="import os,json;print(json.dumps({k:os.environ[k] for k in ('PATH','LEAN_PATH')}))"
    settings=json.loads(run(['lake','env','python3','-c',query],project))
    env=os.environ.copy();env.update(settings)
    roots=[str((project/p).resolve()) if not pathlib.Path(p).is_absolute() else p
           for p in env['LEAN_PATH'].split(os.pathsep) if p]
    build=ROOT/'build/rechecked'
    previous=None
    if args.resume and (build/'receipt.partial.json').exists():
        previous=json.loads((build/'receipt.partial.json').read_text())
        assert previous['mathlib']==PIN and previous['leancert']==LEANCERT_PIN
    elif build.exists():shutil.rmtree(build)
    build.mkdir(parents=True,exist_ok=True)
    env['LEAN_PATH']=os.pathsep.join([str(build),*roots])
    lean=shutil.which('lean',path=env['PATH']);assert lean
    version=run([lean,'--version'],ROOT,env).strip()
    assert 'version 4.33.1,' in version,version
    if previous:assert previous['lean']==version
    receipt={'lean':version,'mathlib':PIN,'leancert':LEANCERT_PIN,
        'global_rg':'NOT_PROVED','source_build':'FRESH','warnings_as_errors':True,
        'rg_modules':[],'dependency_modules':[]}
    started=time.monotonic()
    oldrows=(previous['dependency_modules']+previous['rg_modules']) if previous else []
    reuse=True
    for index,(m,source,kind) in enumerate(files):
        output=build/(m.replace('.','/')+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
        sha=hashlib.sha256(source.read_bytes()).hexdigest()
        if reuse and index<len(oldrows) and oldrows[index]['name']==m and oldrows[index]['source_sha256']==sha and output.exists():
            receipt['rg_modules' if kind=='RG' else 'dependency_modules'].append(oldrows[index])
            print('RETAINED_CHECKED_PREFIX',m,flush=True)
            continue
        reuse=False
        cmd=[lean,'-j1','-DwarningAsError=true']
        if kind=='LeanCert':cmd+=['-R',str(vendor)]
        if kind=='RG':cmd+=['-DautoImplicit=false','-DrelaxedAutoImplicit=false']
        cmd+=['-o',str(output),str(source)]
        log=build/(m+'.log');t0=time.monotonic()
        with log.open('w') as f:
            try:
                p=subprocess.run(cmd,cwd=ROOT,env=env,text=True,stdout=f,
                    stderr=subprocess.STDOUT,timeout=args.module_timeout)
            except subprocess.TimeoutExpired:
                raise RuntimeError('Timed out: '+m+'; inspect '+str(log))
        content=log.read_text()
        assert p.returncode==0,content
        assert not re.search(r'\b(error|warning):',content),content
        profiles=[]
        for name,axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",content):
            used={a.strip() for a in axioms.split(',') if a.strip()}
            assert used<=ALLOWED,(name,used)
            profiles.append({'name':name,'axioms':sorted(used)})
        for name in re.findall(r"'([^']+)' does not depend on any axioms",content):
            profiles.append({'name':name,'axioms':[]})
        if kind=='RG':assert profiles,'No printed axiom profile: '+m
        row={'name':m,'seconds':round(time.monotonic()-t0,3),
             'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'profiles':profiles}
        receipt['rg_modules' if kind=='RG' else 'dependency_modules'].append(row)
        receipt['seconds']=round(sum(r['seconds'] for r in receipt['dependency_modules']+receipt['rg_modules']),3)
        (build/'receipt.partial.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print('PASS',kind,m,round(time.monotonic()-t0,2),'s',len(profiles),'printed profiles',flush=True)
    receipt['printed_axiom_profiles']=sum(len(m['profiles']) for m in receipt['rg_modules'])
    receipt['resumed']=bool(previous)
    (build/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS_RG_SOURCE_CLOSURE',len(modules),'RG sources;',len(vmods),
          'dependency sources;',receipt['printed_axiom_profiles'],
          'profiles; GLOBAL RG NOT_PROVED',flush=True)

if __name__=='__main__':main()
