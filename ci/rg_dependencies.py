#!/usr/bin/env python3
"""Materialize the exact existing Lake lock using shallow Git checkouts."""
import hashlib,json,pathlib,re,subprocess

root=pathlib.Path.cwd().resolve();lock=root/'lake-manifest.json';raw=lock.read_bytes();manifest=json.loads(raw)
packages=root/manifest['packagesDir'];assert packages.resolve().is_relative_to(root);packages.mkdir(parents=True,exist_ok=True)
for package in manifest['packages']:
    name,rev,url=package['name'],package['rev'],package['url']
    assert package['type']=='git' and re.fullmatch(r'[A-Za-z0-9_-]+',name) and re.fullmatch(r'[a-f0-9]{40}',rev)
    assert re.fullmatch(r'https://github.com/(leanprover|leanprover-community)/[A-Za-z0-9_.-]+',url)
    target=packages/name;assert target.resolve().is_relative_to(packages.resolve())
    if not target.exists():
        target.mkdir()
        subprocess.run(['git','init','-q',str(target)],check=True)
        subprocess.run(['git','-C',str(target),'remote','add','origin',url],check=True)
        subprocess.run(['git','-C',str(target),'fetch','-q','--depth','1','origin',rev],check=True)
        subprocess.run(['git','-C',str(target),'checkout','-q','--detach',rev],check=True)
    actual=subprocess.check_output(['git','-C',str(target),'rev-parse','HEAD'],text=True).strip()
    assert actual==rev,(name,actual,rev)
    print('LOCKED_PACKAGE',name,rev,flush=True)
assert lock.read_bytes()==raw
print('UNCHANGED_LAKE_LOCK',hashlib.sha256(raw).hexdigest(),flush=True)
