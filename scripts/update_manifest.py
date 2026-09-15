#!/usr/bin/env python3
"""Refresh release hashes after intentional edits, preserving the frozen-code guards."""
from pathlib import Path
import datetime,hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
subprocess.run([sys.executable,str(ROOT/'verification/audit/check.py')],check=True)
for name,expected in json.loads((ROOT/'experiments/source-hashes.json').read_text()).items():
    actual=hashlib.sha256((ROOT/'experiments'/name).read_bytes()).hexdigest()
    if actual!=expected: raise SystemExit(f'Original experiment source changed: {name}')
# Use Git's ignore rules so local caches, exports and private validation notes
# never become payload dependencies. Include new, not-yet-staged public files.
paths=subprocess.check_output(['git','ls-files','--cached','--others','--exclude-standard','-z'],cwd=ROOT).decode().split('\0')
files={}
for name in sorted(set(paths)-{'','RELEASE_MANIFEST.json'}):
    if subprocess.run(['git','check-ignore','--quiet','--no-index',name],cwd=ROOT).returncode==0: continue
    p=ROOT/name
    if p.is_file():files[name]=hashlib.sha256(p.read_bytes()).hexdigest()
manifest=ROOT/'RELEASE_MANIFEST.json'
data=json.loads(manifest.read_text())
data['date']=datetime.date.today().isoformat();data['files']=files
manifest.write_text(json.dumps(data,indent=2)+'\n')
print(f'Release manifest refreshed: {len(files)} public files; frozen sources unchanged.')
