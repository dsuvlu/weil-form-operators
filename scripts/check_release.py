#!/usr/bin/env python3
"""Check the release payload, archive-preserved Python files and local doc links."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
def require(ok,message):
    if not ok: raise SystemExit(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
manifest=ROOT/'RELEASE_MANIFEST.json'
if manifest.exists():
    for name,expected in json.loads(manifest.read_text())['files'].items():
        require((ROOT/name).is_file() and sha(ROOT/name)==expected, f'Release file changed/missing: {name}')
    print('Release manifest: PASS')
for name,expected in json.loads((ROOT/'experiments/source-hashes.json').read_text()).items():
    p=ROOT/'experiments'/name
    require(sha(p)==expected,f'Archive Python file changed: {name}')
    compile(p.read_text(),str(p),'exec')
print('Archive Python preservation and syntax: PASS')
for p in (ROOT/name for name in json.loads(manifest.read_text())['files'] if name.endswith('.md')):
    relative=p.relative_to(ROOT)
    if '.lake' in relative.parts or 'archived' in relative.parts:continue
    text=p.read_text()
    require('/home/' not in text,f'Private absolute path in public documentation: {relative}')
    for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)',text):
        if target.startswith(('http:','https:','mailto:','#')):continue
        target=target.split('#')[0]
        require((p.parent/target).exists(),f'Broken local link in {relative}: {target}')
print('Public documentation links: PASS')
subprocess.run([sys.executable,str(ROOT/'verification/audit/check.py')],check=True)
