#!/usr/bin/env python3
"""Check the frozen source distribution; optionally audit its compiled environment."""
import argparse, hashlib, json, re, subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise SystemExit(message)

def static():
    snap = json.loads((ROOT/'SNAPSHOT.json').read_text())
    manifest_path = HERE/'archived/source-hashes.json'
    require(sha(manifest_path) == snap['source_manifest_sha256'], 'Source manifest mismatch')
    manifest = json.loads(manifest_path.read_text())
    sources = {p.relative_to(ROOT).as_posix() for p in (ROOT/'Riemann').rglob('*.lean')} | {'Riemann.lean'}
    require(sources == set(manifest), 'Unexpected or missing Lean implementation source')
    for relative, expected in manifest.items():
        require(sha(ROOT/relative) == expected, f'Frozen source changed: {relative}')
        # Frozen sources contain none of these words, including in comments.
        require(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', (ROOT/relative).read_text()),
                f'Forbidden proof construct: {relative}')
    for relative, expected in snap['configuration_sha256'].items():
        require(sha(ROOT/relative) == expected, f'Pinned configuration changed: {relative}')
    evidence = HERE/'archived/pass7-evidence-hashes.json'
    require(sha(evidence) == snap['evidence_manifest_sha256'], 'Evidence manifest mismatch')
    for relative, expected in json.loads(evidence.read_text()).items():
        require(sha(HERE/'archived'/relative) == expected, f'Archived evidence changed: {relative}')
    modules = {p[:-5].replace('/', '.'): p for p in manifest}
    seen = set()
    def visit(name):
        if name in seen: return
        require(name in modules, f'Missing project import: {name}')
        seen.add(name)
        for line in (ROOT/modules[name]).read_text().splitlines():
            if line.startswith('import '):
                for imp in line.split()[1:]:
                    if imp == 'Riemann' or imp.startswith('Riemann.'): visit(imp)
    visit('Riemann')
    require(seen == set(modules), 'Unreachable project modules')
    print(f'Source preservation and import audit: PASS ({len(sources)} files)')
    return snap

def compiled():
    latest = HERE/'latest'; latest.mkdir(exist_ok=True)
    log = latest/'environment.jsonl.log'
    p = subprocess.run(['lake', 'env', 'lean', 'audit/drivers/distribution-audit.lean'],
                       cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.write_text(p.stdout)
    require(p.returncode == 0, f'Lean audit failed; inspect {log}')
    rows = []
    for line in p.stdout.splitlines():
        if line.startswith('{'):
            rows.append(json.loads(line))
    expected = [json.loads(s) for s in (HERE/'archived/environment-types.jsonl').read_text().splitlines() if s.strip()]
    actual = {r['name']:r for r in rows}
    require(len(actual) == len(rows), 'Duplicate environment names')
    require(set(actual) == {r['name'] for r in expected}, 'Compiled namespace inventory mismatch')
    allowed = {'propext','Classical.choice','Quot.sound'}
    for old in expected:
        row = actual[old['name']]
        require(row['kind'] == old['kind'] and row['type'] == old['type'], f'Elaborated type mismatch: {old["name"]}')
        require(row['kind'] != 'axiom' and not row['unsafe'], f'Custom axiom/unsafe declaration: {row["name"]}')
        require(set(row['axioms']) <= allowed, f'Unexpected transitive axiom: {row["name"]}')
    (latest/'summary.json').write_text(json.dumps({'status':'PASS','namespace_declarations':len(rows),
        'allowed_axioms':sorted(allowed),'elaborated_types_match':True},indent=2)+'\n')
    print(f'Compiled namespace/type/transitive-axiom audit: PASS ({len(rows)} declarations)')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args=parser.parse_args()
    static()
    if args.compiled: compiled()
