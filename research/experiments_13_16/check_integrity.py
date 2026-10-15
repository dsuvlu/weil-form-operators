#!/usr/bin/env python3
"""Separate research payload integrity; never regenerates either manifest."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
manifest = json.loads((HERE / "RESEARCH_MANIFEST.json").read_text())
for name, expected in manifest["files"].items():
    path = ROOT / name
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise SystemExit(f"Research file changed/missing: {name}")
    if path.suffix == ".py":
        compile(path.read_text(), str(path), "exec")
excluded = {"generated", ".venv", "__pycache__"}
actual = {str(path.relative_to(ROOT)) for path in HERE.rglob("*")
          if path.is_file() and not excluded.intersection(path.relative_to(HERE).parts)
          and path.name != "RESEARCH_MANIFEST.json"}
expected = {name for name in manifest["files"] if name.startswith(str(HERE.relative_to(ROOT)) + "/")}
if actual != expected:
    raise SystemExit(f"Unmanifested/missing research payload: {sorted(actual ^ expected)}")
raw_manifest = json.loads((HERE / "IMPORT_PROVENANCE.json").read_text())
for name, expected in raw_manifest["imported_files"].items():
    if hashlib.sha256((HERE / name).read_bytes()).hexdigest() != expected:
        raise SystemExit(f"Original import changed: {name}")
print(f"Research integrity and immutable import: PASS ({len(manifest['files'])} files)")
