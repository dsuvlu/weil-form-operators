"""Isolated output paths and JSON metadata for the reviewed research fork."""
from pathlib import Path
import importlib.metadata
import json
import platform
import sys

ROOT = Path(__file__).resolve().parents[3]
EXPERIMENTS = ROOT / "experiments"
if str(EXPERIMENTS) not in sys.path:
    sys.path.append(str(EXPERIMENTS))
OUTPUT = Path(__file__).resolve().parents[1] / "generated"
SCHEMA_VERSION = 1
STATUS = "Numerical diagnostic, uncertified"


def output_dir():
    for name in ("results", "figures"):
        (OUTPUT / name).mkdir(parents=True, exist_ok=True)
    return OUTPUT


def versions():
    result = {"python": platform.python_version(), "status": STATUS}
    for name in ("mpmath", "python-flint", "numpy", "matplotlib"):
        try:
            result[name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            result[name] = None
    result["solver"] = "flint eig(algorithm=approx)" if result["python-flint"] else "mpmath eig/eigsy"
    return result


def write_json(path, payload):
    """Generated data never overwrites imported results. NaNs are prohibited."""
    path = Path(path).resolve()
    if OUTPUT not in path.parents:
        raise ValueError("Research outputs must remain in generated/")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, allow_nan=False) + "\n")
