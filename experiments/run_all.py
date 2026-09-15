"""Run the demonstration experiments in numerical order.

By default this runs the ordinary float64 demonstrations.  The explicit
precision-ladder experiment is skipped so a first-time user gets the simple,
fast path.  Add ``--include-precision-ladder`` to run Experiment 12 as well.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import sys


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument(
    "--include-precision-ladder",
    action="store_true",
    help="also run experiment_12_precision_ladder.py",
)
args = parser.parse_args()

root = Path(__file__).resolve().parent
scripts = sorted(root.glob("experiment_*.py"))

if not args.include_precision_ladder:
    scripts = [script for script in scripts if script.name != "experiment_12_precision_ladder.py"]

for script in scripts:
    print("\n" + "=" * 78)
    print(f"RUNNING {script.name}")
    print("=" * 78)
    subprocess.run([sys.executable, str(script)], cwd=root, check=True)
