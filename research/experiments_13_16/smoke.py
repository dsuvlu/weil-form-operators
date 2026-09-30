#!/usr/bin/env python3
"""Bounded reviewed diagnostics; no moving-family or large-DH sweeps."""
from pathlib import Path
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "reviewed"))
import experiment_13_characteristic_mean as e13
import experiment_14_lefschetz_decomposition as e14
import experiment_15_davenport_heilbronn_control as e15
import experiment_16_arithmetic_localization as e16
import research_runtime as runtime
import weil_general as wg
import mpmath as mp


def run():
    zeta = e13.precision_stable(5, 6, max_dps=120)
    dh = e15.characteristic_point(20, N=4, precisions=[60, 84])
    assert zeta["status"] == dh["status"] == "precision_stable"
    lefschetz = e14.run(13, 14, 120)
    assert lefschetz["neg_J_even"] == 1 and lefschetz["neg_J_odd"] == 0
    surgery = e16.surgery(20)
    assert len(surgery) == 4 and all(row["precision_stable"] for row in surgery)
    matrix_difference = wg.check_against_repo(20, 4, 80)
    assert matrix_difference < mp.mpf("1e-70")
    sources = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((HERE / "reviewed").glob("*.py"))}
    report = dict(schema_version=runtime.SCHEMA_VERSION,evidence_status=runtime.STATUS,
                  environment=runtime.versions(),reviewed_source_hashes=sources,
                  cases=dict(zeta_x5_N6=zeta,dh_x20_N4=dh,lefschetz_x13_N14=lefschetz,
                             surgery_x20=surgery,matrix_difference=mp.nstr(matrix_difference,80)),
                  not_run=["full moving-family/cutoff sweeps", "large DH 300/500 in reviewed fork",
                           "all residue/decomposition modes", "global zero count", "rigorous interval certification"])
    path = runtime.OUTPUT / "results" / "smoke.json"
    runtime.write_json(path,report)
    print("Research smoke: PASS")
    return report


if __name__ == "__main__":
    run()
