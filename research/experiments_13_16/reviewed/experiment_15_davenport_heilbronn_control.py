"""Experiment 15: the Davenport-Heilbronn control for Paper IV's premises.

DH: f = (1-i kappa)/2 L(s,chi) + (1+i kappa)/2 L(s,chi-bar), chi mod 5 with
chi(2) = i.  It has conductor 5, the odd Gamma factor Gamma_R(s+1), no poles, a
functional equation with root number +1, NO Euler product, and zeros off the
critical line (numerically located near 0.8085 + 85.699i and 0.6508 + 114.163i).
The matched control is L(s, chi) itself: same conductor, Gamma factor and
absence of poles, with an Euler product.  (The conductor enters the finite
matrix as log q times the identity, so it must match.)

Modes
  verify          functional equation and two guessed off-line roots of DH (no completeness claim)
  spectra         least eigenvalue and number of negative eigenvalues, DH vs
                  L(chi), along x; for each negative DH direction, the zero-side
                  energy carried by each known off-line quadruplet
  characteristic  DH ground parity, corrected roots near the off-line height,
                  lowest corrected roots, and the complete characteristic mean

Every eigenvalue is computed at two precisions (3N+60 and 1.4x that digits),
with coefficients recomputed at each precision.  Finite diagnostics; proves
nothing.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import research_runtime as runtime
import research_diagnostics as diagnostics

import mpmath as mp

import weil_general as wg

HERE = runtime.output_dir()
OUT = HERE / "results" / "experiment_15_dh_control.json"
OFFLINE_GUESSES = [("0.808517182457", "85.6993484854"), ("0.650830080610", "114.163342731")]


def offline_zeros(dps=60):
    mp.mp.dps = dps
    return [mp.findroot(wg.dh_function, mp.mpc(*g)) for g in OFFLINE_GUESSES]


def verify():
    mp.mp.dps = 30
    print(f"kappa = {mp.nstr(wg.dh_kappa(), 12)}")
    for s in [mp.mpf("0.3") + 7j, mp.mpf("0.9") + 23.5j]:
        rel = abs(wg.dh_completed(s) - wg.dh_completed(1 - s)) / abs(wg.dh_completed(s))
        print(f"functional equation at s={mp.nstr(s, 4)}: relative defect {mp.nstr(rel, 3)}")
    for r in offline_zeros(40):
        print(f"off-line zero {mp.nstr(r, 14)}  |f| = {mp.nstr(abs(wg.dh_function(r)), 3)}")
    c = wg.dh_coeffs(10)
    print("Lambda_f(6) != 0 (no Euler product):", mp.nstr(c[6], 6))


def spectra_point(fam, x, zeros):
    N = wg.cutoff(x)
    runs = []
    for dps in [3 * N + 60, int(1.4 * (3 * N + 60))]:
        try:
            (H, L, om), c, kw = wg.family_matrix(fam, x, N, dps)
            ev, V = wg.sym_eig(H, dps, vectors=True)
            r = dict(dps=dps, coefficient_dps=dps, eigenvalues=ev, parities=[wg.parity(v) for v in V],
                     lam=ev[0], lam2=ev[1], n_neg=sum(1 for e in ev if e < 0), attribution=[])
            if fam == "dh":
                for i, e in enumerate(ev):
                    if e >= 0:
                        break
                    v = wg.normalize(V[i])
                    r["attribution"].append(dict(
                        eig=mp.nstr(e, 5), parity=mp.nstr(wg.parity(v), 2),
                        E85=mp.nstr(wg.quadruplet_energy(v, L, om, zeros[0]), 5),
                        E114=mp.nstr(wg.quadruplet_energy(v, L, om, zeros[1]), 5)))
            runs.append(r)
        except (ArithmeticError, ValueError, RuntimeError) as error:
            runs.append(dict(dps=dps,status="numerical_failure",error_type=type(error).__name__,error=str(error)))
    if any(r.get("status") == "numerical_failure" for r in runs):
        return dict(schema_version=runtime.SCHEMA_VERSION,evidence_status=runtime.STATUS,
                    family=fam,x=x,N=N,status="numerical_failure",
                    attempts=[diagnostics.serialize(r,r["dps"]) for r in runs])
    a, b = runs
    floor = mp.power(10, -(a["dps"] - 25))
    differences = [abs(u-v)/max(abs(u), abs(v), floor) for u,v in zip(a["eigenvalues"],b["eigenvalues"])]
    parity_difference = max(abs(u-v) for u,v in zip(a["parities"],b["parities"]))
    stable = a["n_neg"] == b["n_neg"] and max(differences) < mp.mpf("1e-12") and parity_difference < mp.mpf("1e-12")
    return dict(schema_version=runtime.SCHEMA_VERSION, evidence_status=runtime.STATUS,
                status="precision_stable_spectrum" if stable else "unresolved_spectrum",
                attempts=[diagnostics.serialize(r,r["dps"]) for r in runs],
                eigenvalue_relative_differences=diagnostics.serialize(differences,b["dps"]),
                max_parity_difference=mp.nstr(parity_difference,b["dps"]), family=fam, x=x, N=N, lam_min=mp.nstr(b["lam"], 8), lam_2=mp.nstr(b["lam2"], 8),
                n_neg=b["n_neg"], two_precision_rel_diff=mp.nstr(abs(a["lam"] - b["lam"]) / max(abs(b["lam"]), floor), 3),
                attribution=b["attribution"])


def analyze_characteristic(x, N, dps):
    (H, L, om), c, kw = wg.family_matrix("dh", x, N, dps)
    ev, V = wg.sym_eig(H, dps, vectors=True)
    v = V[0]
    par = wg.parity(v)
    residual, relative = diagnostics.eigenpair_residual(H, ev[0], v)
    gap = ev[1] - ev[0]
    status = diagnostics.selection_status(gap, par, dps, diagnostics.matrix_norm(H), residual)
    out = dict(x=x, N=N, dps=dps, coefficient_dps=dps, L=L, E0=ev[0],
               energy_sign=int(mp.sign(ev[0])), gap=gap, eigenvalues=ev,
               ground_parity=par, eigenpair_residual_absolute=residual,
               eigenpair_residual_scaled=relative, selection_status=status)
    if status == "selected":
        out.update(wg.corrected_root_diagnostics(v, om, L, N, dps))
    return out


def characteristic_point(x, N=None, precisions=None):
    N = wg.cutoff(x) if N is None else N
    dps = 3 * N + 60
    precisions = precisions or [dps, int(1.4 * dps)]
    return diagnostics.precision_record(x, N, analyze_characteristic, precisions, family="dh")


def sampled_online_roots(lo=70, hi=130, step=0.02):
    """Sign-change samples only: may miss tangencies, even multiplicity or close roots."""
    if step <= 0 or hi <= lo:
        raise ValueError("Require step > 0 and hi > lo")
    mp.mp.dps = 20
    f = lambda t: mp.re(wg.dh_completed(mp.mpf(1) / 2 + 1j * t))
    ts = [lo + step * k for k in range(int((hi - lo) / step) + 1)]
    vals = [f(t) for t in ts]
    return [mp.nstr(mp.findroot(f, (ts[i], ts[i + 1]), solver="bisect"), 10)
            for i in range(len(ts) - 1) if vals[i] * vals[i + 1] < 0]


def plot(saved):
    import matplotlib.pyplot as plt
    import research_presentation as ui

    ui.use_style()
    fig, ax = plt.subplots(figsize=(7.5, 4.6))
    for fam, col, lab in [("lchi5", ui.BLUE, "L(s, χ) mod 5 (Euler product)"), ("dh", ui.ORANGE, "Davenport–Heilbronn")]:
        pts = sorted((r["x"], float(r["lam_min"])) for r in saved["spectra"] if r["family"] == fam and "lam_min" in r)
        xs = [math.log(p[0]) for p in pts]
        ys = [math.log10(abs(p[1])) for p in pts]
        ax.plot(xs, ys, "-", color=col, lw=1.2, label=lab)
        for X, Y, (_, lam) in zip(xs, ys, pts):
            ax.plot(X, Y, "o", color=col, mfc=col if lam > 0 else "white", mec=col, mew=1.6, ms=7, zorder=3)
    ax.axvline(math.log(215), color=ui.MUTED, ls="--", lw=1)
    ax.text(math.log(215) - 0.05, -125, "off-line zero at height 85.7\nsampled sign change (x = 200–230)", fontsize=8, color=ui.MUTED, ha="right")
    ax.set_xlabel("L = log x   (N = ⌈2L²⌉)")
    ax.set_ylabel("log₁₀ |least eigenvalue|")
    ax.legend(frameon=False, fontsize=8, loc="lower left")
    ui.save(fig, "experiment_15_dh_control.svg",
            title="Sampled Davenport–Heilbronn carriers develop negative directions",
            subtitle="Filled: positive least eigenvalue; open: negative. Paired parities are observed in these finite samples, not established as a general count.",
            source="Paper IV premises · Davenport–Heilbronn control · finite diagnostic · proves nothing")
    fig.savefig(HERE / "figures" / "experiment_15_dh_control.png", dpi=160, bbox_inches="tight")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", choices=["verify", "spectra", "characteristic", "plot"])
    ap.add_argument("--x", type=int, nargs="*")
    ap.add_argument("--quick", action="store_true", help="small x only (a few minutes)")
    args = ap.parse_args()
    if args.mode == "verify":
        verify()
        return
    saved = json.loads(OUT.read_text()) if OUT.exists() else {}
    if args.mode == "plot":
        plot(saved)
        return
    if args.mode == "spectra":
        zeros = offline_zeros(60)
        xs = args.x or ([20, 50] if args.quick else [20, 50, 100, 150, 200, 230, 260, 300, 500])
        rows = []
        for x in xs:
            for fam in (["dh", "lchi5"] if x not in (230, 260) else ["dh"]):
                try:
                    rows.append(spectra_point(fam, x, zeros))
                except (ArithmeticError, ValueError, RuntimeError) as error:
                    rows.append(dict(family=fam,x=x,N=wg.cutoff(x),status="numerical_failure",
                                     error_type=type(error).__name__,error=str(error)))
                print(json.dumps(rows[-1]), flush=True)
    else:
        xs = args.x or ([100] if args.quick else [200, 300, 500])
        rows = [characteristic_point(x) for x in xs]
        for r in rows:
            print(json.dumps(r))
        if not args.quick and not args.x:
            saved["sampled_online_roots"] = dict(method="sign-change samples; incomplete", lo=70, hi=130, step=0.02, roots=sampled_online_roots())
    saved[args.mode] = rows
    saved.setdefault("requested_carriers", {})[args.mode] = xs
    saved.update(schema_version=runtime.SCHEMA_VERSION, evidence_status=runtime.STATUS, environment=runtime.versions())
    runtime.write_json(OUT, saved)


if __name__ == "__main__":
    main()
