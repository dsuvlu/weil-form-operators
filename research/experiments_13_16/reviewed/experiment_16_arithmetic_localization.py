"""Experiment 16: where does the Euler-product signal live in the finite Weil form?

Modes (each a finite diagnostic; none proves anything):

  surgery        DH with one coefficient property changed at a time, same
                 archimedean part: S1 prime-power support only, S2 Lambda_f
                 clipped to >= 0, S3 the Euler product built from DH's prime
                 values.  S1-S3 break the functional equation.
  decomposition  exact split of W(v) = archimedean + prime powers + composites
                 for DH's negative directions, and the same v under L(chi)'s form.
  residues       per-prime-power energies e_n = -c_n q_v(log n) (q_v = the state's
                 autocorrelation) and the partial residue
                 R(X) = polar + archimedean - sum_{n<=X} for the lowest even and
                 odd states of a balanced form (zeta, chi4 = L(s,chi_-4), dh).
  cramer         zeta's archimedean and polar parts with the true primes below T
                 and Cramer-random masses (probability 1/log n, weight log n) above.

Readings recorded in results/experiment_16_localization.json:
  * surgery and Cramer forms fail at order one (the functional equation is
    the scaffold of the near-null structure);
  * DH's negativity is a 40+-digit cancellation between O(1) archimedean,
    prime-power and composite energies;
  * the sign coherence of zeta's near-null prime energies is nodal (the even
    ground has no sign change); the edge settlement (the last masses cut the
    residue by orders of magnitude and the last one fixes its sign) appears in
    every balanced form tested, DH included, so these particular samples do not distinguish the presence of an Euler product.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from pathlib import Path

import research_runtime as runtime
import research_diagnostics as diagnostics

import mpmath as mp

import weil_general as wg

HERE = runtime.output_dir()
OUT = HERE / "results" / "experiment_16_localization.json"


def _prec(x):
    N = wg.cutoff(x)
    return N, 3 * N + 60


# ---- surgery ------------------------------------------------------------------


def surgery_coeffs(variant, x):
    c = wg.dh_coeffs(x)
    if variant == "S0":
        return c
    if variant == "S1":
        return {n: v for n, v in c.items() if wg.prime_power(n)}
    if variant == "S2":
        return {n: v for n, v in c.items() if v > 0}
    if variant == "S3":
        out = {}
        for n in range(2, int(math.ceil(x))):
            t = wg.prime_power(n)
            if t and n < x and wg.dh_a(t[0]) != 0:
                out[n] = wg.dh_a(t[0]) ** t[1] * mp.log(t[0]) / mp.sqrt(n)
        return out


def surgery(x):
    N, dps = _prec(x)
    rows = []
    for variant in ["S0", "S1", "S2", "S3"]:
        res = []
        failures = []
        for d in [dps, int(1.4 * dps)]:
            try:
                mp.mp.dps = d
                c = surgery_coeffs(variant, x)
                (H, L, om), _, _ = wg.family_matrix("dh", x, N, d, coeffs=c)
                ev, _ = wg.sym_eig(H, d)
                res.append((ev, sum(1 for e in ev if e < 0), d))
            except (ArithmeticError,ValueError,RuntimeError) as error:
                failures.append(dict(dps=d,status="numerical_failure",error=str(error)))
        if failures:
            attempts = [dict(dps=d,eigenvalues=diagnostics.serialize(ev,d),n_neg=n) for ev,n,d in res] + failures
            rows.append(dict(variant=variant,x=x,N=N,status="numerical_failure",precision_stable=False,
                             attempts=sorted(attempts,key=lambda r:r["dps"]),evidence_status=runtime.STATUS))
            continue
        (a, na, da), (b, nb, db) = res
        floor = mp.power(10, -(da - 25))
        differences = [abs(u-v)/max(abs(u),abs(v),floor) for u,v in zip(a,b)]
        rows.append(dict(variant=variant, x=x, N=N, lam_min=mp.nstr(b[0], db), n_neg=nb,
                         evidence_status=runtime.STATUS, coefficient_precisions=[da,db],
                         attempts=[dict(dps=d,eigenvalues=diagnostics.serialize(ev,d),n_neg=n) for ev,n,d in res],
                         max_eigenvalue_relative_difference=mp.nstr(max(differences),db),
                         precision_stable=bool(na == nb and max(differences) < mp.mpf("1e-12"))))
        print(f"{variant} x={x}: {nb} negative eigenvalues; precision_stable={rows[-1]['precision_stable']}", flush=True)
    return rows


# ---- decomposition --------------------------------------------------------------


def decomposition(x):
    N, dps = _prec(x)
    mp.mp.dps = dps
    (H, L, om), c, kw = wg.family_matrix("dh", x, N, dps)
    ev, V = wg.sym_eig(H, dps, vectors=True)
    A = wg.family_matrix("dh", x, N, dps, coeffs={})[0][0]
    Hpp = wg.family_matrix("dh", x, N, dps, coeffs={n: v for n, v in c.items() if wg.prime_power(n)})[0][0]
    Hco = wg.family_matrix("dh", x, N, dps, coeffs={n: v for n, v in c.items() if not wg.prime_power(n)})[0][0]
    Hlc = wg.family_matrix("lchi5", x, N, dps)[0][0]
    rows = []
    for i, e in enumerate(ev):
        if e >= 0:
            break
        v = wg.normalize(V[i])
        a = wg.quad(A, v)
        pp, co = wg.quad(Hpp, v) - a, wg.quad(Hco, v) - a
        rows.append(dict(x=x, eig=mp.nstr(e, dps), archimedean=mp.nstr(a, dps), prime_powers=mp.nstr(pp, dps),
                         composites=mp.nstr(co, dps), closure=mp.nstr(a + pp + co - e, dps),
                         dps=dps, coefficient_dps=dps, evidence_status=runtime.STATUS,
                         same_vector_under_Lchi=mp.nstr(wg.quad(Hlc, v), 5)))
        print(json.dumps(rows[-1]), flush=True)
    return rows


# ---- residues -------------------------------------------------------------------


def residue_trails(fam, x, coeffs=None, keep_last=5, marks=(2, 3, 5, 11, 31, 101, 199, 307, 401, 499)):
    N, dps = _prec(x)
    mp.mp.dps = dps
    (H, L, om), c, kw = wg.family_matrix(fam, x, N, dps, coeffs=coeffs)
    base = wg.family_matrix(fam, x, N, dps, coeffs={})[0][0]  # polar + archimedean
    ev, V = wg.sym_eig(H, dps, vectors=True)
    first = {}
    for i, v in enumerate(V):
        first.setdefault("even" if wg.parity(v) > 0 else "odd", i)
        if len(first) == 2:
            break
    out = dict(family=fam, x=x, N=N, dps=dps, evidence_status=runtime.STATUS,
               precision_status="single_precision_diagnostic", lam_min=mp.nstr(ev[0], 4), n_neg=sum(1 for e in ev if e < 0))
    for p, i in first.items():
        v = wg.normalize(V[i])
        R = wg.quad(base, v)
        ns = sorted(c)
        trail, signs = [], []
        for n in ns:
            e_n = -c[n] * wg.qv(v, om, L, mp.log(n))
            signs.append(1 if e_n > 0 else -1)
            R += e_n
            if n in marks or n in ns[-keep_last:]:
                trail.append((n, mp.nstr(R, 3)))
        out[p] = dict(eig=mp.nstr(ev[i], 4), trail=trail, positive_terms=signs.count(1), negative_terms=signs.count(-1))
    print(json.dumps(out), flush=True)
    return out


def cramer_coeffs(seed, x, T, *, dps):
    """Build masses at explicit precision, independent of prior calls."""
    mp.mp.dps = dps
    true = wg.zeta_coeffs(x)
    rng = random.Random(seed)
    c = {n: v for n, v in true.items() if n <= T}
    for n in range(T + 1, x):
        if rng.random() < 1 / math.log(n):
            c[n] = mp.log(n) / mp.sqrt(n)
    return c


# ---- plot -------------------------------------------------------------------------


def plot(saved):
    import matplotlib.pyplot as plt
    import research_presentation as ui

    ui.use_style()
    cases = [("zeta", 300, "odd", ui.BLUE, "ζ, x = 300 (odd)"), ("zeta", 1000, "odd", ui.AQUA, "ζ, x = 1000 (odd)"),
             ("chi4", 300, "odd", ui.ORANGE, "L(s, χ₋₄), x = 300 (odd)"), ("dh", 200, "even", ui.MUTED, "DH, x = 200 (even)")]
    fig, ax = plt.subplots(figsize=(7.5, 4.6))
    for fam, x, p, col, lab in cases:
        rec = next((r for r in saved.get("residues", []) if r["family"] == fam and r["x"] == x), None)
        if not rec or p not in rec:
            continue
        tr = rec[p]["trail"][-4:]  # the last four masses below x
        k = list(range(-len(tr) + 1, 1))
        vals = [float(v) for _, v in tr]
        ys = [math.log10(abs(v)) - math.log10(abs(vals[-1])) for v in vals]
        ax.plot(k, ys, "-", color=col, lw=1.3, label=lab)
        for kk, y, v in zip(k, ys, vals):
            ax.plot(kk, y, "o", color=col, mfc=col if v > 0 else "white", mec=col, mew=1.5, ms=7, zorder=3)
    ax.set_xticks([-3, -2, -1, 0])
    ax.set_xticklabels(["after 4th-last", "after 3rd-last", "after 2nd-last", "after last = final"])
    ax.set_xlabel("partial residue R(X) as the last four masses below x are added")
    ax.set_ylabel("log₁₀ |R| relative to the final residue")
    ax.legend(frameon=False, fontsize=8)
    ui.save(fig, "experiment_16_edge_settlement.svg",
            title="Selected finite carriers show cancellation in the last few sampled masses",
            subtitle="Filled: residue positive; open: negative. Observed with and without an Euler product; this test does not establish an arithmetic distinction.",
            source="Experiment 16 · residues mode · finite diagnostic · proves nothing")
    fig.savefig(HERE / "figures" / "experiment_16_edge_settlement.png", dpi=160, bbox_inches="tight")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", choices=["surgery", "decomposition", "residues", "cramer", "plot"])
    ap.add_argument("--x", type=int)
    ap.add_argument("--family", default="zeta", choices=["zeta", "chi4", "dh"])
    ap.add_argument("--seeds", type=int, nargs="*", default=[1, 2, 3, 4])
    ap.add_argument("--T", type=int, default=30)
    ap.add_argument("--save", action="store_true", help="append rows to the results file")
    args = ap.parse_args()
    saved = json.loads(OUT.read_text()) if OUT.exists() else {}
    if args.mode == "plot":
        plot(saved)
        return
    if args.mode == "surgery":
        rows = surgery(args.x or 300)
    elif args.mode == "decomposition":
        rows = decomposition(args.x or 300)
    elif args.mode == "residues":
        rows = [residue_trails(args.family, args.x or 300)]
    else:
        x = args.x or 300
        rows = [dict(seed=s, T=args.T, coefficient_dps=_prec(x)[1], **residue_trails("zeta", x, coeffs=cramer_coeffs(s, x, args.T, dps=_prec(x)[1]), keep_last=3))
                for s in args.seeds]
    if args.save:
        saved.setdefault(args.mode, []).extend(rows if isinstance(rows, list) else [rows])
        saved.update(schema_version=runtime.SCHEMA_VERSION, evidence_status=runtime.STATUS, environment=runtime.versions())
        runtime.write_json(OUT, saved)


if __name__ == "__main__":
    main()
