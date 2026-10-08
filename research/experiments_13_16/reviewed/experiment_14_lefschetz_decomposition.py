"""Experiment 14: a Castelnuovo-Severi / Lefschetz decomposition of the finite Weil form.

In Weil's function-field proof, d(D) = 2(D.e)(D.f) - D^2: a rank-2 hyperbolic
term from the trivial classes e, f, minus the intersection form, and Hodge index
says -D^2 has one negative direction, inside span{e, f}.

For zeta the polar term of the Weil form is the rank-2 hyperbolic form
    P = 2|c><c| - 2|s><s|,  c = cosh((t-L/2)/2) (even),  s = sinh((t-L/2)/2) (odd),
so W = P + J with J the archimedean, constant and prime terms (the analogue of
-D^2).  Checks, on the reflection-even and -odd blocks:

 1. Hodge-index signature: J has exactly one negative eigenvalue (even block).
 2. Hyperbolic plane: u = -sqrt2 J^{-1}c, w = -sqrt2 J^{-1}s satisfy u.u = 1,
    w.w = -1 in the form -J.  By Sherman-Morrison the defects are
    1/(2g-1) and 1/(1+2h), g = <c,W_e^{-1}c>, h = <s,W_o^{-1}s>; both equal
    E_0/(2<c,v_0>^2) (odd: with s and the odd ground) to leading order.
 3. Radical alignment: W^{-1}c and W^{-1}s against the even and odd grounds.
 4. Primitive gap: least eigenvalue of W compressed to c-perp (s-perp), placed
    on a log scale between E_0 and E_1 (interlacing position in [0, 1]).

For W > 0, J_even has one negative direction iff 2g > 1 and J_odd > 0.
Ground-mode approximations and alignment additionally need inverse-ground-mode
domination; this script measures that behavior but does not establish it uniformly.
Finite diagnostic along a predetermined family; proves nothing.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import research_runtime as runtime
import research_diagnostics as diagnostics

import mpmath as mp
from flint import acb, acb_mat, arb, arb_mat

from experiment_13_characteristic_mean import parity_blocks
from weil_general import cutoff

HERE = runtime.output_dir()
OUT = HERE / "results" / "experiment_14_lefschetz.json"


def polar_vectors(L, N, dps):
    """Components of c and s on U_j, j = -N..N (c real even, s = i*r with r odd)."""
    mp.mp.dps = dps
    b = L / 2
    g, r = [], []
    for j in range(-N, N + 1):
        w = 2 * mp.pi * j / L
        zp, zm = mp.mpf(1) / 2 + 1j * w, -mp.mpf(1) / 2 + 1j * w
        Ep, Em = (mp.exp(zp * b) - 1) / zp, (mp.exp(zm * b) - 1) / zm
        g.append((-1) ** j * 2 * (mp.re(Ep + Em) / 2) / mp.sqrt(L))
        r.append((-1) ** j * 2 * (mp.im(Ep - Em) / 2) / mp.sqrt(L))
    return g, r


def _A(v, dps):
    return arb(mp.nstr(v, dps + 5, strip_zeros=False))


def _eig(M, vec=False):
    n = M.nrows()
    C = acb_mat([[acb(M[i, j]) for j in range(n)] for i in range(n)])
    if vec:
        E, R = C.eig(right=True, algorithm="approx")
        o = sorted(range(n), key=lambda i: E[i].real.mid())
        return [E[i].real for i in o], [[R[k, i].real for k in range(n)] for i in o]
    return sorted((e.real for e in C.eig(algorithm="approx")), key=lambda t: t.mid()), None


def _dot(a, b):
    return sum((x * y for x, y in zip(a, b)), arb(0))


def _compress(W, c):
    n = len(c)
    nc = _dot(c, c).sqrt()
    v = list(c)
    v[0] = v[0] + nc if v[0].mid() >= 0 else v[0] - nc
    vv = _dot(v, v)
    Q = arb_mat([[(1 if i == j else 0) - 2 * v[i] * v[j] / vv for j in range(n)] for i in range(n)])
    B = Q * W * Q
    return arb_mat([[B[i, j] for j in range(1, n)] for i in range(1, n)])


def run(x, N, dps):
    from flint import ctx

    L, om, He, Ho = parity_blocks(x, N, dps)
    ctx.prec = int(dps * 3.33) + 32
    g, r = polar_vectors(L, N, dps)
    ce = [_A(g[N], dps)] + [_A(mp.sqrt(2) * g[N + k], dps) for k in range(1, N + 1)]
    so = [_A(mp.sqrt(2) * r[N + k], dps) for k in range(1, N + 1)]
    We = arb_mat([[_A(v, dps) for v in row] for row in He])
    Wo = arb_mat([[_A(v, dps) for v in row] for row in Ho])
    Ee, Ve = _eig(We, True)
    Eo, Vo = _eig(Wo, True)
    ye = We.solve(arb_mat([[t] for t in ce]))
    yo = Wo.solve(arb_mat([[t] for t in so]))
    ye = [ye[i, 0] for i in range(N + 1)]
    yo = [yo[i, 0] for i in range(N)]
    gg, hh = _dot(ce, ye), _dot(so, yo)
    Je = arb_mat([[We[i, j] - 2 * ce[i] * ce[j] for j in range(N + 1)] for i in range(N + 1)])
    Jo = arb_mat([[Wo[i, j] + 2 * so[i] * so[j] for j in range(N)] for i in range(N)])
    neg = lambda M: sum(1 for e in _eig(M)[0] if e.mid() < 0)
    du, dw = 1 / (2 * gg - 1), 1 / (1 + 2 * hh)
    pe = Ee[0] / (2 * _dot(ce, Ve[0]) ** 2)
    po = Eo[0] / (2 * _dot(so, Vo[0]) ** 2)
    sin2 = lambda y, v: 1 - _dot(y, v) ** 2 / (_dot(y, y) * _dot(v, v))
    mue, muo = _eig(_compress(We, ce))[0][0], _eig(_compress(Wo, so))[0][0]
    f = lambda a: mp.mpf(a.mid().str(dps, radius=False))
    l10 = lambda a: float(mp.log10(abs(f(a))))
    pos = lambda m, a, b: (l10(m) - l10(a)) / (l10(b) - l10(a))
    return dict(
        x=x, N=N, L=float(L), dps=dps, coefficient_dps=dps, evidence_status=runtime.STATUS,
        precision_status="single_precision_aggregate_diagnostic",
        raw_midpoints={key: mp.nstr(f(val), dps) for key,val in
                       dict(E0=Ee[0], E1=Ee[1], O0=Eo[0], O1=Eo[1],g=gg,h=hh,
                            defect_u=du,defect_w=dw,primitive_even=mue,primitive_odd=muo).items()},
        log10_E0=l10(Ee[0]), log10_E1=l10(Ee[1]), log10_O0=l10(Eo[0]), log10_O1=l10(Eo[1]),
        neg_J_even=neg(Je), neg_J_odd=neg(Jo),
        log10_defect_u=l10(du), log10_defect_w=l10(dw),
        defect_u_over_prediction=float(f(du / pe)), defect_w_over_prediction=float(f(dw / po)),
        overlap_c_ground=float(f(_dot(ce, Ve[0]) ** 2 / _dot(ce, ce))),
        overlap_s_oddground=float(f(_dot(so, Vo[0]) ** 2 / _dot(so, so))),
        log10_sin2_align_even=l10(sin2(ye, Ve[0])), log10_sin2_align_odd=l10(sin2(yo, Vo[0])),
        interlace_pos_even=pos(mue, Ee[0], Ee[1]), interlace_pos_odd=pos(muo, Eo[0], Eo[1]),
    )


def show(rows):
    print("    x     L  log10E0 | nJ-e nJ-o | defect u   w   ratio | c-ovl  s-ovl  | sin2 e/o      | prim e/o")
    for r in rows:
        print(f"{r['x']:5d} {r['L']:5.2f} {r['log10_E0']:8.1f} |   {r['neg_J_even']}    {r['neg_J_odd']}  | "
              f"{r['log10_defect_u']:7.1f} {r['log10_defect_w']:7.1f} {r['defect_u_over_prediction']:5.2f} | "
              f"{r['overlap_c_ground']:.3f}  {r['overlap_s_oddground']:.4f} | {r['log10_sin2_align_even']:6.1f} "
              f"{r['log10_sin2_align_odd']:6.1f} | {r['interlace_pos_even']:.3f} {r['interlace_pos_odd']:.3f}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--quick", action="store_true", help="x in {13, 30} (about a minute)")
    ap.add_argument("--x", type=int, nargs="*", help="explicit list of x")
    ap.add_argument("--from-json", action="store_true", help="print the saved table")
    args = ap.parse_args()
    if args.from_json:
        show(json.loads(OUT.read_text())["rows"])
        return
    xs = args.x or ([13, 30] if args.quick else [13, 30, 100, 200, 500, 1000])
    rows, records = [], []
    for x in xs:
        N = cutoff(x)
        d = 3 * N + 60
        record = dict(x=x,N=N,requested_precisions=[d,int(d*1.3)],attempts=[],
                      status="aggregate_diagnostic_only",evidence_status=runtime.STATUS)
        for digits in record["requested_precisions"]:
            try:
                result = run(x,N,digits)
                diagnostics.require_finite(result)
                record["attempts"].append(result)
            except (ArithmeticError,ValueError,RuntimeError) as error:
                record["attempts"].append(dict(dps=digits,status="numerical_failure",error=str(error)))
                record["status"] = "numerical_failure"
        if record["status"] != "numerical_failure":
            a, last = record["attempts"]
            keys = ["log10_defect_u", "log10_defect_w", "interlace_pos_even", "interlace_pos_odd"]
            record["aggregate_agreement"] = max(abs(a[k] - last[k]) for k in keys)
            rows.append(last)
        records.append(record)
        print(f"x={x}: {record['status']}",flush=True)
    show(rows)
    runtime.write_json(OUT,dict(schema_version=runtime.SCHEMA_VERSION,evidence_status=runtime.STATUS,
                               environment=runtime.versions(),requested_carriers=xs,records=records,rows=rows))


if __name__ == "__main__":
    main()
