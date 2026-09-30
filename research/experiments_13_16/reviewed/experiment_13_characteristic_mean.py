"""Experiment 13: the complete characteristic mean along a moving family.

Paper IV, eq. (12) and Theorems 1-3.  For the full Fourier matrix H on an
interval of length L = log x with cutoff N, suppose the least eigenvalue is
simple with an even eigenvector.  The anchor-normalized characteristic has
corrected roots +-eta_k (k = 1..N) and the untouched lattice xi_n = 2 pi n / L,
n > N.  With alpha = 1/4 the complete characteristic mean is

    mu = sum_k alpha^2/(eta_k^2 + alpha^2) + sum_{n>N} alpha^2/(xi_n^2 + alpha^2).

Paper IV proves that a uniform bound on mu along an unbounded selected family
gives compactness and zero retention.  This script measures mu.  It proves
nothing: it is a falsification test of the mean premise on finite carriers.

Method.
* Matrix entries: ``high_precision.mp_arithmetic_interpolation_and_derivative``
  and ``mp_gamma_multiplier`` (the Paper I Fourier matrix), at working
  precision ``dps``.
* Reflection splits H into even (N+1) and odd (N) blocks.  Selection is checked
  by requiring the even ground to lie strictly below the second even and the
  lowest odd eigenvalue.
* In the repository's (0, L) coordinates the endpoint functional is
  sum_j v_j / sqrt(L).  With v normalized there and v even,
      Q(w) = 1 + sum_k d_k/(w - p_k),  p_k = xi_k^2,  d_k = 2 v_k p_k / sqrt(L),
  so eta_k^2 are the eigenvalues of diag(p) - 1 d^T.
* The least eigenvalue decays exponentially in N (below 1e-250 at x = 1000,
  N = 96).  Insufficient precision silently produces spurious small or complex
  roots and a fake jump in mu, so each point is accepted only when two
  successive precisions pass numerical selection, residual and root-by-root checks.
* Lattice tail in closed form: sum_{n>=1} alpha^2/(xi_n^2+alpha^2)
  = (pi a coth(pi a) - 1)/2 with a = alpha L / (2 pi), minus the n <= N terms.

Reference value.  If the corrected roots were exactly the positive Xi zeros
gamma, the corrected part would be sum alpha^2/(gamma^2+alpha^2)
= (alpha/2) ell(alpha) = ell(1/4)/8, where ell = xi'/xi(1/2 + .) as in Paper II.

Backend: python-flint (arb/acb) if installed, otherwise mpmath (slower).
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import time
from pathlib import Path

import research_runtime as runtime
import research_diagnostics as diagnostics

import mpmath as mpm

from high_precision import mp_arithmetic_interpolation_and_derivative, mp_gamma_multiplier

try:  # optional fast backend
    from flint import acb, acb_mat, arb, ctx

    HAVE_FLINT = True
except ImportError:  # pragma: no cover
    HAVE_FLINT = False

ALPHA = mpm.mpf(1) / 4
HERE = runtime.output_dir()


# -----------------------------------------------------------------------------
# Finite computation
# -----------------------------------------------------------------------------


def parity_blocks(x: int, N: int, dps: int):
    """Even and odd blocks of the Fourier matrix, as mpmath nested lists."""

    mpm.mp.dps = dps
    L = mpm.log(mpm.mpf(x))
    om = [2 * mpm.pi * k / L for k in range(N + 1)]
    a, ad, g = [], [], []
    for w in om:
        value, derivative = mp_arithmetic_interpolation_and_derivative(mpm.mpf(x), w, dps=dps)
        a.append(value)
        ad.append(derivative)
        g.append(mp_gamma_multiplier(w, dps=dps))

    # a_x is odd in the frequency; a_x' and the Gamma multiplier are even.
    A = lambda j: a[j] if j >= 0 else -a[-j]
    W = lambda j: om[j] if j >= 0 else -om[-j]

    def h(j: int, k: int):
        if j == k:
            return g[abs(j)] + 2 * ad[abs(j)] / L
        return 2 / L * (A(j) - A(k)) / (W(j) - W(k))

    s2 = mpm.sqrt(2)
    even = [[None] * (N + 1) for _ in range(N + 1)]
    odd = [[None] * N for _ in range(N)]
    for i in range(N + 1):
        for j in range(i, N + 1):
            if i == j == 0:
                val = h(0, 0)
            elif i == 0:
                val = (h(0, j) + h(0, -j)) / s2
            else:
                val = (h(i, j) + h(i, -j) + h(-i, j) + h(-i, -j)) / 2
            even[i][j] = even[j][i] = val
    for i in range(1, N + 1):
        for j in range(i, N + 1):
            val = (h(i, j) - h(i, -j) - h(-i, j) + h(-i, -j)) / 2
            odd[i - 1][j - 1] = odd[j - 1][i - 1] = val
    return L, om, even, odd


def _eig_flint(rows, dps, vectors=False):
    to_arb = lambda t: arb(mpm.nstr(t, dps + 5, strip_zeros=False))
    conv = lambda v: acb(to_arb(mpm.re(v)), to_arb(mpm.im(v)))
    M = acb_mat([[conv(v) for v in r] for r in rows])
    if vectors:
        E, R = M.eig(right=True, algorithm="approx")
        E = [mpm.mpc(mpm.mpf(e.real.mid().str(dps, radius=False)),
                     mpm.mpf(e.imag.mid().str(dps, radius=False))) for e in E]
        R = [[mpm.mpc(mpm.mpf(R[i, j].real.mid().str(dps, radius=False)),
                      mpm.mpf(R[i, j].imag.mid().str(dps, radius=False)))
              for j in range(len(rows))] for i in range(len(rows))]
        return E, R
    E = M.eig(algorithm="approx")
    return [mpm.mpc(mpm.mpf(e.real.mid().str(dps, radius=False)),
                    mpm.mpf(e.imag.mid().str(dps, radius=False))) for e in E], None


def _eig_mpmath(rows, dps, vectors=False, symmetric=True):
    M = mpm.matrix(rows)
    if symmetric:
        E, V = mpm.eigsy(M)
        E = [E[i] for i in range(len(rows))]
        R = [[V[i, j] for j in range(len(rows))] for i in range(len(rows))]
        return E, (R if vectors else None)
    E = mpm.eig(M, left=False, right=False)
    return list(E), None


def analyze(x: int, N: int, dps: int) -> dict:
    """Resolve the full simple-even ground and all finite secular roots numerically."""
    if x <= 1 or N < 1 or dps < 40:
        raise ValueError("Require x > 1, N >= 1 and dps >= 40")
    t0 = time.time()
    if HAVE_FLINT:
        ctx.prec = int(dps * 3.33) + 32
    L, om, even, odd = parity_blocks(x, N, dps)
    eig = _eig_flint if HAVE_FLINT else _eig_mpmath
    Ee, Re = eig(even, dps, vectors=True)
    Eo, Ro = eig(odd, dps, vectors=True)
    diagnostics.require_finite([Ee, Eo, Re, Ro], "parity eigenpairs")
    scale = max(diagnostics.matrix_norm(even), diagnostics.matrix_norm(odd))
    if any(abs(mpm.im(e)) > diagnostics.quality_tolerance(dps) * max(1, scale) for e in Ee + Eo):
        raise ArithmeticError("Symmetric eigenvalues have unresolved imaginary parts")
    order_e = sorted(range(len(Ee)), key=lambda i: mpm.re(Ee[i]))
    order_o = sorted(range(len(Eo)), key=lambda i: mpm.re(Eo[i]))
    spectrum = sorted([(mpm.re(Ee[i]), 1, i) for i in order_e] +
                      [(mpm.re(Eo[i]), -1, i) for i in order_o])
    E0, parity, idx = spectrum[0]
    rows, vectors = (even, Re) if parity == 1 else (odd, Ro)
    u = [vectors[i][idx] for i in range(len(rows))]
    # Fix the arbitrary eigenvector phase; inspect before using real coordinates.
    phase = max(u, key=abs)
    u = [v / phase for v in u]
    vector_imag = max(abs(mpm.im(v)) for v in u)
    if vector_imag > diagnostics.quality_tolerance(dps):
        raise ArithmeticError("Symmetric eigenvector is not numerically real after phase normalization")
    u = [mpm.re(v) for v in u]
    norm = mpm.sqrt(mpm.fsum(v*v for v in u))
    u = [v / norm for v in u]
    residual, relative = diagnostics.eigenpair_residual(rows, E0, u)
    gap = spectrum[1][0] - E0
    status = diagnostics.selection_status(gap, parity, dps, scale, residual)
    result = dict(x=x, N=N, dps=dps, coefficient_dps=dps, L=L, E0=E0,
                  energy_sign=int(mpm.sign(E0)), gap=gap,
                  gap_even=mpm.re(Ee[order_e[1]] - Ee[order_e[0]]),
                  gap_odd=mpm.re(Eo[order_o[0]] - Ee[order_e[0]]),
                  ground_parity=parity, eigenpair_residual_absolute=residual,
                  eigenpair_residual_scaled=relative, vector_scaled_imag=vector_imag,
                  eigenvalues=[e[0] for e in spectrum], selection_status=status)
    if status == "selected":
        positive = [u[k] / mpm.sqrt(2) for k in range(1, N + 1)]
        full = list(reversed(positive)) + [u[0]] + positive
        full_om = [-w for w in reversed(om[1:])] + om
        def root_eig(matrix, digits):
            return (_eig_flint(matrix, digits)[0] if HAVE_FLINT else
                    _eig_mpmath(matrix, digits, symmetric=False)[0])
        result.update(diagnostics.roots_from_vector(full, full_om, L, N, dps, root_eig))
    result["seconds"] = time.time() - t0
    return result


def passes(r: dict) -> bool:
    """A resolved finite diagnostic, independent of the sign of E0."""
    return r.get("selection_status") == "selected" and r.get("root_status") == "resolved"


def precision_stable(x: int, N: int, tol="1e-12", max_dps: int = 1500) -> dict:
    """Keep all attempts; agreement is a numerical diagnostic, never a certificate."""
    dps, precisions = 3 * N + 60, []
    while dps <= max_dps:
        precisions.append(dps)
        dps = int(dps * 1.5)
    return diagnostics.precision_record(x, N, analyze, precisions, tol=tol)


# -----------------------------------------------------------------------------
# Diagnostics, output
# -----------------------------------------------------------------------------


def xi_limit() -> float:
    """ell(1/4)/8: the corrected mean if the corrected roots were the Xi zeros."""

    mpm.mp.dps = 30
    xi = lambda s: s * (s - 1) / 2 * mpm.pi ** (-s / 2) * mpm.gamma(s / 2) * mpm.zeta(s)
    return float(mpm.diff(xi, mpm.mpf(3) / 4) / xi(mpm.mpf(3) / 4) / 8)


def tracking(eta, zeros, tol=1e-6):
    k = 0
    while k < min(len(eta), len(zeros)) and abs(eta[k] - zeros[k]) < tol:
        k += 1
    return k, (float(zeros[k - 1]) if k else 0.0)


def row_of(record, zeros) -> dict:
    """Plot summary only; the JSON record retains every high-precision attempt."""
    if record["status"] != "precision_stable":
        raise ValueError("Only precision-stable carriers have a plotted mean")
    r = record["result"]
    with mpm.workdps(r["dps"]):
        eta = [mpm.mpf(v) for v in r["eta"]]
        k, height = tracking(eta, zeros)
        E0 = mpm.mpf(r["E0"])
        return dict(x=r["x"], N=r["N"], L=float(r["L"]), dps=r["dps"],
                    energy_sign=r["energy_sign"], log10_abs_E0=float(mpm.log10(abs(E0))) if E0 else None,
                    mu=float(r["mu"]), mu_corr=float(r["mu_corr"]), mu_lat=float(r["mu_lat"]),
                    eta1=float(eta[0]), tracked_zeros=k, tracked_height=height)


def write_csv(rows, path: Path) -> None:
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {path.name}")


def plot(family, sweep, limit, stem="experiment_13_characteristic_mean"):
    import matplotlib.pyplot as plt
    import research_presentation as ui

    ui.use_style()
    fig, axes = plt.subplots(1, 3, figsize=(11.5, 3.6))

    ax = axes[0]
    L = [r["L"] for r in family]
    ax.plot(L, [1e3 * r["mu"] for r in family], "o-", color=ui.BLUE, label="complete mean μ")
    ax.plot(L, [1e3 * r["mu_corr"] for r in family], "s-", color=ui.ORANGE, ms=4, label="corrected roots")
    ax.plot(L, [1e3 * r["mu_lat"] for r in family], "^-", color=ui.AQUA, ms=4, label="untouched lattice")
    ax.axhline(1e3 * limit, color=ui.MUTED, ls="--", lw=1)
    ax.text(L[-1], 1e3 * limit * 0.97, "ℓ(1/4)/8: conditional Ξ-zero comparison",
            ha="right", va="top", fontsize=7.5, color=ui.MUTED)
    ax.set_xlabel("L = log x   (N = ⌈2L²⌉)")
    ax.set_ylabel("× 10⁻³")
    ax.set_ylim(0, 1e3 * max(r["mu"] for r in family) * 1.25)
    ax.legend(frameon=False, fontsize=8, loc="lower right")
    ax.set_title("Mean along the family", fontsize=10)

    ax = axes[1]
    N = [r["N"] for r in sweep]
    ax.plot(N, [1e3 * r["mu"] for r in sweep], "o-", color=ui.BLUE, label="μ")
    ax.plot(N, [1e3 * r["mu_corr"] for r in sweep], "s-", color=ui.ORANGE, ms=4, label="corrected")
    ax.plot(N, [1e3 * r["mu_lat"] for r in sweep], "^-", color=ui.AQUA, ms=4, label="lattice")
    ax.axhline(1e3 * limit, color=ui.MUTED, ls="--", lw=1)
    ax.set_xscale("log")
    ax.set_xlabel(f"cutoff N   (x = {sweep[0]['x']})")
    ax.legend(frameon=False, fontsize=8)
    ax.set_title("Mean against the cutoff", fontsize=10)

    ax = axes[2]
    ax.plot(L, [r["tracked_height"] for r in family], "o-", color=ui.BLUE, label="height of Ξ zeros matched to 1e-6")
    ax2 = ax.twinx()
    ax2.plot(L, [-r["log10_abs_E0"] if r["log10_abs_E0"] is not None else float("nan") for r in family], "s--", color=ui.ORANGE, ms=4, label="−log₁₀ |E|")
    ax.set_xlabel("L = log x")
    ax.set_ylabel("tracked height")
    ax2.set_ylabel("−log₁₀ |least eigenvalue|", color=ui.ORANGE)
    ax.set_title("Zero tracking and precision demand", fontsize=10)
    h1, l1 = ax.get_legend_handles_labels()
    h2, l2 = ax2.get_legend_handles_labels()
    ax.legend(h1 + h2, l1 + l2, frameon=False, fontsize=8, loc="upper left")

    last = family[-1]
    path = ui.save(
        fig, f"{stem}.svg",
        title="Sampled characteristic means: corrected roots and a nonzero lattice tail",
        subtitle=(f"x ≤ {last['x']}: μ ≤ {max(r['mu'] for r in family):.5f}; corrected part "
                  f"{last['mu_corr']:.5f} vs ℓ(1/4)/8 = {limit:.5f}; plotted points passed numerical selection "
                  "and agreed at two precisions."),
        source="Paper IV · Numerical diagnostic, uncertified · finite samples only",
    )
    fig.savefig(HERE / "figures" / f"{stem}.png", dpi=160, bbox_inches="tight")
    return path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--quick", action="store_true", help="x <= 50, still a research sweep")
    parser.add_argument("--c", type=float, default=2.0)
    parser.add_argument("--x", type=int, nargs="+", help="explicit carriers; omit cutoff sweep")
    parser.add_argument("--N", type=int, help="fixed cutoff, with --x")
    parser.add_argument("--max-dps", type=int, default=1500)
    parser.add_argument("--no-plot", action="store_true")
    parser.add_argument("--from-json", action="store_true", help="replot generated reviewed rows")
    args = parser.parse_args()
    stem = HERE / "results" / "characteristic_mean"
    if args.from_json:
        saved = json.loads(stem.with_suffix(".json").read_text())
        if saved["family"] and saved["sweep"]:
            plot(saved["family"], saved["sweep"], saved["xi_limit"])
        return
    if args.c <= 0 or (args.N is not None and (args.N < 1 or not args.x)) or (args.x and any(x <= 1 for x in args.x)):
        parser.error("Require c > 0, x > 1, and N >= 1 only with --x")
    mpm.mp.dps = 30
    xs = args.x or [2, 3, 5, 8, 13, 20, 30, 50] + ([] if args.quick else [100, 200, 500, 1000])
    family_records = [precision_stable(x, args.N or max(4, math.ceil(args.c * math.log(x)**2)),
                                       max_dps=args.max_dps) for x in xs]
    x_sweep = 30 if args.quick else 100
    Ns = [] if args.x else [3, 5, 8, 11, 16, 21, 32] + ([] if args.quick else [42, 64])
    sweep_records = [precision_stable(x_sweep, N, max_dps=args.max_dps) for N in Ns]
    max_roots = max((r["N"] for r in family_records + sweep_records), default=0)
    zeros = [mpm.im(mpm.zetazero(n)) for n in range(1, max_roots + 1)]
    family = [row_of(r, zeros) for r in family_records if r["status"] == "precision_stable"]
    sweep = [row_of(r, zeros) for r in sweep_records if r["status"] == "precision_stable"]
    limit = xi_limit()
    saved = dict(schema_version=runtime.SCHEMA_VERSION, evidence_status=runtime.STATUS,
                 requested_family=xs, requested_sweep=Ns, family_records=family_records,
                 sweep_records=sweep_records, family=family, sweep=sweep, xi_limit=limit)
    runtime.write_json(stem.with_suffix(".json"), saved)
    for rows, suffix in ((family, "family"), (sweep, "cutoff")):
        if rows:
            write_csv(rows, stem.with_name(f"characteristic_mean_{suffix}.csv"))
    if not args.no_plot and family and sweep:
        plot(family, sweep, limit)
    for record in family_records + sweep_records:
        print(f"x={record['x']} N={record['N']}: {record['status']}")


if __name__ == "__main__":
    main()
