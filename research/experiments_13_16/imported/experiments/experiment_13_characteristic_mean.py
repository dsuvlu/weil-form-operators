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
  successive precisions both pass the selection check and agree on mu.
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

import mpmath as mpm

from high_precision import mp_arithmetic_interpolation_and_derivative, mp_gamma_multiplier

try:  # optional fast backend
    from flint import acb, acb_mat, arb, ctx

    HAVE_FLINT = True
except ImportError:  # pragma: no cover
    HAVE_FLINT = False

ALPHA = mpm.mpf(1) / 4
HERE = Path(__file__).parent


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
        E = [mpm.mpf(e.real.mid().str(dps, radius=False)) for e in E]
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
    t0 = time.time()
    if HAVE_FLINT:
        ctx.prec = int(dps * 3.33) + 32
    L, om, even, odd = parity_blocks(x, N, dps)
    eig = _eig_flint if HAVE_FLINT else _eig_mpmath

    Ee, R = eig(even, dps, vectors=True)
    Eo, _ = eig(odd, dps)
    Ee = [mpm.re(e) for e in Ee]
    order = sorted(range(len(Ee)), key=lambda i: Ee[i])
    E0, E1 = Ee[order[0]], Ee[order[1]]
    O0 = min(mpm.re(e) for e in Eo)

    u = [R[i][order[0]] for i in range(N + 1)]
    sqL = mpm.sqrt(L)
    vk = [u[k] / mpm.sqrt(2) for k in range(1, N + 1)]
    endpoint = (u[0] + 2 * mpm.fsum(vk)) / sqL
    vk = [q / endpoint for q in vk]
    p = [om[k] ** 2 for k in range(1, N + 1)]
    d = [2 * vk[k] * p[k] / sqL for k in range(N)]
    M = [[(p[i] if i == j else 0) - d[j] for j in range(N)] for i in range(N)]
    w = eig(M, dps)[0] if HAVE_FLINT else _eig_mpmath(M, dps, symmetric=False)[0]
    w = sorted(w, key=lambda z: mpm.re(z))

    al2 = ALPHA**2
    eta2 = [mpm.re(z) for z in w]
    max_imag = max(abs(mpm.im(z)) for z in w)
    mu_corr = mpm.fsum(al2 / (e + al2) for e in eta2)
    a = ALPHA * L / (2 * mpm.pi)
    mu_lat = (mpm.pi * a * mpm.coth(mpm.pi * a) - 1) / 2 - mpm.fsum(al2 / (q + al2) for q in p)
    return dict(
        x=x, N=N, dps=dps, L=L, E0=E0, gap_even=E1 - E0, gap_odd=O0 - E0,
        max_imag=max_imag, min_eta2=eta2[0],
        eta=[mpm.sqrt(e) if e > 0 else mpm.nan for e in eta2],
        mu_corr=mu_corr, mu_lat=mu_lat, mu=mu_corr + mu_lat, seconds=time.time() - t0,
    )


def passes(r: dict) -> bool:
    """Selection resolved above working precision; corrected roots real and positive."""

    floor = mpm.mpf(10) ** (-(r["dps"] - 25))
    return bool(
        r["E0"] > floor and r["gap_even"] > floor and r["gap_odd"] > floor
        and r["min_eta2"] > 0 and r["max_imag"] < 1e-6 * max(1, r["min_eta2"])
    )


def certified(x: int, N: int, tol: float = 1e-12, max_dps: int = 1500) -> dict:
    """Raise precision until two successive passing runs agree on mu."""

    dps, prev = 3 * N + 60, None
    while dps <= max_dps:
        r = analyze(x, N, dps)
        ok = passes(r)
        print(f"   x={x:5d} N={N:3d} dps={dps:4d} pass={ok!s:5} mu={mpm.nstr(r['mu'], 12)}  "
              f"[{r['seconds']:.1f}s]", flush=True)
        if ok and prev is not None and passes(prev) and abs(r["mu"] - prev["mu"]) <= tol * r["mu"]:
            return r
        prev, dps = r, int(dps * 1.5)
    raise RuntimeError(f"no stable result for x={x}, N={N} below dps={max_dps}")


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


def row_of(r, zeros) -> dict:
    k, height = tracking(r["eta"], zeros)
    return dict(
        x=r["x"], N=r["N"], L=float(r["L"]), dps=r["dps"],
        log10_E0=float(mpm.log10(r["E0"])),
        log10_gap_even=float(mpm.log10(r["gap_even"])),
        log10_gap_odd=float(mpm.log10(r["gap_odd"])),
        mu=float(r["mu"]), mu_corr=float(r["mu_corr"]), mu_lat=float(r["mu_lat"]),
        eta1=float(r["eta"][0]), tracked_zeros=k, tracked_height=height,
    )


def write_csv(rows, path: Path) -> None:
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {path.name}")


def plot(family, sweep, limit, stem="experiment_13_characteristic_mean"):
    import matplotlib.pyplot as plt
    import presentation as ui

    ui.use_style()
    fig, axes = plt.subplots(1, 3, figsize=(11.5, 3.6))

    ax = axes[0]
    L = [r["L"] for r in family]
    ax.plot(L, [1e3 * r["mu"] for r in family], "o-", color=ui.BLUE, label="complete mean μ")
    ax.plot(L, [1e3 * r["mu_corr"] for r in family], "s-", color=ui.ORANGE, ms=4, label="corrected roots")
    ax.plot(L, [1e3 * r["mu_lat"] for r in family], "^-", color=ui.AQUA, ms=4, label="untouched lattice")
    ax.axhline(1e3 * limit, color=ui.MUTED, ls="--", lw=1)
    ax.text(L[-1], 1e3 * limit * 0.97, "ℓ(1/4)/8: ceiling if corrected roots = Ξ zeros",
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
    ax2.plot(L, [-r["log10_E0"] for r in family], "s--", color=ui.ORANGE, ms=4, label="−log₁₀ E")
    ax.set_xlabel("L = log x")
    ax.set_ylabel("tracked height")
    ax2.set_ylabel("−log₁₀ least eigenvalue", color=ui.ORANGE)
    ax.set_title("Zero tracking and precision demand", fontsize=10)
    h1, l1 = ax.get_legend_handles_labels()
    h2, l2 = ax2.get_legend_handles_labels()
    ax.legend(h1 + h2, l1 + l2, frameon=False, fontsize=8, loc="upper left")

    last = family[-1]
    path = ui.save(
        fig, f"{stem}.svg",
        title="The complete characteristic mean stays small and flattens toward its Ξ-zero value",
        subtitle=(f"x ≤ {last['x']}: μ ≤ {max(r['mu'] for r in family):.5f}; corrected part "
                  f"{last['mu_corr']:.5f} vs ℓ(1/4)/8 = {limit:.5f}; every point passed selection "
                  "and agreed at two precisions."),
        source="Paper IV, eq. (12) and Theorems 1-3 · exploratory moving experiment · proves nothing",
    )
    fig.savefig(HERE / "figures" / f"{stem}.png", dpi=160, bbox_inches="tight")
    return path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--quick", action="store_true", help="x <= 50 only (about a minute)")
    parser.add_argument("--c", type=float, default=2.0, help="family cutoff N = ceil(c L^2)")
    parser.add_argument("--from-json", action="store_true", help="replot saved rows without recomputing")
    args = parser.parse_args()

    stem = HERE / "results" / "characteristic_mean"
    if args.from_json:
        saved = json.loads(stem.with_suffix(".json").read_text())
        plot(saved["family"], saved["sweep"], saved["xi_limit"])
        return

    print(f"backend: {'python-flint' if HAVE_FLINT else 'mpmath (slow)'}")
    mpm.mp.dps = 30
    zeros = [mpm.im(mpm.zetazero(n)) for n in range(1, 161)]

    xs = [2, 3, 5, 8, 13, 20, 30, 50] + ([] if args.quick else [100, 200, 500, 1000])
    family = [row_of(certified(x, max(4, math.ceil(args.c * math.log(x) ** 2))), zeros) for x in xs]
    x_sweep = 30 if args.quick else 100
    Ns = [3, 5, 8, 11, 16, 21, 32] + ([] if args.quick else [42, 64])
    sweep = [row_of(certified(x_sweep, N), zeros) for N in Ns]

    limit = xi_limit()
    write_csv(family, stem.with_name("characteristic_mean_family.csv"))
    write_csv(sweep, stem.with_name("characteristic_mean_cutoff.csv"))
    stem.with_suffix(".json").write_text(json.dumps(dict(family=family, sweep=sweep, xi_limit=limit), indent=1))
    plot(family, sweep, limit)

    print(f"\nxi-zero reference ell(1/4)/8 = {limit:.8f}")
    print("    x    L     N   log10 E   mu          corrected   lattice     zeros tracked")
    for r in family:
        print(f"{r['x']:5d} {r['L']:5.2f} {r['N']:4d} {r['log10_E0']:8.1f}   {r['mu']:.8f}  "
              f"{r['mu_corr']:.8f}  {r['mu_lat']:.8f}  {r['tracked_zeros']:3d} (to {r['tracked_height']:.1f})")


if __name__ == "__main__":
    main()
