"""Shared high-precision machinery for experiments 13-16.

* ``weil_matrix`` builds the localized Weil matrix of a degree-1 L-function in
  the repository's Fourier basis U_j(t) = e^{i w_j t}/sqrt(L) on (0, L), from the
  explicit formula (Iwaniec-Kowalski, Thm 5.12):
      archimedean symbol   log q - log pi + Re psi(1/4 + a/2 + i r/2),
      prime side           c_n = Lambda_F(n)/sqrt(n)  (real or complex),
      polar term           2 cosh(y/2)  (zeta only).
  With a=0, q=1, polar=True and the von Mangoldt coefficients it reproduces
  ``high_precision.mp_build_weil_matrix`` (checked to 1e-79 at 80 digits;
  ``check_against_repo`` repeats the comparison).
* Coefficient families: zeta, L(s, chi) for the odd quartic character mod 5,
  L(s, chi_-4), and the Davenport-Heilbronn function built from chi mod 5.
* Linear algebra through python-flint (arb/acb) at the working precision.

Requires the isolated pinned research requirements; leave the release lock unchanged.
"""

from __future__ import annotations

import math

import research_runtime as runtime
import research_diagnostics as diagnostics

import mpmath as mp
from flint import acb, acb_mat, arb, ctx

ALPHA = mp.mpf(1) / 4


# -----------------------------------------------------------------------------
# Matrix
# -----------------------------------------------------------------------------


def lattice(x, N):
    L = mp.log(mp.mpf(x))
    return L, [2 * mp.pi * j / L for j in range(-N, N + 1)]


def weil_matrix(x, N, dps, c, a=0, logq=0, polar=False):
    """Full (2N+1)x(2N+1) real symmetric Weil matrix; c maps n -> Lambda_F(n)/sqrt(n)."""

    mp.mp.dps = dps
    L, om = lattice(x, N)
    b = mp.mpf(1) / 4 + mp.mpf(a) / 2
    ys = {n: mp.log(n) for n in c}
    tol = mp.mpf(10) ** (-dps - 5)

    def lam_sum(f):  # sum over trivial-zero offsets lambda_k = 2(b+k), k >= 0
        s, k = mp.mpf(0), 0
        while True:
            lam = 2 * (b + k)
            s += f(lam)
            if mp.exp(-lam * L) < tol:
                return s
            k += 1

    def S_w(w):  # int_0^L w_b(y) sin(wy) dy at lattice frequencies
        return mp.im(mp.psi(0, b + 1j * w / 2)) / 2 - lam_sum(lambda l: w * mp.exp(-l * L) / (l * l + w * w))

    def A_diag(w):
        tail = 2 * lam_sum(lambda l: mp.exp(-l * L) * l / (l * l + w * w))
        corr = lam_sum(lambda l: mp.re(mp.exp(-(l - 1j * w) * L) * (1 + (l - 1j * w) * L) / (l - 1j * w) ** 2))
        ywt = (2 / L) * (mp.re(mp.psi(1, b - 1j * w / 2)) / 4 - corr)
        return logq - mp.log(mp.pi) + mp.re(mp.psi(0, b + 1j * w / 2)) + tail + ywt

    half = mp.mpf(1) / 2

    def S_P(w):
        return mp.im(sum((mp.exp(z * L) - 1) / z for z in (half + 1j * w, -half + 1j * w)))

    def P_diag(w):
        tot = 0
        for z in (half + 1j * w, -half + 1j * w):
            I0 = (mp.exp(z * L) - 1) / z
            I1 = (mp.exp(z * L) * (z * L - 1) + 1) / z**2
            tot += 2 * mp.re(I0 - I1 / L)
        return tot

    E = [mp.fsum(cn * mp.exp(-1j * w * ys[n]) for n, cn in c.items()) for w in om]
    Sw = [S_w(w) for w in om]
    SP = [S_P(w) for w in om] if polar else None
    n = len(om)
    H = [[None] * n for _ in range(n)]
    for i in range(n):
        wi = om[i]
        d = A_diag(wi) - 2 * mp.fsum((1 - ys[m] / L) * mp.re(cn * mp.exp(-1j * wi * ys[m])) for m, cn in c.items())
        if polar:
            d += P_diag(wi)
        H[i][i] = d
        for k in range(i + 1, n):
            D = om[k] - om[i]
            v = (2 / L) * (Sw[k] - Sw[i]) / D - (2 / (L * D)) * mp.im(E[k] - E[i])
            if polar:
                v -= (2 / L) * (SP[k] - SP[i]) / D
            H[i][k] = H[k][i] = v
    return H, L, om


def check_against_repo(x=50, N=8, dps=80):
    from high_precision import mp_build_weil_matrix

    Hm, _, _ = mp_build_weil_matrix(x, N, dps=dps)
    Hg, _, _ = weil_matrix(x, N, dps, zeta_coeffs(x), polar=True)
    return max(abs(Hm[i, j] - Hg[i][j]) for i in range(2 * N + 1) for j in range(2 * N + 1))


def cutoff(x, c=2.0):
    return max(4, math.ceil(c * math.log(x) ** 2))


# -----------------------------------------------------------------------------
# Coefficient families (evaluate at the working precision!)
# -----------------------------------------------------------------------------


def prime_power(n):
    """(p, k) if n = p^k with k >= 1, else None."""
    for p in range(2, n + 1):
        if n % p == 0:
            k, m = 0, n
            while m % p == 0:
                m //= p
                k += 1
            return (p, k) if m == 1 else None
    return None


def zeta_coeffs(x):
    out = {}
    for n in range(2, int(math.ceil(x))):
        t = prime_power(n)
        if t and n < x:
            out[n] = mp.log(t[0]) / mp.sqrt(n)
    return out


CHI5 = {0: 0, 1: 1, 2: 1j, 3: -1j, 4: -1}  # odd character mod 5 with chi(2) = i


def chi4(n):
    return 0 if n % 2 == 0 else (1 if n % 4 == 1 else -1)


def lchi5_coeffs(x):
    return {n: v * CHI5[n % 5] for n, v in zeta_coeffs(x).items() if CHI5[n % 5] != 0}


def chi4_coeffs(x):
    return {n: v * chi4(n) for n, v in zeta_coeffs(x).items() if chi4(n) != 0}


def dh_kappa():
    return (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)


def dh_a(n):
    """DH Dirichlet coefficient: Re chi(n) + kappa Im chi(n)."""
    return mp.re(CHI5[n % 5]) + dh_kappa() * mp.im(CHI5[n % 5])


def dh_function(s):
    return sum(dh_a(r) * mp.zeta(s, mp.mpf(r) / 5) for r in range(1, 5)) * mp.mpf(5) ** (-s)


def dh_completed(s):
    return (5 / mp.pi) ** (s / 2) * mp.gamma((s + 1) / 2) * dh_function(s)


def dh_coeffs(x):
    """Lambda_f(n)/sqrt(n) from a(n) log n = sum_{d|n} Lambda_f(d) a(n/d); no Euler product."""
    M = int(math.ceil(x)) - 1
    a = [0] + [dh_a(n) for n in range(1, M + 1)]
    Lam = [mp.mpf(0)] * (M + 1)
    for n in range(2, M + 1):
        s = a[n] * mp.log(n)
        for d in range(2, n):
            if n % d == 0:
                s -= Lam[d] * a[n // d]
        Lam[n] = s
    return {n: Lam[n] / mp.sqrt(n) for n in range(2, M + 1) if n < x and Lam[n] != 0}


FAMILIES = {
    "zeta": (zeta_coeffs, dict(a=0, logq=0, polar=True)),
    "dh": (dh_coeffs, dict(a=1, logq=None, polar=False)),       # logq = log 5
    "lchi5": (lchi5_coeffs, dict(a=1, logq=None, polar=False)),  # logq = log 5
    "chi4": (chi4_coeffs, dict(a=1, logq=None, polar=False)),    # logq = log 4
}
CONDUCTOR = {"zeta": 1, "dh": 5, "lchi5": 5, "chi4": 4}


def family_matrix(fam, x, N, dps, coeffs=None):
    make, kw = FAMILIES[fam]
    mp.mp.dps = dps
    c = make(x) if coeffs is None else coeffs
    kw = dict(kw, logq=mp.log(CONDUCTOR[fam]))
    return weil_matrix(x, N, dps, c, **kw), c, kw


# -----------------------------------------------------------------------------
# Linear algebra and diagnostics
# -----------------------------------------------------------------------------


def _to_arb(v, dps):
    return arb(mp.nstr(v, dps + 5, strip_zeros=False))


def sym_eig(H, dps, vectors=False):
    """Approximate real-symmetric eigenpairs; reject unresolved complex output."""
    mp.mp.dps = dps
    ctx.prec = int(dps * 3.33) + 32
    n = len(H)
    M = acb_mat([[acb(_to_arb(v, dps)) for v in row] for row in H])
    read = lambda z: mp.mpc(mp.mpf(z.real.mid().str(dps, radius=False)),
                            mp.mpf(z.imag.mid().str(dps, radius=False)))
    result = M.eig(right=True, algorithm="approx") if vectors else M.eig(algorithm="approx")
    values, R = result if vectors else (result, None)
    values = [read(e) for e in values]
    diagnostics.require_finite(values, "symmetric eigenvalues")
    tol = diagnostics.quality_tolerance(dps)
    if max(abs(mp.im(e)) for e in values) > tol * max(1, diagnostics.matrix_norm(H)):
        raise ArithmeticError("Unresolved complex symmetric eigenvalues")
    order = sorted(range(n), key=lambda i: mp.re(values[i]))
    out = []
    if vectors:
        for i in order:
            v = [read(R[k, i]) for k in range(n)]
            diagnostics.require_finite(v, "symmetric eigenvector")
            phase = max(v, key=abs)
            v = [t / phase for t in v]
            if max(abs(mp.im(t)) for t in v) > tol:
                raise ArithmeticError("Unresolved complex symmetric eigenvector")
            out.append(normalize([mp.re(t) for t in v]))
    return [mp.re(values[i]) for i in order], (out if vectors else None)


def normalize(v):
    s = mp.sqrt(mp.fsum(t * t for t in v))
    return [t / s for t in v]


def parity(v):
    """+1 for reflection-even (j -> -j), -1 for odd."""
    return mp.fsum(a * b for a, b in zip(v, v[::-1])) / mp.fsum(a * a for a in v)


def quad(H, v):
    return mp.fsum(v[i] * mp.fsum(H[i][j] * v[j] for j in range(len(v))) for i in range(len(v)))


def qv(v, om, L, y):
    """v^T Q(y) v, Q(y)_jk = q_jk(y) from the repo's pair correlation."""
    n = len(v)
    s = [mp.sin(w * y) for w in om]
    diag = mp.fsum(v[j] ** 2 * 2 * (1 - y / L) * mp.cos(om[j] * y) for j in range(n))
    off = mp.fsum(v[j] * v[k] * (s[j] - s[k]) / (om[j] - om[k]) for j in range(n) for k in range(j + 1, n))
    return diag - (4 / L) * off


def fourier_at(v, L, om, r):
    """F(r) = sum_k v_k int_0^L U_k(t) e^{-irt} dt (entire in r)."""
    return sum(vk * (mp.exp(-1j * r * L) - 1) / (1j * (w - r)) for vk, w in zip(v, om)) / mp.sqrt(L)


def quadruplet_energy(v, L, om, rho):
    """Zero-side energy of an off-line quadruplet {g, conj g, -g, -conj g}, g = (rho - 1/2)/i."""
    g = (rho - mp.mpf(1) / 2) / 1j
    F = lambda r: fourier_at(v, L, om, r)
    return 2 * mp.re(mp.conj(F(mp.conj(g))) * F(g)) + 2 * mp.re(mp.conj(F(-g)) * F(-mp.conj(g)))


def corrected_root_diagnostics(v_even, om, L, N, dps):
    """Retain full complex roots; never silently discard imaginary parts."""
    mp.mp.dps = dps
    if abs(parity(v_even) - 1) > diagnostics.quality_tolerance(dps):
        raise ValueError("An even vector is required")
    def eig(rows, digits):
        ctx.prec = int(digits * 3.33) + 32
        M = acb_mat([[acb(_to_arb(v, digits)) for v in row] for row in rows])
        return [mp.mpc(mp.mpf(z.real.mid().str(digits, radius=False)),
                       mp.mpf(z.imag.mid().str(digits, radius=False)))
                for z in M.eig(algorithm="approx")]
    return diagnostics.roots_from_vector(v_even, om, L, N, dps, eig)


def corrected_roots_and_mean(v_even, om, L, N, dps):
    """Compatibility helper: fail closed unless all root-quality checks pass."""
    result = corrected_root_diagnostics(v_even, om, L, N, dps)
    if result["root_status"] != "resolved":
        raise ArithmeticError(f"Corrected roots unresolved: {result['root_status']}")
    return [mp.re(w) for w in result["roots_squared"]], result["mu"]
