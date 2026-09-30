"""Finite precision diagnostics. None of these tolerances is a rigorous enclosure."""
from __future__ import annotations

import math
import mpmath as mp
import research_runtime as runtime


def require_finite(value, label="value"):
    if isinstance(value, dict):
        for key, val in value.items():
            require_finite(val, f"{label}.{key}")
    elif isinstance(value, (tuple, list)):
        for i, val in enumerate(value):
            require_finite(val, f"{label}[{i}]")
    elif isinstance(value, (mp.mpf, mp.mpc, float, complex)) and not mp.isfinite(value):
        raise ValueError(f"Nonfinite {label}")


def decimal(value, dps):
    require_finite(value)
    return mp.nstr(value, dps, strip_zeros=False)


def serialize(value, dps):
    require_finite(value)
    if isinstance(value, dict):
        return {key: serialize(val, dps) for key, val in value.items()}
    if isinstance(value, (list, tuple)):
        return [serialize(val, dps) for val in value]
    if isinstance(value, mp.mpc):
        return {"real": decimal(value.real, dps), "imag": decimal(value.imag, dps)}
    if isinstance(value, mp.mpf):
        return decimal(value, dps)
    return value


def matrix_norm(rows):
    require_finite(rows, "matrix")
    return max(mp.fsum(abs(value) for value in row) for row in rows)


def eigenpair_residual(rows, eigenvalue, vector):
    require_finite([rows, eigenvalue, vector], "eigenpair")
    norm_v = max(abs(v) for v in vector)
    absolute = max(abs(mp.fsum(a * b for a, b in zip(row, vector)) - eigenvalue * vector[i])
                   for i, row in enumerate(rows)) / norm_v
    return absolute, absolute / max(mp.mpf(1), matrix_norm(rows), abs(eigenvalue))


def quality_tolerance(dps):
    return mp.power(10, -min(30, dps // 3))


def selection_status(gap, parity, dps, scale=1, residual_absolute=0, endpoint=None):
    require_finite([gap, parity, scale, residual_absolute, endpoint], "selection")
    floor = mp.power(10, -(dps - 25)) * max(1, scale)
    # A negative energy is deliberately not a selection criterion.
    if gap <= floor or residual_absolute >= gap * quality_tolerance(dps):
        return "unresolved_gap"
    if abs(parity + 1) <= quality_tolerance(dps):
        return "odd_ground"
    if abs(parity - 1) > quality_tolerance(dps):
        return "unresolved_parity"
    if endpoint is not None and abs(endpoint) <= floor:
        return "unresolved_endpoint"
    return "selected"


def polynomial_residual(root, poles, weights):
    """Scaled residual of prod(w-p)+sum d_j prod_{k!=j}(w-p_k), O(N)."""
    factors = [root - p for p in poles]
    prefix = [mp.mpc(1)]
    for factor in factors:
        prefix.append(prefix[-1] * factor)
    suffix = mp.mpc(1)
    terms = [prefix[-1]]
    for j in range(len(factors) - 1, -1, -1):
        terms.append(weights[j] * prefix[j] * suffix)
        suffix *= factors[j]
    scale = mp.fsum(abs(term) for term in terms)
    return abs(mp.fsum(terms)) / scale if scale else mp.mpf(0)


def roots_from_vector(vector, om, L, N, dps, eig):
    """Inspect every algebraic secular root before constructing a real mean."""
    mp.mp.dps = dps
    if N < 1 or len(vector) != 2 * N + 1 or len(om) != 2 * N + 1 or L <= 0:
        raise ValueError("Invalid characteristic dimensions or length")
    require_finite([vector, om, L], "characteristic input")
    sqL = mp.sqrt(L)
    endpoint = mp.fsum(vector) / sqL
    out = {"endpoint_magnitude": abs(endpoint), "root_status": "unresolved_endpoint"}
    if abs(endpoint) <= mp.power(10, -(dps - 25)):
        return out
    vk = [v / endpoint for v in vector[N + 1:]]
    poles = [om[N + k] ** 2 for k in range(1, N + 1)]
    weights = [2 * vk[k] * poles[k] / sqL for k in range(N)]
    matrix = [[(poles[i] if i == j else 0) - weights[j] for j in range(N)] for i in range(N)]
    roots = list(eig(matrix, dps))
    require_finite(roots, "secular roots")
    if len(roots) != N:
        out.update(root_status="wrong_root_count", algebraic_root_count=len(roots), roots_squared=roots)
        return out
    roots = sorted(roots, key=lambda z: (mp.re(z), mp.im(z)))
    root_residuals = [polynomial_residual(w, poles, weights) for w in roots]
    max_scaled_imag = max(abs(mp.im(w)) / max(1, abs(w)) for w in roots)
    out.update(roots_squared=roots, polynomial_residuals=root_residuals,
               max_scaled_imag=max_scaled_imag, min_real_root_squared=min(mp.re(w) for w in roots),
               algebraic_root_count=len(roots))
    tol = quality_tolerance(dps)
    if len(roots) != N or max_scaled_imag > tol or max(root_residuals) > tol:
        out["root_status"] = "unstable_roots"
        return out
    if any(mp.re(w) <= 0 for w in roots):
        out["root_status"] = "nonpositive_roots"
        return out
    alpha2 = mp.mpf(1) / 16
    a = mp.sqrt(alpha2) * L / (2 * mp.pi)
    corr = mp.fsum(alpha2 / mp.re(w + alpha2) for w in roots)
    lat = (mp.pi * a * mp.coth(mp.pi * a) - 1) / 2 - mp.fsum(alpha2 / (p + alpha2) for p in poles)
    inv = [1 / (p + alpha2) for p in poles]
    denom = 1 - mp.fsum(d * t for d, t in zip(weights, inv))
    if denom == 0:
        out["root_status"] = "unresolved_trace_mean"
        return out
    trace_mean = alpha2 * (mp.fsum(inv) + mp.fsum(d * t**2 for d, t in zip(weights, inv)) / denom)
    require_finite([corr, lat, trace_mean], "mean")
    trace_diff = abs(corr - trace_mean) / max(mp.mpf(1), abs(corr), abs(trace_mean))
    out.update(trace_mean_corr=trace_mean, trace_mean_scaled_difference=trace_diff)
    if trace_diff > tol:
        out["root_status"] = "unstable_trace_mean"
        return out
    out.update(root_status="resolved", eta=[mp.sqrt(mp.re(w)) for w in roots],
               mu_corr=corr, mu_lat=lat, mu=corr + lat)
    return out


def compare_runs(previous, current, tol="1e-12"):
    """Root-by-root and gap/eigenvalue stability, not just a stable total mean."""
    require_finite([previous, current], "precision comparison")
    tol = mp.mpf(tol)
    if previous.get("selection_status") != "selected" or current.get("selection_status") != "selected":
        return {"stable": False, "reason": "selection_not_resolved"}
    if previous.get("root_status") != "resolved" or current.get("root_status") != "resolved":
        return {"stable": False, "reason": "roots_not_resolved"}
    a, b = previous["roots_squared"], current["roots_squared"]
    if len(a) != len(b):
        return {"stable": False, "reason": "root_count_changed"}
    differences = [abs(x - y) / max(1, abs(x), abs(y)) for x, y in zip(a, b)]
    mean_diff = abs(previous["mu"] - current["mu"]) / max(abs(previous["mu"]), abs(current["mu"]), mp.mpf("1e-1000"))
    spectral = {key: abs(previous[key] - current[key]) / max(abs(previous[key]), abs(current[key]), mp.power(10, -(previous["dps"] - 25)))
                for key in ("E0", "gap")}
    stable = max(differences + [mean_diff] + list(spectral.values())) <= tol
    return dict(stable=bool(stable), root_scaled_differences=differences,
                mean_relative_difference=mean_diff, spectral_relative_differences=spectral, tolerance=tol)


def precision_record(x, N, analyze, precisions, tol="1e-12", family="zeta"):
    """Keep every attempt, including negative, odd, unresolved and failed carriers."""
    record = dict(schema_version=runtime.SCHEMA_VERSION, evidence_status=runtime.STATUS,
                  family=family, x=x, N=N, requested_precisions=list(precisions),
                  environment=runtime.versions(), attempts=[], status="numerical_failure")
    previous = None
    for dps in precisions:
        try:
            current = analyze(x, N, dps)
            comparison = compare_runs(previous, current, tol) if previous else None
            saved = serialize(current, dps)
            if comparison:
                saved["comparison"] = serialize(comparison, dps)
            record["attempts"].append(saved)
            if comparison and comparison["stable"]:
                record.update(status="precision_stable", result=saved)
                return record
            record["status"] = current.get("selection_status", "numerical_failure")
            if record["status"] == "selected":
                record["status"] = current.get("root_status", "unresolved_roots")
                if record["status"] == "resolved":
                    record["status"] = "unresolved_precision"
            previous = current
        except (ArithmeticError, ValueError, RuntimeError) as error:
            record["attempts"].append(dict(dps=dps, status="numerical_failure",
                                            error_type=type(error).__name__, error=str(error)))
            record["status"] = "numerical_failure"
            previous = None
    return record
