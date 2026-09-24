"""Experiment 2: exact finite Euler synthesis, Mobius inversion, and current.

Paper I, Proposition 2.  On a window of length L = log x every V_n = S_{log n}
with n >= x vanishes, so the Euler product terminates:

    Z_L(s) = prod_{p<x} (I - p^{-s} V_p)^{-1} = sum_{n<x} n^{-s} V_n,
    Z_L(s)^{-1} = sum_{n<x} mu(n) n^{-s} V_n,
    -Z_L(s)^{-1} Z_L'(s) = sum_{1<n<x} Lambda(n) n^{-s} V_n.

Elements of the finite shift algebra are stored as {n: coefficient of V_n}.
"""

import matplotlib.pyplot as plt
import numpy as np

from common import (
    derivative_of_synthesis,
    direct_euler_synthesis,
    euler_product_synthesis,
    maximum_dictionary_error,
    mobius_inverse_coefficients,
    mobius_table,
    multiply_shift_algebra,
    prime_current_coefficients,
)
import presentation as ui


ui.use_style()
ui.banner(
    2,
    "Finite Euler synthesis, Mobius inverse, and prime current",
    status=ui.IDENTITY,
    reference="Paper I, Proposition 2",
    claim=(
        "On the window x = 30 the Euler product terminates and equals the "
        "Dirichlet synthesis, its inverse carries the Mobius coefficients, and "
        "its negative logarithmic derivative has exactly the von Mangoldt "
        "coefficients Lambda(n) n^(-s)."
    ),
)

x = 30.0
s = 0.75 + 0.20j

Z_direct = direct_euler_synthesis(x, s)
Z_product = euler_product_synthesis(x, s)
Z_inverse = mobius_inverse_coefficients(x, s)
Z_derivative = derivative_of_synthesis(x, s)
current_expected = prime_current_coefficients(x, s)

identity = multiply_shift_algebra(Z_product, Z_inverse, x)
current_from_log_derivative = multiply_shift_algebra(Z_inverse, Z_derivative, x)
current_from_log_derivative = {n: -c for n, c in current_from_log_derivative.items()}

product_error = maximum_dictionary_error(Z_direct, Z_product)
inverse_error = maximum_dictionary_error(identity, {1: 1.0})
current_error = maximum_dictionary_error(current_from_log_derivative, current_expected)

print("finite Euler product error:", product_error)
print("finite inverse error:", inverse_error)
print("logarithmic derivative error:", current_error)

integers = np.arange(1, int(x))
z_magnitude = np.array([abs(Z_direct.get(int(n), 0.0)) for n in integers])
mu_magnitude = np.array([abs(Z_inverse.get(int(n), 0.0)) for n in integers])
current_magnitude = np.array([abs(current_expected.get(int(n), 0.0)) for n in integers])

mu = mobius_table(int(x) - 1)[1:]
squarefree_count = int(np.count_nonzero(mu))
prime_powers = [int(n) for n in integers if current_expected.get(int(n), 0.0) != 0.0]

ui.reading(
    "All three identities hold to rounding error (largest coefficient error "
    f"{max(product_error, inverse_error, current_error):.1e}).  The synthesis "
    f"touches every n < 30; the inverse keeps only the {squarefree_count} "
    f"squarefree n; the current keeps only the {len(prime_powers)} prime powers.",
    figures=(
        "experiment_02_euler_coefficients.svg",
        "experiment_02_mobius_coefficients.svg",
        "experiment_02_current_coefficients.svg",
    ),
)

source = "Paper I, Proposition 2, eq. (10)  ·  x = 30, s = 0.75 + 0.2i  ·  " + ui.IDENTITY

# -----------------------------------------------------------------------------
# Figure 1: the synthesis sum_{n<x} n^{-s} V_n.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 3.4))
ax = fig.add_subplot()
ui.lollipop(ax, integers, z_magnitude, ui.BLUE)
ax.axhline(0.0, color=ui.AXIS, lw=0.9)
ax.set_xlim(0.0, x)
ax.set_ylim(-0.05, 1.12)
ax.set_xticks([1, 5, 10, 15, 20, 25, 29])
ax.set_xlabel(r"$n$")
ax.set_ylabel(r"$|n^{-s}|$")
ui.save(
    fig,
    "experiment_02_euler_coefficients.svg",
    title="The terminating Euler product reaches every integer below x",
    subtitle=(
        r"$\Pi_{p<30}\,(I - p^{-s}V_p)^{-1} = \Sigma_{n<30}\, n^{-s} V_n$, "
        r"coefficient magnitudes $|n^{-s}| = n^{-0.75}$."
        "\n"
        rf"Expanding the product and summing directly agree to ${ui.sci(product_error)}$."
    ),
    source=source,
)

# -----------------------------------------------------------------------------
# Figure 2: the Mobius inverse, with its signs.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 3.6))
ax = fig.add_subplot()
signed = mu * mu_magnitude
positive = mu > 0
negative = mu < 0
ui.lollipop(ax, integers[positive], signed[positive], ui.BLUE, label=r"$\mu(n) = +1$")
ui.lollipop(ax, integers[negative], signed[negative], ui.ORANGE, label=r"$\mu(n) = -1$")
ax.plot(integers[mu == 0], np.zeros(np.count_nonzero(mu == 0)), linestyle="none",
        marker="x", markersize=4.5, markeredgewidth=1.1, color=ui.MUTED,
        label=r"$\mu(n) = 0$ (square factor)")
ax.axhline(0.0, color=ui.AXIS, lw=0.9)
ax.set_xlim(0.0, x)
ax.set_ylim(-0.75, 1.12)
ax.set_xticks([1, 5, 10, 15, 20, 25, 29])
ax.set_xlabel(r"$n$")
ax.set_ylabel(r"$\mu(n)\,|n^{-s}|$")
ax.legend(loc="upper right", ncols=3)
ui.save(
    fig,
    "experiment_02_mobius_coefficients.svg",
    title="The inverse keeps only squarefree n, with Möbius signs",
    subtitle=(
        r"$Z_L(s)^{-1} = \Sigma_{n<30}\, \mu(n)\, n^{-s} V_n$; "
        rf"$Z_L(s)\,Z_L(s)^{{-1}} = I$ to ${ui.sci(inverse_error)}$ in every coefficient."
    ),
    source=source,
)

# -----------------------------------------------------------------------------
# Figure 3: the prime current, supported on prime powers.
# -----------------------------------------------------------------------------

fig = plt.figure(figsize=(8.0, 3.4))
ax = fig.add_subplot()
is_prime = np.array([n in {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} for n in integers])
ui.lollipop(ax, integers[is_prime], current_magnitude[is_prime], ui.BLUE, label="prime $p$")
higher = (current_magnitude > 0.0) & ~is_prime
ui.lollipop(ax, integers[higher], current_magnitude[higher], ui.ORANGE, label=r"prime power $p^k,\ k \geq 2$")
power_names = {4: "$2^2$", 8: "$2^3$", 9: "$3^2$", 16: "$2^4$", 25: "$5^2$", 27: "$3^3$"}
for n, text in power_names.items():
    ax.annotate(text, (n, current_magnitude[n - 1]), xytext=(0, 7), textcoords="offset points",
                ha="center", va="bottom", fontsize=8.0, color=ui.INK_2)
ax.axhline(0.0, color=ui.AXIS, lw=0.9)
ax.set_xlim(0.0, x)
ax.set_ylim(-0.02, 0.5)
ax.set_xticks([1, 5, 10, 15, 20, 25, 29])
ax.set_xlabel(r"$n$")
ax.set_ylabel(r"$\Lambda(n)\,|n^{-s}|$")
ax.legend(loc="upper right", ncols=2)
ui.save(
    fig,
    "experiment_02_current_coefficients.svg",
    title="The logarithmic derivative isolates prime powers",
    subtitle=(
        r"$-Z_L(s)^{-1} Z_L'(s) = \Sigma_{1<n<30}\, \Lambda(n)\, n^{-s} V_n$; "
        rf"computed in the shift algebra, it matches $\Lambda(n)\,n^{{-s}}$ to ${ui.sci(current_error)}$."
    ),
    source=source,
)
