"""Experiment 4: visualize the explicit completed critical kernel.

The figure is always drawn with NumPy/Matplotlib.  The optional precision
argument only changes the scalar diagnostic for the L1 integral, which makes
this script a simple first example of the precision ladder.
"""

import argparse
import math

import matplotlib.pyplot as plt
import numpy as np

from common import FIGURE_DIR, critical_kernel
from high_precision import mp_completed_kernel_l1
from precision import add_precision_arguments, resolve_precision


parser = argparse.ArgumentParser(description=__doc__)
add_precision_arguments(parser)
args = parser.parse_args()
precision = resolve_precision(args)

y = np.linspace(0.0, 10.0, 12000)
K = critical_kernel(y)

if precision.uses_mpmath:
    absolute_integral = mp_completed_kernel_l1(10.0, dps=precision.dps)
    print(f"precision profile           = {precision.name}")
    print(f"integral_0^10 |K(y)| dy    = {absolute_integral}")
else:
    absolute_integral = np.trapezoid(np.abs(K), y)
    print("precision profile           = float64")
    print(f"integral_0^10 |K(y)| dy    = {absolute_integral:.12f}")

theoretical_bound = 8.0 * math.pi / 3.0
print(f"theoretical L1 bound       = {theoretical_bound:.12f}")

plt.figure(figsize=(9, 4.5))
plt.plot(y, K)
for n in range(2, 20):
    location = math.log(n)
    if location <= y[-1]:
        plt.axvline(location, alpha=0.15)
plt.xlabel("y")
plt.ylabel("K(y)")
plt.title("Critical completed kernel with arithmetic thresholds y = log n")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_04_completed_kernel.svg")
plt.close()

plt.figure(figsize=(9, 4.5))
plt.plot(y, np.exp(2.5 * y) * K / math.pi)
plt.xlim(0.0, 4.0)
plt.xlabel("y")
plt.ylabel("exp(5y/2) K(y) / pi")
plt.title("Removing the exponential envelope exposes the arithmetic sawtooth")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_04_scaled_kernel.svg")
plt.close()

mask = y <= math.log(30.0)
r = np.exp(y[mask])
K_r = K[mask]
plt.figure(figsize=(9, 4.5))
plt.plot(r, K_r)
plt.xlabel("r = exp(y)")
plt.ylabel("K(log r)")
plt.title("The same kernel in multiplicative coordinates")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_04_multiplicative_kernel.svg")
plt.close()
