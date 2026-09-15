"""Experiment 3: the absorbing derivative generator and Volterra resolvent."""

import matplotlib.pyplot as plt
import numpy as np

from common import FIGURE_DIR, volterra_resolvent


L = 3.0
t = np.linspace(0.0, L, 1600)
b = 1.3

f = 1.0 + 0.25 * np.cos(2.0 * np.pi * t / L)
R = volterra_resolvent(t, f, b)
R_derivative = np.gradient(R, t)
residual = b * R - R_derivative - f

print(f"R_b f at the absorbing endpoint: {R[-1]:.3e}")
print(f"max residual in (b-A)R_b f=f: {np.max(np.abs(residual[5:-5])):.3e}")

plt.figure(figsize=(8, 4.5))
plt.plot(t, f, label="f")
plt.plot(t, np.real(R), label="R_b f")
plt.axvline(L)
plt.xlabel("t")
plt.ylabel("value")
plt.title("The Volterra resolvent integrates backward from the absorbing endpoint")
plt.legend()
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_03_volterra_resolvent.svg")
plt.close()

plt.figure(figsize=(8, 4.5))
plt.plot(t, np.real(residual))
plt.xlabel("t")
plt.ylabel("residual")
plt.title("Numerical check of (b - A_L) R_b f = f")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_03_resolvent_residual.svg")
plt.close()
