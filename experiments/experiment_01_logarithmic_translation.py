"""Experiment 1: integer multiplication as logarithmic translation."""

import math

import matplotlib.pyplot as plt
import numpy as np

from common import FIGURE_DIR


L = math.log(30.0)
t = np.linspace(0.0, L, 1200)


def test_function(x):
    return np.exp(-((x - 2.4) / 0.35) ** 2)


def killed_shift(y):
    values = np.zeros_like(t)
    mask = t + y < L
    values[mask] = test_function(t[mask] + y)
    return values


f = test_function(t)
S2 = killed_shift(math.log(2.0))
S6_direct = killed_shift(math.log(6.0))

# Apply S_log(3) to S_log(2) by evaluating the already shifted function.
S2_then_3 = np.zeros_like(t)
shifted_points = t + math.log(3.0)
S2_then_3 = np.interp(shifted_points, t, S2, left=0.0, right=0.0)

error = np.max(np.abs(S2_then_3 - S6_direct))
print(f"max |S_log(3) S_log(2) f - S_log(6) f| = {error:.3e}")

plt.figure(figsize=(8, 4.5))
plt.plot(t, f, label="f")
plt.plot(t, S2, label="S_log(2) f")
plt.plot(t, S6_direct, label="S_log(6) f")
plt.xlabel("t")
plt.ylabel("value")
plt.title("Multiplication becomes translation on the logarithmic interval")
plt.legend()
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_01_shifted_functions.svg")
plt.close()

plt.figure(figsize=(8, 2.8))
for n in range(2, 16):
    x = math.log(n)
    if x < L:
        plt.scatter([x], [0.0])
        plt.text(x, 0.05, str(n), ha="center", va="bottom")
plt.axvline(L)
plt.yticks([])
plt.xlabel("t = log n")
plt.title("The arithmetic nodes are logarithmically spaced")
plt.tight_layout()
plt.savefig(FIGURE_DIR / "experiment_01_logarithmic_nodes.svg")
plt.close()
