import Riemann.Analysis.HalfLine.Kernel

/-! # Arithmetic translations of the completed smoothing kernel

A finite translated exponential sum is evaluated exactly. The cutoff theorem
is pointwise with the inclusive threshold log(n)≤y; changing single threshold
values later does not change the strong integral.
-/
noncomputable section
open scoped BigOperators
namespace Riemann.Analysis.HalfLine

/-- The two resolvent kernels after their critical cancellation. -/
def smoothingKernel (y : ℝ) : ℝ :=
  if 0 ≤ y then 2*Real.pi*(3*Real.exp (-5*y/2)-2*Real.exp (-3*y/2)) else 0

/-- A single raw Euler term after smoothing; n=0 is omitted explicitly. -/
def arithmeticKernelTerm (n : ℕ) (y : ℝ) : ℝ :=
  if n = 0 then 0 else Real.exp (-Real.log n/2)*smoothingKernel (y-Real.log n)

lemma weighted_exponential {n : ℕ} (hn : 0 < n) (k : ℕ) (y : ℝ) :
    Real.exp (-Real.log n/2)*Real.exp (-((k:ℝ)+1/2)*(y-Real.log n)) =
      Real.exp (-((k:ℝ)+1/2)*y)*(n:ℝ)^k := by
  rw [← Real.exp_add]
  have he : -Real.log n/2+-((k:ℝ)+1/2)*(y-Real.log n) =
      -((k:ℝ)+1/2)*y + (k:ℝ)*Real.log n := by ring
  rw [he, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity : (0:ℝ)<n)]

lemma arithmeticKernelTerm_of_le {n : ℕ} (hn : 0 < n) {y : ℝ}
    (hy : Real.log n ≤ y) :
    arithmeticKernelTerm n y = 2*Real.pi*(3*Real.exp (-5*y/2)*(n:ℝ)^2 -
      2*Real.exp (-3*y/2)*(n:ℝ)) := by
  simp only [arithmeticKernelTerm, ne_of_gt hn, ↓reduceIte,
    smoothingKernel, sub_nonneg.mpr hy]
  have h2 := weighted_exponential hn 2 y
  have h1 := weighted_exponential hn 1 y
  norm_num at h2 h1
  simp only [← neg_mul] at h2 h1
  have e2 : -(5/2:ℝ)*(y-Real.log n) = -5*(y-Real.log n)/2 := by ring
  have e1 : -(3/2:ℝ)*(y-Real.log n) = -3*(y-Real.log n)/2 := by ring
  have e3 : -(5/2:ℝ)*y = -5*y/2 := by ring
  have e4 : -(3/2:ℝ)*y = -3*y/2 := by ring
  rw [e2,e3] at h2
  rw [e1,e4] at h1
  linear_combination 6*Real.pi*h2 - 4*Real.pi*h1

lemma arithmeticKernelTerm_eq_zero {n : ℕ} {y : ℝ}
    (hy : y < Real.log n) : arithmeticKernelTerm n y = 0 := by
  by_cases hn : n=0
  · simp [arithmeticKernelTerm, hn]
  · simp [arithmeticKernelTerm, hn, smoothingKernel, not_le.mpr (sub_neg.mpr hy)]

/-- All terms past the arithmetic count vanish before summation. -/
lemma arithmeticKernelTerm_of_count_lt {n : ℕ} {y : ℝ}
    (hn : arithmeticCount y < n) : arithmeticKernelTerm n y = 0 := by
  apply arithmeticKernelTerm_eq_zero
  apply (Real.lt_log_iff_exp_lt (by exact_mod_cast (Nat.zero_le _).trans_lt hn)).mpr
  exact (Nat.floor_lt (Real.exp_pos y).le).mp hn

/-- The completed arithmetic kernel is derived from its finite translated sum. -/
theorem sum_arithmeticKernelTerm (N : ℕ) (y : ℝ) (hN : arithmeticCount y ≤ N) :
    (∑ n ∈ Finset.range (N+1), arithmeticKernelTerm n y) = criticalKernel y := by
  have hsum : (∑ n ∈ Finset.range (N+1), arithmeticKernelTerm n y) =
      ∑ n ∈ Finset.range (arithmeticCount y+1), arithmeticKernelTerm n y := by
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hN 1))
    intro n hn hn0
    apply arithmeticKernelTerm_of_count_lt
    simp only [Finset.mem_range, not_lt] at hn0
    omega
  rw [hsum]
  calc
    _ = ∑ n ∈ Finset.range (arithmeticCount y+1),
        2*Real.pi*(3*Real.exp (-5*y/2)*(n:ℝ)^2-2*Real.exp (-3*y/2)*(n:ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hn0 : n=0
      · simp [hn0, arithmeticKernelTerm]
      · apply arithmeticKernelTerm_of_le (Nat.pos_of_ne_zero hn0)
        apply (Real.log_le_iff_le_exp (by positivity : (0:ℝ)<n)).mpr
        exact (Nat.cast_le.mpr (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hn))).trans
          (arithmeticCount_le y)
    _ = 2*Real.pi*(3*Real.exp (-5*y/2)*
        (∑ n ∈ Finset.range (arithmeticCount y+1), (n:ℝ)^2)-
        2*Real.exp (-3*y/2)*(∑ n ∈ Finset.range (arithmeticCount y+1), (n:ℝ))) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = criticalKernel y := criticalKernel_arithmetic_sums y

end Riemann.Analysis.HalfLine
