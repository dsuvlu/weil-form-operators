import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-! Finite Dirichlet-convolution synthesis in a commutative algebra. The bound
is inclusive: all n>X are killed. In the paper's strict-cutoff notation this
corresponds to a cutoff X+1, with any additional killed terms harmless. -/

noncomputable section
open Finset
namespace Riemann.Arithmetic

variable {R : Type*} [CommRing R] [Algebra ℝ R]

/-- Coefficientwise multiplication by a completely multiplicative representation. -/
def twist (w : ℕ →*₀ R) (f : ArithmeticFunction ℝ) : ArithmeticFunction R where
  toFun n := algebraMap ℝ R (f n) * w n
  map_zero' := by simp

@[simp] theorem twist_apply (w : ℕ →*₀ R) (f : ArithmeticFunction ℝ) (n : ℕ) :
    twist w f n = algebraMap ℝ R (f n) * w n := rfl

theorem twist_mul (w : ℕ →*₀ R) (f g : ArithmeticFunction ℝ) :
    twist w (f*g) = twist w f * twist w g := by
  ext n
  simp only [twist_apply, ArithmeticFunction.mul_apply, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' : d.1*d.2=n := (Nat.mem_divisorsAntidiagonal.mp hd).1
  rw [map_mul, ← hd', map_mul]
  ring

/-- Finite synthesis of arithmetic coefficients; finiteness concerns the sum. -/
def synthesis (X : ℕ) (w : ℕ →*₀ R) (f : ArithmeticFunction ℝ) : R :=
  ∑ n ∈ Ioc 0 X, twist w f n

theorem synthesis_mul (X : ℕ) (w : ℕ →*₀ R)
    (hkill : ∀ n, X < n → w n = 0) (f g : ArithmeticFunction ℝ) :
    synthesis X w (f*g) = synthesis X w f * synthesis X w g := by
  unfold synthesis
  rw [twist_mul, ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter,
    Finset.sum_mul_sum, ← Finset.sum_product']
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hnot
  have hlarge : X < d.1*d.2 := by simpa only [mem_filter, hd, true_and, not_le] using hnot
  simp only [twist_apply]
  calc
    (algebraMap ℝ R (f d.1) * w d.1) * (algebraMap ℝ R (g d.2) * w d.2) =
      (algebraMap ℝ R (f d.1) * algebraMap ℝ R (g d.2)) * w (d.1*d.2) := by
        rw [map_mul]; ring
    _ = 0 := by rw [hkill _ hlarge, mul_zero]

@[simp] theorem synthesis_one (X : ℕ) (hX : 1 ≤ X) (w : ℕ →*₀ R) :
    synthesis X w 1 = 1 := by
  simp [synthesis, ArithmeticFunction.one_apply, hX]

@[simp] theorem synthesis_neg (X : ℕ) (w : ℕ →*₀ R) (f : ArithmeticFunction ℝ) :
    synthesis X w (-f) = -synthesis X w f := by
  simp [synthesis, ArithmeticFunction.neg_apply]

open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-- All-integer finite Euler synthesis, before its prime factorization. -/
def eulerSynthesis (X : ℕ) (w : ℕ →*₀ R) : R := synthesis X w ζ

/-- Explicit finite Möbius polynomial. -/
def moebiusInverse (X : ℕ) (w : ℕ →*₀ R) : R := synthesis X w μ

theorem eulerSynthesis_sum (X : ℕ) (w : ℕ →*₀ R) :
    eulerSynthesis X w = ∑ n ∈ Ioc 0 X, w n := by
  unfold eulerSynthesis synthesis
  apply Finset.sum_congr rfl
  intro n hn
  simp [twist, ne_of_gt (mem_Ioc.mp hn).1]

theorem moebiusInverse_mul_eulerSynthesis (X : ℕ) (hX : 1 ≤ X) (w : ℕ →*₀ R)
    (hkill : ∀ n, X < n → w n = 0) :
    moebiusInverse X w * eulerSynthesis X w = 1 := by
  rw [moebiusInverse, eulerSynthesis, ← synthesis_mul X w hkill,
    ArithmeticFunction.coe_moebius_mul_coe_zeta, synthesis_one X hX]

theorem eulerSynthesis_mul_moebiusInverse (X : ℕ) (hX : 1 ≤ X) (w : ℕ →*₀ R)
    (hkill : ∀ n, X < n → w n = 0) :
    eulerSynthesis X w * moebiusInverse X w = 1 := by
  rw [mul_comm]; exact moebiusInverse_mul_eulerSynthesis X hX w hkill

/-- A unit with the stated finite Möbius inverse, not an assumed inverse. -/
def eulerUnit (X : ℕ) (hX : 1 ≤ X) (w : ℕ →*₀ R)
    (hkill : ∀ n, X < n → w n = 0) : Rˣ where
  val := eulerSynthesis X w
  inv := moebiusInverse X w
  val_inv := eulerSynthesis_mul_moebiusInverse X hX w hkill
  inv_val := moebiusInverse_mul_eulerSynthesis X hX w hkill

/-- Formal coefficient derivative of the finite Dirichlet polynomial. -/
def eulerCoefficientDerivative (X : ℕ) (w : ℕ →*₀ R) : R :=
  -synthesis X w ArithmeticFunction.log

/-- The negative finite logarithmic coefficient derivative is the Mangoldt current. -/
theorem logarithmicCurrent (X : ℕ) (w : ℕ →*₀ R)
    (hkill : ∀ n, X < n → w n = 0) :
    -(moebiusInverse X w * eulerCoefficientDerivative X w) =
      synthesis X w ArithmeticFunction.vonMangoldt := by
  rw [moebiusInverse, eulerCoefficientDerivative, mul_neg, neg_neg,
    ← synthesis_mul X w hkill, ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]

end Riemann.Arithmetic
