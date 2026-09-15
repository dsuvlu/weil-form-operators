import Riemann.Arithmetic.MultiplicativeShift
import Riemann.Arithmetic.LogarithmicCurrent
import Riemann.Arithmetic.FiniteEulerProduct
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
open Finset
namespace Riemann.Arithmetic

/-- Inclusive bookkeeping bound; terms at or beyond exp L vanish exactly. -/
def arithmeticBound (L : ℝ) : ℕ := Nat.ceil (Real.exp L)

theorem arithmeticBound_pos (L : ℝ) : 1 ≤ arithmeticBound L := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro h
  have he := Nat.le_ceil (Real.exp L)
  rw [show Nat.ceil (Real.exp L) = 0 from h] at he
  have he0 : Real.exp L ≤ 0 := by simpa using he
  exact (not_le_of_gt (Real.exp_pos L)) he0

@[simp] theorem weightedShift_apply (L : ℝ) (s : ℂ) (n : ℕ) :
    weightedShift L s n = algebraMap ℂ (shiftAlgebra L) (dirichletWeight s n) *
      shiftCharacter L n := rfl

theorem weightedShift_killed (L : ℝ) (s : ℂ) {n : ℕ}
    (h : Real.exp L ≤ (n : ℝ)) : weightedShift L s n = 0 := by
  have hV : shiftCharacter L n = 0 := by
    apply Subtype.ext
    exact multiplicativeShift_killed_of_exp_le L h
  simp [hV]

theorem weightedShift_bound (L : ℝ) (s : ℂ) (n : ℕ)
    (hn : arithmeticBound L < n) : weightedShift L s n = 0 := by
  apply weightedShift_killed
  exact (Nat.le_ceil (Real.exp L)).trans (by exact_mod_cast le_of_lt hn)

/-- The finite arithmetic operator, in the genuine generated shift algebra. -/
def nativeEuler (L : ℝ) (s : ℂ) : shiftAlgebra L :=
  eulerSynthesis (arithmeticBound L) (weightedShift L s)

def nativeMoebius (L : ℝ) (s : ℂ) : shiftAlgebra L :=
  moebiusInverse (arithmeticBound L) (weightedShift L s)

def nativeCoefficientDerivative (L : ℝ) (s : ℂ) : shiftAlgebra L :=
  eulerCoefficientDerivative (arithmeticBound L) (weightedShift L s)

def nativeMangoldtCurrent (L : ℝ) (s : ℂ) : shiftAlgebra L :=
  synthesis (arithmeticBound L) (weightedShift L s) ArithmeticFunction.vonMangoldt

/-- This finite sum has precisely the strict physical survival cutoff. -/
theorem nativeEuler_sum (L : ℝ) (s : ℂ) :
    nativeEuler L s = ∑ n ∈ (Ioc 0 (arithmeticBound L)).filter
      (fun n : ℕ => (n : ℝ) < Real.exp L), weightedShift L s n := by
  rw [nativeEuler, eulerSynthesis_sum]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnot
  exact weightedShift_killed L s (by simpa only [mem_filter, hn, true_and, not_lt] using hnot)

theorem nativeMoebius_left_inverse (L : ℝ) (s : ℂ) :
    nativeMoebius L s * nativeEuler L s = 1 :=
  moebiusInverse_mul_eulerSynthesis _ (arithmeticBound_pos L) _ (weightedShift_bound L s)

theorem nativeMoebius_right_inverse (L : ℝ) (s : ℂ) :
    nativeEuler L s * nativeMoebius L s = 1 := by
  rw [mul_comm]; exact nativeMoebius_left_inverse L s

theorem native_logarithmicCurrent (L : ℝ) (s : ℂ) :
    -(nativeMoebius L s * nativeCoefficientDerivative L s) = nativeMangoldtCurrent L s :=
  logarithmicCurrent _ _ (weightedShift_bound L s)

/-- Finite coefficient synthesis with every nonsurviving arithmetic term removed. -/
theorem synthesis_weightedShift_sum (L : ℝ) (s : ℂ) (a : ArithmeticFunction ℝ) :
    synthesis (arithmeticBound L) (weightedShift L s) a =
      ∑ n ∈ (Ioc 0 (arithmeticBound L)).filter (fun n : ℕ => (n : ℝ) < Real.exp L),
        a n • weightedShift L s n := by
  unfold synthesis
  symm
  calc
    _ = ∑ n ∈ (Ioc 0 (arithmeticBound L)).filter
        (fun n : ℕ => (n : ℝ) < Real.exp L), twist (weightedShift L s) a n := by
      simp only [twist_apply, Algebra.smul_def]
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hn hnot
      have hk : weightedShift L s n = 0 := weightedShift_killed L s
        (by simpa only [mem_filter, hn, true_and, not_lt] using hnot)
      simp [hk]

open scoped ArithmeticFunction.Moebius

/-- Möbius coefficients in the native physical survival window. -/
theorem nativeMoebius_sum (L : ℝ) (s : ℂ) :
    nativeMoebius L s = ∑ n ∈ (Ioc 0 (arithmeticBound L)).filter
      (fun n : ℕ => (n : ℝ) < Real.exp L), (μ n : ℝ) • weightedShift L s n := by
  exact synthesis_weightedShift_sum L s (μ : ArithmeticFunction ℝ)

/-- The current has Λ(p^k)=log p for k>0, with Λ(1)=0. -/
theorem nativeMangoldtCurrent_sum (L : ℝ) (s : ℂ) :
    nativeMangoldtCurrent L s = ∑ n ∈ (Ioc 0 (arithmeticBound L)).filter
      (fun n : ℕ => (n : ℝ) < Real.exp L),
        ArithmeticFunction.vonMangoldt n • weightedShift L s n :=
  synthesis_weightedShift_sum L s ArithmeticFunction.vonMangoldt

/-- Explicit function action with the same physical surviving indices. -/
theorem nativeEuler_apply (L : ℝ) (s : ℂ) (f : WindowFunctions L) (t : Window L) :
    (nativeEuler L s : Module.End ℂ (WindowFunctions L)) f t =
      ∑ n ∈ (Ioc 0 (arithmeticBound L)).filter (fun n : ℕ => (n : ℝ) < Real.exp L),
        Complex.exp (-s * (Real.log n : ℂ)) * (killedShift L (natLog n) f t) := by
  rw [nativeEuler_sum]
  change ((shiftAlgebra L).val (∑ n ∈ (Ioc 0 (arithmeticBound L)).filter
    (fun n : ℕ => (n : ℝ) < Real.exp L), weightedShift L s n)) f t = _
  rw [map_sum]
  simp only [LinearMap.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := ne_of_gt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  simp [weightedShift_apply, dirichletWeight, hn0, multiplicativeShift_eq L hn0,
    Algebra.algebraMap_eq_smul_one]

/-- Explicit terminating inverse of the prime denominator. -/
def nativePrimeFactor (L : ℝ) (s : ℂ) (p : ℕ) : shiftAlgebra L :=
  ∑ k ∈ Finset.range (arithmeticBound L + 1), (weightedShift L s p)^k

theorem nativePrimeFactor_left_inverse (L : ℝ) (s : ℂ) {p : ℕ} (hp : p.Prime) :
    nativePrimeFactor L s p * (1 - weightedShift L s p) = 1 :=
  primeEulerFactor_left_inverse _ _ (weightedShift_bound L s) hp

theorem nativePrimeFactor_right_inverse (L : ℝ) (s : ℂ) {p : ℕ} (hp : p.Prime) :
    (1 - weightedShift L s p) * nativePrimeFactor L s p = 1 :=
  primeEulerFactor_right_inverse _ _ (weightedShift_bound L s) hp

/-- Only surviving prime powers occur in a local factor. -/
theorem nativePrimeFactor_sum (L : ℝ) (s : ℂ) (p : ℕ) :
    nativePrimeFactor L s p =
      ∑ k ∈ (Finset.range (arithmeticBound L + 1)).filter
        (fun k : ℕ => (p^k : ℝ) < Real.exp L), weightedShift L s (p^k) := by
  unfold nativePrimeFactor
  simp only [← map_pow]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k hk hnot
  apply weightedShift_killed
  have h := hnot
  simpa only [mem_filter, hk, true_and, not_lt, Nat.cast_pow] using h

theorem nativePrimeFactor_eq_one (L : ℝ) (s : ℂ) {p : ℕ}
    (hp : Real.exp L ≤ (p : ℝ)) : nativePrimeFactor L s p = 1 := by
  simp [nativePrimeFactor, weightedShift_killed L s hp]

/-- The Euler product is indexed by exactly the surviving physical primes. -/
theorem nativeEuler_factorization (L : ℝ) (s : ℂ) :
    nativeEuler L s = ∏ p ∈ (Nat.primesBelow (arithmeticBound L + 1)).filter
      (fun p : ℕ => (p : ℝ) < Real.exp L), nativePrimeFactor L s p := by
  rw [nativeEuler, eulerSynthesis_sum, finiteEuler_factorization _ _ (weightedShift_bound L s)]
  change (∏ p ∈ Nat.primesBelow (arithmeticBound L + 1), nativePrimeFactor L s p) = _
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro p hp hnot
  apply nativePrimeFactor_eq_one
  simpa only [mem_filter, hp, true_and, not_lt] using hnot

end Riemann.Arithmetic
