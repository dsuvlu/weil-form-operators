import Riemann.Arithmetic.EulerSupport
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorial.Basic

/-! Finite Euler products for a terminating multiplicative representation.
Every local inverse is an explicitly terminating geometric sum. No analytic
Euler product or convergence hypothesis enters these identities. -/

noncomputable section
open scoped BigOperators

namespace Riemann.Arithmetic

variable {R : Type*} [CommRing R]

/-- A completely multiplicative representation viewed as an arithmetic function. -/
def multiplicativeCoefficients (w : ℕ →*₀ R) : ArithmeticFunction R := w.toZeroHom

theorem multiplicativeCoefficients_isMultiplicative (w : ℕ →*₀ R) :
    (multiplicativeCoefficients w).IsMultiplicative :=
  ⟨w.map_one, fun _ => w.map_mul _ _⟩

/-- Classical divisor factorization, before applying the finite-window cutoff. -/
theorem divisorSum_eulerFactorization (w : ℕ →*₀ R) {M : ℕ} (hM : M ≠ 0) :
    (∑ n ∈ M.divisors, w n) =
      ∏ p ∈ M.primeFactors, ∑ k ∈ Finset.range (M.factorization p + 1), (w p) ^ k := by
  let f := multiplicativeCoefficients w
  have hf := ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (multiplicativeCoefficients_isMultiplicative w)
  have h := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    ((↑ArithmeticFunction.zeta : ArithmeticFunction R) * f) hf hM
  rw [ArithmeticFunction.coe_zeta_mul_apply] at h
  change (∑ n ∈ M.divisors, w n) = _ at h
  rw [h]
  change (∏ p ∈ M.factorization.support,
    ((↑ArithmeticFunction.zeta : ArithmeticFunction R) * f) (p ^ M.factorization p)) = _
  apply Finset.prod_congr M.support_factorization
  intro p hp
  rw [ArithmeticFunction.coe_zeta_mul_apply,
    Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]
  apply Finset.sum_congr rfl
  intro k hk
  exact w.map_pow p k

/-- A prime factor is nilpotent at a uniform finite exponent. -/
theorem primeWeight_pow_eq_zero (w : ℕ →*₀ R) (X : ℕ)
    (hkill : ∀ n, X < n → w n = 0) {p : ℕ} (hp : p.Prime) :
    (w p) ^ (X + 1) = 0 := by
  rw [← map_pow]
  exact hkill _ ((Nat.lt_succ_self X).trans (Nat.lt_pow_self hp.one_lt))

/-- Left inverse of each Euler denominator, given by a finite sum. -/
theorem primeEulerFactor_left_inverse (w : ℕ →*₀ R) (X : ℕ)
    (hkill : ∀ n, X < n → w n = 0) {p : ℕ} (hp : p.Prime) :
    (∑ k ∈ Finset.range (X + 1), (w p) ^ k) * (1 - w p) = 1 := by
  rw [geom_sum_mul_neg, primeWeight_pow_eq_zero w X hkill hp, sub_zero]

/-- Right inverse of each Euler denominator, given by the same finite sum. -/
theorem primeEulerFactor_right_inverse (w : ℕ →*₀ R) (X : ℕ)
    (hkill : ∀ n, X < n → w n = 0) {p : ℕ} (hp : p.Prime) :
    (1 - w p) * (∑ k ∈ Finset.range (X + 1), (w p) ^ k) = 1 := by
  rw [mul_comm]
  exact primeEulerFactor_left_inverse w X hkill hp

/-- Exact terminating Euler factorization. The bound is inclusive, and every
omitted integer has zero image in the multiplicative representation. -/
theorem finiteEuler_factorization (w : ℕ →*₀ R) (X : ℕ)
    (hkill : ∀ n, X < n → w n = 0) :
    (∑ n ∈ Finset.Ioc 0 X, w n) =
      ∏ p ∈ Nat.primesBelow (X + 1), ∑ k ∈ Finset.range (X + 1), (w p) ^ k := by
  rw [← sum_factorial_divisors_eq_Ioc X w hkill,
    divisorSum_eulerFactorization w (Nat.factorial_ne_zero X),
    factorial_primeFactors_eq_primesBelow]
  apply Finset.prod_congr rfl
  intro p hp
  exact prime_geometric_sum_eq_range X w hkill (Nat.mem_primesBelow.mp hp).2

/-- The finite prime-denominator product is an explicit inverse of the
all-integer synthesis. -/
theorem finiteEuler_denominator_inverse (w : ℕ →*₀ R) (X : ℕ)
    (hkill : ∀ n, X < n → w n = 0) :
    (∑ n ∈ Finset.Ioc 0 X, w n) *
      (∏ p ∈ Nat.primesBelow (X + 1), (1 - w p)) = 1 := by
  rw [finiteEuler_factorization w X hkill, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro p hp
  exact primeEulerFactor_left_inverse w X hkill (Nat.mem_primesBelow.mp hp).2

end Riemann.Arithmetic
