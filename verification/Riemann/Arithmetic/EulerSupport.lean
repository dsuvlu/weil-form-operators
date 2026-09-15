import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Factorization.Divisors
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Elementary support bookkeeping for a terminating finite Euler product.
Factorial divisors contain every positive index up to the cutoff; all other
terms vanish by the stated multiplicative support condition.
-/

noncomputable section
open scoped BigOperators

namespace Riemann.Arithmetic

/-- The prime support of X! is exactly the primes at most X. -/
theorem factorial_primeFactors_eq_primesBelow (X : ℕ) :
    (X.factorial).primeFactors = Nat.primesBelow (X + 1) := by
  ext p
  rw [Nat.mem_primeFactors, Nat.mem_primesBelow]
  constructor
  · rintro ⟨hp, hd, _⟩
    exact ⟨Nat.lt_succ_of_le (hp.dvd_factorial.mp hd), hp⟩
  · rintro ⟨hpX, hp⟩
    exact ⟨hp, hp.dvd_factorial.mpr (Nat.le_of_lt_succ hpX), Nat.factorial_ne_zero X⟩

variable {R : Type*} [CommRing R]

/-- Replacing factorial divisors by the entire supported positive interval loses no term. -/
theorem sum_factorial_divisors_eq_Ioc (X : ℕ) (w : ℕ →*₀ R)
    (hkill : ∀ n : ℕ, X < n → w n = 0) :
    (∑ n ∈ (X.factorial).divisors, w n) = ∑ n ∈ Finset.Ioc 0 X, w n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    have h := Finset.mem_Ioc.mp hn
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial h.1 h.2, Nat.factorial_ne_zero X⟩
  · intro n hn hnot
    apply hkill
    have hp : 0 < n := Nat.pos_of_mem_divisors hn
    simp only [Finset.mem_Ioc, not_and] at hnot
    exact Nat.lt_of_not_ge (hnot hp)

/-- A nonzero prime-power weight lies within both useful exponent cutoffs. -/
theorem nonzero_prime_power_support (X : ℕ) (w : ℕ →*₀ R)
    (hkill : ∀ n : ℕ, X < n → w n = 0) {p k : ℕ} (hp : p.Prime)
    (hw : (w p) ^ k ≠ 0) : k ≤ X ∧ k ≤ (X.factorial).factorization p := by
  have hpow : p ^ k ≤ X := by
    by_contra hn
    have hz := hkill (p ^ k) (Nat.lt_of_not_ge hn)
    exact hw (by simpa only [map_pow] using hz)
  constructor
  · exact le_trans (Nat.lt_pow_self hp.one_lt).le hpow
  · apply (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero X)).mp
    exact Nat.dvd_factorial (pow_pos hp.pos _) hpow

/-- The factorial valuation and uniform cutoff give the same terminating local factor. -/
theorem prime_geometric_sum_eq_range (X : ℕ) (w : ℕ →*₀ R)
    (hkill : ∀ n : ℕ, X < n → w n = 0) {p : ℕ} (hp : p.Prime) :
    (∑ k ∈ Finset.range ((X.factorial).factorization p + 1), (w p) ^ k) =
      ∑ k ∈ Finset.range (X + 1), (w p) ^ k := by
  apply Finset.sum_congr_of_eq_on_inter
  · intro k hk hnot
    by_contra hw
    have h := (nonzero_prime_power_support X w hkill hp hw).1
    exact hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
  · intro k hk hnot
    by_contra hw
    have h := (nonzero_prime_power_support X w hkill hp hw).2
    exact hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
  · intros
    rfl

end Riemann.Arithmetic
