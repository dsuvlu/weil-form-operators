import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! # Real endpoint inverse-square-root sums

Elementary square-root telescoping gives a uniform error for inclusive real
endpoints. This is the scalar estimate used by the raw Euler graph witness.
-/
noncomputable section
open Finset
namespace Riemann.Analysis.HalfLine

lemma sqrt_increment_lower {x : ℝ} (hx : 0 < x) :
    2 * (Real.sqrt (x + 1) - Real.sqrt x) ≤ (Real.sqrt x)⁻¹ := by
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hx)).2
  nlinarith [Real.sq_sqrt hx.le, Real.sq_sqrt (show 0 ≤ x + 1 by linarith),
    sq_nonneg (Real.sqrt (x + 1) - Real.sqrt x)]

lemma sqrt_increment_upper {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt (x + 1))⁻¹ ≤ 2 * (Real.sqrt (x + 1) - Real.sqrt x) := by
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (show 0 < x + 1 by linarith))).2
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt (show 0 ≤ x + 1 by linarith),
    sq_nonneg (Real.sqrt (x + 1) - Real.sqrt x)]

lemma sqrt_short_increment {a b : ℝ} (ha : 0 < a) (hb : b ≤ a + 1) :
    2 * (Real.sqrt b - Real.sqrt a) ≤ (Real.sqrt a)⁻¹ := by
  calc
    _ ≤ 2 * (Real.sqrt (a + 1) - Real.sqrt a) := by gcongr
    _ ≤ _ := sqrt_increment_lower ha

lemma inv_sqrt_sum_bounds {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    2 * (Real.sqrt (q + 1) - Real.sqrt p) ≤
        ∑ n ∈ Icc p q, (Real.sqrt n)⁻¹ ∧
    (∑ n ∈ Icc p q, (Real.sqrt n)⁻¹) ≤
        (Real.sqrt p)⁻¹ + 2 * (Real.sqrt q - Real.sqrt p) := by
  induction q, hpq using Nat.le_induction with
  | base =>
      simp only [Icc_self, sum_singleton]
      constructor
      · exact sqrt_increment_lower (by exact_mod_cast hp)
      · simp
  | succ q hpq ih =>
      rw [sum_Icc_succ_top (Nat.le_succ_of_le hpq)]
      have hl := sqrt_increment_lower (x := (q : ℝ) + 1) (by positivity)
      have hu := sqrt_increment_upper (x := (q : ℝ)) (by positivity)
      push_cast at *
      constructor <;> linarith [ih.1, ih.2]

/-- Inclusive real endpoint comparison with an explicit absolute error. -/
theorem inv_sqrt_sum_real_endpoints {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    |(∑ n ∈ Icc ⌈a⌉₊ ⌊b⌋₊, (Real.sqrt n)⁻¹) -
      2 * (Real.sqrt b - Real.sqrt a)| ≤ (Real.sqrt a)⁻¹ := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hc := Nat.le_ceil a
  have hcl := Nat.ceil_lt_add_one ha0.le
  have hf := Nat.floor_le hb0
  have hfl := Nat.lt_floor_add_one b
  have hpa : Real.sqrt a ≤ Real.sqrt (⌈a⌉₊ : ℝ) := Real.sqrt_le_sqrt hc
  have hqb : Real.sqrt (⌊b⌋₊ : ℝ) ≤ Real.sqrt b := Real.sqrt_le_sqrt hf
  have hbq : Real.sqrt b ≤ Real.sqrt ((⌊b⌋₊ : ℝ) + 1) :=
    Real.sqrt_le_sqrt hfl.le
  have hp : 0 < ⌈a⌉₊ := by exact_mod_cast (show (0 : ℝ) < ⌈a⌉₊ by linarith)
  have hi : (Real.sqrt (⌈a⌉₊ : ℝ))⁻¹ ≤ (Real.sqrt a)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr ha0) hpa
  by_cases hpq : ⌈a⌉₊ ≤ ⌊b⌋₊
  · obtain ⟨hl, hu⟩ := inv_sqrt_sum_bounds hp hpq
    have hs := sqrt_short_increment ha0 hcl.le
    apply abs_le.mpr
    constructor <;> linarith
  · have hempty : Icc ⌈a⌉₊ ⌊b⌋₊ = ∅ := Icc_eq_empty (by omega)
    rw [hempty, sum_empty, zero_sub, abs_neg, abs_of_nonneg (by
      have := Real.sqrt_le_sqrt hab
      linarith)]
    have hqp : (⌊b⌋₊ : ℝ) + 1 ≤ ⌈a⌉₊ := by exact_mod_cast (show ⌊b⌋₊ + 1 ≤ ⌈a⌉₊ by omega)
    exact sqrt_short_increment ha0 (by linarith)

end Riemann.Analysis.HalfLine
