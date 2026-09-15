import Riemann.Analysis.HalfLine.InverseSqrtSum
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Scalar raw Euler box outputs

The lower endpoint is clamped at one, and both arithmetic endpoints are
inclusive. The estimates retain the main region and the terminal strip.
-/
noncomputable section
open Finset Set Filter
open scoped Topology
namespace Riemann.Analysis.HalfLine

def rawBoxScalar (T t : ℝ) : ℝ :=
  if 0 ≤ t then Real.exp (-T/2) *
    ∑ n ∈ Icc ⌈max 1 (Real.exp (T-t))⌉₊ ⌊Real.exp (T+1-t)⌋₊,
      (Real.sqrt n)⁻¹ else 0

def graphDefectScalar (t : ℝ) : ℝ :=
  if 0 ≤ t then 2*(Real.exp (1/2)-1)*Real.exp (-t/2) else 0

lemma rawBoxScalar_nonneg (T t : ℝ) : 0 ≤ rawBoxScalar T t := by
  unfold rawBoxScalar
  split_ifs <;> positivity

lemma graphDefectScalar_nonneg (t : ℝ) : 0 ≤ graphDefectScalar t := by
  unfold graphDefectScalar
  split_ifs
  · have := Real.one_le_exp (show (0:ℝ) ≤ 1/2 by norm_num)
    positivity
  · rfl

lemma box_main_term (T t : ℝ) :
    Real.exp (-T/2) * (2*(Real.sqrt (Real.exp (T+1-t)) -
      Real.sqrt (Real.exp (T-t)))) =
        2*(Real.exp (1/2)-1)*Real.exp (-t/2) := by
  rw [← Real.exp_half, ← Real.exp_half]
  have h1 : Real.exp (-T/2)*Real.exp ((T+1-t)/2) =
      Real.exp (1/2)*Real.exp (-t/2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-T/2)*Real.exp ((T-t)/2) = Real.exp (-t/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith

/-- Uniform error in the main region, before taking any limit. -/
theorem rawBoxScalar_main_error {T t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    |rawBoxScalar T t - graphDefectScalar t| ≤ Real.exp (-T+t/2) := by
  have ha : 1 ≤ Real.exp (T-t) := Real.one_le_exp (sub_nonneg.mpr htT)
  have hab : Real.exp (T-t) ≤ Real.exp (T+1-t) := Real.exp_le_exp.mpr (by linarith)
  have hb := inv_sqrt_sum_real_endpoints ha hab
  rw [rawBoxScalar, graphDefectScalar, if_pos ht, if_pos ht, max_eq_right ha,
    ← box_main_term T t, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-T/2)*(Real.sqrt (Real.exp (T-t)))⁻¹ :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_half, ← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring

/-- A global exponential envelope, including the terminal strip. -/
theorem rawBoxScalar_le (T t : ℝ) (ht : 0 ≤ t) :
    rawBoxScalar T t ≤ 2*Real.exp (1/2)*Real.exp (-t/2) := by
  let p : ℕ := ⌈max 1 (Real.exp (T-t))⌉₊
  let q : ℕ := ⌊Real.exp (T+1-t)⌋₊
  have hp1 : (1:ℝ) ≤ p := (le_max_left _ _).trans (Nat.le_ceil _)
  have hp : 0 < p := by exact_mod_cast (show (0:ℝ) < p by linarith)
  have hsp : 1 ≤ Real.sqrt p := by
    simpa using Real.sqrt_le_sqrt hp1
  have hsq : Real.sqrt q ≤ Real.sqrt (Real.exp (T+1-t)) :=
    Real.sqrt_le_sqrt (Nat.floor_le (Real.exp_pos _).le)
  have hi : (Real.sqrt p)⁻¹ ≤ 1 := by
    simpa using inv_anti₀ (show (0:ℝ)<1 by norm_num) hsp
  have hsum : (∑ n ∈ Icc p q, (Real.sqrt n)⁻¹) ≤
      2*Real.sqrt (Real.exp (T+1-t)) := by
    by_cases hpq : p ≤ q
    · have h := (inv_sqrt_sum_bounds hp hpq).2
      linarith
    · rw [Finset.Icc_eq_empty (by omega), sum_empty]
      positivity
  unfold rawBoxScalar
  rw [if_pos ht]
  calc
    _ ≤ Real.exp (-T/2)*(2*Real.sqrt (Real.exp (T+1-t))) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_half]
      have he : Real.exp (-T/2)*Real.exp ((T+1-t)/2) =
          Real.exp (1/2)*Real.exp (-t/2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      nlinarith

theorem rawBoxScalar_error_envelope (T t : ℝ) :
    |rawBoxScalar T t - graphDefectScalar t| ≤
      if 0 ≤ t then 4*Real.exp (1/2)*Real.exp (-t/2) else 0 := by
  by_cases ht : 0 ≤ t
  · rw [if_pos ht]
    have hraw := rawBoxScalar_le T t ht
    have hdef := graphDefectScalar_nonneg t
    have hraw0 := rawBoxScalar_nonneg T t
    rw [abs_le]
    unfold graphDefectScalar at hdef ⊢
    rw [if_pos ht] at hdef ⊢
    constructor <;> nlinarith [Real.exp_pos (-t/2), Real.exp_pos (1/2)]
  · simp [rawBoxScalar, graphDefectScalar, ht]

/-- Pointwise convergence of the translated boxes' arithmetic outputs. -/
theorem rawBoxScalar_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ => rawBoxScalar n t) atTop (𝓝 (graphDefectScalar t)) := by
  by_cases ht : 0 ≤ t
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hexp : Tendsto (fun n : ℕ => Real.exp (-(n:ℝ)+t/2)) atTop (𝓝 0) := by
      have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        tendsto_natCast_atTop_atTop).mul_const (Real.exp (t/2))
      simpa only [Function.comp_def, zero_mul, Real.exp_add] using h
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ?_ hexp
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop t)] with n hn
    exact rawBoxScalar_main_error ht hn
  · simp only [rawBoxScalar, graphDefectScalar, ht, ↓reduceIte]
    exact tendsto_const_nhds

end Riemann.Analysis.HalfLine
