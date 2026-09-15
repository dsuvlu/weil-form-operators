import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Scalar logarithmic bounds for a finite positive spectral measure. -/
noncomputable section
open Set MeasureTheory
namespace Riemann.Capacity

/-- One positive eigenvalue contributes between the logarithmic and linear
parameter-ratio multiples of its soft occupation at the left endpoint. -/
theorem scalar_log_ratio_bounds {l a b : ℝ} (hl : 0 < l) (ha : 0 < a) (hab : a ≤ b) :
    Real.log (b/a) * (a/(l+a)) ≤ Real.log ((l+b)/(l+a)) ∧
      Real.log ((l+b)/(l+a)) ≤ (b/a-1) * (a/(l+a)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hla := add_pos hl ha
  have hlb := add_pos hl hb
  have hint : IntervalIntegrable (fun t : ℝ => 1/(l+t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro t ht
    exact (continuousAt_const.div (continuousAt_const.add continuousAt_id)
      (add_pos hl (lt_of_lt_of_le ha ht.1)).ne').continuousWithinAt
  have heq : (∫ t in a..b, 1/(l+t)) = Real.log ((l+b)/(l+a)) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Real.log (l+t))
      (f' := fun t => 1/(l+t)) (a := a) (b := b) (fun t ht => ?_) hint
    · rw [Real.log_div hlb.ne' hla.ne']
      exact h
    · rw [uIcc_of_le hab] at ht
      exact ((hasDerivAt_id t).const_add l).log (add_pos hl (lt_of_lt_of_le ha ht.1)).ne'
  have hinv : IntervalIntegrable (fun t : ℝ => 1/t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro t ht
    exact (continuousAt_const.div continuousAt_id (lt_of_lt_of_le ha ht.1).ne').continuousWithinAt
  constructor
  · have hmono := intervalIntegral.integral_mono_on hab
      (hinv.const_mul (a/(l+a))) hint (fun t ht => ?_)
    · rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos ha hb, heq] at hmono
      nlinarith
    · have htpos := lt_of_lt_of_le ha ht.1
      rw [div_mul_div_comm, mul_one]
      apply (div_le_div_iff₀ (mul_pos hla htpos) (add_pos hl htpos)).mpr
      nlinarith [mul_nonneg hl.le (sub_nonneg.mpr ht.1)]
  · have hmono := intervalIntegral.integral_mono_on hab hint
      (intervalIntegrable_const (c := 1/(l+a))) (fun t ht => ?_)
    · rw [heq, intervalIntegral.integral_const] at hmono
      have hfactor : (b/a-1)*(a/(l+a)) = (b-a)*(1/(l+a)) := by field_simp
      rw [hfactor]
      exact hmono
    · exact one_div_le_one_div_of_le hla (by linarith [ht.1])

/-- Finite positive spectral sums inherit the exact capacity bounds. -/
theorem finite_log_ratio_bounds {ι : Type*} [Fintype ι]
    (lambda : ι → ℝ) (hl : ∀ i, 0 < lambda i)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (b/a) * (∑ i, a/(lambda i+a)) ≤
      ∑ i, Real.log ((lambda i+b)/(lambda i+a)) ∧
    (∑ i, Real.log ((lambda i+b)/(lambda i+a))) ≤
      (b/a-1) * (∑ i, a/(lambda i+a)) := by
  simp only [Finset.mul_sum]
  exact ⟨Finset.sum_le_sum (fun i _ => (scalar_log_ratio_bounds (hl i) ha hab).1),
    Finset.sum_le_sum (fun i _ => (scalar_log_ratio_bounds (hl i) ha hab).2)⟩

end Riemann.Capacity
