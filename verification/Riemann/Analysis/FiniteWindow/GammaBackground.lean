import Riemann.Analysis.FiniteWindow.GammaCurrent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Exact scalar normalization between the compensated Gamma current and the
native Archimedean background. The finite subtraction integral is evaluated. -/
noncomputable section
open MeasureTheory Set
namespace Riemann.Analysis.FiniteWindow

def nativeGammaConstant (L : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (4 * Real.pi * Real.tanh (L / 2))

lemma tanh_half_exp (L : ℝ) :
    Real.tanh (L/2) = (1 - Real.exp (-L)) / (1 + Real.exp (-L)) := by
  rw [Real.tanh_eq]
  apply (div_eq_div_iff (by positivity : Real.exp (L/2) + Real.exp (-(L/2)) ≠ 0)
    (by positivity : 1 + Real.exp (-L) ≠ 0)).mpr
  have he : Real.exp (L/2) * Real.exp (-L) = Real.exp (-(L/2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith [he]

/-- The finite-window Gamma constant agrees with the native tanh normalization. -/
theorem gammaConstant_sub_native {L : ℝ} (hL : 0 < L) :
    gammaConstant L - nativeGammaConstant L / 2 =
      Real.log (1 + Real.exp (-L)) - Real.log 2 := by
  have hm : 0 < 1 - Real.exp (-L) := by
    have he := Real.exp_lt_one_iff.mpr (show -L < 0 by linarith)
    linarith
  have hp : 0 < 1 + Real.exp (-L) := by positivity
  have hq : 1 - Real.exp (-2*L) = (1 - Real.exp (-L)) * (1 + Real.exp (-L)) := by
    have he : Real.exp (-2*L) = Real.exp (-L) * Real.exp (-L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have hh := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)
    norm_num only [show (2 : ℝ) * 2 = 4 by norm_num] at hh
    linarith
  unfold gammaConstant nativeGammaConstant
  rw [tanh_half_exp, hq, Real.log_mul hm.ne' hp.ne',
    Real.log_mul (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (div_ne_zero hm.ne' hp.ne'),
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero,
    Real.log_div hm.ne' hp.ne', h4]
  ring

lemma hasDerivAt_log_logistic (y : ℝ) :
    HasDerivAt (fun y => Real.log (1 + Real.exp (-y)))
      (-(Real.exp y + 1)⁻¹) y := by
  have he := (hasDerivAt_id y).neg.exp
  have hp0 : 1 + Real.exp (-y) ≠ 0 := by positivity
  have hh := ((hasDerivAt_const y (1 : ℝ)).add he).log
    (by simpa only [Pi.add_apply, Pi.neg_apply, id_eq] using hp0)
  convert! hh using 1
  simp only [Pi.add_apply, Pi.neg_apply, id_eq]
  rw [Real.exp_neg]
  have hp : Real.exp y ≠ 0 := (Real.exp_pos y).ne'
  have hs : Real.exp y + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The integrable scalar background difference has this exact finite integral. -/
theorem integral_logistic {L : ℝ} (_hL : 0 ≤ L) :
    (∫ y in 0..L, (Real.exp y + 1)⁻¹) =
      Real.log 2 - Real.log (1 + Real.exp (-L)) := by
  have hi : IntervalIntegrable (fun y => (Real.exp y + 1)⁻¹) volume 0 L := by
    apply Continuous.intervalIntegrable
    exact (Real.continuous_exp.add continuous_const).inv₀ (fun y => (add_pos (Real.exp_pos y) zero_lt_one).ne')
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := L)
    (fun y _ => (hasDerivAt_log_logistic y).neg) (by simpa only [neg_neg] using hi)
  simpa only [Pi.neg_apply, neg_neg, neg_sub_neg, neg_zero, Real.exp_zero, one_add_one_eq_two] using hh

/-- The two normalizations differ by exactly the finite scalar subtraction. -/
theorem gamma_background_cancellation {L : ℝ} (hL : 0 < L) :
    gammaConstant L - nativeGammaConstant L / 2 +
      (∫ y in 0..L, (Real.exp y + 1)⁻¹) = 0 := by
  rw [gammaConstant_sub_native hL, integral_logistic hL.le]
  ring

end Riemann.Analysis.FiniteWindow
