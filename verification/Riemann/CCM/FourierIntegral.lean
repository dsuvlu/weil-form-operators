import Riemann.CCM.FourierSection
import Riemann.Basic.ComplexSinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The centered observation of a native finite Fourier polynomial. -/

noncomputable section
open scoped BigOperators Interval

namespace Riemann.CCM.Native

/-- The native finite centered Fourier observation, including removable frequencies. -/
def centeredFourierObservation {N : ℕ} (L : ℝ) (v : Section N) (z : ℂ) : ℂ :=
  (Real.sqrt L : ℂ) * ∑ i, v i * (-1 : ℂ) ^ (mode i) *
    Riemann.Basic.complexSinc ((L : ℂ) * (z - (frequency L i : ℂ)) / 2)

/-- The finite observation is entire for every fixed coefficient vector. -/
theorem differentiable_centeredFourierObservation {N : ℕ} (L : ℝ) (v : Section N) :
    Differentiable ℂ (centeredFourierObservation L v) := by
  apply Differentiable.const_mul
  apply Differentiable.fun_sum
  intro i hi
  apply Differentiable.const_mul
  exact Riemann.Basic.differentiable_complexSinc.comp
    (((differentiable_id.sub_const _).const_mul (L : ℂ)).div_const 2)

/-- Integral of a complex exponential over a symmetric finite interval. -/
theorem integral_symmetric_exp (L : ℝ) (w : ℂ) :
    (∫ t in -(L / 2)..L / 2, Complex.exp (-Complex.I * w * (t : ℂ))) =
      (L : ℂ) * Riemann.Basic.complexSinc ((L : ℂ) * w / 2) := by
  by_cases hL : L = 0
  · simp [hL]
  by_cases hw : w = 0
  · simp [hw, Complex.real_smul]
  have hc : -Complex.I * w ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hw
  have ha : (L : ℂ) * w / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hL) hw) (by norm_num)
  rw [integral_exp_mul_complex hc, Riemann.Basic.complexSinc_of_ne_zero ha]
  have he₁ : -Complex.I * w * ((L / 2 : ℝ) : ℂ) = -((L : ℂ) * w / 2) * Complex.I := by
    push_cast; ring
  have he₂ : -Complex.I * w * ((-(L / 2) : ℝ) : ℂ) = ((L : ℂ) * w / 2) * Complex.I := by
    push_cast; ring
  rw [he₁, he₂, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  field_simp [Complex.ofReal_ne_zero.mpr hL]
  ring

/-- The centered interval exponential is exactly the removable sinc expression. -/
theorem integral_centered_exp (L : ℝ) (w : ℂ) :
    (∫ t in (0 : ℝ)..L, Complex.exp (-Complex.I * w * ((t : ℂ) - (L : ℂ) / 2))) =
      (L : ℂ) * Riemann.Basic.complexSinc ((L : ℂ) * w / 2) := by
  have hfun : (fun t : ℝ => Complex.exp (-Complex.I * w * ((t : ℂ) - (L : ℂ) / 2))) =
      (fun t : ℝ => Complex.exp (-Complex.I * w * ((t - L / 2 : ℝ) : ℂ))) := by
    ext t; push_cast; rfl
  rw [hfun]
  rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => Complex.exp (-Complex.I * w * (t : ℂ))) (L / 2)]
  simpa only [zero_sub, show L - L / 2 = L / 2 by ring] using integral_symmetric_exp L w

/-- Half-period phases are the signed integer Fourier phases. -/
theorem frequency_half_period {N : ℕ} {L : ℝ} (hL : 0 < L) (i : Index N) :
    Complex.exp (Complex.I * (frequency L i : ℂ) * (L : ℂ) / 2) =
      (-1 : ℂ) ^ (mode i) := by
  have he : Complex.I * (frequency L i : ℂ) * (L : ℂ) / 2 =
      (mode i : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    unfold frequency
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hL)]
  rw [he, Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- Centering a single mode separates its half-period phase from the shifted exponential. -/
theorem centered_mode_factor {N : ℕ} {L : ℝ} (hL : 0 < L)
    (i : Index N) (z : ℂ) (t : ℝ) :
    Complex.exp (Complex.I * (frequency L i * t)) *
      Complex.exp (-Complex.I * z * ((t : ℂ) - (L : ℂ) / 2)) =
    (-1 : ℂ) ^ (mode i) *
      Complex.exp (-Complex.I * (z - (frequency L i : ℂ)) * ((t : ℂ) - (L : ℂ) / 2)) := by
  rw [← frequency_half_period hL i, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- The actual centered integral of a native finite Fourier polynomial. -/
theorem integral_fourierFunction_centered {N : ℕ} {L : ℝ} (hL : 0 < L)
    (v : Section N) (z : ℂ) :
    (∫ t in (0 : ℝ)..L, fourierFunction L v t *
      Complex.exp (-Complex.I * z * ((t : ℂ) - (L : ℂ) / 2))) =
      centeredFourierObservation L v z := by
  simp only [fourierFunction, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · unfold centeredFourierObservation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have he : (fun t : ℝ => v i * ((Real.sqrt L)⁻¹ : ℂ) *
        Complex.exp (Complex.I * (frequency L i * t)) *
        Complex.exp (-Complex.I * z * ((t : ℂ) - (L : ℂ) / 2))) =
      (fun t : ℝ => (v i * ((Real.sqrt L)⁻¹ : ℂ) * (-1 : ℂ) ^ (mode i)) *
        Complex.exp (-Complex.I * (z - (frequency L i : ℂ)) * ((t : ℂ) - (L : ℂ) / 2))) := by
      ext t
      rw [mul_assoc, centered_mode_factor hL]
      ring
    rw [he, intervalIntegral.integral_const_mul, integral_centered_exp]
    have hs : (Real.sqrt L : ℂ) ^ 2 = (L : ℂ) := by
      exact_mod_cast Real.sq_sqrt hL.le
    have hs0 : (Real.sqrt L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hL)
    push_cast
    rw [← hs]
    field_simp
  · intro i hi
    apply Continuous.intervalIntegrable
    fun_prop

end Riemann.CCM.Native
