import Riemann.Analysis.GammaKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convolution

/-! # Scalar kernel of the regularized Gamma current

The logarithmic primitives below are proved by differentiation on the positive
axis. They provide the coefficients in the finite-window convolution, before
any limit of current operators is taken.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Riemann.Analysis.GammaCompletion

def logPrimitive (y : ℝ) : ℝ := y + Real.log (1 - Real.exp (-2 * y)) / 2

def currentConstant : ℝ := (Real.eulerMascheroniConstant + Real.log Real.pi) / 2

def limitingCurrentKernel (y : ℝ) : ℝ :=
  Real.exp (-y / 2) * (currentConstant + logPrimitive y)

def cutoffCurrentKernel (δ y : ℝ) : ℝ :=
  Real.exp (-y / 2) * (currentConstant + Real.log (1 - Real.exp (-2 * δ)) / 2 +
    if δ < y then logPrimitive y - logPrimitive δ else 0)

theorem hasDerivAt_half_log {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => Real.log (1 - Real.exp (-2 * y)) / 2)
      (Real.exp (-2 * y) / (1 - Real.exp (-2 * y))) y := by
  have he := ((hasDerivAt_id y).const_mul (-2)).exp
  have hh := (((hasDerivAt_const y (1 : ℝ)).sub he).log (base_arg_pos hy).ne').div_const 2
  convert! hh using 1
  simp only [Pi.sub_apply, id_eq] at *
  field_simp
  ring

theorem hasDerivAt_logPrimitive {y : ℝ} (hy : 0 < y) :
    HasDerivAt logPrimitive (1 - Real.exp (-2 * y))⁻¹ y := by
  convert! (hasDerivAt_id y).add (hasDerivAt_half_log hy) using 1
  have hq := (base_arg_pos hy).ne'
  have heq : (1 - Real.exp (-2 * y))⁻¹ =
      1 + Real.exp (-2 * y) / (1 - Real.exp (-2 * y)) := by
    have hh := inv_mul_cancel₀ hq
    rw [div_eq_mul_inv]
    nlinarith [hh]
  exact heq


theorem continuousOn_inverse_base {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun y => (1 - Real.exp (-2 * y))⁻¹) (Icc a b) := by
  apply ContinuousOn.inv₀
  · fun_prop
  · intro y hy
    exact (base_arg_pos (ha.trans_le hy.1)).ne'

theorem integral_inverse_base {δ t : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) :
    (∫ y in δ..t, (1 - Real.exp (-2 * y))⁻¹) = logPrimitive t - logPrimitive δ := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    rw [uIcc_of_le hδt] at hy
    exact hasDerivAt_logPrimitive (hδ.trans_le hy.1)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hδt]
    exact continuousOn_inverse_base hδ

theorem integral_scalar_subtraction {δ t : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) :
    (∫ y in δ..t, Real.exp (-2 * y) / (1 - Real.exp (-2 * y))) =
      Real.log (1 - Real.exp (-2 * t)) / 2 -
        Real.log (1 - Real.exp (-2 * δ)) / 2 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    rw [uIcc_of_le hδt] at hy
    exact hasDerivAt_half_log (hδ.trans_le hy.1)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hδt]
    exact (show ContinuousOn (fun y => Real.exp (-2 * y)) (Icc δ t) by fun_prop).mul
      (continuousOn_inverse_base hδ)

theorem cutoffCurrentKernel_of_lt {δ y : ℝ} (h : δ < y) :
    cutoffCurrentKernel δ y = limitingCurrentKernel y - δ * Real.exp (-y / 2) := by
  rw [cutoffCurrentKernel, if_pos h]
  dsimp [logPrimitive, limitingCurrentKernel]
  ring

theorem cutoffCurrentKernel_of_le {δ y : ℝ} (h : y ≤ δ) :
    cutoffCurrentKernel δ y = Real.exp (-y / 2) *
      (currentConstant + Real.log (1 - Real.exp (-2 * δ)) / 2) := by
  simp only [cutoffCurrentKernel, if_neg (not_lt.mpr h), add_zero]

theorem limitingCurrentKernel_eq (y : ℝ) :
    (2 * Real.pi) * limitingCurrentKernel y = -criticalDerivative y := by
  dsimp [limitingCurrentKernel, currentConstant, logPrimitive, criticalDerivative]
  ring

end Riemann.Analysis.GammaCompletion
