import Riemann.Analysis.FiniteWindow.KilledShiftHilbert
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Finite-window Volterra operators by strong vector integration

The integral is taken separately for each vector, not in the operator-norm
Banach space. Every complex parameter is admitted on a fixed finite window.
-/

noncomputable section
open MeasureTheory Set Filter
namespace Riemann.Analysis.FiniteWindow

/-- The exponentially weighted strongly continuous orbit. -/
def weightedOrbit (L : ℝ) (b : ℂ) (f : Hilbert L) (y : ℝ) : Hilbert L :=
  Complex.exp (-b * (y : ℂ)) • shift L y f

theorem continuous_weightedOrbit (L : ℝ) (b : ℂ) (f : Hilbert L) :
    Continuous (weightedOrbit L b f) :=
  (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).smul
    (continuous_shift_apply L f)

theorem norm_weightedOrbit_le (L : ℝ) (b : ℂ) (f : Hilbert L) {y : ℝ}
    (hy : y ∈ uIcc 0 L) :
    ‖weightedOrbit L b f y‖ ≤ Real.exp (‖b‖ * |L|) * ‖f‖ := by
  have habs : |y| ≤ |L| := by
    rcases mem_uIcc.mp hy with h | h
    · simpa using abs_le_max_abs_abs h.1 h.2
    · simpa using abs_le_max_abs_abs h.1 h.2
  rw [weightedOrbit, norm_smul]
  apply mul_le_mul _ (norm_shift_apply_le L y f) (norm_nonneg _) (Real.exp_pos _).le
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  simpa only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left habs (norm_nonneg b)

/-- A coarse explicit bound valid for every complex parameter and finite length. -/
theorem norm_volterra_integral_le (L : ℝ) (b : ℂ) (f : Hilbert L) :
    ‖∫ y in 0..L, weightedOrbit L b f y‖ ≤
      (|L| * Real.exp (‖b‖ * |L|)) * ‖f‖ := by
  calc
    _ ≤ (Real.exp (‖b‖ * |L|) * ‖f‖) * |L - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun y hy =>
        norm_weightedOrbit_le L b f (uIoc_subset_uIcc hy)
    _ = _ := by rw [sub_zero]; ring

def volterraLinearMap (L : ℝ) (b : ℂ) : Hilbert L →ₗ[ℂ] Hilbert L where
  toFun f := ∫ y in 0..L, weightedOrbit L b f y
  map_add' f g := by
    simp only [weightedOrbit, map_add, smul_add]
    exact intervalIntegral.integral_add ((continuous_weightedOrbit L b f).intervalIntegrable _ _)
      ((continuous_weightedOrbit L b g).intervalIntegrable _ _)
  map_smul' c f := by
    simp only [weightedOrbit, map_smul, RingHom.id_apply, smul_comm _ c]
    exact intervalIntegral.integral_smul c _

/-- The finite-window Volterra resolvent. Its integral is defined for all `b : ℂ`. -/
def volterra (L : ℝ) (b : ℂ) : Hilbert L →L[ℂ] Hilbert L :=
  (volterraLinearMap L b).mkContinuous (|L| * Real.exp (‖b‖ * |L|))
    (norm_volterra_integral_le L b)

@[simp] theorem volterra_apply (L : ℝ) (b : ℂ) (f : Hilbert L) :
    volterra L b f = ∫ y in 0..L, weightedOrbit L b f y := rfl

theorem norm_volterra_le (L : ℝ) (b : ℂ) :
    ‖volterra L b‖ ≤ |L| * Real.exp (‖b‖ * |L|) :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    (norm_volterra_integral_le L b)

@[simp] theorem weightedOrbit_zero (L : ℝ) (b : ℂ) (f : Hilbert L) :
    weightedOrbit L b f 0 = f := by simp [weightedOrbit]

theorem weightedOrbit_eq_zero (L : ℝ) (b : ℂ) (f : Hilbert L) {y : ℝ}
    (hy : L ≤ y) : weightedOrbit L b f y = 0 := by
  simp [weightedOrbit, shift_eq_zero L hy]

theorem shift_weightedOrbit (L : ℝ) (b : ℂ) (f : Hilbert L) {h y : ℝ}
    (hh : 0 ≤ h) (hy : 0 ≤ y) :
    shift L h (weightedOrbit L b f y) =
      Complex.exp (b * (h : ℂ)) • weightedOrbit L b f (y + h) := by
  have hs := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T f) (shift_add L hh hy)
  have he : Complex.exp (b * (h : ℂ)) * Complex.exp (-b * ((y + h : ℝ) : ℂ)) =
      Complex.exp (-b * (y : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [weightedOrbit, map_smul, ← mul_smul, he]
  rw [add_comm y h]
  exact congrArg (fun v : Hilbert L => Complex.exp (-b * (y : ℂ)) • v) hs

/-- Sliding the strong integral exposes its initial segment. This identity
is the source of the actual right derivative of the resolvent orbit. -/
theorem shift_volterra (L : ℝ) (hL : 0 ≤ L) (b : ℂ) (f : Hilbert L)
    {h : ℝ} (hh : 0 ≤ h) :
    shift L h (volterra L b f) = Complex.exp (b * (h : ℂ)) •
      (volterra L b f - ∫ y in 0..h, weightedOrbit L b f y) := by
  let w := weightedOrbit L b f
  have hw := continuous_weightedOrbit L b f
  have ht : (∫ y in L..L + h, w y) = 0 := by
    calc
      _ = ∫ _y in L..L + h, (0 : Hilbert L) := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact weightedOrbit_eq_zero L b f ((uIcc_of_le (by linarith : L ≤ L + h) ▸ hy).1)
      _ = 0 := by simp
  have htail : (∫ y in h..L + h, w y) = ∫ y in h..L, w y := by
    have he := intervalIntegral.integral_add_adjacent_intervals
      (hw.intervalIntegrable (μ := volume) h L) (hw.intervalIntegrable (μ := volume) L (L + h))
    rw [ht, add_zero] at he
    exact he.symm
  have hhead : (∫ y in h..L, w y) = (∫ y in 0..L, w y) - ∫ y in 0..h, w y := by
    have he := intervalIntegral.integral_add_adjacent_intervals
      (hw.intervalIntegrable (μ := volume) 0 h) (hw.intervalIntegrable (μ := volume) h L)
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using he)
  change shift L h (∫ y in 0..L, w y) = _
  rw [← (shift L h).intervalIntegral_comp_comm (hw.intervalIntegrable (μ := volume) 0 L)]
  calc
    _ = ∫ y in 0..L, Complex.exp (b * (h : ℂ)) • w (y + h) := by
      apply intervalIntegral.integral_congr
      intro y hy
      exact shift_weightedOrbit L b f hh ((uIcc_of_le hL ▸ hy).1)
    _ = Complex.exp (b * (h : ℂ)) • ∫ y in h..L + h, w y := by
      rw [intervalIntegral.integral_smul, intervalIntegral.integral_comp_add_right, zero_add]
    _ = _ := by rw [htail, hhead]; rfl

end Riemann.Analysis.FiniteWindow
