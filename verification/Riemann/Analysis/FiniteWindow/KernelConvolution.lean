import Riemann.Analysis.FiniteWindow.StrongKernelIntegral
import Riemann.Analysis.FiniteWindow.KilledShiftHilbert
import Mathlib.Analysis.Convolution

/-! # Convolution of strong killed-shift kernels

All integrations in the Hilbert carrier act on vectors. Scalar kernel
integrability and contraction estimates justify Fubini; no operator-valued
measurability is assumed.
-/
noncomputable section
open MeasureTheory Filter Set Function

namespace Riemann.Analysis.FiniteWindow

lemma integrable_scalar_shift (L : ℝ) {k : ℝ → ℂ} (hk : Integrable k)
    (u : Hilbert L) : Integrable (fun y => k y • shift L y u) := by
  apply (hk.norm.mul_const ‖u‖).mono'
    (hk.aestronglyMeasurable.smul (continuous_shift_apply L u).aestronglyMeasurable)
  filter_upwards with y
  change ‖k y • shift L y u‖ ≤ ‖k y‖ * ‖u‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_shift_apply_le L y u) (norm_nonneg _)

/-- Scalar convolution represents composition of two positive-time shift integrals. -/
theorem integral_shift_comp {L : ℝ} {k l : ℝ → ℂ}
    (hk : Integrable k) (hl : Integrable l)
    (hkm : StronglyMeasurable k) (hlm : StronglyMeasurable l)
    (hk0 : ∀ y < 0, k y = 0) (hl0 : ∀ y < 0, l y = 0) (u : Hilbert L) :
    (∫ y, k y • shift L y (∫ z, l z • shift L z u)) =
      ∫ t, (∫ y, k y * l (t-y)) • shift L t u := by
  have hj : Integrable (fun p : ℝ × ℝ =>
      (k p.1 * l (p.2-p.1)) • shift L p.2 u) (volume.prod volume) := by
    have hbound := ((measurePreserving_prod_sub volume volume).integrable_comp_of_integrable
      (hk.norm.mul_prod hl.norm)).mul_const ‖u‖
    apply hbound.mono'
    · exact ((hkm.comp_measurable measurable_fst).mul
        (hlm.comp_measurable (measurable_snd.sub measurable_fst))).smul
          ((continuous_shift_apply L u).stronglyMeasurable.comp_measurable measurable_snd)
        |>.aestronglyMeasurable
    · filter_upwards with p
      change ‖(k p.1 * l (p.2-p.1)) • shift L p.2 u‖ ≤
        (‖k p.1‖ * ‖l (p.2-p.1)‖) * ‖u‖
      rw [norm_smul, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_shift_apply_le L p.2 u)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    _ = ∫ y, ∫ z, (k y * l z) • shift L (y+z) u := by
      apply integral_congr_ae
      filter_upwards with y
      rw [← (shift L y).integral_comp_comm (integrable_scalar_shift L hl u),
        ← integral_smul]
      apply integral_congr_ae
      filter_upwards with z
      by_cases hy : 0 ≤ y
      · by_cases hz : 0 ≤ z
        · have hs := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T u) (shift_add L hy hz)
          simp only [map_smul, smul_smul]
          exact congrArg ((k y * l z) • ·) hs
        · simp [hl0 z (lt_of_not_ge hz)]
      · simp [hk0 y (lt_of_not_ge hy)]
    _ = ∫ y, ∫ t, (k y * l (t-y)) • shift L t u := by
      apply integral_congr_ae
      filter_upwards with y
      have he := integral_sub_right_eq_self (μ := volume)
        (fun z : ℝ => (k y * l z) • shift L (y+z) u) y
      simpa only [add_sub_cancel] using he.symm
    _ = ∫ t, ∫ y, (k y * l (t-y)) • shift L t u := integral_integral_swap hj
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      exact integral_smul_const _ _

end Riemann.Analysis.FiniteWindow
