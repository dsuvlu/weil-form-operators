import Riemann.Analysis.HalfLine.ArithmeticKernel
import Riemann.Analysis.HalfLine.CompletedOperator
import Mathlib.Analysis.Convolution

/-! # Strong integration of the translated arithmetic smoothing seed -/
noncomputable section
open MeasureTheory Filter Set
namespace Riemann.Analysis.HalfLine

lemma integrable_scalar_shift {k : ℝ → ℂ} (hk : Integrable k) (f : Hilbert) :
    Integrable (fun y => k y • shift y f) := by
  apply (hk.norm.mul_const ‖f‖).mono'
    (hk.aestronglyMeasurable.smul (continuous_shift_apply f).aestronglyMeasurable)
  filter_upwards with y
  change ‖k y • shift y f‖ ≤ ‖k y‖ * ‖f‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_shift_apply_le y f) (norm_nonneg _)

lemma smoothingKernel_eq_volterra (y : ℝ) :
    (smoothingKernel y : ℂ) = (2*Real.pi : ℂ) *
      (3*volterraKernel (5/2) y-2*volterraKernel (3/2) y) := by
  by_cases hy : 0 ≤ y
  · simp only [smoothingKernel, if_pos hy, volterraKernel, indicator_of_mem (show y ∈ Ici (0:ℝ) from hy)]
    push_cast
    ring_nf
  · simp [smoothingKernel, hy, volterraKernel]

lemma integrable_smoothingKernel : Integrable (fun y => (smoothingKernel y : ℂ)) := by
  simp_rw [smoothingKernel_eq_volterra]
  exact (((integrable_volterraKernel (by norm_num : (0:ℝ)<5/2)).const_mul 3).sub
    ((integrable_volterraKernel (by norm_num : (0:ℝ)<3/2)).const_mul 2)).const_mul _

/-- The bounded smoothing factor after the two critical polar cancellations. -/
def smoothingOperator : Hilbert →L[ℂ] Hilbert :=
  (2*Real.pi : ℂ) • ((3:ℂ) • volterra (5/2) - (2:ℂ) • volterra (3/2))

lemma volterra_apply_global {b : ℝ} (hb : 0 < b) (f : Hilbert) :
    volterra b f = ∫ y, volterraKernel b y • shift y f := by
  change (∫ y, volterraKernelL1 b y • shift y f) = _
  apply integral_congr_ae
  filter_upwards [volterraKernelL1_ae hb] with y hy
  rw [hy]

theorem smoothingOperator_apply (f : Hilbert) :
    smoothingOperator f = ∫ y, (smoothingKernel y : ℂ) • shift y f := by
  simp only [smoothingOperator, smul_apply,
    sub_apply]
  rw [volterra_apply_global (by norm_num : (0:ℝ)<5/2),
    volterra_apply_global (by norm_num : (0:ℝ)<3/2)]
  have h3 : Integrable (fun y => (3:ℂ) • (volterraKernel (5/2) y • shift y f)) :=
    (integrable_volterra_orbit (by norm_num : (0:ℝ)<5/2) f).smul (3:ℂ)
  have h2 : Integrable (fun y => (2:ℂ) • (volterraKernel (3/2) y • shift y f)) :=
    (integrable_volterra_orbit (by norm_num : (0:ℝ)<3/2) f).smul (2:ℂ)
  have he (y : ℝ) : (smoothingKernel y : ℂ) • shift y f =
      (2*Real.pi:ℂ) • ((3:ℂ) • (volterraKernel (5/2) y • shift y f) -
        (2:ℂ) • (volterraKernel (3/2) y • shift y f)) := by
    rw [smoothingKernel_eq_volterra]
    module
  simp_rw [he]
  rw [integral_smul, integral_sub h3 h2, integral_smul, integral_smul]

/-- Translation of a strong scalar-kernel integral, with the directed shift sign. -/
theorem integral_shift_translate {k : ℝ → ℂ}
    (hk0 : ∀ y < 0, k y = 0) {a : ℝ} (ha : 0 ≤ a) (f : Hilbert) :
    (∫ y, k y • shift y (shift a f)) =
      ∫ y, k (y-a) • shift y f := by
  calc
    _ = ∫ y, k y • shift (y+a) f := by
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : 0 ≤ y
      · have hs := congrArg (fun T : Hilbert →L[ℂ] Hilbert => T f) (shift_add hy ha)
        exact congrArg (k y • ·) hs
      · simp [hk0 y (lt_of_not_ge hy)]
    _ = _ := by
      have h := integral_sub_right_eq_self (μ := volume)
        (fun y => k y • shift (y+a) f) a
      simpa only [sub_add_cancel] using h.symm

/-- Each raw Euler translate produces its explicitly translated scalar seed. -/
theorem smoothingOperator_raw_term {n : ℕ} (hn : 0 < n) (f : Hilbert) :
    smoothingOperator ((Real.exp (-Real.log n/2) : ℂ) • shift (Real.log n) f) =
      ∫ y, (arithmeticKernelTerm n y : ℂ) • shift y f := by
  rw [map_smul, smoothingOperator_apply, integral_shift_translate
    (fun y hy => by simp [smoothingKernel, not_le.mpr hy])
    (Real.log_nonneg (by exact_mod_cast hn)), ← integral_smul]
  apply integral_congr_ae
  filter_upwards with y
  simp [arithmeticKernelTerm, ne_of_gt hn, mul_smul]

lemma integrable_arithmeticKernelTerm (n : ℕ) :
    Integrable (fun y => (arithmeticKernelTerm n y : ℂ)) := by
  by_cases hn : n=0
  · simp [arithmeticKernelTerm, hn]
  · simp only [arithmeticKernelTerm, if_neg hn, Complex.ofReal_mul]
    exact (integrable_smoothingKernel.comp_sub_right (Real.log n)).const_mul _

lemma sum_arithmeticKernelTerm_Ioc (N : ℕ) (y : ℝ) (hN : arithmeticCount y ≤ N) :
    (∑ n ∈ Finset.Ioc 0 N, arithmeticKernelTerm n y) = criticalKernel y := by
  rw [← sum_arithmeticKernelTerm N y hN]
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_range] at *
    omega
  · intro n hn hn0
    have hz : n=0 := by
      simp only [Finset.mem_Ioc, Finset.mem_range] at *
      omega
    simp [hz, arithmeticKernelTerm]

end Riemann.Analysis.HalfLine
