import Riemann.Analysis.GammaCutoffKernel
import Riemann.Analysis.FiniteWindow.GammaCurrent
import Riemann.Analysis.FiniteWindow.KernelConvolution

/-! Scalar cutoff convolution for the actual finite-window current. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Riemann.Analysis.FiniteWindow

def gammaResolventKernel (L y : ℝ) : ℂ :=
  (Ioo 0 L).indicator (fun y => (Real.exp (-y / 2) : ℂ)) y

def gammaPositiveKernel (L δ y : ℝ) : ℂ :=
  (Ioo δ L).indicator (fun y => (gammaWeight y : ℂ)) y

lemma gammaResolventKernel_measurable (L : ℝ) : StronglyMeasurable (gammaResolventKernel L) := by
  apply StronglyMeasurable.indicator _ measurableSet_Ioo
  exact (show Continuous (fun y : ℝ => (Real.exp (-y / 2) : ℂ)) by fun_prop).stronglyMeasurable

lemma gammaPositiveKernel_measurable (L δ : ℝ) : StronglyMeasurable (gammaPositiveKernel L δ) := by
  apply StronglyMeasurable.indicator _ measurableSet_Ioo
  apply Measurable.stronglyMeasurable
  unfold gammaWeight
  fun_prop

lemma gammaResolventKernel_integrable {L : ℝ} : Integrable (gammaResolventKernel L) := by
  apply (integrable_indicator_iff measurableSet_Ioo).mpr
  have hc : Continuous (fun y : ℝ => (Real.exp (-y / 2) : ℂ)) := by fun_prop
  exact (ContinuousOn.integrableOn_compact isCompact_Icc hc.continuousOn).mono_set Ioo_subset_Icc_self

lemma gammaPositiveKernel_integrable {L δ : ℝ} (hδ : 0 < δ) :
    Integrable (gammaPositiveKernel L δ) := by
  apply (integrable_indicator_iff measurableSet_Ioo).mpr
  apply IntegrableOn.mono_set _ Ioo_subset_Icc_self
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply Complex.continuous_ofReal.comp_continuousOn
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro y hy
    exact (GammaCompletion.base_arg_pos (hδ.trans_le hy.1)).ne'

lemma gammaResolventKernel_neg (L : ℝ) {y : ℝ} (hy : y < 0) :
    gammaResolventKernel L y = 0 := by
  exact indicator_of_notMem (by intro h; linarith [h.1]) _

lemma gammaPositiveKernel_neg {L δ y : ℝ} (hδ : 0 < δ) (hy : y < 0) :
    gammaPositiveKernel L δ y = 0 := by
  exact indicator_of_notMem (by intro h; linarith [h.1]) _

lemma gamma_kernel_product {L δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Ioo 0 L) (y : ℝ) :
    gammaPositiveKernel L δ y * gammaResolventKernel L (t-y) =
      (Ioo δ t).indicator (fun y =>
        ((Real.exp (-t / 2) / (1 - Real.exp (-2 * y)) : ℝ) : ℂ)) y := by
  by_cases hy : y ∈ Ioo δ t
  · have hyL : y ∈ Ioo δ L := ⟨hy.1, hy.2.trans ht.2⟩
    have hty : t-y ∈ Ioo 0 L := by constructor <;> linarith [hy.1, hy.2, ht.2]
    simp only [gammaPositiveKernel, gammaResolventKernel, indicator_of_mem hy,
      indicator_of_mem hyL, indicator_of_mem hty, gammaWeight]
    norm_cast
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    ring
  · have h : y ∉ Ioo δ L ∨ t-y ∉ Ioo 0 L := by
      by_contra hn
      push Not at hn
      exact hy ⟨hn.1.1, by linarith [hn.2.1]⟩
    rcases h with h | h
    · simp only [gammaPositiveKernel, indicator_of_notMem h, zero_mul,
        indicator_of_notMem hy]
    · simp only [gammaResolventKernel, indicator_of_notMem h, mul_zero,
        indicator_of_notMem hy]

lemma gamma_kernel_convolution {L δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Ioo 0 L) :
    (∫ y, gammaPositiveKernel L δ y * gammaResolventKernel L (t-y)) =
      ((Real.exp (-t / 2) *
        (if δ < t then GammaCompletion.logPrimitive t - GammaCompletion.logPrimitive δ
          else 0) : ℝ) : ℂ) := by
  simp_rw [gamma_kernel_product hδ ht]
  rw [integral_indicator measurableSet_Ioo]
  by_cases hδt : δ < t
  · rw [if_pos hδt]
    simp_rw [div_eq_mul_inv, Complex.ofReal_mul]
    rw [integral_const_mul]
    rw [integral_complex_ofReal]
    congr 2
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hδt.le]
    exact GammaCompletion.integral_inverse_base hδ hδt.le
  · rw [if_neg hδt, Ioo_eq_empty hδt]
    simp

lemma gammaIntegrand_split (L y : ℝ) (f : Hilbert L) :
    gammaIntegrand L f y = (gammaWeight y : ℂ) • shift L y f -
      ((Real.exp (-2 * y) / (1 - Real.exp (-2 * y)) : ℝ) : ℂ) • f := by
  dsimp [gammaIntegrand, gammaWeight, gammaRemainder]
  generalize Real.exp (-y / 2) = a
  generalize Real.exp (-2 * y) = b
  module

lemma continuousOn_gammaWeight {δ L : ℝ} (hδ : 0 < δ) :
    ContinuousOn gammaWeight (Icc δ L) := by
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro y hy
    exact (GammaCompletion.base_arg_pos (hδ.trans_le hy.1)).ne'

lemma gammaTruncated_eq {L δ : ℝ} (hδ : 0 < δ) (hδL : δ ≤ L) (f : Hilbert L) :
    gammaTruncated L δ f =
      ((GammaCompletion.currentConstant + Real.log (1 - Real.exp (-2 * δ)) / 2 : ℝ) : ℂ) • f +
        ∫ y in δ..L, (gammaWeight y : ℂ) • shift L y f := by
  have hw : IntervalIntegrable (fun y => (gammaWeight y : ℂ) • shift L y f) volume δ L := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hδL]
    exact (Complex.continuous_ofReal.comp_continuousOn (continuousOn_gammaWeight hδ)).smul
      (continuous_shift_apply L f).continuousOn
  have hr : IntervalIntegrable (fun y =>
      ((Real.exp (-2 * y) / (1 - Real.exp (-2 * y)) : ℝ) : ℂ) • f) volume δ L := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hδL]
    have hc : ContinuousOn (fun y => Real.exp (-2 * y) / (1 - Real.exp (-2 * y))) (Icc δ L) := by
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro y hy
        exact (GammaCompletion.base_arg_pos (hδ.trans_le hy.1)).ne'
    exact (Complex.continuous_ofReal.comp_continuousOn hc).smul continuousOn_const
  unfold gammaTruncated
  simp_rw [gammaIntegrand_split]
  rw [intervalIntegral.integral_sub hw hr, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_ofReal, GammaCompletion.integral_scalar_subtraction hδ hδL]
  dsimp [gammaConstant, GammaCompletion.currentConstant]
  module

lemma integral_gammaResolventKernel {L : ℝ} (hL : 0 ≤ L) (f : Hilbert L) :
    (∫ y, gammaResolventKernel L y • shift L y f) = volterra L (1/2) f := by
  rw [volterra_apply, intervalIntegral.integral_of_le hL, integral_Ioc_eq_integral_Ioo]
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ Ioo 0 L
  · simp only [gammaResolventKernel, indicator_of_mem hy, weightedOrbit]
    congr 1
    rw [show -(1 / 2 : ℂ) * (y : ℂ) = ((-y / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
  · simp [gammaResolventKernel, indicator_of_notMem hy]

lemma integral_gammaPositiveKernel {L δ : ℝ} (hδL : δ ≤ L) (f : Hilbert L) :
    (∫ y, gammaPositiveKernel L δ y • shift L y f) =
      ∫ y in δ..L, (gammaWeight y : ℂ) • shift L y f := by
  rw [intervalIntegral.integral_of_le hδL, integral_Ioc_eq_integral_Ioo,
    ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ Ioo δ L <;> simp [gammaPositiveKernel, hy]

lemma gamma_convolution_integrable {L δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t => ∫ y, gammaPositiveKernel L δ y * gammaResolventKernel L (t-y)) := by
  exact (gammaPositiveKernel_integrable hδ).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) gammaResolventKernel_integrable

/-- The actual strong cutoff current composed with its critical resolvent has
exactly the scalar cutoff kernel. Both sides act on arbitrary Hilbert vectors. -/
theorem gammaTruncated_volterra {L δ : ℝ} (hδ : 0 < δ) (hδL : δ ≤ L) (f : Hilbert L) :
    gammaTruncated L δ (volterra L (1/2) f) =
      ∫ t in Ioo 0 L, (GammaCompletion.cutoffCurrentKernel δ t : ℂ) • shift L t f := by
  have hL : 0 ≤ L := hδ.le.trans hδL
  let a : ℂ := ((GammaCompletion.currentConstant +
    Real.log (1 - Real.exp (-2 * δ)) / 2 : ℝ) : ℂ)
  let cv : ℝ → ℂ := fun t => ∫ y, gammaPositiveKernel L δ y * gammaResolventKernel L (t-y)
  have hcv : Integrable cv := gamma_convolution_integrable hδ
  have hres := integrable_scalar_shift L (gammaResolventKernel_integrable (L := L)) f
  have hcvs := integrable_scalar_shift L hcv f
  rw [gammaTruncated_eq hδ hδL, ← integral_gammaPositiveKernel hδL,
    ← integral_gammaResolventKernel hL,
    integral_shift_comp (gammaPositiveKernel_integrable hδ) gammaResolventKernel_integrable
      (gammaPositiveKernel_measurable L δ) (gammaResolventKernel_measurable L)
      (fun y hy => gammaPositiveKernel_neg hδ hy) (fun y hy => gammaResolventKernel_neg L hy)]
  change a • (∫ y, gammaResolventKernel L y • shift L y f) +
    (∫ t, cv t • shift L t f) = _
  rw [← integral_smul]
  have has : Integrable (fun y => a • (gammaResolventKernel L y • shift L y f)) := hres.smul a
  rw [← integral_add has hcvs]
  have he : (∫ t in Ioo 0 L,
      a • (gammaResolventKernel L t • shift L t f) + cv t • shift L t f) =
      ∫ t, a • (gammaResolventKernel L t • shift L t f) + cv t • shift L t f := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    by_cases ht0 : 0 < t
    · have htL : L ≤ t := le_of_not_gt (fun hh => ht ⟨ht0, hh⟩)
      rw [shift_eq_zero L htL]
      simp
    · have hres0 : gammaResolventKernel L t = 0 :=
        indicator_of_notMem (fun hh => ht0 hh.1) _
      have hcv0 : cv t = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards with y
        by_cases hy : y ∈ Ioo δ L
        · have hty : t-y ∉ Ioo 0 L := by intro hh; linarith [hy.1, hh.1]
          simp [gammaResolventKernel, indicator_of_notMem hty]
        · simp [gammaPositiveKernel, indicator_of_notMem hy]
      simp [hres0, hcv0]
  rw [← he]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [show cv t = _ from gamma_kernel_convolution hδ ht]
  simp only [gammaResolventKernel, indicator_of_mem ht]
  dsimp [a, GammaCompletion.cutoffCurrentKernel]
  module

end Riemann.Analysis.FiniteWindow
