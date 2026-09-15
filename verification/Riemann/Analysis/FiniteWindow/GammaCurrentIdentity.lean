import Riemann.Analysis.GammaCutoffLimit
import Riemann.Analysis.FiniteWindow.GammaCurrentConvolution
import Riemann.Analysis.FiniteWindow.ShiftCommutation

/-! Identification of the literal Gamma current by strong cutoff convergence.
The left identity holds on every Hilbert source after applying the resolvent;
the right identity is restricted to the declared current domain. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Riemann.Analysis.FiniteWindow

lemma integrableOn_real_kernel_shift {L : ℝ} {k : ℝ → ℝ}
    (hk : IntegrableOn k (Ioo 0 L) volume) (f : Hilbert L) :
    IntegrableOn (fun y => (k y : ℂ) • shift L y f) (Ioo 0 L) volume := by
  have hm : AEStronglyMeasurable (fun y => (k y : ℂ)) (volume.restrict (Ioo 0 L)) :=
    hk.ofReal.aestronglyMeasurable
  have hv : AEStronglyMeasurable (fun y => (k y : ℂ) • shift L y f)
      (volume.restrict (Ioo 0 L)) := hm.smul (continuous_shift_apply L f).aestronglyMeasurable
  apply (hk.norm.mul_const ‖f‖).mono' hv
  filter_upwards with y
  rw [norm_smul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (norm_shift_apply_le L y f) (norm_nonneg _)

lemma norm_real_kernel_shift_le {L : ℝ} {k : ℝ → ℝ}
    (hk : IntegrableOn k (Ioo 0 L) volume) (f : Hilbert L) :
    ‖∫ y in Ioo 0 L, (k y : ℂ) • shift L y f‖ ≤
      (∫ y in Ioo 0 L, ‖k y‖) * ‖f‖ := by
  calc
    _ ≤ ∫ y in Ioo 0 L, ‖(k y : ℂ) • shift L y f‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioo 0 L, ‖k y‖ * ‖f‖ := by
      apply integral_mono_ae (integrableOn_real_kernel_shift hk f).norm (hk.norm.mul_const _)
      filter_upwards with y
      rw [norm_smul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (norm_shift_apply_le L y f) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

lemma gamma_cutoff_action_tendsto {L : ℝ} (hL : 0 < L) (f : Hilbert L) :
    Tendsto (fun δ => ∫ y in Ioo 0 L,
      (GammaCompletion.cutoffCurrentKernel δ y : ℂ) • shift L y f)
      (𝓝[Ioo 0 L] 0) (𝓝 (∫ y in Ioo 0 L,
        (GammaCompletion.limitingCurrentKernel y : ℂ) • shift L y f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (GammaCompletion.tendsto_integral_norm_cutoffCurrentKernel hL).mul_const ‖f‖
  simp only [zero_mul] at ht
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hk := GammaCompletion.cutoffCurrentKernel_integrable hL hδ.1 hδ.2.le
  have h0 := GammaCompletion.limitingCurrentKernel_integrable hL
  rw [← integral_sub (integrableOn_real_kernel_shift hk f) (integrableOn_real_kernel_shift h0 f)]
  have he : (fun y => (GammaCompletion.cutoffCurrentKernel δ y : ℂ) • shift L y f -
      (GammaCompletion.limitingCurrentKernel y : ℂ) • shift L y f) =
      (fun y => (((GammaCompletion.cutoffCurrentKernel δ -
        GammaCompletion.limitingCurrentKernel) y : ℝ) : ℂ) • shift L y f) := by
    funext y
    simp only [Pi.sub_apply, Complex.ofReal_sub, sub_smul]
  rw [he]
  exact norm_real_kernel_shift_le (hk.sub h0) f

lemma gamma_limiting_action {L : ℝ} (hL : 0 < L) (f : Hilbert L) :
    (2 * Real.pi : ℂ) • (∫ y in Ioo 0 L,
      (GammaCompletion.limitingCurrentKernel y : ℂ) • shift L y f) =
      -gammaDerivative L f := by
  rw [gammaDerivative_apply hL, ← integral_smul, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with y
  rw [smul_smul, show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_mul, GammaCompletion.limitingCurrentKernel_eq,
    Complex.ofReal_neg, neg_smul]

/-- The left Gamma current identity is proved for every Hilbert source. -/
theorem gammaCurrent_volterra {L : ℝ} (hL : 0 < L) (f : Hilbert L) :
    (2 * Real.pi : ℂ) • gammaCurrent L
      ⟨volterra L (1/2) f, (hasGenerator_volterra L hL.le (1/2) f).mem_gammaCurrentDomain hL⟩ =
      -gammaDerivative L f := by
  let rf : gammaCurrentDomain L :=
    ⟨volterra L (1/2) f, (hasGenerator_volterra L hL.le (1/2) f).mem_gammaCurrentDomain hL⟩
  have hdom := (gammaTruncated_tendsto hL rf).mono_left
    (nhdsWithin_mono (0 : ℝ) Ioo_subset_Icc_self)
  have hker := gamma_cutoff_action_tendsto hL f
  have he : (fun δ => gammaTruncated L δ (volterra L (1/2) f)) =ᶠ[𝓝[Ioo 0 L] 0]
      (fun δ => ∫ y in Ioo 0 L,
        (GammaCompletion.cutoffCurrentKernel δ y : ℂ) • shift L y f) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact gammaTruncated_volterra hδ.1 hδ.2.le f
  haveI : NeBot (𝓝[Ioo 0 L] (0 : ℝ)) := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hL.ne]
    exact ⟨le_rfl, hL.le⟩
  have hx := tendsto_nhds_unique (hdom.congr' he) hker
  change (2 * Real.pi : ℂ) • gammaCurrent L rf = _
  rw [hx]
  exact gamma_limiting_action hL f

/-- The critical Gamma factor smooths every Hilbert input into the current domain. -/
theorem gammaOperator_half_mem_gammaCurrentDomain {L : ℝ} (hL : 0 < L) (f : Hilbert L) :
    gammaOperator L (1/2) f ∈ gammaCurrentDomain L := by
  rw [gammaOperator_half hL]
  exact (gammaCurrentDomain L).smul_mem (2 * Real.pi : ℂ)
    ((hasGenerator_volterra L hL.le (1/2) f).mem_gammaCurrentDomain hL)

/-- The actual left logarithmic-current identity, with the smoothing domain proved. -/
theorem gammaCurrent_gammaOperator_half {L : ℝ} (hL : 0 < L) (f : Hilbert L) :
    gammaCurrent L ⟨gammaOperator L (1/2) f, gammaOperator_half_mem_gammaCurrentDomain hL f⟩ =
      -gammaDerivative L f := by
  let rf : gammaCurrentDomain L :=
    ⟨volterra L (1/2) f, (hasGenerator_volterra L hL.le (1/2) f).mem_gammaCurrentDomain hL⟩
  have he : (⟨gammaOperator L (1/2) f, gammaOperator_half_mem_gammaCurrentDomain hL f⟩ :
      gammaCurrentDomain L) = (2 * Real.pi : ℂ) • rf := by
    apply Subtype.ext
    exact congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T f) (gammaOperator_half hL)
  rw [he, map_smul]
  exact gammaCurrent_volterra hL f

/-- The corresponding right identity holds precisely on the declared current domain. -/
theorem gammaOperator_half_gammaCurrent {L : ℝ} (hL : 0 < L) (f : gammaCurrentDomain L) :
    gammaOperator L (1/2) (gammaCurrent L f) = -gammaDerivative L f := by
  rw [← gammaCurrent_commute (gammaOperator L (1/2)) (gammaOperator_commute_shift L (1/2)) f]
  exact gammaCurrent_gammaOperator_half hL f

end Riemann.Analysis.FiniteWindow
