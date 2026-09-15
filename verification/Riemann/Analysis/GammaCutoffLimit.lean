import Riemann.Analysis.GammaCutoffKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # L¹ convergence of the regularized Gamma convolution kernel

The logarithmic singularity is dominated by an integrable quarter power.
The norm estimate is on the scalar kernel; it does not integrate the shift
family in the operator norm topology.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Riemann.Analysis.GammaCompletion

def logMajorant (L y : ℝ) : ℝ :=
  4 * (2 * Real.exp (-2 * L)) ^ (-(1 / 4 : ℝ)) * y ^ (-(1 / 4 : ℝ))

theorem logMajorant_nonneg (L y : ℝ) (hy : 0 ≤ y) : 0 ≤ logMajorant L y := by
  dsimp [logMajorant]
  positivity

theorem abs_log_base_le {L y : ℝ} (hy : y ∈ Ioo 0 L) :
    |Real.log (1 - Real.exp (-2 * y))| ≤ logMajorant L y := by
  have hc : 0 < 2 * Real.exp (-2 * L) := by positivity
  have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hc hy.1)
    (base_arg_lower hy.1.le hy.2.le) (show -(1 / 4 : ℝ) ≤ 0 by norm_num)
  rw [Real.mul_rpow hc.le hy.1.le] at hpow
  exact (abs_log_le_quarter (base_arg_pos hy.1) (base_arg_le_one y)).trans
    (by dsimp [logMajorant]; nlinarith)

theorem logMajorant_integrable {L : ℝ} (hL : 0 < L) :
    IntegrableOn (logMajorant L) (Ioo 0 L) := by
  have hp : IntegrableOn (fun y : ℝ => y ^ (-(1 / 4 : ℝ))) (Ioo 0 L) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hL).mpr (by norm_num)
  exact hp.const_mul _

theorem log_base_monotone {y δ : ℝ} (hy : 0 < y) (hyδ : y ≤ δ) :
    Real.log (1 - Real.exp (-2 * y)) ≤ Real.log (1 - Real.exp (-2 * δ)) := by
  apply Real.log_le_log (base_arg_pos hy)
  have he : Real.exp (-2 * δ) ≤ Real.exp (-2 * y) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

theorem log_base_nonpos {y : ℝ} (hy : 0 < y) :
    Real.log (1 - Real.exp (-2 * y)) ≤ 0 :=
  Real.log_nonpos (base_arg_pos hy).le (base_arg_le_one y)

theorem norm_limitingCurrentKernel_le {L y : ℝ} (hy : y ∈ Ioo 0 L) :
    ‖limitingCurrentKernel y‖ ≤ |currentConstant| + L + logMajorant L y / 2 := by
  have he : Real.exp (-y / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hy.1])
  have ht : |currentConstant + logPrimitive y| ≤
      |currentConstant| + y + |Real.log (1 - Real.exp (-2 * y))| / 2 := by
    dsimp [logPrimitive]
    calc
      _ ≤ |currentConstant| + |y + Real.log (1 - Real.exp (-2 * y)) / 2| := abs_add_le _ _
      _ ≤ _ := by
        have hh := abs_add_le y (Real.log (1 - Real.exp (-2 * y)) / 2)
        rw [abs_of_pos hy.1, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
        linarith
  rw [limitingCurrentKernel, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.norm_eq_abs]
  calc
    _ ≤ |currentConstant + logPrimitive y| := mul_le_of_le_one_left (abs_nonneg _) he
    _ ≤ _ := by linarith [abs_log_base_le hy, hy.2]

theorem norm_cutoffCurrentKernel_sub_le {L δ y : ℝ}
    (hδ : 0 < δ) (hδL : δ ≤ L) (hy : y ∈ Ioo 0 L) :
    ‖cutoffCurrentKernel δ y - limitingCurrentKernel y‖ ≤ L + logMajorant L y / 2 := by
  have he : Real.exp (-y / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hy.1])
  by_cases hd : δ < y
  · rw [cutoffCurrentKernel_of_lt hd]
    have heq : limitingCurrentKernel y - δ * Real.exp (-y/2) - limitingCurrentKernel y =
        -(δ * Real.exp (-y/2)) := by ring
    rw [heq, norm_neg, Real.norm_eq_abs, abs_of_pos (mul_pos hδ (Real.exp_pos _))]
    have hm : δ * Real.exp (-y/2) ≤ δ := mul_le_of_le_one_right hδ.le he
    linarith [logMajorant_nonneg L y hy.1.le]
  · have hyδ : y ≤ δ := le_of_not_gt hd
    rw [cutoffCurrentKernel_of_le hyδ]
    have hlog := log_base_monotone hy.1 hyδ
    have hn := log_base_nonpos hδ
    have hny := log_base_nonpos hy.1
    have hq : cutoffCurrentKernel δ y - limitingCurrentKernel y =
        Real.exp (-y/2) * ((Real.log (1 - Real.exp (-2*δ)) -
          Real.log (1 - Real.exp (-2*y))) / 2 - y) := by
      rw [cutoffCurrentKernel_of_le hyδ]
      dsimp [limitingCurrentKernel, logPrimitive]
      ring
    rw [← cutoffCurrentKernel_of_le hyδ, hq, norm_mul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    have hab : |(Real.log (1 - Real.exp (-2*δ)) -
          Real.log (1 - Real.exp (-2*y))) / 2 - y| ≤
        |Real.log (1 - Real.exp (-2*y))| / 2 + y := by
      rw [abs_of_nonpos hny]
      apply abs_le.mpr
      constructor <;> linarith [hy.1]
    calc
      _ ≤ |(Real.log (1 - Real.exp (-2*δ)) -
          Real.log (1 - Real.exp (-2*y))) / 2 - y| :=
        mul_le_of_le_one_left (abs_nonneg _) he
      _ ≤ _ := by linarith [abs_log_base_le hy, hy.2]

theorem measurable_limitingCurrentKernel : Measurable limitingCurrentKernel := by
  unfold limitingCurrentKernel logPrimitive
  fun_prop

theorem measurable_cutoffCurrentKernel (δ : ℝ) : Measurable (cutoffCurrentKernel δ) := by
  have hm : Measurable (fun y => if δ < y then logPrimitive y - logPrimitive δ else 0) :=
    Measurable.ite measurableSet_Ioi (by unfold logPrimitive; fun_prop) measurable_const
  exact (show Measurable (fun y : ℝ => Real.exp (-y/2)) by fun_prop).mul
    (measurable_const.add hm)

theorem limitingCurrentKernel_integrable {L : ℝ} (hL : 0 < L) :
    IntegrableOn limitingCurrentKernel (Ioo 0 L) := by
  apply ((integrableOn_const (C := |currentConstant| + L) (hs := by simp [Real.volume_Ioo])).add
    ((logMajorant_integrable hL).div_const 2)).mono'
  · exact measurable_limitingCurrentKernel.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact norm_limitingCurrentKernel_le hy

theorem cutoffCurrentKernel_integrable {L : ℝ} (hL : 0 < L) {δ : ℝ}
    (hδ : 0 < δ) (hδL : δ ≤ L) : IntegrableOn (cutoffCurrentKernel δ) (Ioo 0 L) := by
  have hi : IntegrableOn (fun y => cutoffCurrentKernel δ y - limitingCurrentKernel y) (Ioo 0 L) := by
    apply ((integrableOn_const (C := L) (hs := by simp [Real.volume_Ioo])).add ((logMajorant_integrable hL).div_const 2)).mono'
    · exact ((measurable_cutoffCurrentKernel δ).sub measurable_limitingCurrentKernel).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      exact norm_cutoffCurrentKernel_sub_le hδ hδL hy
  convert hi.add (limitingCurrentKernel_integrable hL) using 1
  all_goals try rfl
  funext y
  exact (sub_add_cancel (cutoffCurrentKernel δ y) (limitingCurrentKernel y)).symm

theorem cutoffCurrentKernel_tendsto {y : ℝ} (hy : 0 < y) :
    Tendsto (fun δ => cutoffCurrentKernel δ y) (𝓝 (0 : ℝ)) (𝓝 (limitingCurrentKernel y)) := by
  have he : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < y := eventually_lt_nhds hy
  have ht : Tendsto (fun δ : ℝ => limitingCurrentKernel y - δ * Real.exp (-y/2))
      (𝓝 0) (𝓝 (limitingCurrentKernel y)) := by
    simpa using (tendsto_const_nhds (x := limitingCurrentKernel y)).sub
      ((tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 0) (𝓝 0)).mul_const (Real.exp (-y/2)))
  exact ht.congr' (he.mono fun δ hδ => (cutoffCurrentKernel_of_lt hδ).symm)

/-- Actual scalar L¹ norm convergence, supplying the operator-norm bound after
strong integration against the contraction semigroup. -/
theorem tendsto_integral_norm_cutoffCurrentKernel {L : ℝ} (hL : 0 < L) :
    Tendsto (fun δ => ∫ y in Ioo 0 L, ‖cutoffCurrentKernel δ y - limitingCurrentKernel y‖)
      (𝓝[Ioo 0 L] 0) (𝓝 (0 : ℝ)) := by
  have hi : IntegrableOn (fun y => L + logMajorant L y / 2) (Ioo 0 L) :=
    (integrableOn_const (C := L) (hs := by simp [Real.volume_Ioo])).add ((logMajorant_integrable hL).div_const 2)
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioo 0 L)) (l := 𝓝[Ioo 0 L] 0)
    (F := fun δ y => ‖cutoffCurrentKernel δ y - limitingCurrentKernel y‖)
    (f := fun _ => (0 : ℝ)) (fun y => L + logMajorant L y / 2)
  suffices hh : Tendsto (fun δ => ∫ y in Ioo 0 L, ‖cutoffCurrentKernel δ y - limitingCurrentKernel y‖)
      (𝓝[Ioo 0 L] 0) (𝓝 (∫ _y in Ioo 0 L, (0 : ℝ))) by simpa using hh
  apply ht
  · exact Eventually.of_forall fun δ =>
      ((measurable_cutoffCurrentKernel δ).sub measurable_limitingCurrentKernel).norm.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    simpa only [norm_norm] using norm_cutoffCurrentKernel_sub_le hδ.1 hδ.2.le hy
  · exact hi
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hpy : Tendsto (fun δ => cutoffCurrentKernel δ y) (𝓝[Ioo 0 L] 0)
        (𝓝 (limitingCurrentKernel y)) :=
      (cutoffCurrentKernel_tendsto hy.1).mono_left nhdsWithin_le_nhds
    simpa using (hpy.sub (tendsto_const_nhds (x := limitingCurrentKernel y))).norm

end Riemann.Analysis.GammaCompletion
