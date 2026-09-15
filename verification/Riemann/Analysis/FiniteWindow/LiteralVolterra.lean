import Riemann.Analysis.FiniteWindow.ACPrimitive

/-! # The literal triangular kernel of the finite Volterra resolvent -/
noncomputable section
open MeasureTheory Filter Set

namespace Riemann.Analysis.FiniteWindow

lemma integrable_weighted_cut_translation {L : ℝ} (_hL : 0 ≤ L)
    (b : ℂ) (f : Hilbert L) :
    Integrable (fun p : ℝ × ℝ => Complex.exp (-b * (p.1 : ℂ)) *
      (Ico 0 L).indicator (fun t => (f : Ambient) (p.1+t)) p.2)
      ((volume.restrict (Ioc 0 L)).prod volume) := by
  apply (integrable_cut_translation (μ := volume.restrict (Ioc 0 L)) L f).bdd_mul (c := Real.exp (‖b‖ * L))
    ((Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_fst))).aestronglyMeasurable)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (ae_restrict_mem measurableSet_Ioc)] with p hp
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  change ‖-b * (p.1 : ℂ)‖ ≤ ‖b‖ * L
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp.1.le]
  exact mul_le_mul_of_nonneg_left hp.2 (norm_nonneg b)

/-- The all-complex strong Volterra integral has a jointly integrable scalar kernel. -/
theorem volterra_ae_integral {L : ℝ} (hL : 0 ≤ L) (b : ℂ) (f : Hilbert L) :
    ((volterra L b f : Ambient) : ℝ → ℂ) =ᵐ[volume]
      fun t => ∫ y in Ioc 0 L, Complex.exp (-b * (y : ℂ)) *
        (Ico 0 L).indicator (fun t => (f : Ambient) (y+t)) t := by
  let F := fun y : ℝ => (weightedOrbit L b f y : Ambient)
  let μ : Measure ℝ := volume.restrict (Ioc 0 L)
  have hF : Integrable F μ :=
    (((supported L).subtypeL.continuous.comp (continuous_weightedOrbit L b f)).intervalIntegrable
      (μ := volume) 0 L).1
  have hrep : ∀ᵐ y ∂μ, (F y : ℝ → ℂ) =ᵐ[volume]
      fun t => Complex.exp (-b * (y : ℂ)) *
        (Ico 0 L).indicator (fun t => (f : Ambient) (y+t)) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have he : (shift L y f : Ambient) = cut L (translate y f) := by
      change (cut L (translate (y.toNNReal : ℝ) f)) = _
      rw [Real.coe_toNNReal y hy.1.le]
    have hs := Lp.coeFn_smul (Complex.exp (-b * (y : ℂ))) (shift L y f : Ambient)
    filter_upwards [hs, cut_ae L (translate y f), translate_ae y f] with t hs hc ht
    have heF : F y = Complex.exp (-b * (y : ℂ)) • (shift L y f : Ambient) := rfl
    rw [heF, hs]
    change Complex.exp (-b * (y : ℂ)) * (shift L y f : Ambient) t = _
    rw [he, hc]
    by_cases hmem : t ∈ Ico 0 L <;> simp [hmem, ht]
  have hi := integral_L2_ae (φ := fun (y t : ℝ) => Complex.exp (-b * (y : ℂ)) *
    (Ico 0 L).indicator (fun t => (f : Ambient) (y+t)) t)
    hF (integrable_weighted_cut_translation hL b f) hrep
  have he : (volterra L b f : Ambient) = ∫ y, F y ∂μ := by
    change (supported L).subtypeL (∫ y in 0..L, weightedOrbit L b f y) = _
    rw [← (supported L).subtypeL.intervalIntegral_comp_comm
      ((continuous_weightedOrbit L b f).intervalIntegrable (μ := volume) 0 L)]
    exact intervalIntegral.integral_of_le hL
  rw [he]
  exact hi

lemma weighted_translated_integral {L t : ℝ} (hL : 0 ≤ L)
    (b : ℂ) (f : Hilbert L) (ht : t ∈ Ico 0 L) :
    (∫ y in Ioc 0 L, Complex.exp (-b * (y : ℂ)) * (f : Ambient) (y+t)) =
    ∫ u in t..L, Complex.exp (-b * ((u-t : ℝ) : ℂ)) * (f : Ambient) u := by
  let g := fun u : ℝ => Complex.exp (-b * ((u-t : ℝ) : ℂ)) * (f : Ambient) u
  have hg (a d : ℝ) : IntervalIntegrable g volume a d :=
    (integrable_supported L f).intervalIntegrable.continuousOn_mul
      (by fun_prop)
  have htail : (∫ u in L..L+t, g u) = 0 := by
    calc
      _ = ∫ _u in L..L+t, (0 : ℂ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [supported_ae L f] with u hu hmem
        have hLu : L < u := (uIoc_of_le (show L ≤ L+t by linarith [ht.1]) ▸ hmem).1
        have hn : u ∉ Ico 0 L := fun h => (not_lt_of_ge hLu.le) h.2
        simp [g, hu, indicator_of_notMem hn]
      _ = 0 := by simp
  rw [← intervalIntegral.integral_of_le hL]
  have hc : (fun y : ℝ => Complex.exp (-b * (y : ℂ)) * (f : Ambient) (y+t)) =
      fun y => g (y+t) := by funext y; simp [g]
  rw [hc, intervalIntegral.integral_comp_add_right, zero_add]
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hg t L) (hg L (L+t))
  rw [htail, add_zero] at hadd
  exact hadd.symm

/-- For every complex b, the bounded operator is exactly the terminal
Volterra integral on the finite interval, including the exponent sign. -/
theorem volterra_ae {L : ℝ} (hL : 0 ≤ L) (b : ℂ) (f : Hilbert L) :
    ((volterra L b f : Ambient) : ℝ → ℂ) =ᵐ[volume]
      (Ico 0 L).indicator (fun t =>
        ∫ u in t..L, Complex.exp (-b * ((u-t : ℝ) : ℂ)) * (f : Ambient) u) := by
  filter_upwards [volterra_ae_integral hL b f] with t ht
  rw [ht]
  by_cases hmem : t ∈ Ico 0 L
  · simp only [indicator_of_mem hmem]
    exact weighted_translated_integral hL b f hmem
  · simp only [indicator_of_notMem hmem, mul_zero, integral_zero]

end Riemann.Analysis.FiniteWindow
