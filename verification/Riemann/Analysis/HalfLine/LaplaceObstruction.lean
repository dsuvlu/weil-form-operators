import Riemann.Analysis.HalfLine.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Laplace decay and strong-integral lower-bound obstruction

Only scalar L¹ domination and genuine shift eigenvectors enter. The bounded
operator is supplied by its actual strong-vector integral formula.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Riemann.Analysis.HalfLine

def laplaceIntegral (k : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ y in Ioi 0, k y * Real.exp (-r*y)

theorem laplaceIntegral_tendsto {k : ℝ → ℝ} (hk : IntegrableOn k (Ioi 0)) :
    Tendsto (laplaceIntegral k) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0:ℝ))) (l := atTop) (fun y => ‖k y‖)
    (F := fun r : ℝ => fun y => k y * Real.exp (-r*y))
    (f := fun _ : ℝ => (0:ℝ))
    (Eventually.of_forall fun r => hk.aestronglyMeasurable.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    ?_ hk.norm ?_
  · change Tendsto (fun r : ℝ => ∫ y in Ioi 0, k y * Real.exp (-r*y)) _ _
    simpa only [integral_zero] using h
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr) hy.le))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have ht : Tendsto (fun r : ℝ => Real.exp (-r*y)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.atTop_mul_const hy)
    simpa using tendsto_const_nhds.mul ht

/-- A strong scalar-kernel integral acts on a unit exponential by its Laplace value. -/
theorem strongIntegral_unitExponential (k : ℝ → ℝ) (r : ℝ) (hr : 0 < r) :
    (∫ y in Ioi 0, (k y : ℂ) • shift y (unitExponential r hr)) =
      (laplaceIntegral k r : ℂ) • unitExponential r hr := by
  calc
    _ = ∫ y in Ioi 0,
        ((k y * Real.exp (-r*y) : ℝ) : ℂ) • unitExponential r hr := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [shift_unitExponential r hr y hy.le, smul_smul, Complex.ofReal_mul]
    _ = _ := by rw [integral_smul_const, integral_complex_ofReal]; rfl

/-- Scalar L¹ kernels cannot give a positive lower norm bound on this carrier. -/
theorem not_boundedBelow_of_strongIntegral {k : ℝ → ℝ}
    (hk : IntegrableOn k (Ioi 0)) (X : Hilbert →L[ℂ] Hilbert)
    (hX : ∀ f, X f = ∫ y in Ioi 0, (k y : ℂ) • shift y f) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ f : Hilbert, c * ‖f‖ ≤ ‖X f‖ := by
  rintro ⟨c, hc, h⟩
  have ht := (laplaceIntegral_tendsto hk).norm
  have he : ∀ᶠ r : ℝ in atTop, ‖laplaceIntegral k r‖ < c :=
    ht.eventually (gt_mem_nhds (by simpa using hc))
  obtain ⟨r, hr, he⟩ := ((eventually_gt_atTop (0:ℝ)).and he).exists
  have hb := h (unitExponential r hr)
  rw [hX, strongIntegral_unitExponential, norm_smul, norm_unitExponential,
    mul_one, mul_one, Complex.norm_real] at hb
  exact (not_lt_of_ge hb) he

end Riemann.Analysis.HalfLine
