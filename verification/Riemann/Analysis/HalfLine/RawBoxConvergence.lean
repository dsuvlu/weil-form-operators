import Riemann.Analysis.HalfLine.CompactBox
import Riemann.Analysis.HalfLine.CompletedObstruction
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # L² convergence of the explicit raw box outputs

The scalar envelope is squared only after the arithmetic sum has been
compared to its main term. This is convergence in the physical norm.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Riemann.Analysis.HalfLine

lemma boxVector_tendsto_zero :
    Tendsto (fun n : ℕ => boxVector n (Nat.cast_nonneg n)) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero, norm_boxVector]
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by norm_num : (0:ℝ)<1/2))
  simpa only [Function.comp_def, neg_mul, div_eq_mul_inv, one_mul] using h

/-- The majorant is an actual integrable function on the whole real line. -/
lemma raw_error_majorant_integrable :
    Integrable (fun t : ℝ => (Ici 0).indicator
      (fun t => 16*Real.exp 1*Real.exp (-t)) t) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ici
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have h := (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul
    (16*Real.exp 1)
  simpa only [IntegrableOn, neg_one_mul] using h

/-- Any actual L² representatives equal to the raw scalar sums converge to the
explicit nonzero graph defect. The next module applies this to rawEuler(box). -/
theorem rawBoxVectors_tendsto (u : ℕ → Hilbert)
    (hu : ∀ n, ((u n : Ambient) : ℝ → ℂ) =ᵐ[volume]
      fun t => (rawBoxScalar n t : ℂ)) :
    Tendsto u atTop (𝓝 rawGraphDefect) := by
  have he (n : ℕ) : (((u n - rawGraphDefect : Hilbert) : Ambient) : ℝ → ℂ) =ᵐ[volume]
      fun t => ((rawBoxScalar n t - graphDefectScalar t : ℝ) : ℂ) := by
    filter_upwards [hu n, rawGraphDefect_ae,
      Lp.coeFn_sub (u n : Ambient) (rawGraphDefect : Ambient)] with t h₁ h₂ h₃
    simp only [Submodule.coe_sub]
    rw [h₃]
    simp only [Pi.sub_apply, h₁, h₂, Complex.ofReal_sub]
  have hall := ae_all_iff.mpr he
  have hdct := tendsto_integral_of_dominated_convergence
    (fun t : ℝ => (Ici 0).indicator (fun t => 16*Real.exp 1*Real.exp (-t)) t)
    (F := fun n t => ‖((u n - rawGraphDefect : Hilbert) : Ambient) t‖^2)
    (f := fun _ : ℝ => (0:ℝ))
    (fun n => (Lp.aestronglyMeasurable _).norm.pow 2)
    raw_error_majorant_integrable ?_ ?_
  · have hs : Tendsto (fun n => ‖u n - rawGraphDefect‖^2) atTop (𝓝 0) := by
      simpa only [← norm_sq_eq_integral, integral_zero] using hdct
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hs
  · intro n
    filter_upwards [he n] with t ht
    rw [ht, Complex.norm_real, Real.norm_eq_abs]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := rawBoxScalar_error_envelope (n:ℝ) t
    by_cases ht0 : 0 ≤ t
    · rw [if_pos ht0] at h
      rw [indicator_of_mem (show t ∈ Ici (0:ℝ) from ht0)]
      have hsq := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.mpr h
      have hexp : (4*Real.exp (1/2)*Real.exp (-t/2))^2 =
          16*Real.exp 1*Real.exp (-t) := by
        rw [mul_pow, mul_pow]
        rw [sq (Real.exp (1/2)), ← Real.exp_add,
          sq (Real.exp (-t/2)), ← Real.exp_add]
        ring_nf
      simpa only [hexp] using hsq
    · simp [ht0, rawBoxScalar, graphDefectScalar]
  · filter_upwards [hall] with t ht
    simp only [ht, Complex.norm_real, Real.norm_eq_abs]
    have h := ((rawBoxScalar_tendsto t).sub_const (graphDefectScalar t)).abs.pow 2
    simpa only [sub_self, abs_zero, zero_pow (by norm_num : (2:ℕ)≠0)] using h

end Riemann.Analysis.HalfLine
