import Riemann.Analysis.HalfLine.CompletedOperator
import Riemann.Analysis.HalfLine.LaplaceObstruction
import Riemann.Analysis.HalfLine.RawBoxScalar

/-! # The two different exponential controls

High-decay unit exponentials obstruct a lower norm bound for the completed
operator. The fixed half-decay vector is instead the raw Euler graph defect;
the bounded polar prefactor annihilates that defect.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Riemann.Analysis.HalfLine

theorem completedOperator_unitExponential (r : ℝ) (hr : 0 < r) :
    completedOperator (unitExponential r hr) =
      (laplaceIntegral criticalKernel r : ℂ) • unitExponential r hr := by
  rw [completedOperator_apply_nonneg, integral_Ici_eq_integral_Ioi]
  exact strongIntegral_unitExponential _ r hr

theorem completed_laplace_tendsto :
    Tendsto (laplaceIntegral criticalKernel) atTop (𝓝 0) :=
  laplaceIntegral_tendsto criticalKernel_integrableOn

/-- The actual completed operator has no positive lower norm bound. -/
theorem completedOperator_not_boundedBelow :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ f : Hilbert, c * ‖f‖ ≤ ‖completedOperator f‖ := by
  apply not_boundedBelow_of_strongIntegral criticalKernel_integrableOn
  intro f
  rw [completedOperator_apply_nonneg, integral_Ici_eq_integral_Ioi]

theorem volterra_exponential {b : ℝ} (hb : 0 < b) (r : ℝ) (hr : 0 < r) :
    volterra b (exponential r hr) = ((b+r)⁻¹ : ℂ) • exponential r hr := by
  rw [volterra_apply hb, integral_Ici_eq_integral_Ioi]
  calc
    _ = ∫ y in Ioi 0, (Real.exp (-(b+r)*y) : ℂ) • exponential r hr := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [shift_exponential r hr y hy.le, smul_smul,
        ← Complex.ofReal_mul, ← Real.exp_add]
      congr 3
      ring
    _ = _ := by
      rw [integral_smul_const, integral_complex_ofReal,
        integral_exp_mul_Ioi (by linarith)]
      congr 1
      push_cast
      simp only [mul_zero, Complex.exp_zero]
      field_simp

/-- The nonzero limiting raw graph output for boxes of width one. -/
def rawGraphDefect : Hilbert :=
  ((2*(Real.exp (1/2)-1) : ℝ) : ℂ) • exponential (1/2) (by norm_num)

theorem rawGraphDefect_ae :
    ((rawGraphDefect : Ambient) : ℝ → ℂ) =ᵐ[volume]
      fun t => (graphDefectScalar t : ℂ) := by
  have hs := Lp.coeFn_smul ((2*(Real.exp (1/2)-1) : ℝ) : ℂ)
    (exponential (1/2) (by norm_num) : Ambient)
  filter_upwards [hs, exponential_ae (1/2) (by norm_num)] with t hs he
  simp only [rawGraphDefect, Submodule.coe_smul]
  rw [hs]
  simp only [Pi.smul_apply, he, exponentialFunction, graphDefectScalar]
  by_cases ht : 0 ≤ t
  · simp only [if_pos ht, indicator_of_mem (show t ∈ Ici (0:ℝ) from ht),
      smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_ofNat]
    rw [show -(1/2:ℝ)*t = -t/2 by ring]
  · simp [ht]

theorem rawGraphDefect_ne_zero : rawGraphDefect ≠ 0 := by
  have he : exponential (1/2) (by norm_num) ≠ 0 := by
    intro h
    have hn := norm_exponential_sq (1/2) (by norm_num)
    rw [h] at hn
    norm_num at hn
  apply smul_ne_zero _ he
  have h : 1 < Real.exp (1/2) := Real.one_lt_exp_iff.mpr (by norm_num)
  exact_mod_cast (show (2:ℝ)*(Real.exp (1/2)-1) ≠ 0 by positivity)

theorem volterra_rawGraphDefect {b : ℝ} (hb : 0 < b) :
    volterra b rawGraphDefect = ((b+1/2)⁻¹ : ℂ) • rawGraphDefect := by
  simp only [rawGraphDefect, map_smul, volterra_exponential hb (1/2) (by norm_num)]
  rw [smul_smul, smul_smul]
  congr 1
  push_cast
  ring

/-- This annihilates the raw defect, not the value of X on that vector. -/
theorem polarFactor_kills_rawGraphDefect :
    (ContinuousLinearMap.id ℂ Hilbert - (2:ℂ) • volterra (3/2)) rawGraphDefect = 0 := by
  simp only [sub_apply, ContinuousLinearMap.id_apply,
    smul_apply, volterra_rawGraphDefect (by norm_num : (0:ℝ)<3/2),
    smul_smul]
  norm_num

theorem polarPrefactor_kills_rawGraphDefect :
    ((ContinuousLinearMap.id ℂ Hilbert - (2:ℂ) • volterra (5/2)).comp
      (ContinuousLinearMap.id ℂ Hilbert - (2:ℂ) • volterra (3/2))) rawGraphDefect = 0 := by
  rw [ContinuousLinearMap.comp_apply, polarFactor_kills_rawGraphDefect, map_zero]

end Riemann.Analysis.HalfLine
