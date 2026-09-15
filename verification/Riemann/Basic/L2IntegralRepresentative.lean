import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Representatives of strong integrals in L²

Testing against finite-measure indicator vectors reduces a Hilbert-space
Bochner integral to scalar Fubini. The explicit joint representative is
integrable separately from the L²-valued map; evaluation at a point is never
used as a continuous functional on L².
-/
noncomputable section

namespace Riemann.Analysis
open MeasureTheory Function
open scoped ENNReal

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
  {μ : Measure Ω} {ν : Measure T} [SFinite μ] [SigmaFinite ν]

/-- A jointly integrable representative computes the strong L² integral a.e. -/
theorem integral_L2_ae {F : Ω → Lp ℂ 2 ν} {φ : Ω → T → ℂ}
    (hF : Integrable F μ) (hφ : Integrable (uncurry φ) (μ.prod ν))
    (hrep : ∀ᵐ y ∂μ, (F y : T → ℂ) =ᵐ[ν] φ y) :
    ((∫ y, F y ∂μ : Lp ℂ 2 ν) : T → ℂ) =ᵐ[ν] fun t => ∫ y, φ y t ∂μ := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s _ hs
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hs.ne
  · intro s _ _
    exact hφ.integral_prod_right.integrableOn
  · intro s hs hνs
    let e : Lp ℂ 2 ν := indicatorConstLp 2 hs hνs.ne (1 : ℂ)
    calc
      _ = inner ℂ e (∫ y, F y ∂μ) := (L2.inner_indicatorConstLp_one hs hνs.ne _).symm
      _ = ∫ y, inner ℂ e (F y) ∂μ :=
        ((innerSL ℂ e).integral_comp_comm hF).symm
      _ = ∫ y, ∫ t in s, φ y t ∂ν ∂μ := by
        apply integral_congr_ae
        filter_upwards [hrep] with y hy
        rw [L2.inner_indicatorConstLp_one hs hνs.ne]
        exact integral_congr_ae (ae_restrict_of_ae hy)
      _ = _ := by
        apply integral_integral_swap
        exact hφ.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)

end Riemann.Analysis
