import Riemann.Analysis.FiniteWindow.GammaBackground
import Riemann.Analysis.FiniteWindow.GammaCurrentConvolution

/-! The native Archimedean current is the same convergent vector integral as the
Gamma current. Singular terms are never integrated separately. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set
namespace Riemann.Analysis.FiniteWindow

/-- The native C8 difference integrand, kept as one convergent expression. -/
def nativeGammaIntegrand (L : ℝ) (f : Hilbert L) (y : ℝ) : Hilbert L :=
  (gammaWeight y : ℂ) • shift L y f -
    (((Real.exp y - Real.exp (-y))⁻¹ : ℝ) : ℂ) • f

lemma gamma_logistic_difference {y : ℝ} (hy : 0 < y) :
    (Real.exp y - Real.exp (-y))⁻¹ -
      Real.exp (-2*y) / (1 - Real.exp (-2*y)) = (Real.exp y + 1)⁻¹ := by
  have ht : 1 < Real.exp y := Real.one_lt_exp_iff.mpr hy
  have ht0 : Real.exp y ≠ 0 := (Real.exp_pos y).ne'
  have hs : Real.exp y + 1 ≠ 0 := by positivity
  have he : Real.exp (-2*y) = (Real.exp y)⁻¹ * (Real.exp y)⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  rw [Real.exp_neg, he]
  have hi : (Real.exp y)⁻¹ < 1 := (inv_lt_one₀ (Real.exp_pos y)).mpr ht
  have hid : Real.exp y - (Real.exp y)⁻¹ ≠ 0 := by linarith
  have hq : 1 - (Real.exp y)⁻¹ * (Real.exp y)⁻¹ ≠ 0 := by
    have hip : 0 < (Real.exp y)⁻¹ := by positivity
    nlinarith
  have hsq : -1 + Real.exp y ^ 2 ≠ 0 := by nlinarith only [ht]
  field_simp
  have hh := mul_inv_cancel₀ hsq
  ring_nf at hh ⊢
  nlinarith only [hh]

lemma nativeGammaIntegrand_eq {L y : ℝ} (hy : 0 < y) (f : Hilbert L) :
    nativeGammaIntegrand L f y = gammaIntegrand L f y -
      (((Real.exp y + 1)⁻¹ : ℝ) : ℂ) • f := by
  rw [nativeGammaIntegrand, gammaIntegrand_split]
  have hs : (Real.exp y - Real.exp (-y))⁻¹ =
      Real.exp (-2*y) / (1 - Real.exp (-2*y)) + (Real.exp y + 1)⁻¹ := by
    linarith [gamma_logistic_difference hy]
  rw [hs]
  push_cast
  module

lemma integrable_logistic_current {L : ℝ} (f : Hilbert L) :
    IntegrableOn (fun y => (((Real.exp y + 1)⁻¹ : ℝ) : ℂ) • f) (Ioo 0 L) volume := by
  have hc : Continuous (fun y => (((Real.exp y + 1)⁻¹ : ℝ) : ℂ) • f) := by
    have h : Continuous (fun y : ℝ => (Real.exp y + 1)⁻¹) :=
      (Real.continuous_exp.add continuous_const).inv₀
        (fun y => (add_pos (Real.exp_pos y) zero_lt_one).ne')
    exact (Complex.continuous_ofReal.comp h).smul continuous_const
  exact (ContinuousOn.integrableOn_compact isCompact_Icc hc.continuousOn).mono_set Ioo_subset_Icc_self

/-- Native C8 integrability follows from the literal Gamma-current domain. -/
theorem nativeGammaIntegrand_integrable {L : ℝ} (f : gammaCurrentDomain L) :
    IntegrableOn (nativeGammaIntegrand L f) (Ioo 0 L) volume := by
  have hh : IntegrableOn (fun y => gammaIntegrand L f y -
      (((Real.exp y + 1)⁻¹ : ℝ) : ℂ) • (f : Hilbert L)) (Ioo 0 L) volume :=
    (show Integrable (gammaIntegrand L (f : Hilbert L))
      (volume.restrict (Ioo 0 L)) from f.property).sub
        (integrable_logistic_current (f : Hilbert L))
  refine hh.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact (nativeGammaIntegrand_eq (L := L) (y := y) hy.1 (f : Hilbert L)).symm

/-- The exact native Archimedean normalization, on the same proved domain. -/
theorem gammaCurrent_native_formula {L : ℝ} (hL : 0 < L) (f : gammaCurrentDomain L) :
    gammaCurrent L f = ((nativeGammaConstant L / 2 : ℝ) : ℂ) • (f : Hilbert L) +
      ∫ y in Ioo 0 L, nativeGammaIntegrand L f y := by
  have hi : (∫ y in Ioo 0 L, nativeGammaIntegrand L f y) =
      (∫ y in Ioo 0 L, gammaIntegrand L f y) -
        ((Real.log 2 - Real.log (1 + Real.exp (-L)) : ℝ) : ℂ) • (f : Hilbert L) := by
    have he : nativeGammaIntegrand L f =ᵐ[volume.restrict (Ioo 0 L)]
        (fun y => gammaIntegrand L f y - (((Real.exp y + 1)⁻¹ : ℝ) : ℂ) • (f : Hilbert L)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      exact nativeGammaIntegrand_eq (L := L) (y := y) hy.1 (f : Hilbert L)
    have hlog : (∫ y in Ioo 0 L, (Real.exp y + 1)⁻¹) =
        Real.log 2 - Real.log (1 + Real.exp (-L)) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hL.le]
      exact integral_logistic hL.le
    rw [integral_congr_ae he, integral_sub f.property (integrable_logistic_current (f : Hilbert L)),
      integral_smul_const, integral_complex_ofReal, hlog]
  rw [hi]
  have hc : gammaConstant L = nativeGammaConstant L / 2 +
      Real.log (1 + Real.exp (-L)) - Real.log 2 := by
    linarith [gammaConstant_sub_native hL]
  change (gammaConstant L : ℂ) • (f : Hilbert L) + _ = _
  rw [hc]
  push_cast
  module

end Riemann.Analysis.FiniteWindow
