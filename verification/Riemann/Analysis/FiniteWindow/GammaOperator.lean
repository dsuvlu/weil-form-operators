import Riemann.Analysis.FiniteWindow.Volterra
import Riemann.Analysis.GammaKernel
import Riemann.Analysis.FiniteWindow.StrongKernelIntegral
import Riemann.Analysis.FiniteWindow.KilledShiftHilbert

/-! # The independent Gamma factor on the actual finite-window Hilbert space

The scalar kernel is integrated against each shift orbit. Its L¹ derivative
therefore gives an operator-norm derivative, without an operator-valued
Bochner integral of translations.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open MeasureTheory Set

namespace Riemann.Analysis.FiniteWindow

local instance (L : ℝ) : ContinuousSMul ℝ (Hilbert L →L[ℂ] Hilbert L) :=
  IsScalarTower.continuousSMul ℂ

/-- Actual shifts as a strongly integrable contraction family. -/
def shiftFamily (L : ℝ) : StrongContractionFamily (volume.restrict (Ioo 0 L)) (Hilbert L) where
  operator := shift L
  measurable_orbit u := (continuous_shift_apply L u).aestronglyMeasurable
  norm_le := norm_shift_le L

/-- Inclusion of real scalar L¹ kernels into complex scalar L¹ kernels. -/
def complexifyKernel (L : ℝ) :
    Lp ℝ 1 (volume.restrict (Ioo 0 L)) →L[ℝ] Lp ℂ 1 (volume.restrict (Ioo 0 L)) :=
  Complex.ofRealCLM.compLpL 1 (volume.restrict (Ioo 0 L))

/-- Independent relative Gamma factor, with reference parameter 5/2. -/
def gammaOperator (L σ : ℝ) : Hilbert L →L[ℂ] Hilbert L :=
  (shiftFamily L).integration (complexifyKernel L (GammaCompletion.kernelL1 L σ))

/-- Its actual critical derivative in bounded-operator norm. -/
def gammaDerivative (L : ℝ) : Hilbert L →L[ℂ] Hilbert L :=
  (shiftFamily L).integration (complexifyKernel L (GammaCompletion.criticalDerivativeL1 L))

theorem hasDerivAt_gammaOperator_half {L : ℝ} (hL : 0 < L) :
    HasDerivAt (gammaOperator L) (gammaDerivative L) (1 / 2) := by
  exact (shiftFamily L).hasDerivAt_integration
    ((complexifyKernel L).hasFDerivAt.comp_hasDerivAt (1 / 2)
      (GammaCompletion.hasDerivAt_kernelL1_half hL))

/-- Every parameter in the displayed open neighborhood has an actual
bounded-operator derivative; the critical derivative is computed above. -/
theorem gammaOperator_hasDerivAt {L σ : ℝ} (hL : 0 < L) (hσ : σ ∈ Ioo 0 1) :
    ∃ T : Hilbert L →L[ℂ] Hilbert L, HasDerivAt (gammaOperator L) T σ := by
  have h := (complexifyKernel L).hasFDerivAt.comp_hasDerivAt σ
    (GammaCompletion.differentiableAt_kernelL1 hL hσ).hasDerivAt
  exact ⟨_, (shiftFamily L).hasDerivAt_integration h⟩

theorem gammaOperator_apply {L σ : ℝ} (hL : 0 < L) (hσ : σ ∈ Icc 0 1)
    (u : Hilbert L) :
    gammaOperator L σ u =
      ∫ y in Ioo 0 L, (GammaCompletion.kernel σ y : ℂ) • shift L y u := by
  change (shiftFamily L).kernelOperator
    (complexifyKernel L (GammaCompletion.kernelL1 L σ)) u = _
  rw [StrongContractionFamily.kernelOperator_apply]
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (GammaCompletion.kernelL1 L σ),
    GammaCompletion.coe_kernelL1 hL hσ] with y hc hk
  change (complexifyKernel L (GammaCompletion.kernelL1 L σ)) y • shift L y u = _
  rw [show (complexifyKernel L (GammaCompletion.kernelL1 L σ)) y =
    (GammaCompletion.kernel σ y : ℂ) from hc.trans (congrArg (fun x : ℝ => (x : ℂ)) hk)]

theorem gammaDerivative_apply {L : ℝ} (hL : 0 < L) (u : Hilbert L) :
    gammaDerivative L u =
      ∫ y in Ioo 0 L, (GammaCompletion.criticalDerivative y : ℂ) • shift L y u := by
  change (shiftFamily L).kernelOperator
    (complexifyKernel L (GammaCompletion.criticalDerivativeL1 L)) u = _
  rw [StrongContractionFamily.kernelOperator_apply]
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (GammaCompletion.criticalDerivativeL1 L),
    GammaCompletion.coe_criticalDerivativeL1 hL] with y hc hk
  change (complexifyKernel L (GammaCompletion.criticalDerivativeL1 L)) y • shift L y u = _
  rw [show (complexifyKernel L (GammaCompletion.criticalDerivativeL1 L)) y =
    (GammaCompletion.criticalDerivative y : ℂ) from hc.trans (congrArg (fun x : ℝ => (x : ℂ)) hk)]

theorem gammaOperator_half_apply {L : ℝ} (hL : 0 < L) (u : Hilbert L) :
    gammaOperator L (1 / 2) u =
      (2 * Real.pi : ℂ) • ∫ y in Ioo 0 L, (Real.exp (-y / 2) : ℂ) • shift L y u := by
  rw [gammaOperator_apply hL (by norm_num), ← integral_smul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [GammaCompletion.kernel_half, Complex.ofReal_mul, mul_smul,
    Complex.ofReal_ofNat]

/-- The critical Gamma factor is the actual half-parameter Volterra resolvent. -/
theorem gammaOperator_half {L : ℝ} (hL : 0 < L) :
    gammaOperator L (1 / 2) = (2 * Real.pi : ℂ) • volterra L (1 / 2) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [gammaOperator_half_apply hL]
  change _ = (2 * Real.pi : ℂ) • volterra L (1 / 2) u
  rw [volterra_apply, intervalIntegral.integral_of_le hL.le, integral_Ioc_eq_integral_Ioo]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  change (Real.exp (-y / 2) : ℂ) • shift L y u =
    Complex.exp (-(1 / 2 : ℂ) * (y : ℂ)) • shift L y u
  rw [show -(1 / 2 : ℂ) * (y : ℂ) = ((-y / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp]

end Riemann.Analysis.FiniteWindow
