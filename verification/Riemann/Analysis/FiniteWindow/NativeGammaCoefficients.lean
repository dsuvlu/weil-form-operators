import Riemann.Analysis.FiniteWindow.NativeCompensatedCurrent
import Riemann.Analysis.FiniteWindow.CompletedCurrent

/-! # Native Gamma coefficients from the actual renormalized current

Every full Fourier vector belongs to the current domain. The singular weight
is integrated only after the identity subtraction, and coefficient integrability
is derived from the actual strong vector integral.
-/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace Riemann.Analysis.FiniteWindow
open Riemann.CCM.Native

theorem gamma_compensated_integrable {N : ℕ} {L : ℝ} (hL : 0 < L)
    (x : Section N) :
    IntegrableOn (compensatedOrbit L gammaWeight gammaRemainder x) (Ioo 0 L) :=
  fourierHilbert_mem_gammaCurrentDomain hL x

/-- Exact native Gamma coefficients in the renormalized-current normalization. -/
def nativeGammaCoefficients (N : ℕ) (L : ℝ) : Coefficients N :=
  scaleCoefficients (-1) (addCoefficients (scalarCoefficients N (2 * gammaConstant L))
    (integralCoefficients (volume.restrict (Ioo 0 L))
      (fun y => compensatedCoefficients N L y (gammaWeight y) (gammaRemainder y))))

/-- The Gamma current is compressed only after its domain inclusion is proved. -/
def nativeGammaCompression (N : ℕ) {L : ℝ} (hL : 0 < L) : Section N →L[ℂ] Section N :=
  LinearMap.toContinuousLinearMap ((fourierInclusion N L).adjoint.toLinearMap.comp
    ((gammaCurrent L).comp (nativeCurrentInclusion N hL)))

theorem nativeGammaCompression_eq {N : ℕ} {L : ℝ} (hL : 0 < L) :
    nativeGammaCompression N hL = (gammaConstant L : ℂ) • 1 +
      compensatedIntegral L gammaWeight gammaRemainder (gamma_compensated_integrable hL) := by
  apply ContinuousLinearMap.ext
  intro x
  have hi := congrArg (fun T : Section N →L[ℂ] Section N => T x)
    (fourierInclusion_adjoint_comp (N := N) hL)
  change (fourierInclusion N L).adjoint (fourierHilbert L x) = x at hi
  change (fourierInclusion N L).adjoint
    ((gammaConstant L : ℂ) • fourierHilbert L x +
      ∫ y in Ioo 0 L, gammaIntegrand L (fourierHilbert L x) y) = _
  rw [map_add, map_smul, hi]
  rfl

/-- Actual negative Hermitian Gamma current, with no coefficient matching premise. -/
theorem nativeGamma_weilOperator {N : ℕ} {L : ℝ} (hL : 0 < L) :
    weilOperator (nativeGammaCoefficients N L) =
      -(nativeGammaCompression N hL + (nativeGammaCompression N hL).adjoint) := by
  rw [nativeGammaCoefficients, weilOperator_scaleCoefficients, weilOperator_addCoefficients,
    weilOperator_scalarCoefficients, ← compensatedIntegral_weilOperator hL gammaWeight gammaRemainder
      (gamma_compensated_integrable hL), nativeGammaCompression_eq]
  simp only [map_add, map_smulₛₗ, Complex.conj_ofReal, ContinuousLinearMap.adjoint_one]
  push_cast
  change (-1 : ℂ) • ((2 * (gammaConstant L : ℂ)) • (1 : Section N →L[ℂ] Section N) + _) = _
  module

@[simp] theorem nativeGammaCoefficients_beta (N : ℕ) (L : ℝ) (i : Index N) :
    (nativeGammaCoefficients N L).beta i =
      ∫ y in Ioo 0 L, gammaWeight y * Real.sin (frequency L i * y) / Real.pi := by
  simp only [nativeGammaCoefficients, scaleCoefficients, addCoefficients, scalarCoefficients,
    integralCoefficients, compensatedCoefficients, zero_add, neg_one_mul]
  rw [← integral_neg]
  congr 1
  funext y
  ring

@[simp] theorem nativeGammaCoefficients_diagonal (N : ℕ) (L : ℝ) (i : Index N) :
    (nativeGammaCoefficients N L).diagonal i = -2 * gammaConstant L -
      2 * ∫ y in Ioo 0 L,
        gammaWeight y * ((1 - y / L) * Real.cos (frequency L i * y) - 1) + gammaRemainder y := by
  simp only [nativeGammaCoefficients, scaleCoefficients, addCoefficients, scalarCoefficients,
    integralCoefficients, compensatedCoefficients, integral_const_mul]
  ring

end Riemann.Analysis.FiniteWindow
