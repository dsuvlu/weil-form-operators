import Riemann.Analysis.FiniteWindow.NativeGammaCoefficients
import Riemann.Analysis.FiniteWindow.NativePolarCoefficients

/-! # Arithmetic and analytic construction of the native completed Weil matrix

The coefficients are assembled from actual prime shifts, the renormalized Gamma
current and the two polar resolvents. Equality with the full native current form
is proved without a matching assumption or a spectral admission.
-/
noncomputable section
open scoped InnerProductSpace
namespace Riemann.Analysis.FiniteWindow
open Riemann.CCM.Native

/-- Canonical coefficients of the actual completed current on the full Fourier section. -/
def nativeCompletedCoefficients (N : ℕ) (L : ℝ) : Coefficients N :=
  addCoefficients (addCoefficients (nativePrimeCoefficients N L (1 / 2))
    (nativeGammaCoefficients N L)) (nativePolarCoefficients N L)

/-- Finite compression of the actual domain-defined completed current. -/
def nativeCompletedCompression (N : ℕ) {L : ℝ} (hL : 0 < L) : Section N →L[ℂ] Section N :=
  LinearMap.toContinuousLinearMap ((fourierInclusion N L).adjoint.toLinearMap.comp
    ((completedCurrent L).comp (nativeCurrentInclusion N hL)))

theorem nativeCompletedCompression_eq {N : ℕ} {L : ℝ} (hL : 0 < L) :
    nativeCompletedCompression N hL = nativeCompression N L (primeCurrent L (1 / 2)) +
      nativeGammaCompression N hL - nativeCompression N L (volterra L (1 / 2)) -
      nativeCompression N L (volterra L (-(1 / 2))) := by
  apply ContinuousLinearMap.ext
  intro x
  change (fourierInclusion N L).adjoint
    (primeCurrent L (1 / 2) (fourierHilbert L x) +
      gammaCurrent L (nativeCurrentInclusion N hL x) -
      volterra L (1 / 2) (fourierHilbert L x) - volterra L (-(1 / 2)) (fourierHilbert L x)) = _
  rw [map_sub, map_sub, map_add]
  rfl

/-- The full native matrix is derived from the actual completed current. -/
theorem nativeCompleted_weilOperator {N : ℕ} {L : ℝ} (hL : 0 < L) :
    weilOperator (nativeCompletedCoefficients N L) =
      -(nativeCompletedCompression N hL + (nativeCompletedCompression N hL).adjoint) := by
  rw [nativeCompletedCoefficients, weilOperator_addCoefficients, weilOperator_addCoefficients,
    nativePrime_weilOperator hL, nativeGamma_weilOperator hL, nativePolar_weilOperator hL,
    nativeCompletedCompression_eq]
  simp only [map_add, map_sub]
  abel

/-- Exact equality of the native physical Weil form and the completed current form. -/
theorem nativeCompletedCurrent_form {N : ℕ} {L : ℝ} (hL : 0 < L) (x y : Section N) :
    completedCurrentForm L (nativeCurrentInclusion N hL x) (nativeCurrentInclusion N hL y) =
      ⟪x, weilOperator (nativeCompletedCoefficients N L) y⟫_ℂ := by
  rw [nativeCompleted_weilOperator hL]
  change -⟪fourierHilbert L x, completedCurrent L (nativeCurrentInclusion N hL y)⟫_ℂ -
    ⟪completedCurrent L (nativeCurrentInclusion N hL x), fourierHilbert L y⟫_ℂ =
    ⟪x, -(nativeCompletedCompression N hL y + (nativeCompletedCompression N hL).adjoint y)⟫_ℂ
  rw [inner_neg_right, inner_add_right, ContinuousLinearMap.adjoint_inner_right]
  have hright : ⟪x, nativeCompletedCompression N hL y⟫_ℂ =
      ⟪fourierHilbert L x, completedCurrent L (nativeCurrentInclusion N hL y)⟫_ℂ :=
    (fourierInclusion N L).adjoint_inner_right x (completedCurrent L (nativeCurrentInclusion N hL y))
  have hleft : ⟪nativeCompletedCompression N hL x, y⟫_ℂ =
      ⟪completedCurrent L (nativeCurrentInclusion N hL x), fourierHilbert L y⟫_ℂ :=
    (fourierInclusion N L).adjoint_inner_left y (completedCurrent L (nativeCurrentInclusion N hL x))
  rw [hright, hleft]
  ring

end Riemann.Analysis.FiniteWindow
