import Riemann.Analysis.FiniteWindow.NativeCompensatedCurrent
import Riemann.Analysis.FiniteWindow.Volterra

/-! # Literal real-parameter Volterra coefficients and the polar contribution -/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace Riemann.Analysis.FiniteWindow
open Riemann.CCM.Native

def realVolterraWeight (b y : ℝ) : ℝ := Real.exp (-b * y)

theorem realVolterra_compensatedOrbit {N : ℕ} (L b : ℝ) (x : Section N) :
    compensatedOrbit L (realVolterraWeight b) (realVolterraWeight b) x =
      weightedOrbit L (b : ℂ) (fourierHilbert L x) := by
  funext y
  simp only [compensatedOrbit, weightedOrbit, realVolterraWeight, Complex.ofReal_exp,
    Complex.ofReal_mul, Complex.ofReal_neg]
  module

theorem realVolterra_compensated_integrable {N : ℕ} {L : ℝ} (hL : 0 < L)
    (b : ℝ) (x : Section N) :
    IntegrableOn (compensatedOrbit L (realVolterraWeight b) (realVolterraWeight b) x) (Ioo 0 L) := by
  rw [realVolterra_compensatedOrbit]
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le).mp
    ((continuous_weightedOrbit L (b : ℂ) (fourierHilbert L x)).intervalIntegrable 0 L)

/-- Coefficients of the actual Hermitian real-parameter Volterra resolvent. -/
def nativeRealVolterraCoefficients (N : ℕ) (L b : ℝ) : Coefficients N :=
  integralCoefficients (volume.restrict (Ioo 0 L))
    (fun y => compensatedCoefficients N L y (realVolterraWeight b y) (realVolterraWeight b y))

theorem realVolterra_compression_eq {N : ℕ} {L : ℝ} (hL : 0 < L) (b : ℝ) :
    nativeCompression N L (volterra L (b : ℂ)) =
      compensatedIntegral L (realVolterraWeight b) (realVolterraWeight b)
        (realVolterra_compensated_integrable hL b) := by
  apply ContinuousLinearMap.ext
  intro x
  change (fourierInclusion N L).adjoint (volterra L (b : ℂ) (fourierHilbert L x)) =
    (fourierInclusion N L).adjoint
      (∫ y in Ioo 0 L, compensatedOrbit L (realVolterraWeight b) (realVolterraWeight b) x y)
  rw [volterra_apply, intervalIntegral.integral_of_le hL.le,
    integral_Ioc_eq_integral_Ioo, realVolterra_compensatedOrbit]

/-- The native divided differences are derived from the actual resolvent kernel. -/
theorem nativeRealVolterra_weilOperator {N : ℕ} {L : ℝ} (hL : 0 < L) (b : ℝ) :
    weilOperator (nativeRealVolterraCoefficients N L b) =
      nativeCompression N L (volterra L (b : ℂ)) +
        (nativeCompression N L (volterra L (b : ℂ))).adjoint := by
  rw [realVolterra_compression_eq hL b]
  exact (compensatedIntegral_weilOperator hL _ _ (realVolterra_compensated_integrable hL b)).symm

/-- Additive Hermitian polar contribution to the negative completed current. -/
def nativePolarCoefficients (N : ℕ) (L : ℝ) : Coefficients N :=
  addCoefficients (nativeRealVolterraCoefficients N L (1 / 2))
    (nativeRealVolterraCoefficients N L (-(1 / 2)))

theorem nativePolar_weilOperator {N : ℕ} {L : ℝ} (hL : 0 < L) :
    weilOperator (nativePolarCoefficients N L) =
      nativeCompression N L (volterra L (1 / 2) + volterra L (-(1 / 2))) +
        (nativeCompression N L (volterra L (1 / 2) + volterra L (-(1 / 2)))).adjoint := by
  rw [nativePolarCoefficients, weilOperator_addCoefficients,
    nativeRealVolterra_weilOperator hL, nativeRealVolterra_weilOperator hL]
  simp only [map_add]
  push_cast
  abel

@[simp] theorem nativeRealVolterraCoefficients_beta (N : ℕ) (L b : ℝ) (i : Index N) :
    (nativeRealVolterraCoefficients N L b).beta i =
      ∫ y in Ioo 0 L, -Real.exp (-b * y) * Real.sin (frequency L i * y) / Real.pi := rfl

@[simp] theorem nativeRealVolterraCoefficients_diagonal (N : ℕ) (L b : ℝ) (i : Index N) :
    (nativeRealVolterraCoefficients N L b).diagonal i =
      ∫ y in Ioo 0 L, 2 * Real.exp (-b * y) * (1 - y / L) * Real.cos (frequency L i * y) := by
  simp only [nativeRealVolterraCoefficients, integralCoefficients, compensatedCoefficients, realVolterraWeight]
  congr 1
  funext y
  ring

end Riemann.Analysis.FiniteWindow
