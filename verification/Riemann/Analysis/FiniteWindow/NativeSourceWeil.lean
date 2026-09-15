import Riemann.Analysis.FiniteWindow.LiteralSourceColumns
import Riemann.Analysis.FiniteWindow.NativeCompletedCoefficients
import Riemann.CCM.NativeCapacity
import Mathlib.Analysis.Matrix.Normed

/-! # Literal source derivatives and native shifted Weil energies

The native coefficients are those proved to arise from the actual completed
current. The full admitted eigenvalue and every column/section are fixed while
the real completion parameter is differentiated. Identities are given both as
pairings and as actual derivatives of finite coefficient matrices.
-/
noncomputable section
open scoped InnerProductSpace Matrix.Norms.Elementwise
namespace Riemann.Analysis.FiniteWindow
open Riemann.CCM.Native Riemann.Capacity

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] {N : ℕ} {L : ℝ}

/-- The literal polarized source derivative is exactly the full native Weil
pairing, with the arithmetic coefficients constructed upstairs. -/
theorem hasDerivAt_nativeSourceWeil (hL : 0 < L) (x y : Section N)
    (hx : endpoint N L x = 0) (hy : endpoint N L y = 0) :
    HasDerivAt (completedSourceGram L (nativeCompletedSource hL x hx)
      (nativeCompletedSource hL y hy))
      ⟪x, weilOperator (nativeCompletedCoefficients N L) y⟫_ℂ (1/2) := by
  rw [← nativeCompletedCurrent_form hL x y]
  exact hasDerivAt_nativeCompletedSourceGram_current hL x y hx hy

theorem hasDerivAt_literalColumnMetric_weil (hL : 0 < L) (W : F →L[ℂ] Section N)
    (hW : ∀ x, endpoint N L (W x) = 0) (x y : F) :
    HasDerivAt (fun σ => ⟪x, literalColumnMetric hL W hW σ y⟫_ℂ)
      ⟪W x, weilOperator (nativeCompletedCoefficients N L) (W y)⟫_ℂ (1/2) := by
  rw [← nativeCompletedCurrent_form hL (W x) (W y)]
  exact hasDerivAt_literalColumnMetric_inner hL W hW x y

/-- BS frozen-source identity for the actual shifted native form. The energy
e₀ is the fixed full admitted eigenvalue, not differentiated with σ. -/
theorem native_columnEnergy_sourceDerivative (hL : 0 < L)
    (A : GroundAdmission (nativeCompletedCoefficients N L))
    (W : F →L[ℂ] Section N) (hW : ∀ x, endpoint N L (W x) = 0) (x y : F) :
    ⟪x, columnEnergy (nativeShifted (nativeCompletedCoefficients N L) A) W y⟫_ℂ =
      deriv (fun σ => ⟪x, literalColumnMetric hL W hW σ y⟫_ℂ) (1/2) -
        (A.e₀ : ℂ) * ⟪x, literalColumnMetric hL W hW (1/2) y⟫_ℂ := by
  rw [(hasDerivAt_literalColumnMetric_weil hL W hW x y).deriv,
    columnEnergy_inner, literalColumnMetric_half]
  change ⟪W x, weilOperator (nativeCompletedCoefficients N L) (W y) -
      (A.e₀ : ℂ) • W y⟫_ℂ = _
  rw [inner_sub_right, inner_smul_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

/-- Matrix-valued derivative of the actual frozen literal-source metric. -/
theorem hasDerivAt_literalColumnMatrix_weil {ι : Type*} [Fintype ι]
    (hL : 0 < L) (W : F →L[ℂ] Section N)
    (hW : ∀ x, endpoint N L (W x) = 0) (basis : ι → F) :
    HasDerivAt (literalColumnMatrix hL W hW basis)
      (Matrix.of fun i j =>
        ⟪W (basis i), weilOperator (nativeCompletedCoefficients N L) (W (basis j))⟫_ℂ)
      (1/2) := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_literalColumnMetric_weil hL W hW (basis i) (basis j)

/-- `B_W = 𝓑′(a) − e₀ 𝓑(a)` in any fixed finite coefficient family. -/
theorem native_columnEnergy_sourceMatrix {ι : Type*} [Fintype ι]
    (hL : 0 < L) (A : GroundAdmission (nativeCompletedCoefficients N L))
    (W : F →L[ℂ] Section N) (hW : ∀ x, endpoint N L (W x) = 0) (basis : ι → F) :
    (Matrix.of fun i j => ⟪basis i, columnEnergy (nativeShifted (nativeCompletedCoefficients N L) A)
      W (basis j)⟫_ℂ) =
      deriv (literalColumnMatrix hL W hW basis) (1/2) -
        (A.e₀ : ℂ) • literalColumnMatrix hL W hW basis (1/2) := by
  have hd : deriv (literalColumnMatrix hL W hW basis) (1/2) =
      (Matrix.of fun i j => ⟪W (basis i), weilOperator (nativeCompletedCoefficients N L) (W (basis j))⟫_ℂ) :=
    (hasDerivAt_literalColumnMatrix_weil hL W hW basis).deriv
  rw [hd]
  funext i j
  have he := native_columnEnergy_sourceDerivative hL A W hW (basis i) (basis j)
  rw [(hasDerivAt_literalColumnMetric_weil hL W hW (basis i) (basis j)).deriv] at he
  exact he

/-- The BS differentiated columns are corrected with an independent, fixed
endpoint-one section before taking their unique literal sources. -/
theorem native_correctedEnergy_sourceMatrix {ι : Type*} [Fintype ι]
    (hL : 0 < L) (A : GroundAdmission (nativeCompletedCoefficients N L))
    (W : F →L[ℂ] Section N) (p : Section N) (hp : endpoint N L p = 1) (basis : ι → F) :
    let D₀ := endpointCorrectedColumns ((derivative L).comp W) (endpointVector N L) p
    let hD₀ := native_endpointCorrectedColumns_zero ((derivative L).comp W) p hp
    (Matrix.of fun i j => ⟪basis i, columnEnergy (nativeShifted (nativeCompletedCoefficients N L) A)
      D₀ (basis j)⟫_ℂ) =
      deriv (literalColumnMatrix hL D₀ hD₀ basis) (1/2) -
        (A.e₀ : ℂ) • literalColumnMatrix hL D₀ hD₀ basis (1/2) := by
  exact native_columnEnergy_sourceMatrix hL A _ _ basis

end Riemann.Analysis.FiniteWindow
