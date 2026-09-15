import Riemann.Analysis.FiniteWindow.CompletedSourceGram
import Riemann.Capacity.BoundaryCorrection

/-! # Finite frozen column maps through the literal completed source

A finite source-column map is bounded by finite dimensionality of its input.
This does not assert boundedness of the inverse on the whole generator domain
equipped with the ambient L² norm.
-/
noncomputable section
open scoped InnerProductSpace
namespace Riemann.Analysis.FiniteWindow
open Riemann.CCM.Native

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] {N : ℕ} {L : ℝ}

def literalSourceColumns (hL : 0 < L) (W : F →L[ℂ] Section N)
    (hW : ∀ x, endpoint N L (W x) = 0) : F →L[ℂ] Hilbert L :=
  ((completedSource L hL).comp
    (((fourierInclusionLinearMap N L).comp W.toLinearMap).codRestrict (generatorDomain L)
      fun x => (mem_generatorDomain_iff L hL.le _).2
        ⟨_, nativeFourier_hasGenerator hL (W x) (hW x)⟩)).toContinuousLinearMap

@[simp] theorem literalSourceColumns_apply (hL : 0 < L) (W : F →L[ℂ] Section N)
    (hW : ∀ x, endpoint N L (W x) = 0) (x : F) :
    literalSourceColumns hL W hW x = nativeCompletedSource hL (W x) (hW x) := rfl

@[simp] theorem frame_literalSourceColumns (hL : 0 < L) (W : F →L[ℂ] Section N)
    (hW : ∀ x, endpoint N L (W x) = 0) (x : F) :
    completedFrame L (1/2) (literalSourceColumns hL W hW x) = fourierHilbert L (W x) :=
  completedFrame_nativeCompletedSource hL (W x) (hW x)

def literalColumnMetric (hL : 0 < L) (W : F →L[ℂ] Section N)
    (hW : ∀ x, endpoint N L (W x) = 0) (σ : ℝ) : F →L[ℂ] F :=
  (literalSourceColumns hL W hW).adjoint.comp
    ((completedFrame L σ).adjoint.comp
      ((completedFrame L σ).comp (literalSourceColumns hL W hW)))

theorem literalColumnMetric_inner (hL : 0 < L) (W : F →L[ℂ] Section N)
    (hW : ∀ x, endpoint N L (W x) = 0) (σ : ℝ) (x y : F) :
    ⟪x, literalColumnMetric hL W hW σ y⟫_ℂ =
      completedSourceGram L (literalSourceColumns hL W hW x)
        (literalSourceColumns hL W hW y) σ := by
  change ⟪x, (literalSourceColumns hL W hW).adjoint
    ((completedFrame L σ).adjoint (completedFrame L σ (literalSourceColumns hL W hW y)))⟫_ℂ = _
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem literalColumnMetric_half (hL : 0 < L) (W : F →L[ℂ] Section N)
    (hW : ∀ x, endpoint N L (W x) = 0) :
    literalColumnMetric hL W hW (1/2) = W.adjoint.comp W := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [literalColumnMetric_inner, literalSourceColumns_apply, literalSourceColumns_apply,
    nativeCompletedSourceGram_half hL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

/-- Every matrix entry in any fixed coefficient family has the literal current
derivative. Support, columns, and all spectral data remain frozen. -/
theorem hasDerivAt_literalColumnMetric_inner (hL : 0 < L) (W : F →L[ℂ] Section N)
    (hW : ∀ x, endpoint N L (W x) = 0) (x y : F) :
    HasDerivAt (fun σ => ⟪x, literalColumnMetric hL W hW σ y⟫_ℂ)
      (completedCurrentForm L (nativeCurrentInclusion N hL (W x))
        (nativeCurrentInclusion N hL (W y))) (1/2) := by
  simp only [literalColumnMetric_inner, literalSourceColumns_apply]
  exact hasDerivAt_nativeCompletedSourceGram_current hL (W x) (W y) (hW x) (hW y)

/-- The actual endpoint correction used by BS produces eligible source columns. -/
theorem native_endpointCorrectedColumns_zero (D : F →L[ℂ] Section N) (p : Section N)
    (hp : endpoint N L p = 1) (x : F) :
    endpoint N L (Riemann.Capacity.endpointCorrectedColumns D (endpointVector N L) p x) = 0 := by
  rw [endpoint_apply]
  apply Riemann.Capacity.endpointCorrectedColumns_boundary
  exact hp


def literalColumnMatrix {ι : Type*} (hL : 0 < L) (W : F →L[ℂ] Section N)
    (hW : ∀ x, endpoint N L (W x) = 0) (basis : ι → F) (σ : ℝ) : Matrix ι ι ℂ :=
  fun i j => ⟪basis i, literalColumnMetric hL W hW σ (basis j)⟫_ℂ

/-- Matrix-valued differentiation in any fixed finite coefficient family. -/
theorem hasDerivAt_literalColumnMatrix {ι : Type*} [Fintype ι]
    (hL : 0 < L) (W : F →L[ℂ] Section N)
    (hW : ∀ x, endpoint N L (W x) = 0) (basis : ι → F) :
    HasDerivAt (literalColumnMatrix hL W hW basis)
      (fun i j => completedCurrentForm L (nativeCurrentInclusion N hL (W (basis i)))
        (nativeCurrentInclusion N hL (W (basis j)))) (1/2) := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_literalColumnMetric_inner hL W hW (basis i) (basis j)

end Riemann.Analysis.FiniteWindow
