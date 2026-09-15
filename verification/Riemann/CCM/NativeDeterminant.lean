import Riemann.CCM.NativeData
import Riemann.CCM.FourierResolvent
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The native finite corrected matrix represents the already constructed CCM
operator. Nonreal determinant nonvanishing follows from its proved real spectrum. -/

noncomputable section
open scoped InnerProductSpace BigOperators
open Matrix InnerProductSpace

namespace Riemann.CCM.Native
variable {N : ℕ}

/-- Matrix/physical-operator dictionary for an arbitrary selected vector. -/
theorem boundaryMatrix_operator (L : ℝ) (v : Section N) :
    ofMatrix (boundaryMatrix L v) =
      derivative L - rankOne ℂ (derivative L v) (endpointVector N L) := by
  ext x i
  simp only [ofMatrix_apply, boundaryMatrix, Basic.correctedMatrix,
    Matrix.sub_apply, Basic.columnRow, freeMatrix, Matrix.mulVec_diagonal,
    endpointRow, _root_.sub_apply, rankOne_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, derivative_apply, sub_mul, Finset.sum_sub_distrib, endpoint_pairing]
  simp only [Matrix.diagonal_apply]
  simp [Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]

/-- The matrix in the determinant is exactly the full original CCM correction. -/
theorem native_boundaryMatrix_operator (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) :
    ofMatrix (boundaryMatrix L (fullData C L hL A).groundVector) =
      (fullData C L hL A).corrected := by
  exact boundaryMatrix_operator L _

/-- Exact finite determinant/endpoint-resolvent ratio, away from the free lattice. -/
theorem native_determinant_ratio (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (z : ℂ) (hz : ∀ i : Index N, z ≠ (frequency L i : ℂ)) :
    (boundaryMatrix L (fullData C L hL A).groundVector - z • 1).det /
      (freeMatrix N L - z • 1).det =
      -z * (((Real.sqrt L)⁻¹ : ℂ) *
        ∑ i, (fullData C L hL A).groundVector i / ((frequency L i : ℂ) - z)) :=
  boundaryMatrix_determinant_ratio L _ (fullData C L hL A).boundary_groundVector z hz

/-- The native corrected determinant cannot vanish at a nonreal parameter. -/
theorem native_boundary_det_ne_zero (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) {z : ℂ} (hz : z.im ≠ 0) :
    (boundaryMatrix L (fullData C L hL A).groundVector - z • 1).det ≠ 0 := by
  intro hdet
  obtain ⟨u, hu, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let x : Section N := WithLp.toLp 2 u
  have hx : x ≠ 0 := by
    intro hx
    apply hu
    funext i
    exact congrArg (fun v : Section N => v i) hx
  have haction : (fullData C L hL A).corrected x = z • x := by
    rw [← native_boundaryMatrix_operator C L hL A]
    ext i
    have hi := congrArg (fun v : Index N → ℂ => v i) hker
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    exact sub_eq_zero.mp hi
  exact hz (native_corrected_eigenvalue_real C L hL A hx haction)

end Riemann.CCM.Native
