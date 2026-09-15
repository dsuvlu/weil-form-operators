import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Rank-one determinant and normalized boundary resolvent

Rows here are linear functionals: no conjugation is implicit in the row `δ`.
For an endpoint adjoint vector η the corresponding row is `star η`.
-/

noncomputable section
namespace Riemann.Basic
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rank-one matrix with column `u` and linear row `δ`. -/
def columnRow (u δ : ι → ℂ) : Matrix ι ι ℂ := fun i j => u i * δ j

omit [Fintype ι] [DecidableEq ι] in
lemma columnRow_eq (u δ : ι → ℂ) :
    columnRow u δ = replicateCol Unit u * replicateRow Unit δ := by
  ext i j
  simp [columnRow, Matrix.mul_apply]

/-- The classical rank-one determinant lemma, in linear-row convention. -/
theorem determinant_add_columnRow (A : Matrix ι ι ℂ) (hA : A.det ≠ 0)
    (u δ : ι → ℂ) :
    (A + columnRow u δ).det = A.det * (1 + δ ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  rw [columnRow_eq, Matrix.det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hA)]
  congr 1
  rw [Matrix.det_unique]
  simp [Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Subtracting a column-row perturbation has the expected minus sign. -/
theorem determinant_sub_columnRow (A : Matrix ι ι ℂ) (hA : A.det ≠ 0)
    (u δ : ι → ℂ) :
    (A - columnRow u δ).det = A.det * (1 - δ ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  have hneg : columnRow (-u) δ = -columnRow u δ := by
    ext i j
    simp [columnRow]
  simpa [hneg, sub_eq_add_neg, Matrix.mulVec_neg, dotProduct_neg] using determinant_add_columnRow A hA (-u) δ

/-- The corrected derivative matrix, with a normalized linear endpoint row. -/
def correctedMatrix (D : Matrix ι ι ℂ) (v δ : ι → ℂ) : Matrix ι ι ℂ :=
  D - columnRow (D *ᵥ v) δ

/-- The finite boundary determinant identity. The inverse and ratio are used
only away from the free spectrum. -/
theorem correctedMatrix_determinant_ratio (D : Matrix ι ι ℂ) (v δ : ι → ℂ)
    (hv : δ ⬝ᵥ v = 1) (z : ℂ) (hz : (D - z • 1).det ≠ 0) :
    (correctedMatrix D v δ - z • 1).det / (D - z • 1).det =
      -z * (δ ⬝ᵥ ((D - z • 1)⁻¹ *ᵥ v)) := by
  let A := D - z • (1 : Matrix ι ι ℂ)
  have hA : A.det ≠ 0 := hz
  have hsplit : correctedMatrix D v δ - z • 1 = A - columnRow (D *ᵥ v) δ := by
    dsimp [correctedMatrix, A]
    abel
  have hD : D *ᵥ v = A *ᵥ v + z • v := by
    simp [A, Matrix.sub_mulVec, Matrix.smul_mulVec]
  have hinv : A⁻¹ *ᵥ (D *ᵥ v) = v + z • (A⁻¹ *ᵥ v) := by
    rw [hD, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
  rw [hsplit, determinant_sub_columnRow A hA]
  change A.det * (1 - δ ⬝ᵥ (A⁻¹ *ᵥ (D *ᵥ v))) / A.det = _
  rw [mul_div_cancel_left₀ _ hA, hinv, dotProduct_add, dotProduct_smul, hv]
  ring

end Riemann.Basic
