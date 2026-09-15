import Riemann.CCM.FourierSection
import Riemann.Basic.Determinant

/-! Finite Fourier resolvent and rank-one boundary determinant. -/
noncomputable section
open scoped InnerProductSpace BigOperators
open Matrix
namespace Riemann.CCM.Native
variable {N : ℕ}

def freeMatrix (N : ℕ) (L : ℝ) : Matrix (Index N) (Index N) ℂ :=
  Matrix.diagonal fun i => (frequency L i : ℂ)

def endpointRow (N : ℕ) (L : ℝ) : Index N → ℂ := fun _ => ((Real.sqrt L)⁻¹ : ℂ)

def boundaryMatrix (L : ℝ) (v : Section N) : Matrix (Index N) (Index N) ℂ :=
  Basic.correctedMatrix (freeMatrix N L) (fun i => v i) (endpointRow N L)

lemma freeMatrix_sub (L : ℝ) (z : ℂ) :
    freeMatrix N L - z • 1 = Matrix.diagonal (fun i => (frequency L i : ℂ) - z) := by
  ext i j
  by_cases h : i = j <;> simp [freeMatrix, h]

lemma freeMatrix_det_ne_zero_iff (L : ℝ) (z : ℂ) :
    (freeMatrix N L - z • 1).det ≠ 0 ↔ ∀ i : Index N, z ≠ (frequency L i : ℂ) := by
  rw [freeMatrix_sub, Matrix.det_diagonal]
  rw [Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, forall_true_left, sub_ne_zero]
  exact forall_congr' (fun i => ne_comm)

lemma freeMatrix_det_ne_zero_of_nonreal (L : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (freeMatrix N L - z • 1).det ≠ 0 := by
  apply (freeMatrix_det_ne_zero_iff L z).mpr
  intro i hi
  exact hz (by simp [hi])

lemma endpointRow_dot (L : ℝ) (v : Section N) :
    endpointRow N L ⬝ᵥ (fun i => v i) = ⟪endpointVector N L, v⟫_ℂ := by
  simp [endpointRow, dotProduct, endpoint_pairing, Finset.mul_sum]

lemma freeMatrix_resolvent (L : ℝ) (v : Section N) (z : ℂ)
    (hz : ∀ i : Index N, z ≠ (frequency L i : ℂ)) :
    endpointRow N L ⬝ᵥ ((freeMatrix N L - z • 1)⁻¹ *ᵥ (fun i => v i)) =
      ((Real.sqrt L)⁻¹ : ℂ) * ∑ i, v i / ((frequency L i : ℂ) - z) := by
  have hinv : (freeMatrix N L - z • 1)⁻¹ =
      Matrix.diagonal (fun i => ((frequency L i : ℂ) - z)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [freeMatrix_sub, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [sub_ne_zero.mpr (hz i).symm]
    · simp [hij]
  rw [hinv]
  simp [endpointRow, dotProduct, Matrix.mulVec_diagonal, div_eq_mul_inv,
    Finset.mul_sum, mul_comm]

/-- The native coefficient form of the finite CCM determinant identity. -/
theorem boundaryMatrix_determinant_ratio (L : ℝ) (v : Section N)
    (hv : ⟪endpointVector N L, v⟫_ℂ = 1) (z : ℂ)
    (hz : ∀ i : Index N, z ≠ (frequency L i : ℂ)) :
    (boundaryMatrix L v - z • 1).det / (freeMatrix N L - z • 1).det =
      -z * (((Real.sqrt L)⁻¹ : ℂ) * ∑ i, v i / ((frequency L i : ℂ) - z)) := by
  rw [boundaryMatrix, Basic.correctedMatrix_determinant_ratio _ _ _
    (by rwa [endpointRow_dot]) z ((freeMatrix_det_ne_zero_iff L z).mpr hz),
    freeMatrix_resolvent L v z hz]

end Riemann.CCM.Native
