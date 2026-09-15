import Riemann.Basic.PositiveGalerkin
import Mathlib.Analysis.InnerProductSpace.Trace

/-! Positive physical compression and the hyperplane inverse formula. -/
noncomputable section
open scoped InnerProductSpace
namespace Riemann.Basic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Orthogonal compression, without an invariance premise. -/
def physicalCompression (V : Submodule ℂ E) (H : E →L[ℂ] E) : V →L[ℂ] V :=
  V.orthogonalProjectionOnto.comp (H.comp V.subtypeL)

@[simp] theorem physicalCompression_inner (V : Submodule ℂ E) (H : E →L[ℂ] E)
    (x y : V) : ⟪x, physicalCompression V H y⟫_ℂ = ⟪(x : E), H y⟫_ℂ :=
  V.inner_orthogonalProjectionOnto_eq_of_mem_left x (H y)

theorem physicalCompression_positive (V : Submodule ℂ E) (H : E →L[ℂ] E)
    (hH : ∀ x, x ≠ 0 → 0 < (⟪x, H x⟫_ℂ).re) (x : V) (hx : x ≠ 0) :
    0 < (⟪x, physicalCompression V H x⟫_ℂ).re := by
  rw [physicalCompression_inner]
  exact hH x (fun h => hx (Subtype.ext h))

theorem physicalCompression_symmetric (V : Submodule ℂ E) (H : E →L[ℂ] E)
    (hH : H.toLinearMap.IsSymmetric) : (physicalCompression V H).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪physicalCompression V H x, y⟫_ℂ = ⟪x, physicalCompression V H y⟫_ℂ
  rw [physicalCompression_inner]
  change ⟪V.orthogonalProjectionOnto (H x), y⟫_ℂ = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  exact hH x y

/-- Constructed inverse of a strictly positive finite operator. -/
def positiveInverse (H : E →L[ℂ] E)
    (hH : ∀ x, x ≠ 0 → 0 < (⟪x, H x⟫_ℂ).re) : E →L[ℂ] E :=
  (strictlyPositiveEquiv H hH).symm.toContinuousLinearMap

@[simp] theorem positiveInverse_left (H : E →L[ℂ] E)
    (hH : ∀ x, x ≠ 0 → 0 < (⟪x, H x⟫_ℂ).re) (x : E) : H (positiveInverse H hH x) = x :=
  (strictlyPositiveEquiv H hH).apply_symm_apply x

@[simp] theorem positiveInverse_right (H : E →L[ℂ] E)
    (hH : ∀ x, x ≠ 0 → 0 < (⟪x, H x⟫_ℂ).re) (x : E) : positiveInverse H hH (H x) = x :=
  (strictlyPositiveEquiv H hH).symm_apply_apply x

theorem positiveInverse_symmetric (H : E →L[ℂ] E)
    (hH : ∀ x, x ≠ 0 → 0 < (⟪x, H x⟫_ℂ).re) (hs : H.toLinearMap.IsSymmetric) :
    (positiveInverse H hH).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪positiveInverse H hH x, y⟫_ℂ = ⟪x, positiveInverse H hH y⟫_ℂ
  have h := hs (positiveInverse H hH x) (positiveInverse H hH y)
  change ⟪H (positiveInverse H hH x), positiveInverse H hH y⟫_ℂ =
    ⟪positiveInverse H hH x, H (positiveInverse H hH y)⟫_ℂ at h
  simpa only [positiveInverse_left] using h.symm

theorem positiveInverse_positive (H : E →L[ℂ] E)
    (hH : ∀ x, x ≠ 0 → 0 < (⟪x, H x⟫_ℂ).re) (hs : H.toLinearMap.IsSymmetric)
    (x : E) (hx : x ≠ 0) : 0 < (⟪x, positiveInverse H hH x⟫_ℂ).re := by
  have hu : positiveInverse H hH x ≠ 0 := by
    intro h
    have hh := positiveInverse_left H hH x
    rw [h, map_zero] at hh
    exact hx hh.symm
  have hp := hH _ hu
  rw [positiveInverse_left] at hp
  have he := hs (positiveInverse H hH x) (positiveInverse H hH x)
  change ⟪H (positiveInverse H hH x), positiveInverse H hH x⟫_ℂ =
    ⟪positiveInverse H hH x, H (positiveInverse H hH x)⟫_ℂ at he
  rw [positiveInverse_left] at he
  rw [he]
  exact hp

def vectorHyperplane (eta : E) : Submodule ℂ E := (innerSL ℂ eta).ker

@[simp] theorem vectorHyperplane_projection_eta (eta : E) :
    (vectorHyperplane eta).orthogonalProjectionOnto eta = 0 := by
  apply Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
  intro x hx
  exact inner_eq_zero_symm.mpr hx

/-- Solve the compression by subtracting the inverse-normal component. -/
theorem hyperplane_inverse_apply (H : E →L[ℂ] E)
    (hH : ∀ x, x ≠ 0 → 0 < (⟪x, H x⟫_ℂ).re) (hs : H.toLinearMap.IsSymmetric)
    (eta : E) (heta : eta ≠ 0) (x : E) :
    ((positiveInverse (physicalCompression (vectorHyperplane eta) H)
      (physicalCompression_positive _ H hH)
      ((vectorHyperplane eta).orthogonalProjectionOnto x) : vectorHyperplane eta) : E) =
    positiveInverse H hH x -
      (⟪eta, positiveInverse H hH x⟫_ℂ / ⟪eta, positiveInverse H hH eta⟫_ℂ) •
        positiveInverse H hH eta := by
  let V := vectorHyperplane eta
  let u := positiveInverse H hH eta
  have hq : ⟪eta, u⟫_ℂ ≠ 0 := by
    intro h
    have hp := positiveInverse_positive H hH hs eta heta
    change 0 < (⟪eta, u⟫_ℂ).re at hp
    rw [h] at hp
    exact (lt_irrefl 0) hp
  let y : V := ⟨positiveInverse H hH x - (⟪eta, positiveInverse H hH x⟫_ℂ / ⟪eta, u⟫_ℂ) • u, by
    change ⟪eta, _⟫_ℂ = 0
    rw [inner_sub_right, inner_smul_right, div_mul_cancel₀ _ hq, sub_self]⟩
  have hy : physicalCompression V H y = V.orthogonalProjectionOnto x := by
    change V.orthogonalProjectionOnto (H (positiveInverse H hH x - _ • u)) = _
    simp only [map_sub, map_smul, positiveInverse_left, u]
    rw [vectorHyperplane_projection_eta, smul_zero, sub_zero]
  have hz := congrArg (positiveInverse (physicalCompression V H)
    (physicalCompression_positive V H hH)) hy
  rw [positiveInverse_right] at hz
  exact (congrArg Subtype.val hz).symm

/-- The inverse defect is a positive rank-one operator. -/
theorem hyperplane_inverse_defect (H : E →L[ℂ] E)
    (hH : ∀ x, x ≠ 0 → 0 < (⟪x, H x⟫_ℂ).re) (hs : H.toLinearMap.IsSymmetric)
    (eta : E) (heta : eta ≠ 0) :
    positiveInverse H hH - (vectorHyperplane eta).subtypeL.comp
      ((positiveInverse (physicalCompression (vectorHyperplane eta) H)
        (physicalCompression_positive _ H hH)).comp
          (vectorHyperplane eta).orthogonalProjectionOnto) =
    (⟪eta, positiveInverse H hH eta⟫_ℂ)⁻¹ •
      InnerProductSpace.rankOne ℂ (positiveInverse H hH eta) (positiveInverse H hH eta) := by
  ext x
  change positiveInverse H hH x -
    (((positiveInverse (physicalCompression (vectorHyperplane eta) H)
      (physicalCompression_positive _ H hH))
      ((vectorHyperplane eta).orthogonalProjectionOnto x) : vectorHyperplane eta) : E) = _
  rw [hyperplane_inverse_apply H hH hs eta heta x]
  simp only [sub_sub_cancel, smul_apply, InnerProductSpace.rankOne_apply,
    smul_smul]
  have hi := positiveInverse_symmetric H hH hs eta x
  change ⟪positiveInverse H hH eta, x⟫_ℂ = ⟪eta, positiveInverse H hH x⟫_ℂ at hi
  rw [hi, div_eq_mul_inv, mul_comm]

/-- Inverse normal energy is real. -/
theorem positiveInverse_energy_real (H : E →L[ℂ] E)
    (hH : ∀ x, x ≠ 0 → 0 < (⟪x, H x⟫_ℂ).re) (hs : H.toLinearMap.IsSymmetric)
    (eta : E) : ((⟪eta, positiveInverse H hH eta⟫_ℂ).re : ℂ) =
      ⟪eta, positiveInverse H hH eta⟫_ℂ := by
  apply Complex.conj_eq_iff_re.mp
  rw [inner_conj_symm]
  exact positiveInverse_symmetric H hH hs eta eta

end Riemann.Basic
