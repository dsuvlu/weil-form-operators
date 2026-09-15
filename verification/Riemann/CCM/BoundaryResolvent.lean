import Riemann.CCM.BoundaryHyperplane
import Riemann.Basic.PositiveGalerkin

/-! Endpoint-normalized Schur reconstruction at the actual full ground energy.
For b=η/m the energy identity is e₀=m(⟪b,Hb⟫−⟪c,Q⁻¹c⟫),
not its incorrectly rescaled alternative. All inverse operators act on ker δ.
-/

noncomputable section
open scoped InnerProductSpace

namespace Riemann.CCM.FullSimpleEvenData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (M : FullSimpleEvenData E)

/-- Physical coupling of the endpoint-one section to the endpoint-zero hyperplane. -/
def boundaryCoupling : M.boundaryHyperplane := M.boundaryProjection (M.H M.boundarySection)

theorem boundaryCoupling_eq_shifted :
    M.boundaryCoupling = M.boundaryProjection (M.shifted M.boundarySection) := by
  simp [boundaryCoupling, shifted_apply, map_sub]

/-- The inverse-weighted endpoint forcing in the physical hyperplane. -/
def boundaryResponse : M.boundaryHyperplane := M.boundaryInverse M.boundaryCoupling

@[simp] theorem boundaryCompression_response :
    M.boundaryCompression M.boundaryResponse = M.boundaryCoupling :=
  M.boundaryCompression_inverse _

theorem boundaryProjection_ground :
    M.boundaryProjection M.groundVector = -M.boundaryResponse := by
  apply M.boundaryCompression_injective
  rw [map_neg, M.boundaryCompression_response]
  change M.boundaryProjection (M.shifted (M.boundaryProjection M.groundVector : E)) = _
  rw [M.boundaryProjection_decomposition, M.boundary_groundVector, one_smul,
    map_sub, M.shifted_groundVector, zero_sub, map_neg, ← M.boundaryCoupling_eq_shifted]

/-- Exact original-ground reconstruction from the positive endpoint compression. -/
theorem groundVector_boundary_resolvent :
    M.groundVector = M.boundarySection - (M.boundaryResponse : E) := by
  have h := congrArg Subtype.val M.boundaryProjection_ground
  rw [M.boundaryProjection_decomposition, M.boundary_groundVector, one_smul] at h
  change M.groundVector - M.boundarySection = -(M.boundaryResponse : E) at h
  exact sub_eq_iff_eq_add.mp h |>.trans (by abel)

@[simp] theorem boundarySection_inner_ground :
    ⟪M.boundarySection, M.groundVector⟫_ℂ = (M.boundaryMass : ℂ)⁻¹ := by
  simp [boundarySection, inner_smul_left]

@[simp] theorem boundarySection_inner_self :
    ⟪M.boundarySection, M.boundarySection⟫_ℂ = (M.boundaryMass : ℂ)⁻¹ := by
  nth_rw 1 [boundarySection]
  simp only [inner_smul_left, M.boundary_boundarySection, mul_one]
  simp

/-- The endpoint-one section has squared physical norm 1/m. -/
theorem boundarySection_norm_sq : ‖M.boundarySection‖ ^ 2 = M.boundaryMass⁻¹ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), M.boundarySection_inner_self]
  simp

/-- The coupling pairing is the physical off-diagonal entry of H. -/
theorem boundaryCoupling_inner (x : M.boundaryHyperplane) :
    ⟪M.boundaryCoupling, x⟫_ℂ = ⟪M.boundarySection, M.H x⟫_ℂ := by
  change ⟪M.boundaryHyperplane.orthogonalProjectionOnto (M.H M.boundarySection), x⟫_ℂ = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  simpa only [M.H_selfadjoint] using
    (ContinuousLinearMap.adjoint_inner_left M.H (x : E) M.boundarySection)

/-- The physical-mass normalized scalar Schur equation, with its exact complex normalization. -/
theorem boundary_schur_complex :
    (M.e₀ : ℂ) = (M.boundaryMass : ℂ) *
      (⟪M.boundarySection, M.H M.boundarySection⟫_ℂ -
        ⟪M.boundaryCoupling, M.boundaryResponse⟫_ℂ) := by
  have hg : M.H M.groundVector = (M.e₀ : ℂ) • M.groundVector := by
    have h := M.shifted_groundVector
    rw [shifted_apply, sub_eq_zero] at h
    exact h
  have he := congrArg (fun x : E => ⟪M.boundarySection, x⟫_ℂ) hg
  rw [inner_smul_right, M.boundarySection_inner_ground] at he
  rw [M.groundVector_boundary_resolvent] at he
  rw [map_sub, inner_sub_right, ← M.boundaryCoupling_inner] at he
  rw [he]
  field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt M.boundaryMass_pos)]

/-- Taking real parts preserves the physical mass factor in the scalar energy equation. -/
theorem boundary_schur_energy :
    M.e₀ = M.boundaryMass *
      ((⟪M.boundarySection, M.H M.boundarySection⟫_ℂ).re -
        (⟪M.boundaryCoupling, M.boundaryResponse⟫_ℂ).re) := by
  have h := congrArg Complex.re M.boundary_schur_complex
  simpa using h

/-- Orthogonality separates boundary mass and inverse-response mass exactly. -/
theorem groundVector_boundary_norm_sq :
    ‖M.groundVector‖ ^ 2 = M.boundaryMass⁻¹ + ‖M.boundaryResponse‖ ^ 2 := by
  rw [M.groundVector_boundary_resolvent, sub_eq_add_neg]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
    M.boundarySection (-(M.boundaryResponse : E)) (by
      simp only [inner_neg_right, M.boundarySection_inner, neg_zero])
  simpa only [← pow_two, norm_neg, M.boundarySection_norm_sq, Submodule.coe_norm] using h

/-- The reciprocal brightness is boundary mass plus inverse-response mass. -/
theorem groundWeight_boundary_inverse :
    M.groundWeight⁻¹ = M.boundaryMass⁻¹ + ‖M.boundaryResponse‖ ^ 2 := by
  rw [← M.groundVector_norm_sq, M.groundVector_boundary_norm_sq]

/-- Exact brightness in the physical-mass boundary chart. -/
theorem groundWeight_boundary :
    M.groundWeight = M.boundaryMass / (1 + M.boundaryMass * ‖M.boundaryResponse‖ ^ 2) := by
  have h := M.groundWeight_boundary_inverse
  have hm := M.boundaryMass_pos
  have hq := M.groundWeight_pos
  have hd : 1 + M.boundaryMass * ‖M.boundaryResponse‖ ^ 2 ≠ 0 :=
    ne_of_gt (by positivity)
  apply (eq_div_iff hd).mpr
  field_simp at h
  nlinarith

/-- Returning from the endpoint-one section to the original endpoint adjoint. -/
theorem mass_smul_boundarySection : (M.boundaryMass : ℂ) • M.boundarySection = M.eta := by
  simp [boundarySection, smul_smul,
    Complex.ofReal_ne_zero.mpr (ne_of_gt M.boundaryMass_pos)]

/-- The unnormalized forcing differs by the exact physical mass. -/
theorem boundary_forcing_scale :
    M.boundaryProjection (M.H M.eta) = (M.boundaryMass : ℂ) • M.boundaryCoupling := by
  nth_rw 1 [← M.mass_smul_boundarySection]
  simp [boundaryCoupling]

/-- Scalar Schur equation in the unnormalized endpoint-adjoint convention. -/
theorem boundary_schur_unnormalized :
    (M.boundaryMass : ℂ) * (M.e₀ : ℂ) = ⟪M.eta, M.H M.eta⟫_ℂ -
      ⟪M.boundaryProjection (M.H M.eta),
        M.boundaryInverse (M.boundaryProjection (M.H M.eta))⟫_ℂ := by
  have h₁ : ⟪M.eta, M.H M.eta⟫_ℂ = (M.boundaryMass : ℂ) ^ 2 *
      ⟪M.boundarySection, M.H M.boundarySection⟫_ℂ := by
    nth_rw 1 [← M.mass_smul_boundarySection]
    nth_rw 1 [← M.mass_smul_boundarySection]
    simp only [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    ring
  rw [h₁, M.boundary_forcing_scale, map_smul, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal]
  rw [M.boundary_schur_complex]
  change _ = _ - (M.boundaryMass : ℂ) * ((M.boundaryMass : ℂ) *
    ⟪M.boundaryCoupling, M.boundaryResponse⟫_ℂ)
  ring

/-- Any endpoint-matched vector decomposes into its actual ground part and occupied residual. -/
theorem boundary_residual_reconstruction (f : E) :
    f - (M.boundaryInverse (M.boundaryProjection (M.shifted f)) : E) =
      ⟪M.eta, f⟫_ℂ • M.groundVector := by
  let y : M.boundaryHyperplane := ⟨f - ⟪M.eta, f⟫_ℂ • M.groundVector, by
    simp only [mem_boundaryHyperplane, inner_sub_right, inner_smul_right,
      M.boundary_groundVector, mul_one, sub_self]⟩
  have hq : M.boundaryCompression y = M.boundaryProjection (M.shifted f) := by
    change M.boundaryProjection (M.shifted (f - ⟪M.eta, f⟫_ℂ • M.groundVector)) = _
    simp only [map_sub, map_smul, M.shifted_groundVector, smul_zero, sub_zero]
  have hy : M.boundaryInverse (M.boundaryProjection (M.shifted f)) = y := by
    rw [← hq, M.boundaryInverse_compression]
  rw [hy]
  change f - (f - ⟪M.eta, f⟫_ℂ • M.groundVector) = _
  abel

/-- The boundary inverse is exactly the generic positive-Galerkin inverse. -/
theorem boundaryInverse_eq_positive_inverse (x : M.boundaryHyperplane) :
    M.boundaryInverse x =
      (Riemann.Basic.strictlyPositiveEquiv M.boundaryCompression
        (fun _ hy => M.boundaryCompression_energy_pos hy)).symm x := by
  apply M.boundaryCompression_injective
  rw [M.boundaryCompression_inverse]
  exact ((Riemann.Basic.strictlyPositiveEquiv M.boundaryCompression
    (fun _ hy => M.boundaryCompression_energy_pos hy)).apply_symm_apply x).symm

end Riemann.CCM.FullSimpleEvenData
