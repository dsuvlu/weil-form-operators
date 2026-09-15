import Riemann.CCM.GroundComplement

/-! Physical endpoint hyperplane and its strictly positive shifted compression.
This is V=ker δ, distinct from the physical ground complement (ker G)⊥.
-/

noncomputable section
open scoped InnerProductSpace

namespace Riemann.CCM.FullSimpleEvenData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (M : FullSimpleEvenData E)

/-- The physical endpoint-zero hyperplane. -/
def boundaryHyperplane : Submodule ℂ E := (innerSL ℂ M.eta).ker

@[simp] theorem mem_boundaryHyperplane (x : E) :
    x ∈ M.boundaryHyperplane ↔ ⟪M.eta, x⟫_ℂ = 0 := Iff.rfl

theorem boundaryHyperplane_eq_orthogonal :
    M.boundaryHyperplane = (Submodule.span ℂ {M.eta})ᗮ := by
  ext x
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.symm

instance boundaryHyperplane_finite : FiniteDimensional ℂ M.boundaryHyperplane := by
  letI := M.finite_dimensional
  infer_instance

instance boundaryHyperplane_complete : CompleteSpace M.boundaryHyperplane :=
  FiniteDimensional.complete ℂ _

/-- Physical orthogonal projection to the endpoint-zero hyperplane. -/
def boundaryProjection : E →L[ℂ] M.boundaryHyperplane :=
  M.boundaryHyperplane.orthogonalProjectionOnto

@[simp] theorem boundaryProjection_coe (x : M.boundaryHyperplane) :
    M.boundaryProjection x = x := by
  exact M.boundaryHyperplane.orthogonalProjectionOnto_mem_subspace_eq_self x

@[simp] theorem boundaryProjection_eta : M.boundaryProjection M.eta = 0 := by
  apply M.boundaryHyperplane.orthogonalProjectionOnto_apply_of_mem_orthogonal
  intro x hx
  exact inner_eq_zero_symm.mpr hx

/-- Squared physical norm of the endpoint adjoint. -/
def boundaryMass : ℝ := ‖M.eta‖ ^ 2

theorem eta_ne_zero : M.eta ≠ 0 := by
  intro h
  exact M.ground_bright (by simp [h])

theorem boundaryMass_pos : 0 < M.boundaryMass :=
  sq_pos_of_pos (norm_pos_iff.mpr M.eta_ne_zero)

/-- The minimum physical-norm vector with endpoint one. -/
def boundarySection : E := (M.boundaryMass : ℂ)⁻¹ • M.eta

@[simp] theorem boundary_boundarySection : ⟪M.eta, M.boundarySection⟫_ℂ = 1 := by
  have hn : ⟪M.eta, M.eta⟫_ℂ = (M.boundaryMass : ℂ) := by
    simp [boundaryMass, inner_self_eq_norm_sq_to_K]
  rw [boundarySection, inner_smul_right, hn]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt M.boundaryMass_pos))

@[simp] theorem boundaryProjection_boundarySection : M.boundaryProjection M.boundarySection = 0 := by
  simp [boundarySection]

/-- Physical compression of the shifted full operator to V; invariance is not assumed. -/
def boundaryCompression : M.boundaryHyperplane →L[ℂ] M.boundaryHyperplane :=
  M.boundaryProjection.comp (M.shifted.comp M.boundaryHyperplane.subtypeL)

@[simp] theorem boundaryCompression_apply (x : M.boundaryHyperplane) :
    M.boundaryCompression x = M.boundaryProjection (M.shifted x) := rfl

@[simp] theorem boundaryCompression_inner (x y : M.boundaryHyperplane) :
    ⟪x, M.boundaryCompression y⟫_ℂ = ⟪(x : E), M.shifted y⟫_ℂ := by
  exact M.boundaryHyperplane.inner_orthogonalProjectionOnto_eq_of_mem_left x (M.shifted y)

theorem boundaryCompression_symmetric : M.boundaryCompression.toLinearMap.IsSymmetric := by
  intro x y
  change ⟪M.boundaryCompression x, y⟫_ℂ = ⟪x, M.boundaryCompression y⟫_ℂ
  rw [M.boundaryCompression_inner]
  change ⟪M.boundaryHyperplane.orthogonalProjectionOnto (M.shifted x), y⟫_ℂ = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  simpa only [M.shifted_selfadjoint] using
    (ContinuousLinearMap.adjoint_inner_left M.shifted (y : E) (x : E))

theorem boundaryCompression_adjoint : M.boundaryCompression.adjoint = M.boundaryCompression :=
  M.boundaryCompression_symmetric.clm_adjoint_eq

/-- No nonzero endpoint-zero vector lies on the bright shifted radical. -/
theorem boundaryHyperplane_shifted_kernel {x : E} (hx : x ∈ M.boundaryHyperplane)
    (hg : M.shifted x = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := (M.shifted_eq_zero_iff x).mp hg
  have he : a * ⟪M.eta, M.ground⟫_ℂ = 0 := by simpa only [mem_boundaryHyperplane, inner_smul_right] using hx
  have ha := (mul_eq_zero.mp he).resolve_right M.ground_bright
  simp [ha]

/-- Strict positivity follows from full leastness, simplicity, and proved brightness. -/
theorem boundaryCompression_energy_pos {x : M.boundaryHyperplane} (hx : x ≠ 0) :
    0 < (⟪x, M.boundaryCompression x⟫_ℂ).re := by
  rw [M.boundaryCompression_inner]
  apply Riemann.positive_energy_pos M.shifted M.shifted_positive
  intro hg
  exact hx (Subtype.ext (M.boundaryHyperplane_shifted_kernel x.property hg))

theorem boundaryCompression_injective : Function.Injective M.boundaryCompression := by
  intro x y hxy
  have hz : M.boundaryCompression (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  by_contra hne
  have hp := M.boundaryCompression_energy_pos (sub_ne_zero.mpr hne)
  rw [hz, inner_zero_right] at hp
  exact (lt_irrefl 0) hp

/-- The compression equipped with its constructed inverse, including the zero-dimensional case. -/
def boundaryCompressionEquiv : M.boundaryHyperplane ≃L[ℂ] M.boundaryHyperplane :=
  (LinearEquiv.ofBijective M.boundaryCompression.toLinearMap
    ⟨M.boundaryCompression_injective,
      LinearMap.injective_iff_surjective.mp M.boundaryCompression_injective⟩).toContinuousLinearEquiv

@[simp] theorem boundaryCompressionEquiv_apply (x : M.boundaryHyperplane) :
    M.boundaryCompressionEquiv x = M.boundaryCompression x := rfl

/-- The actual inverse of the positive physical compression. -/
def boundaryInverse : M.boundaryHyperplane →L[ℂ] M.boundaryHyperplane :=
  M.boundaryCompressionEquiv.symm.toContinuousLinearMap

@[simp] theorem boundaryCompression_inverse (x : M.boundaryHyperplane) :
    M.boundaryCompression (M.boundaryInverse x) = x :=
  M.boundaryCompressionEquiv.apply_symm_apply x

@[simp] theorem boundaryInverse_compression (x : M.boundaryHyperplane) :
    M.boundaryInverse (M.boundaryCompression x) = x :=
  M.boundaryCompressionEquiv.symm_apply_apply x

/-- The physical decomposition into endpoint section and endpoint-zero component. -/
theorem boundaryProjection_decomposition (x : E) :
    (M.boundaryProjection x : E) = x - ⟪M.eta, x⟫_ℂ • M.boundarySection := by
  let y : M.boundaryHyperplane := ⟨x - ⟪M.eta, x⟫_ℂ • M.boundarySection, by
    simp only [mem_boundaryHyperplane, inner_sub_right, inner_smul_right,
      M.boundary_boundarySection, mul_one, sub_self]⟩
  have h := M.boundaryProjection_coe y
  change M.boundaryProjection (x - ⟪M.eta, x⟫_ℂ • M.boundarySection) = y at h
  simp only [map_sub, map_smul, M.boundaryProjection_boundarySection, smul_zero, sub_zero] at h
  exact congrArg Subtype.val h

@[simp] theorem boundarySection_inner (x : M.boundaryHyperplane) :
    ⟪M.boundarySection, (x : E)⟫_ℂ = 0 := by
  simp only [boundarySection, inner_smul_left]
  rw [show ⟪M.eta, (x : E)⟫_ℂ = 0 from x.property, mul_zero]

/-- The inverse is self-adjoint in the same physical hyperplane metric. -/
theorem boundaryInverse_symmetric : M.boundaryInverse.toLinearMap.IsSymmetric := by
  intro x y
  have h := M.boundaryCompression_symmetric (M.boundaryInverse x) (M.boundaryInverse y)
  change ⟪M.boundaryCompression (M.boundaryInverse x), M.boundaryInverse y⟫_ℂ =
    ⟪M.boundaryInverse x, M.boundaryCompression (M.boundaryInverse y)⟫_ℂ at h
  rw [M.boundaryCompression_inverse, M.boundaryCompression_inverse] at h
  exact h.symm

theorem boundaryInverse_adjoint : M.boundaryInverse.adjoint = M.boundaryInverse :=
  M.boundaryInverse_symmetric.clm_adjoint_eq

end Riemann.CCM.FullSimpleEvenData
