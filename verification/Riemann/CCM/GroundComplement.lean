import Riemann.CCM.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-! The full CCM ground complement with its positive shifted metric.

The corrected operator is compressed by the physical orthogonal projection;
no invariance of that physical complement under the correction is assumed.
-/

noncomputable section

open scoped InnerProductSpace

namespace Riemann.CCM.FullSimpleEvenData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (M : FullSimpleEvenData E)

/-- The physical orthogonal complement of the shifted radical. -/
def groundComplementSubmodule : Submodule ℂ E := (LinearMap.ker M.shifted.toLinearMap)ᗮ

instance groundComplementSubmodule_complete : CompleteSpace ↥M.groundComplementSubmodule := by
  letI := M.finite_dimensional
  exact FiniteDimensional.complete ℂ _

/-- A distinct type carrying the shifted, rather than physical, metric. -/
def GroundComplement := ↥M.groundComplementSubmodule

instance : AddCommGroup M.GroundComplement :=
  inferInstanceAs (AddCommGroup ↥M.groundComplementSubmodule)
instance : Module ℂ M.GroundComplement :=
  inferInstanceAs (Module ℂ ↥M.groundComplementSubmodule)

/-- The underlying linear identification with the physical complement. -/
def groundComplementLinearEquiv : M.GroundComplement ≃ₗ[ℂ] M.groundComplementSubmodule :=
  LinearEquiv.refl ℂ _

/-- Inclusion in the original physical vector space, without a metric assertion. -/
def groundComplementIncl : M.GroundComplement →ₗ[ℂ] E :=
  M.groundComplementSubmodule.subtype.comp M.groundComplementLinearEquiv.toLinearMap

theorem groundComplementIncl_injective : Function.Injective M.groundComplementIncl :=
  Subtype.val_injective

/-- The positive-definite inner product obtained by restricting the shifted form. -/
@[implicit_reducible]
def groundComplementCore : InnerProductSpace.Core ℂ M.GroundComplement where
  inner x y := ⟪M.groundComplementIncl x, M.shifted (M.groundComplementIncl y)⟫_ℂ
  conj_inner_symm x y := by
    rw [inner_conj_symm]
    simpa only [M.shifted_selfadjoint] using
      (ContinuousLinearMap.adjoint_inner_left M.shifted
        (M.groundComplementIncl y) (M.groundComplementIncl x))
  re_inner_nonneg x := M.shifted_nonneg _
  add_left x y z := by simp only [map_add, inner_add_left]
  smul_left x y r := by simp only [map_smul, inner_smul_left]
  definite x hx := by
    apply M.groundComplementIncl_injective
    change M.groundComplementIncl x = 0
    by_contra hne
    have hp := M.shifted_positive_on_complement
      (M.groundComplementLinearEquiv x).property hne
    change 0 < (⟪M.groundComplementIncl x, M.shifted (M.groundComplementIncl x)⟫_ℂ).re at hp
    rw [hx] at hp
    exact (lt_irrefl 0) hp

noncomputable instance : NormedAddCommGroup M.GroundComplement :=
  @InnerProductSpace.Core.toNormedAddCommGroup _ _ _ _ _ M.groundComplementCore

noncomputable instance : InnerProductSpace ℂ M.GroundComplement :=
  InnerProductSpace.ofCore M.groundComplementCore.toCore

@[simp] theorem groundComplement_inner (x y : M.GroundComplement) :
    ⟪x, y⟫_ℂ = ⟪M.groundComplementIncl x, M.shifted (M.groundComplementIncl y)⟫_ℂ := rfl

instance : FiniteDimensional ℂ M.GroundComplement := by
  letI := M.finite_dimensional
  exact FiniteDimensional.of_injective M.groundComplementIncl M.groundComplementIncl_injective

instance : CompleteSpace M.GroundComplement := FiniteDimensional.complete ℂ _

/-- The shifted and physical metrics give equivalent finite-dimensional topologies. -/
noncomputable def groundComplementTopologyEquiv :
    M.GroundComplement ≃L[ℂ] M.groundComplementSubmodule :=
  M.groundComplementLinearEquiv.toContinuousLinearEquiv

/-- The physical orthogonal projection, with codomain given its shifted metric. -/
noncomputable def groundComplementProjection : E →L[ℂ] M.GroundComplement := by
  letI := M.finite_dimensional
  exact (M.groundComplementLinearEquiv.symm.toLinearMap.comp
    M.groundComplementSubmodule.orthogonalProjectionOnto.toLinearMap).toContinuousLinearMap

@[simp] theorem groundComplementProjection_incl (x : E) :
    M.groundComplementIncl (M.groundComplementProjection x) =
      M.groundComplementSubmodule.starProjection x := rfl

/-- Projection removes a vector in the radical, so does not change its shifted image. -/
theorem shifted_groundComplementProjection (x : E) :
    M.shifted (M.groundComplementIncl (M.groundComplementProjection x)) = M.shifted x := by
  letI := M.finite_dimensional
  have hk := M.groundComplementSubmodule.sub_starProjection_mem_orthogonal x
  change x - M.groundComplementSubmodule.starProjection x ∈
    (LinearMap.ker M.shifted.toLinearMap)ᗮᗮ at hk
  rw [Submodule.orthogonal_orthogonal] at hk
  have hz : M.shifted (x - M.groundComplementSubmodule.starProjection x) = 0 := hk
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-- Pairing with the shifted image also ignores the removed radical component. -/
theorem groundComplementProjection_inner (x y : E) :
    ⟪M.groundComplementIncl (M.groundComplementProjection x), M.shifted y⟫_ℂ =
      ⟪x, M.shifted y⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_left M.shifted y,
    M.shifted_selfadjoint, M.shifted_groundComplementProjection]
  simpa only [M.shifted_selfadjoint] using
    (ContinuousLinearMap.adjoint_inner_left M.shifted y x)

/-- The corrected operator compressed to the physical complement, using the shifted norm. -/
noncomputable def complementCorrected : M.GroundComplement →L[ℂ] M.GroundComplement :=
  (M.groundComplementProjection.toLinearMap.comp
    (M.corrected.toLinearMap.comp M.groundComplementIncl)).toContinuousLinearMap

@[simp] theorem complementCorrected_apply (x : M.GroundComplement) :
    M.complementCorrected x =
      M.groundComplementProjection (M.corrected (M.groundComplementIncl x)) := rfl

/-- Symmetry is in the positive shifted inner product, after physical compression. -/
theorem complementCorrected_symmetric : M.complementCorrected.toLinearMap.IsSymmetric := by
  intro x y
  change ⟪M.complementCorrected x, y⟫_ℂ = ⟪x, M.complementCorrected y⟫_ℂ
  simp only [groundComplement_inner, complementCorrected_apply,
    M.groundComplementProjection_inner, M.shifted_groundComplementProjection]
  exact M.weighted_symmetry _ _

/-- Actual adjoint equality in the complete positive-metric ground complement. -/
theorem complementCorrected_adjoint : M.complementCorrected.adjoint = M.complementCorrected :=
  M.complementCorrected_symmetric.clm_adjoint_eq

/-- Native selfadjointness of the compressed operator. -/
theorem complementCorrected_selfadjoint : IsSelfAdjoint M.complementCorrected :=
  M.complementCorrected_adjoint

/-- Every spectral value of the operator on the positive-metric space is real. -/
theorem complementCorrected_spectrum_real {z : ℂ}
    (hz : z ∈ spectrum ℂ M.complementCorrected) : z.im = 0 :=
  M.complementCorrected_selfadjoint.im_eq_zero_of_mem_spectrum hz

/-- The radical is exactly the canonical original ground line. -/
theorem shifted_kernel_eq_groundVector_span :
    LinearMap.ker M.shifted.toLinearMap = Submodule.span ℂ {M.groundVector} := by
  rw [← M.groundProjector_range_eq_kernel, M.groundProjector_range,
    M.groundVector_eq_normalizedGround]
  simp only [normalizedGround]
  exact (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero M.ground_bright)) M.ground).symm

/-- Thus the space used above is precisely the physical complement of ℂv. -/
theorem groundComplementSubmodule_eq :
    M.groundComplementSubmodule = (Submodule.span ℂ {M.groundVector})ᗮ := by
  unfold groundComplementSubmodule
  rw [M.shifted_kernel_eq_groundVector_span]

/-- The quotient by the shifted radical is linearly equivalent to the constructed metric space. -/
noncomputable def groundQuotientEquiv :
    (E ⧸ LinearMap.ker M.shifted.toLinearMap) ≃ₗ[ℂ] M.GroundComplement := by
  letI := M.finite_dimensional
  exact ((LinearMap.ker M.shifted.toLinearMap).quotientEquivOfIsCompl
    M.groundComplementSubmodule (LinearMap.ker M.shifted.toLinearMap).isCompl_orthogonal).trans
    M.groundComplementLinearEquiv.symm

/-- Adding a radical vector to a representative leaves the corrected image unchanged. -/
theorem corrected_representative_independent (x k : E)
    (hk : k ∈ LinearMap.ker M.shifted.toLinearMap) :
    M.corrected (x + k) = M.corrected x := by
  rw [map_add, M.corrected_kills_kernel k hk, add_zero]

/-- Consequently the projected corrected image is independent of the representative. -/
theorem complementCorrected_representative_independent (x k : E)
    (hk : k ∈ LinearMap.ker M.shifted.toLinearMap) :
    M.groundComplementProjection (M.corrected (x + k)) =
      M.groundComplementProjection (M.corrected x) := by
  rw [M.corrected_representative_independent x k hk]

/-- The shifted image of every physical vector lies in the physical ground complement. -/
theorem shifted_mem_groundComplement (x : E) :
    M.shifted x ∈ M.groundComplementSubmodule := by
  intro y hy
  rw [← ContinuousLinearMap.adjoint_inner_left M.shifted x y,
    M.shifted_selfadjoint]
  change M.shifted y = 0 at hy
  rw [hy, inner_zero_left]

/-- In particular, the shifted operator preserves the physical ground complement. -/
theorem shifted_groundComplement_invariant {x : E}
    (_hx : x ∈ M.groundComplementSubmodule) :
    M.shifted x ∈ M.groundComplementSubmodule :=
  M.shifted_mem_groundComplement x

/-- The shifted quadratic form is strictly positive on every nonzero complement vector. -/
theorem groundComplement_energy_pos {x : M.GroundComplement} (hx : x ≠ 0) :
    0 < (⟪M.groundComplementIncl x, M.shifted (M.groundComplementIncl x)⟫_ℂ).re := by
  apply M.shifted_positive_on_complement (M.groundComplementLinearEquiv x).property
  intro hz
  change M.groundComplementIncl x = 0 at hz
  apply hx
  apply M.groundComplementIncl_injective
  simpa only [map_zero] using hz

/-- Removing the radical component before correction leaves its image unchanged. -/
theorem corrected_groundComplementProjection (x : E) :
    M.corrected (M.groundComplementIncl (M.groundComplementProjection x)) = M.corrected x := by
  have hk : M.shifted (x - M.groundComplementIncl (M.groundComplementProjection x)) = 0 := by
    rw [map_sub, M.shifted_groundComplementProjection, sub_self]
  have hb := M.corrected_kills_kernel _ hk
  rw [map_sub, sub_eq_zero] at hb
  exact hb.symm

/-- Physical projection intertwines the full correction with the positive-metric model. -/
theorem complementCorrected_projection_intertwines (x : E) :
    M.complementCorrected (M.groundComplementProjection x) =
      M.groundComplementProjection (M.corrected x) := by
  rw [M.complementCorrected_apply, M.corrected_groundComplementProjection]

/-- Nonzero eigenvalues of the full correction have nonzero projected eigenvectors. -/
theorem groundComplementProjection_eigenvector_ne_zero {x : E} {z : ℂ}
    (hx : x ≠ 0) (hz : z ≠ 0) (heigen : M.corrected x = z • x) :
    M.groundComplementProjection x ≠ 0 := by
  intro hp
  have hg : M.shifted x = 0 := by
    rw [← M.shifted_groundComplementProjection x, hp, map_zero, map_zero]
  have hb := M.corrected_kills_kernel x hg
  rw [heigen] at hb
  exact hx ((smul_eq_zero.mp hb).resolve_left hz)

/-- Reality of full corrected eigenvalues through the constructed positive-metric model. -/
theorem corrected_eigenvalue_real_via_complement {x : E} {z : ℂ}
    (hx : x ≠ 0) (heigen : M.corrected x = z • x) : z.im = 0 := by
  by_cases hz : z = 0
  · simp [hz]
  have hp := M.groundComplementProjection_eigenvector_ne_zero hx hz heigen
  have he : M.complementCorrected (M.groundComplementProjection x) =
      z • M.groundComplementProjection x := by
    rw [M.complementCorrected_projection_intertwines, heigen, map_smul]
  have hev : Module.End.HasEigenvalue M.complementCorrected.toLinearMap z :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr he, hp⟩
  apply M.complementCorrected_spectrum_real
  rw [ContinuousLinearMap.spectrum_eq]
  exact hev.mem_spectrum

end Riemann.CCM.FullSimpleEvenData
