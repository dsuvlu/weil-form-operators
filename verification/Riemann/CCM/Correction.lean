import Riemann.CCM.GroundProjector
import Riemann.Basic.Projector

/-! The original boundary correction and its shifted-metric symmetry. -/

open scoped InnerProductSpace
open InnerProductSpace

namespace Riemann.CCM.FullSimpleEvenData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (M : FullSimpleEvenData E)

/-- The finite original CCM derivative: derivative minus the selected boundary
correction. The underlying metric here is still the physical inner product. -/
noncomputable def corrected : E →L[ℂ] E :=
  M.D - rankOne ℂ (M.D M.groundVector) M.eta

@[simp] theorem corrected_apply (x : E) :
    M.corrected x = M.D x - ⟪M.eta, x⟫_ℂ • M.D M.groundVector := rfl

@[simp] theorem corrected_ground : M.corrected M.groundVector = 0 := by
  rw [corrected_apply, M.boundary_groundVector, one_smul, sub_self]

/-- The corrected derivative agrees with the periodic derivative on the actual
endpoint hyperplane. -/
theorem corrected_on_boundary_kernel {x : E} (hx : ⟪M.eta, x⟫_ℂ = 0) :
    M.corrected x = M.D x := by simp [hx]

/-- Source Lemma 5.4(i), with the physical normalization and shifted form. -/
theorem shifted_corrected_apply (x : E) :
    M.shifted (M.corrected x) = M.shifted (M.D x) + ⟪M.eta, x⟫_ℂ • M.b := by
  rw [corrected_apply, map_sub, map_smul, M.shifted_D_groundVector]
  simp only [smul_neg, sub_neg_eq_add]

/-- The full shifted metric intertwines the correction and its physical adjoint. -/
theorem metric_intertwining :
    M.shifted.comp M.corrected = M.corrected.adjoint.comp M.shifted := by
  ext x
  change M.shifted (M.corrected x) = M.corrected.adjoint (M.shifted x)
  have hpair : ⟪M.D M.groundVector, M.shifted x⟫_ℂ = -⟪M.b, x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left M.shifted x,
      M.shifted_selfadjoint, M.shifted_D_groundVector, inner_neg_left]
  have hdisp := M.shifted_displacement x
  rw [M.shifted_corrected_apply]
  simp only [corrected, map_sub, adjoint_rankOne, M.D_selfadjoint,
    sub_apply, rankOne_apply, hpair, neg_smul, sub_neg_eq_add]
  have h := congrArg (fun y : E => y + M.shifted (M.D x) +
    ⟪M.b, x⟫_ℂ • M.eta) hdisp
  abel_nf at h ⊢
  exact h.symm

/-- Symmetry for the shifted sesquilinear form, before constructing its quotient. -/
theorem weighted_symmetry (x y : E) :
    ⟪M.corrected x, M.shifted y⟫_ℂ = ⟪x, M.shifted (M.corrected y)⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right M.corrected x (M.shifted y)]
  exact congrArg (fun z : E => ⟪x, z⟫_ℂ)
    (congrArg (fun T : E →L[ℂ] E => T y) M.metric_intertwining).symm

/-- The endpoint condition and the killed ground determine the correction uniquely. -/
theorem corrected_unique (A : E →L[ℂ] E)
    (hA : A M.groundVector = 0)
    (hkernel : ∀ x, ⟪M.eta, x⟫_ℂ = 0 → A x = M.D x) : A = M.corrected := by
  ext x
  have hz : ⟪M.eta, x - ⟪M.eta, x⟫_ℂ • M.groundVector⟫_ℂ = 0 := by
    rw [inner_sub_right, inner_smul_right, M.boundary_groundVector, mul_one,
      sub_self]
  have h := hkernel _ hz
  simpa only [map_sub, map_smul, hA, smul_zero, sub_zero, corrected_apply] using h

/-- The projector formula selects exactly the already derived bright ground. -/
theorem projector_ground (P : E →L[ℂ] E) (hP : P.comp P = P)
    (hPstar : P.adjoint = P) (hPu : P M.ground = M.ground)
    (hrange : P.range = Submodule.span ℂ {M.ground}) :
    Riemann.Basic.projectorNormalized P M.eta = M.groundVector := by
  rw [M.groundVector_eq_normalizedGround]
  exact Riemann.Basic.projectorNormalized_eq_normalized_ground
    P hP hPstar M.eta M.ground hPu M.ground_bright hrange

end Riemann.CCM.FullSimpleEvenData
