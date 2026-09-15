import Riemann.CCM.Brightness
import Riemann.Basic.Projector

/-! The actual physical orthogonal projector onto the full ground line and its
canonical endpoint normalization. No projector is supplied as an extra input. -/

open scoped InnerProductSpace

namespace Riemann.CCM.FullSimpleEvenData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (M : FullSimpleEvenData E)

/-- The ground projector is constructed from the actual simple ground eigenspace. -/
noncomputable def groundProjector : E →L[ℂ] E :=
  Riemann.Basic.lineProjector M.ground

theorem groundProjector_idempotent : M.groundProjector.comp M.groundProjector =
    M.groundProjector := by
  exact Riemann.Basic.lineProjector_comp M.ground

theorem groundProjector_selfadjoint : M.groundProjector.adjoint = M.groundProjector := by
  exact Riemann.Basic.lineProjector_adjoint M.ground

theorem groundProjector_ground : M.groundProjector M.ground = M.ground := by
  exact Riemann.Basic.lineProjector_self M.ground

theorem groundProjector_range : M.groundProjector.range = Submodule.span ℂ {M.ground} :=
  Riemann.Basic.lineProjector_range M.ground

/-- This is the projector onto the kernel of the full shifted matrix. -/
theorem groundProjector_range_eq_kernel : M.groundProjector.range =
    LinearMap.ker M.shifted.toLinearMap := by
  rw [M.groundProjector_range]
  ext x
  change x ∈ Submodule.span ℂ {M.ground} ↔ M.shifted x = 0
  rw [M.shifted_eq_zero_iff, Submodule.mem_span_singleton]
  exact exists_congr fun a => eq_comm

/-- Boundary visibility is strictly positive at this fixed admitted carrier. -/
noncomputable def groundWeight : ℝ := Riemann.Basic.boundaryWeight M.groundProjector M.eta

theorem groundProjector_eta_ne_zero : M.groundProjector M.eta ≠ 0 :=
  Riemann.Basic.projector_boundary_ne_zero M.groundProjector M.groundProjector_selfadjoint
    M.eta M.ground M.groundProjector_ground M.ground_bright

theorem groundWeight_pos : 0 < M.groundWeight :=
  Riemann.Basic.boundaryWeight_pos _ _ M.groundProjector_eta_ne_zero

theorem groundWeight_pairing : ⟪M.eta, M.groundProjector M.eta⟫_ℂ =
    (M.groundWeight : ℂ) :=
  Riemann.Basic.inner_projector_eq_weight M.groundProjector M.groundProjector_idempotent
    M.groundProjector_selfadjoint M.eta

/-- The phase-free original ground: v = P₀ η / q. -/
noncomputable def groundVector : E :=
  Riemann.Basic.projectorNormalized M.groundProjector M.eta

@[simp] theorem groundProjector_groundVector :
    M.groundProjector M.groundVector = M.groundVector :=
  Riemann.Basic.projectorNormalized_fixed _ M.groundProjector_idempotent _

theorem groundVector_eq_normalizedGround : M.groundVector = M.normalizedGround :=
  Riemann.Basic.projectorNormalized_eq_normalized_ground M.groundProjector
    M.groundProjector_idempotent M.groundProjector_selfadjoint M.eta M.ground
    M.groundProjector_ground M.ground_bright M.groundProjector_range

@[simp] theorem boundary_groundVector : ⟪M.eta, M.groundVector⟫_ℂ = 1 := by
  rw [M.groundVector_eq_normalizedGround, M.boundary_normalizedGround]

@[simp] theorem shifted_groundVector : M.shifted M.groundVector = 0 := by
  rw [M.groundVector_eq_normalizedGround, M.shifted_normalizedGround]

@[simp] theorem reflection_groundVector : M.reflection M.groundVector = M.groundVector := by
  rw [M.groundVector_eq_normalizedGround, M.reflection_normalizedGround]

theorem groundVector_norm_sq : ‖M.groundVector‖ ^ 2 = M.groundWeight⁻¹ :=
  Riemann.Basic.projectorNormalized_norm_sq _ _ M.groundProjector_eta_ne_zero

theorem shifted_D_groundVector : M.shifted (M.D M.groundVector) = -M.b := by
  rw [M.groundVector_eq_normalizedGround, M.shifted_D_normalizedGround]

end Riemann.CCM.FullSimpleEvenData
