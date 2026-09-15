import Riemann.CCM.BoundaryWeyl
import Riemann.Basic.PositiveSchurTransitivity

/-! Schur reconstruction of the actual occupied boundary response.
A chart is an explicit physical isometry whose block matrix is the existing
positive endpoint compression. No component of the forcing is discarded.
-/
noncomputable section
open scoped InnerProductSpace
namespace Riemann.CCM.FullSimpleEvenData
open Riemann.Basic.PositiveSchur
variable {E U W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
variable (M : FullSimpleEvenData E)

/-- Identify the already defined occupied response with a physical block solve. -/
theorem boundaryResponse_schur (S : Data U W)
    (e : Space U W ≃ₗᵢ[ℂ] M.boundaryHyperplane)
    (hQ : ∀ z, M.boundaryCompression (e z) = e (block S.A S.B S.C z)) :
    M.boundaryResponse = e (S.solution (e.symm M.boundaryCoupling).fst
      (e.symm M.boundaryCoupling).snd) := by
  apply M.boundaryCompression_injective
  rw [show M.boundaryCompression M.boundaryResponse = M.boundaryCoupling from
    M.boundaryCompression_inverse M.boundaryCoupling, hQ, S.solve]
  exact (e.apply_symm_apply M.boundaryCoupling).symm

/-- Native ground reconstruction retains both the complementary forcing and the lifted short. -/
theorem groundVector_schur (S : Data U W)
    (e : Space U W ≃ₗᵢ[ℂ] M.boundaryHyperplane)
    (hQ : ∀ z, M.boundaryCompression (e z) = e (block S.A S.B S.C z)) :
    M.groundVector = M.boundarySection -
      (e (WithLp.toLp 2 ((0 : U), S.inverseC (e.symm M.boundaryCoupling).snd)) : E) -
      (e (S.lift (S.inverseShort (S.effective (e.symm M.boundaryCoupling).fst
        (e.symm M.boundaryCoupling).snd))) : E) := by
  rw [M.groundVector_boundary_resolvent, M.boundaryResponse_schur S e hQ, S.reconstruction,
    map_add, Submodule.coe_add]
  abel

/-- Every boundary observation sees the complete Schur reconstruction. -/
theorem boundaryObservation_schur (S : Data U W)
    (e : Space U W ≃ₗᵢ[ℂ] M.boundaryHyperplane)
    (hQ : ∀ z, M.boundaryCompression (e z) = e (block S.A S.B S.C z))
    (ell : E →ₗ[ℂ] ℂ) :
    ell M.groundVector = ell M.boundarySection -
      ell (e (WithLp.toLp 2 ((0 : U), S.inverseC (e.symm M.boundaryCoupling).snd))) -
      ell (e (S.lift (S.inverseShort (S.effective (e.symm M.boundaryCoupling).fst
        (e.symm M.boundaryCoupling).snd)))) := by
  rw [M.groundVector_schur S e hQ, map_sub, map_sub]

/-- Positive split of the occupied forcing energy in the same physical chart. -/
theorem boundaryEnergy_schur (S : Data U W)
    (e : Space U W ≃ₗᵢ[ℂ] M.boundaryHyperplane)
    (hQ : ∀ z, M.boundaryCompression (e z) = e (block S.A S.B S.C z)) :
    ⟪M.boundaryCoupling, M.boundaryResponse⟫_ℂ =
      ⟪(e.symm M.boundaryCoupling).snd, S.inverseC (e.symm M.boundaryCoupling).snd⟫_ℂ +
      ⟪S.effective (e.symm M.boundaryCoupling).fst (e.symm M.boundaryCoupling).snd,
        S.inverseShort (S.effective (e.symm M.boundaryCoupling).fst
          (e.symm M.boundaryCoupling).snd)⟫_ℂ := by
  rw [M.boundaryResponse_schur S e hQ]
  nth_rw 1 [← e.apply_symm_apply M.boundaryCoupling]
  rw [e.inner_map_map]
  exact S.energy _ _

/-- The normalized boundary characteristic retains the actual signed anchor. -/
theorem normalizedBoundaryObservation_schur (S : Data U W)
    (e : Space U W ≃ₗᵢ[ℂ] M.boundaryHyperplane)
    (hQ : ∀ z, M.boundaryCompression (e z) = e (block S.A S.B S.C z))
    (ell anchor : E →ₗ[ℂ] ℂ) :
    ell M.groundVector / anchor M.groundVector =
    (ell M.boundarySection - ell (e (S.solution (e.symm M.boundaryCoupling).fst
      (e.symm M.boundaryCoupling).snd))) /
    (anchor M.boundarySection - anchor (e (S.solution (e.symm M.boundaryCoupling).fst
      (e.symm M.boundaryCoupling).snd))) := by
  rw [M.boundary_observation ell, M.boundary_observation anchor,
    M.boundaryResponse_schur S e hQ]

theorem schur_anchor_ne_zero (S : Data U W)
    (e : Space U W ≃ₗᵢ[ℂ] M.boundaryHyperplane)
    (hQ : ∀ z, M.boundaryCompression (e z) = e (block S.A S.B S.C z))
    (anchor : E →ₗ[ℂ] ℂ) (ha : anchor M.groundVector ≠ 0) :
    anchor M.boundarySection - anchor (e (S.solution (e.symm M.boundaryCoupling).fst
      (e.symm M.boundaryCoupling).snd)) ≠ 0 := by
  rw [← M.boundaryResponse_schur S e hQ, ← M.boundary_observation anchor]
  exact ha

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- In the order retained ⊕ (remaining ⊕ first-eliminated), eliminate F first,
then W. This is BV's three-block solve with an explicit permutation of coordinates. -/
theorem boundaryResponse_schur_transitive (T : ThreeData U W F)
    (e : Space U (Space W F) ≃ₗᵢ[ℂ] M.boundaryHyperplane)
    (hQ : ∀ z, M.boundaryCompression (e z) = e (block T.direct.A T.direct.B T.direct.C z)) :
    M.boundaryResponse = e (T.successiveSolution (e.symm M.boundaryCoupling).fst
      (e.symm M.boundaryCoupling).snd.fst (e.symm M.boundaryCoupling).snd.snd) := by
  rw [M.boundaryResponse_schur T.direct e hQ]
  congr 1
  exact T.solution_transitivity _ _ _

/-- Successive elimination preserves every occupied observation, not just the determinant. -/
theorem boundaryObservation_schur_transitive (T : ThreeData U W F)
    (e : Space U (Space W F) ≃ₗᵢ[ℂ] M.boundaryHyperplane)
    (hQ : ∀ z, M.boundaryCompression (e z) = e (block T.direct.A T.direct.B T.direct.C z))
    (ell : E →ₗ[ℂ] ℂ) :
    ell M.groundVector = ell M.boundarySection -
      ell (e (T.successiveSolution (e.symm M.boundaryCoupling).fst
        (e.symm M.boundaryCoupling).snd.fst (e.symm M.boundaryCoupling).snd.snd)) := by
  rw [M.boundary_observation ell, M.boundaryResponse_schur_transitive T e hQ]

end Riemann.CCM.FullSimpleEvenData
