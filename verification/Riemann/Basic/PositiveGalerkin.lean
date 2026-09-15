import Riemann.Basic.MetricSpectrum
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Positive Galerkin approximation

The column map is injective and the real energy of the ambient operator is
strictly positive. Both inverses are constructed from these hypotheses. The
algebraic projection identities already hold under strict accretivity. When
Q is also self-adjoint, they give orthogonality in the positive Q metric;
the Galerkin map need not be an ordinary orthogonal projection.
-/

noncomputable section

namespace Riemann.Basic

open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ E] in
/-- Strict positivity forces injectivity, including in dimension zero. -/
theorem strictlyPositive_injective (Q : E →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re) : Function.Injective Q := by
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro x hx
  change x = 0
  by_contra h
  have hp := hQ x h
  have hz : Q x = 0 := hx
  simp [hz] at hp

/-- The inverse of a finite strictly positive operator, with no assumed inverse. -/
def strictlyPositiveEquiv (Q : E →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re) : E ≃L[ℂ] E :=
  (LinearEquiv.ofBijective Q.toLinearMap
    ⟨strictlyPositive_injective Q hQ,
      LinearMap.injective_iff_surjective.mp (strictlyPositive_injective Q hQ)⟩).toContinuousLinearEquiv

@[simp] theorem strictlyPositiveEquiv_apply (Q : E →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re) (x : E) :
    strictlyPositiveEquiv Q hQ x = Q x := rfl

/-- The compressed energy Gram of an injective column map. -/
def galerkinGram (Q : E →L[ℂ] E) (Z : F →L[ℂ] E) : F →L[ℂ] F :=
  Z.adjoint.comp (Q.comp Z)

theorem galerkinGram_inner (Q : E →L[ℂ] E) (Z : F →L[ℂ] E) (x y : F) :
    inner ℂ x (galerkinGram Q Z y) = inner ℂ (Z x) (Q (Z y)) :=
  Z.adjoint_inner_right x (Q (Z y))

theorem galerkinGram_selfAdjoint (Q : E →L[ℂ] E) (Z : F →L[ℂ] E)
    (hQ : Q.adjoint = Q) : (galerkinGram Q Z).adjoint = galerkinGram Q Z := by
  simp [galerkinGram, ContinuousLinearMap.adjoint_comp, hQ,
    ContinuousLinearMap.comp_assoc]

theorem galerkinGram_positive (Q : E →L[ℂ] E) (Z : F →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re)
    (hZ : Function.Injective Z) (x : F) (hx : x ≠ 0) :
    0 < (inner ℂ x (galerkinGram Q Z x)).re := by
  rw [galerkinGram_inner]
  exact hQ (Z x) (fun h => hx (hZ (by simpa using h)))

/-- The actual invertible Gram, not a separately supplied matrix inverse. -/
def galerkinGramEquiv (Q : E →L[ℂ] E) (Z : F →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re)
    (hZ : Function.Injective Z) : F ≃L[ℂ] F :=
  strictlyPositiveEquiv (galerkinGram Q Z) (galerkinGram_positive Q Z hQ hZ)

/-- The Galerkin response `Z (Z* Q Z)⁻¹ Z* c`. -/
def galerkinResponse (Q : E →L[ℂ] E) (Z : F →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re)
    (hZ : Function.Injective Z) (c : E) : E :=
  Z ((galerkinGramEquiv Q Z hQ hZ).symm (Z.adjoint c))

/-- The forcing left after the hierarchy response. -/
def galerkinResidual (Q : E →L[ℂ] E) (Z : F →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re)
    (hZ : Function.Injective Z) (c : E) : E :=
  c - Q (galerkinResponse Q Z hQ hZ c)

theorem galerkinResidual_adjoint_eq_zero (Q : E →L[ℂ] E) (Z : F →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re)
    (hZ : Function.Injective Z) (c : E) :
    Z.adjoint (galerkinResidual Q Z hQ hZ c) = 0 := by
  unfold galerkinResidual
  rw [map_sub]
  apply sub_eq_zero.mpr
  symm
  exact (galerkinGramEquiv Q Z hQ hZ).apply_symm_apply (Z.adjoint c)

/-- The response error is Q-orthogonal to every hierarchy column. -/
theorem positiveGalerkin_projection (Q : E →L[ℂ] E) (Z : F →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re)
    (hZ : Function.Injective Z) (c : E) (a : F) :
    inner ℂ (Z a)
      (Q ((strictlyPositiveEquiv Q hQ).symm c - galerkinResponse Q Z hQ hZ c)) = 0 := by
  have hs : Q ((strictlyPositiveEquiv Q hQ).symm c) = c :=
    (strictlyPositiveEquiv Q hQ).apply_symm_apply c
  rw [map_sub, hs, ← Z.adjoint_inner_right]
  change inner ℂ a (Z.adjoint (galerkinResidual Q Z hQ hZ c)) = 0
  rw [galerkinResidual_adjoint_eq_zero]
  simp

/-- Exact hierarchy plus residual decomposition of the inverse response. -/
theorem positiveGalerkin_decomposition (Q : E →L[ℂ] E) (Z : F →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re)
    (hZ : Function.Injective Z) (c : E) :
    (strictlyPositiveEquiv Q hQ).symm c = galerkinResponse Q Z hQ hZ c +
      (strictlyPositiveEquiv Q hQ).symm (galerkinResidual Q Z hQ hZ c) := by
  apply (strictlyPositiveEquiv Q hQ).injective
  simp only [map_add, ContinuousLinearEquiv.apply_symm_apply, strictlyPositiveEquiv_apply,
    galerkinResidual, add_sub_cancel]

/-- Every continuous linear observation has the same exact decomposition. -/
theorem positiveGalerkin_observation (Q : E →L[ℂ] E) (Z : F →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re)
    (hZ : Function.Injective Z) (c : E) (ell : E →L[ℂ] ℂ) :
    ell ((strictlyPositiveEquiv Q hQ).symm c) = ell (galerkinResponse Q Z hQ hZ c) +
      ell ((strictlyPositiveEquiv Q hQ).symm (galerkinResidual Q Z hQ hZ c)) := by
  conv_lhs => rw [positiveGalerkin_decomposition Q Z hQ hZ c]
  exact map_add ell _ _

/-- The response belongs to the column range. -/
theorem galerkinResponse_mem_range (Q : E →L[ℂ] E) (Z : F →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re)
    (hZ : Function.Injective Z) (c : E) :
    galerkinResponse Q Z hQ hZ c ∈ Z.range :=
  ⟨(galerkinGramEquiv Q Z hQ hZ).symm (Z.adjoint c), rfl⟩

/-- The Galerkin response reproduces vectors already in the hierarchy. -/
theorem galerkinResponse_reproduces (Q : E →L[ℂ] E) (Z : F →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re)
    (hZ : Function.Injective Z) (a : F) :
    galerkinResponse Q Z hQ hZ (Q (Z a)) = Z a := by
  unfold galerkinResponse
  congr 1
  exact (galerkinGramEquiv Q Z hQ hZ).symm_apply_apply a

/-- Riesz-vector version of the exact observation decomposition. -/
theorem positiveGalerkin_inner_observation (Q : E →L[ℂ] E) (Z : F →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re)
    (hZ : Function.Injective Z) (c w : E) :
    inner ℂ w ((strictlyPositiveEquiv Q hQ).symm c) =
      inner ℂ (Z.adjoint w) ((galerkinGramEquiv Q Z hQ hZ).symm (Z.adjoint c)) +
      inner ℂ w ((strictlyPositiveEquiv Q hQ).symm (galerkinResidual Q Z hQ hZ c)) := by
  have h := positiveGalerkin_observation Q Z hQ hZ c (innerSL ℂ w)
  simpa only [innerSL_apply_apply, galerkinResponse, Z.adjoint_inner_left] using h

/-- For a self-adjoint positive operator, the inverse energy splits exactly
into hierarchy energy and residual energy. -/
theorem positiveGalerkin_energy (Q : E →L[ℂ] E) (Z : F →L[ℂ] E)
    (hQ : ∀ x : E, x ≠ 0 → 0 < (inner ℂ x (Q x)).re)
    (hZ : Function.Injective Z) (hself : Q.adjoint = Q) (c : E) :
    inner ℂ c ((strictlyPositiveEquiv Q hQ).symm c) =
      inner ℂ (Z.adjoint c) ((galerkinGramEquiv Q Z hQ hZ).symm (Z.adjoint c)) +
      inner ℂ (galerkinResidual Q Z hQ hZ c)
        ((strictlyPositiveEquiv Q hQ).symm (galerkinResidual Q Z hQ hZ c)) := by
  rw [positiveGalerkin_inner_observation Q Z hQ hZ c c]
  congr 1
  let r := galerkinResidual Q Z hQ hZ c
  have hinv : Q ((strictlyPositiveEquiv Q hQ).symm r) = r :=
    (strictlyPositiveEquiv Q hQ).apply_symm_apply r
  have ho : inner ℂ (galerkinResponse Q Z hQ hZ c) r = 0 := by
    rw [galerkinResponse, ← Z.adjoint_inner_right]
    change inner ℂ _ (Z.adjoint (galerkinResidual Q Z hQ hZ c)) = 0
    rw [galerkinResidual_adjoint_eq_zero]
    simp
  have hc : c = Q (galerkinResponse Q Z hQ hZ c) + r := by
    dsimp [r, galerkinResidual]
    abel
  calc
    inner ℂ c ((strictlyPositiveEquiv Q hQ).symm r) =
        inner ℂ (Q (galerkinResponse Q Z hQ hZ c)) ((strictlyPositiveEquiv Q hQ).symm r) +
        inner ℂ r ((strictlyPositiveEquiv Q hQ).symm r) := by
          conv_lhs => rw [hc]
          exact inner_add_left _ _ _
    _ = inner ℂ r ((strictlyPositiveEquiv Q hQ).symm r) := by
      rw [← Q.adjoint_inner_right, hself, hinv, ho, zero_add]

end Riemann.Basic
