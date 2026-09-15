import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Rank-one convention

We use mathlib's `InnerProductSpace.rankOne ℂ a b` directly. It maps `x` to
`⟪b, x⟫ • a`, with the inner product conjugate-linear in its first argument.
Adjoints and compositions are the native continuous-linear-map operations.
-/

noncomputable section

namespace Riemann.Basic

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The boundary row represented by its Riesz vector. -/
abbrev boundaryRow (η : E) : E →L[ℂ] ℂ := innerSL ℂ η

@[simp] theorem boundaryRow_apply (η x : E) : boundaryRow η x = inner ℂ η x := rfl

@[simp] theorem boundaryRow_adjoint_one [CompleteSpace E] (η : E) :
    (boundaryRow η).adjoint 1 = η := by
  simp [boundaryRow, ContinuousLinearMap.adjoint_innerSL_apply]

end Riemann.Basic
