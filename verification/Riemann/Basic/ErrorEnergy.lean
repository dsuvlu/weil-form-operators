import Riemann.Basic.RankOne

/-!
# Error energy at a null vector

This is an identity for the actual Hilbert-space adjoint. No positivity or
finite-dimensionality assumption is needed; arithmetic applications must
separately identify the operator and its null vector.
-/

namespace Riemann.Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Translating a vector by a null vector preserves a self-adjoint quadratic pairing. -/
theorem inner_error_energy (G : E →L[ℂ] E) (hG : G.adjoint = G)
    (v p : E) (hv : G v = 0) :
    inner ℂ p (G p) = inner ℂ (v - p) (G (v - p)) := by
  have hcross : inner ℂ v (G p) = 0 := by
    rw [← G.adjoint_inner_left p v, hG, hv]
    simp
  simp [map_sub, hv, inner_sub_left, inner_neg_right, hcross]

/-- The real error-energy identity used for a positive semidefinite shifted form. -/
theorem error_energy (G : E →L[ℂ] E) (hG : G.adjoint = G)
    (v p : E) (hv : G v = 0) :
    (inner ℂ p (G p)).re = (inner ℂ (v - p) (G (v - p))).re :=
  congrArg Complex.re (inner_error_energy G hG v p hv)

end Riemann.Basic
