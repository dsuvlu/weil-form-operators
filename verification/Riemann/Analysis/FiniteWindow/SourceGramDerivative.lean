import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Linear

/-! # Frozen-source differentiation with an explicit current domain

These are the calculus/form lemmas used by the analytic completion. The
left-current equation on literal outputs is an explicit hypothesis. A
right-current equation on the input core is not substituted for it.
-/
noncomputable section
open scoped ComplexConjugate

namespace Riemann.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local instance : ContinuousSMul ℝ (E →L[ℂ] E) := IsScalarTower.continuousSMul ℂ

/-- The negative Hermitian current on a declared linear domain; no unbounded
adjoint operator or ambient boundedness is asserted. -/
def currentForm (D : Submodule ℂ E) (J : D →ₗ[ℂ] E) (u v : D) : ℂ :=
  -inner ℂ (u : E) (J v) - inner ℂ (J u) (v : E)

lemma currentForm_hermitian (D : Submodule ℂ E) (J : D →ₗ[ℂ] E) (u v : D) :
    currentForm D J v u = conj (currentForm D J u v) := by
  simp only [currentForm, map_sub, map_neg, inner_conj_symm]
  ring

/-- Polarized derivative for two genuinely frozen source vectors. -/
theorem hasDerivAt_frozenSourceGram {X : ℝ → E →L[ℂ] E} {X' : E →L[ℂ] E} {a : ℝ}
    (hX : HasDerivAt X X' a) (u v : E) :
    HasDerivAt (fun s => inner ℂ (X s u) (X s v))
      (inner ℂ (X a u) (X' v) + inner ℂ (X' u) (X a v)) a := by
  have hu : HasDerivAt (fun s => X s u) (X' u) a := by
    exact ((ContinuousLinearMap.apply ℂ E u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt a hX
  have hv : HasDerivAt (fun s => X s v) (X' v) a := by
    exact ((ContinuousLinearMap.apply ℂ E v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt a hX
  exact hu.inner ℂ hv

/-- The domain-correct literal-output formula requires `J X = -X′`.
The source vectors themselves need not belong to the domain of J. -/
theorem hasDerivAt_frozenSourceGram_current
    {X : ℝ → E →L[ℂ] E} {X' : E →L[ℂ] E} {a : ℝ}
    (hX : HasDerivAt X X' a) (D : Submodule ℂ E) (J : D →ₗ[ℂ] E)
    (hmem : ∀ u, X a u ∈ D)
    (hleft : ∀ u, X' u = -J ⟨X a u, hmem u⟩) (u v : E) :
    HasDerivAt (fun s => inner ℂ (X s u) (X s v))
      (currentForm D J ⟨X a u, hmem u⟩ ⟨X a v, hmem v⟩) a := by
  have h := hasDerivAt_frozenSourceGram hX u v
  simpa only [hleft, inner_neg_right, inner_neg_left, currentForm, sub_eq_add_neg] using h

/-- The finite coefficient Gram has the entrywise polarized derivative.
The entire source-column family U remains fixed. -/
theorem hasDerivAt_frozenSourceColumnGram {ι : Type*} [Fintype ι]
    {X : ℝ → E →L[ℂ] E} {X' : E →L[ℂ] E} {a : ℝ}
    (hX : HasDerivAt X X' a) (U : ι → E) :
    HasDerivAt (fun s i j => inner ℂ (X s (U i)) (X s (U j)))
      (fun i j => inner ℂ (X a (U i)) (X' (U j)) +
        inner ℂ (X' (U i)) (X a (U j))) a := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_frozenSourceGram hX (U i) (U j)

end Riemann.Analysis
