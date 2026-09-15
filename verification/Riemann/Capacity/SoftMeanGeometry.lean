import Riemann.Capacity.SoftMean
import Riemann.Basic.PositiveSchur

/-! Congruence invariance and orthogonal-sum additivity of finite soft means. -/
noncomputable section
namespace Riemann.Capacity
open scoped InnerProductSpace
open Riemann.Basic Riemann.Basic.PositiveSchur
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The inverse-mass operator transforms by similarity under simultaneous
congruence of both positive forms. -/
theorem inverse_mass_congruence (H B : E →L[ℂ] E)
    (hH : ∀ x, x ≠ 0 → 0 < (inner ℂ x (H x)).re) (e : F ≃L[ℂ] E) :
    (positiveInverse (galerkinGram H e.toContinuousLinearMap)
      (galerkinGram_positive H e.toContinuousLinearMap hH e.injective)).comp
      (galerkinGram B e.toContinuousLinearMap) =
    e.symm.toContinuousLinearMap.comp ((positiveInverse H hH).comp
      (B.comp e.toContinuousLinearMap)) := by
  ext x
  apply strictlyPositive_injective (galerkinGram H e.toContinuousLinearMap)
    (galerkinGram_positive H e.toContinuousLinearMap hH e.injective)
  simp only [ContinuousLinearMap.comp_apply, positiveInverse_left]
  simp [galerkinGram]

theorem inverseMassTrace_congruence (H B : E →L[ℂ] E)
    (hH : ∀ x, x ≠ 0 → 0 < (inner ℂ x (H x)).re) (e : F ≃L[ℂ] E) :
    inverseMassTrace (galerkinGram H e.toContinuousLinearMap)
      (galerkinGram_positive H e.toContinuousLinearMap hH e.injective)
      (galerkinGram B e.toContinuousLinearMap) = inverseMassTrace H hH B := by
  unfold inverseMassTrace
  rw [inverse_mass_congruence]
  exact LinearMap.trace_conj' ((positiveInverse H hH).comp B).toLinearMap e.symm.toLinearEquiv

/-- Trace of an actual diagonal block operator in the physical L² product. -/
theorem trace_diagonal (A : E →L[ℂ] E) (C : F →L[ℂ] F) :
    LinearMap.trace ℂ (Space E F) (block A 0 C).toLinearMap =
      LinearMap.trace ℂ E A.toLinearMap + LinearMap.trace ℂ F C.toLinearMap := by
  have h := LinearMap.trace_conj' (LinearMap.prodMap A.toLinearMap C.toLinearMap)
    (WithLp.linearEquiv 2 ℂ (E × F)).symm
  rw [LinearMap.trace_prodMap'] at h
  convert h using 1
  congr 1
  ext z
  apply (WithLp.equiv 2 (E × F)).injective
  apply Prod.ext <;> simp [block, LinearEquiv.conj_apply]

@[simp] theorem diagonal_apply (A : E →L[ℂ] E) (C : F →L[ℂ] F) (z : Space E F) :
    block A 0 C z = WithLp.toLp 2 (A z.fst,C z.snd) := by
  apply (WithLp.equiv 2 (E × F)).injective
  apply Prod.ext <;> simp [block]

namespace PositivePencil
variable (P : PositivePencil E)

/-- Both forms, including the physical mass, undergo the same congruence. -/
def congruence (e : F ≃L[ℂ] E) : PositivePencil F where
  energy := galerkinGram P.energy e.toContinuousLinearMap
  mass := galerkinGram P.mass e.toContinuousLinearMap
  energy_symmetric := by
    intro x y
    change inner ℂ (galerkinGram P.energy e.toContinuousLinearMap x) y =
      inner ℂ x (galerkinGram P.energy e.toContinuousLinearMap y)
    rw [← inner_conj_symm, galerkinGram_inner, inner_conj_symm, galerkinGram_inner]
    exact P.energy_symmetric (e x) (e y)
  mass_symmetric := by
    intro x y
    change inner ℂ (galerkinGram P.mass e.toContinuousLinearMap x) y =
      inner ℂ x (galerkinGram P.mass e.toContinuousLinearMap y)
    rw [← inner_conj_symm, galerkinGram_inner, inner_conj_symm, galerkinGram_inner]
    exact P.mass_symmetric (e x) (e y)
  energy_nonneg x := by
    rw [galerkinGram_inner]
    exact P.energy_nonneg (e x)
  mass_positive := galerkinGram_positive P.mass e.toContinuousLinearMap P.mass_positive e.injective

@[simp] theorem congruence_pencil (e : F ≃L[ℂ] E) (s : ℝ) :
    (P.congruence e).pencil s = galerkinGram (P.pencil s) e.toContinuousLinearMap := by
  ext x
  simp [pencil, congruence, galerkinGram]

 theorem softMean_congruence (e : F ≃L[ℂ] E) (s : ℝ) (hs : 0 < s) :
    (P.congruence e).softMean s hs = P.softMean s hs := by
  unfold softMean
  simp only [congruence_pencil]
  change s * (inverseMassTrace (galerkinGram (P.pencil s) e.toContinuousLinearMap) _
    (galerkinGram P.mass e.toContinuousLinearMap)).re = _
  rw [inverseMassTrace_congruence]

/-- Physical orthogonal sum of two pencils. -/
def orthogonalSum (Q : PositivePencil F) : PositivePencil (Space E F) where
  energy := block P.energy 0 Q.energy
  mass := block P.mass 0 Q.mass
  energy_symmetric := by
    intro x y
    change inner ℂ ((block P.energy 0 Q.energy) x) y =
      inner ℂ x ((block P.energy 0 Q.energy) y)
    simp only [diagonal_apply, WithLp.prod_inner_apply]
    change inner ℂ (P.energy x.fst) y.fst + inner ℂ (Q.energy x.snd) y.snd =
      inner ℂ x.fst (P.energy y.fst) + inner ℂ x.snd (Q.energy y.snd)
    exact congrArg₂ (fun a b : ℂ => a+b)
      (P.energy_symmetric x.fst y.fst) (Q.energy_symmetric x.snd y.snd)
  mass_symmetric := by
    intro x y
    change inner ℂ ((block P.mass 0 Q.mass) x) y = inner ℂ x ((block P.mass 0 Q.mass) y)
    simp only [diagonal_apply, WithLp.prod_inner_apply]
    change inner ℂ (P.mass x.fst) y.fst + inner ℂ (Q.mass x.snd) y.snd =
      inner ℂ x.fst (P.mass y.fst) + inner ℂ x.snd (Q.mass y.snd)
    exact congrArg₂ (fun a b : ℂ => a+b)
      (P.mass_symmetric x.fst y.fst) (Q.mass_symmetric x.snd y.snd)
  energy_nonneg x := by
    simp only [diagonal_apply, WithLp.prod_inner_apply, Complex.add_re]
    exact add_nonneg (P.energy_nonneg _) (Q.energy_nonneg _)
  mass_positive x hx := by
    simp only [diagonal_apply, WithLp.prod_inner_apply, Complex.add_re]
    change 0 < (inner ℂ x.fst (P.mass x.fst)).re + (inner ℂ x.snd (Q.mass x.snd)).re
    by_cases h1 : x.fst = 0
    · have h2 : x.snd ≠ 0 := by
        intro h2
        apply hx
        apply (WithLp.equiv 2 (E × F)).injective
        exact Prod.ext h1 h2
      simpa [h1] using Q.mass_positive x.snd h2
    · have hn : 0 ≤ (inner ℂ x.snd (Q.mass x.snd)).re := by
        by_cases h2 : x.snd = 0
        · simp [h2]
        · exact (Q.mass_positive _ h2).le
      exact add_pos_of_pos_of_nonneg (P.mass_positive _ h1) hn

@[simp] theorem orthogonalSum_pencil (Q : PositivePencil F) (s : ℝ) :
    (P.orthogonalSum Q).pencil s = block (P.pencil s) 0 (Q.pencil s) := by
  ext x
  apply (WithLp.equiv 2 (E × F)).injective
  apply Prod.ext <;> simp [pencil, orthogonalSum, block]

 theorem softMean_orthogonalSum (Q : PositivePencil F) (s : ℝ) (hs : 0 < s) :
    (P.orthogonalSum Q).softMean s hs = P.softMean s hs + Q.softMean s hs := by
  have hi : (positiveInverse ((P.orthogonalSum Q).pencil s)
      ((P.orthogonalSum Q).pencil_positive s hs)).comp (P.orthogonalSum Q).mass =
    block ((positiveInverse (P.pencil s) (P.pencil_positive s hs)).comp P.mass) 0
      ((positiveInverse (Q.pencil s) (Q.pencil_positive s hs)).comp Q.mass) := by
    ext x
    apply strictlyPositive_injective ((P.orthogonalSum Q).pencil s)
      ((P.orthogonalSum Q).pencil_positive s hs)
    simp only [ContinuousLinearMap.comp_apply, positiveInverse_left]
    rw [orthogonalSum_pencil]
    apply (WithLp.equiv 2 (E × F)).injective
    apply Prod.ext <;> simp [orthogonalSum, block]
  simp only [softMean, inverseMassTrace]
  rw [hi, trace_diagonal, Complex.add_re]
  ring

end PositivePencil
end Riemann.Capacity
