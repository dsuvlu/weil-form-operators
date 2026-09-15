import Riemann.Basic.PositiveGalerkin
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Positive block Schur elimination

Finite complex Hilbert spaces use the physical orthogonal product and the
conjugate-first inner product. All inverses are constructed from positivity.
The source is classical block elimination, in the conventions of BV SD1–SD7.
-/

noncomputable section
namespace Riemann.Basic.PositiveSchur
open scoped InnerProductSpace

variable {U W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

abbrev Space (U W : Type*) := WithLp 2 (U × W)

/-- The actual block operator on the orthogonal Hilbert direct sum. -/
def block (A : U →L[ℂ] U) (B : W →L[ℂ] U) (C : W →L[ℂ] W) :
    Space U W →L[ℂ] Space U W :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ U W).symm.toContinuousLinearMap.comp
    (((A.comp (WithLp.fstL 2 ℂ U W)) + (B.comp (WithLp.sndL 2 ℂ U W))).prod
      ((B.adjoint.comp (WithLp.fstL 2 ℂ U W)) + (C.comp (WithLp.sndL 2 ℂ U W))))

@[simp] theorem block_apply (A : U →L[ℂ] U) (B : W →L[ℂ] U) (C : W →L[ℂ] W)
    (x : U) (y : W) : block A B C (WithLp.toLp 2 (x,y)) =
      WithLp.toLp 2 (A x+B y, B.adjoint x+C y) := rfl

/-- Positive Hermitian block data; no inverse is part of the input. -/
structure Data (U W : Type*) [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [FiniteDimensional ℂ U] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] where
  A : U →L[ℂ] U
  B : W →L[ℂ] U
  C : W →L[ℂ] W
  selfA : A.adjoint = A
  selfC : C.adjoint = C
  positive : ∀ z : Space U W, z ≠ 0 → 0 < (inner ℂ z (block A B C z)).re

namespace Data
variable (M : Data U W)

 theorem A_positive (x : U) (hx : x ≠ 0) : 0 < (inner ℂ x (M.A x)).re := by
  have hz : WithLp.toLp 2 (x,(0:W)) ≠ 0 := by
    intro h
    exact hx (congrArg (fun z : Space U W => z.fst) h)
  simpa using M.positive _ hz

 theorem C_positive (y : W) (hy : y ≠ 0) : 0 < (inner ℂ y (M.C y)).re := by
  have hz : WithLp.toLp 2 ((0:U),y) ≠ 0 := by
    intro h
    exact hy (congrArg (fun z : Space U W => z.snd) h)
  simpa using M.positive _ hz

 def inverseC : W →L[ℂ] W :=
  (strictlyPositiveEquiv M.C M.C_positive).symm.toContinuousLinearMap

@[simp] theorem C_inverseC (y : W) : M.C (M.inverseC y) = y :=
  (strictlyPositiveEquiv M.C M.C_positive).apply_symm_apply y

@[simp] theorem inverseC_C (y : W) : M.inverseC (M.C y) = y :=
  (strictlyPositiveEquiv M.C M.C_positive).symm_apply_apply y

 theorem inverseC_symmetric (x y : W) :
    inner ℂ (M.inverseC x) y = inner ℂ x (M.inverseC y) := by
  conv_lhs => rw [← M.C_inverseC y]
  rw [← M.selfC, ContinuousLinearMap.adjoint_inner_right, M.C_inverseC]

 theorem inverseC_adjoint : M.inverseC.adjoint = M.inverseC := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (M.inverseC_symmetric x y).symm

 def short : U →L[ℂ] U := M.A - M.B.comp (M.inverseC.comp M.B.adjoint)

@[simp] theorem short_apply (x : U) : M.short x = M.A x - M.B (M.inverseC (M.B.adjoint x)) := rfl

 def lift (x : U) : Space U W := WithLp.toLp 2 (x,-M.inverseC (M.B.adjoint x))

@[simp] theorem block_lift (x : U) :
    block M.A M.B M.C (M.lift x) = WithLp.toLp 2 (M.short x,0) := by
  simp [lift, sub_eq_add_neg]

 theorem short_inner (x y : U) :
    inner ℂ (M.lift x) (block M.A M.B M.C (M.lift y)) = inner ℂ x (M.short y) := by
  rw [M.block_lift]
  simp [lift]

 theorem short_positive (x : U) (hx : x ≠ 0) : 0 < (inner ℂ x (M.short x)).re := by
  rw [← M.short_inner]
  apply M.positive
  intro h
  exact hx (congrArg (fun z : Space U W => z.fst) h)

 theorem short_adjoint : M.short.adjoint = M.short := by
  simp [short, ContinuousLinearMap.adjoint_comp, M.selfA, M.inverseC_adjoint,
    ContinuousLinearMap.comp_assoc]

 def inverseShort : U →L[ℂ] U :=
  (strictlyPositiveEquiv M.short M.short_positive).symm.toContinuousLinearMap

@[simp] theorem short_inverseShort (x : U) : M.short (M.inverseShort x) = x :=
  (strictlyPositiveEquiv M.short M.short_positive).apply_symm_apply x

@[simp] theorem inverseShort_short (x : U) : M.inverseShort (M.short x) = x :=
  (strictlyPositiveEquiv M.short M.short_positive).symm_apply_apply x

 def effective (f : U) (g : W) : U := f - M.B (M.inverseC g)
 def solution (f : U) (g : W) : Space U W := WithLp.toLp 2
    (M.inverseShort (M.effective f g),
      M.inverseC (g-M.B.adjoint (M.inverseShort (M.effective f g))))

 theorem solve (f : U) (g : W) :
    block M.A M.B M.C (M.solution f g) = WithLp.toLp 2 (f,g) := by
  have hs := M.short_inverseShort (M.effective f g)
  apply (WithLp.equiv 2 (U × W)).injective
  apply Prod.ext
  · change M.A (M.inverseShort (M.effective f g)) +
        M.B (M.inverseC (g - M.B.adjoint (M.inverseShort (M.effective f g)))) = f
    rw [map_sub, map_sub]
    change M.A (M.inverseShort (M.effective f g)) -
      M.B (M.inverseC (M.B.adjoint (M.inverseShort (M.effective f g)))) = _ at hs
    calc
      _ = M.short (M.inverseShort (M.effective f g)) + M.B (M.inverseC g) := by
        simp only [short_apply]
        abel
      _ = f := by rw [M.short_inverseShort]; simp [effective]
  · change M.B.adjoint (M.inverseShort (M.effective f g)) +
      M.C (M.inverseC (g - M.B.adjoint (M.inverseShort (M.effective f g)))) = g
    rw [M.C_inverseC]
    abel

 theorem solution_unique (f : U) (g : W) (z : Space U W)
    (hz : block M.A M.B M.C z = WithLp.toLp 2 (f,g)) : z = M.solution f g :=
  strictlyPositive_injective _ M.positive (hz.trans (M.solve f g).symm)

 theorem reconstruction (f : U) (g : W) :
    M.solution f g = WithLp.toLp 2 ((0:U),M.inverseC g) +
      M.lift (M.inverseShort (M.effective f g)) := by
  apply (WithLp.equiv 2 (U × W)).injective
  apply Prod.ext
  · simp [solution, lift]
  · simp [solution, lift, sub_eq_add_neg]

 theorem observation (f : U) (g : W) (ell : Space U W →L[ℂ] ℂ) :
    ell (M.solution f g) = ell (WithLp.toLp 2 ((0:U),M.inverseC g)) +
      ell (M.lift (M.inverseShort (M.effective f g))) := by
  rw [M.reconstruction, map_add]

 theorem energy (f : U) (g : W) :
    inner ℂ (WithLp.toLp 2 (f,g)) (M.solution f g) =
      inner ℂ g (M.inverseC g) +
      inner ℂ (M.effective f g) (M.inverseShort (M.effective f g)) := by
  simp only [solution, WithLp.prod_inner_apply]
  rw [map_sub, inner_sub_right, ← M.inverseC_symmetric g (M.B.adjoint _),
    M.B.adjoint_inner_right]
  simp only [effective, inner_sub_left]
  abel

/-- Identification with the actual inverse of the full positive block. -/
theorem solution_eq_inverse (f : U) (g : W) :
    M.solution f g = (strictlyPositiveEquiv (block M.A M.B M.C) M.positive).symm
      (WithLp.toLp 2 (f,g)) := by
  apply (strictlyPositiveEquiv (block M.A M.B M.C) M.positive).injective
  exact (M.solve f g).trans
    ((strictlyPositiveEquiv (block M.A M.B M.C) M.positive).apply_symm_apply _).symm

/-- The inverse energy of the complementary positive block is nonnegative. -/
theorem inverseC_energy_nonneg (g : W) : 0 ≤ (inner ℂ g (M.inverseC g)).re := by
  by_cases h : M.inverseC g = 0
  · simp [h]
  · have hp := M.C_positive (M.inverseC g) h
    rw [M.C_inverseC, M.inverseC_symmetric] at hp
    exact hp.le

/-- The retained forcing contributes nonnegative Schur energy. -/
theorem inverseShort_energy_nonneg (f : U) : 0 ≤ (inner ℂ f (M.inverseShort f)).re := by
  by_cases h : M.inverseShort f = 0
  · simp [h]
  · have hp := M.short_positive (M.inverseShort f) h
    rw [M.short_inverseShort] at hp
    rw [← Complex.conj_re, inner_conj_symm]
    exact hp.le

/-- The actual block is self-adjoint in the physical product metric. -/
theorem block_adjoint : (block M.A M.B M.C).adjoint = block M.A M.B M.C := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ x.fst (M.A y.fst + M.B y.snd) +
      inner ℂ x.snd (M.B.adjoint y.fst + M.C y.snd) =
    inner ℂ (M.A x.fst + M.B x.snd) y.fst +
      inner ℂ (M.B.adjoint x.fst + M.C x.snd) y.snd
  simp only [inner_add_left, inner_add_right]
  rw [← M.A.adjoint_inner_right, M.selfA, ← M.C.adjoint_inner_right, M.selfC,
    M.B.adjoint_inner_left, M.B.adjoint_inner_right]
  abel

/-- The graph lift as a continuous linear column map. -/
def liftMap : U →L[ℂ] Space U W :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ U W).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℂ U).prod (-(M.inverseC.comp M.B.adjoint)))

@[simp] theorem liftMap_apply (x : U) : M.liftMap x = M.lift x := rfl

theorem liftMap_injective : Function.Injective M.liftMap := by
  intro x y h
  exact congrArg (fun z : Space U W => z.fst) h

/-- The physical graph Gram includes the complementary displacement. -/
theorem lift_inner (x y : U) :
    inner ℂ (M.lift x) (M.lift y) = inner ℂ x y +
      inner ℂ (M.inverseC (M.B.adjoint x)) (M.inverseC (M.B.adjoint y)) := by
  simp [lift]

/-- Pullback of the full form to its graph is exactly the Schur short. -/
theorem graph_gram : galerkinGram (block M.A M.B M.C) M.liftMap = M.short := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [galerkinGram_inner]
  exact M.short_inner y x

/-- Nonorthogonal retained columns carry the congruent short and forcing. -/
theorem raw_short {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (R : F →L[ℂ] U) :
    galerkinGram (block M.A M.B M.C) (M.liftMap.comp R) = galerkinGram M.short R := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [galerkinGram_inner, galerkinGram_inner]
  exact M.short_inner (R y) (R x)

/-- The physical mass, rather than an identity matrix, multiplies an energy
parameter after a general change of columns. -/
theorem raw_pencil {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (R : F →L[ℂ] U) (H : U →L[ℂ] U) (e : ℂ) :
    galerkinGram (H - e • ContinuousLinearMap.id ℂ U) R =
      galerkinGram H R - e • galerkinGram (ContinuousLinearMap.id ℂ U) R := by
  ext x
  simp [galerkinGram]

end Data
end Riemann.Basic.PositiveSchur
