import Riemann.Basic.PositiveSchur

/-!
# Three-block Schur transitivity, including forcing and observation

Successive elimination is compared with elimination of the entire complement.
All spaces are finite physical Hilbert spaces; no complementary block is dropped.
Source: BV SD12 and the reconstruction in SD1–SD2.
-/
noncomputable section
namespace Riemann.Basic.PositiveSchur
open scoped InnerProductSpace
variable {U V W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- A block row between physical orthogonal sums. -/
def row (D : V →L[ℂ] U) (E : W →L[ℂ] U) : Space V W →L[ℂ] U :=
  D.comp (WithLp.fstL 2 ℂ V W) + E.comp (WithLp.sndL 2 ℂ V W)

omit [FiniteDimensional ℂ U] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
@[simp] theorem row_apply (D : V →L[ℂ] U) (E : W →L[ℂ] U) (v : V) (w : W) :
    row D E (WithLp.toLp 2 (v,w)) = D v + E w := rfl

 theorem row_adjoint_apply (D : V →L[ℂ] U) (E : W →L[ℂ] U) (u : U) :
    (row D E).adjoint u = WithLp.toLp 2 (D.adjoint u,E.adjoint u) := by
  apply ext_inner_right ℂ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ u (D z.fst + E z.snd) =
    inner ℂ (D.adjoint u) z.fst + inner ℂ (E.adjoint u) z.snd
  rw [inner_add_right, D.adjoint_inner_left, E.adjoint_inner_left]

/-- A positive three-block matrix, with its complete complementary block
already expressed as positive two-block data. -/
structure ThreeData (U V W : Type*) [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [FiniteDimensional ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] where
  A : U →L[ℂ] U
  D : V →L[ℂ] U
  E : W →L[ℂ] U
  tail : Data V W
  selfA : A.adjoint = A
  positive : ∀ z : Space U (Space V W), z ≠ 0 →
    0 < (inner ℂ z (block A (row D E) (block tail.A tail.B tail.C) z)).re

namespace ThreeData
variable (T : ThreeData U V W)

/-- Full positivity alone supplies the principal-tail positivity required by
`ThreeData`; the diagonal Hermitian hypotheses remain explicit. -/
def ofBlocks (A : U →L[ℂ] U) (D : V →L[ℂ] U) (E : W →L[ℂ] U)
    (F : V →L[ℂ] V) (K : W →L[ℂ] V) (C : W →L[ℂ] W)
    (hA : A.adjoint = A) (hF : F.adjoint = F) (hC : C.adjoint = C)
    (hp : ∀ z : Space U (Space V W), z ≠ 0 →
      0 < (inner ℂ z (block A (row D E) (block F K C) z)).re) : ThreeData U V W where
  A := A
  D := D
  E := E
  selfA := hA
  tail := {
    A := F
    B := K
    C := C
    selfA := hF
    selfC := hC
    positive := by
      intro z hz
      have hn : WithLp.toLp 2 ((0:U),z) ≠ 0 := by
        intro h
        exact hz (congrArg (fun x : Space U (Space V W) => x.snd) h)
      simpa using hp _ hn }
  positive := hp


/-- Direct elimination of V⊕W. -/
def direct : Data U (Space V W) where
  A := T.A
  B := row T.D T.E
  C := block T.tail.A T.tail.B T.tail.C
  selfA := T.selfA
  selfC := T.tail.block_adjoint
  positive := T.positive

 theorem direct_inverseC (g : V) (h : W) :
    T.direct.inverseC (WithLp.toLp 2 (g,h)) = T.tail.solution g h :=
  (T.tail.solution_eq_inverse g h).symm

/-- First elimination: the W block is removed. -/
def firstA : U →L[ℂ] U := T.A - T.E.comp (T.tail.inverseC.comp T.E.adjoint)
def firstB : V →L[ℂ] U := T.D - T.E.comp (T.tail.inverseC.comp T.tail.B.adjoint)
def firstForcing (f : U) (h : W) : U := f - T.E (T.tail.inverseC h)

def successiveShort : U →L[ℂ] U :=
  T.firstA - T.firstB.comp (T.tail.inverseShort.comp T.firstB.adjoint)

def successiveForcing (f : U) (g : V) (h : W) : U :=
  T.firstForcing f h - T.firstB (T.tail.inverseShort (T.tail.effective g h))

 theorem firstB_adjoint (u : U) :
    T.firstB.adjoint u = T.D.adjoint u -
      T.tail.B (T.tail.inverseC (T.E.adjoint u)) := by
  simp [firstB, ContinuousLinearMap.adjoint_comp, T.tail.inverseC_adjoint]

/-- The graph used in the first elimination of W. -/
def firstLift (z : Space U V) : Space U (Space V W) :=
  WithLp.toLp 2 (z.fst, WithLp.toLp 2
    (z.snd, -T.tail.inverseC (T.E.adjoint z.fst + T.tail.B.adjoint z.snd)))

theorem firstLift_energy (z : Space U V) :
    inner ℂ (T.firstLift z)
      (block T.A (row T.D T.E) (block T.tail.A T.tail.B T.tail.C) (T.firstLift z)) =
    inner ℂ z (block T.firstA T.firstB T.tail.short z) := by
  unfold firstLift
  rw [block_apply, row_adjoint_apply, block_apply, row_apply]
  change inner ℂ z.fst (T.A z.fst + (T.D z.snd + T.E
      (-T.tail.inverseC (T.E.adjoint z.fst + T.tail.B.adjoint z.snd)))) +
    (inner ℂ z.snd (T.D.adjoint z.fst + (T.tail.A z.snd + T.tail.B
      (-T.tail.inverseC (T.E.adjoint z.fst + T.tail.B.adjoint z.snd)))) +
    inner ℂ (-T.tail.inverseC (T.E.adjoint z.fst + T.tail.B.adjoint z.snd))
      (T.E.adjoint z.fst + (T.tail.B.adjoint z.snd + T.tail.C
        (-T.tail.inverseC (T.E.adjoint z.fst + T.tail.B.adjoint z.snd))))) = _
  simp only [map_neg, T.tail.C_inverseC]
  have hz : T.E.adjoint z.fst + (T.tail.B.adjoint z.snd -
      (T.E.adjoint z.fst + T.tail.B.adjoint z.snd)) = 0 := by abel
  simp only [sub_eq_add_neg] at hz
  rw [hz, inner_zero_right, add_zero]
  change _ = inner ℂ z.fst (T.firstA z.fst + T.firstB z.snd) +
    inner ℂ z.snd (T.firstB.adjoint z.fst + T.tail.short z.snd)
  rw [T.firstB_adjoint]
  simp only [firstA, firstB, sub_apply, ContinuousLinearMap.comp_apply,
    Data.short_apply, map_add, inner_add_right, inner_sub_right, inner_neg_right]
  abel

/-- The intermediate two-block operator is strictly positive. -/
theorem first_positive (z : Space U V) (hz : z ≠ 0) :
    0 < (inner ℂ z (block T.firstA T.firstB T.tail.short z)).re := by
  rw [← T.firstLift_energy]
  apply T.positive
  intro h
  have hu := congrArg (fun x : Space U (Space V W) => x.fst) h
  have hv := congrArg (fun x : Space U (Space V W) => x.snd.fst) h
  apply hz
  apply (WithLp.equiv 2 (U × V)).injective
  exact Prod.ext hu hv

/-- A second positive block problem, with the eliminated W contribution retained. -/
def first : Data U V where
  A := T.firstA
  B := T.firstB
  C := T.tail.short
  selfA := by
    simp [firstA, ContinuousLinearMap.adjoint_comp, T.selfA,
      T.tail.inverseC_adjoint, ContinuousLinearMap.comp_assoc]
  selfC := T.tail.short_adjoint
  positive := T.first_positive

theorem first_short : T.first.short = T.successiveShort := rfl

theorem first_effective (f : U) (g : V) (h : W) :
    T.first.effective (T.firstForcing f h) (T.tail.effective g h) =
      T.successiveForcing f g h := rfl

/-- Exact effective forcing after either order of elimination. -/
theorem forcing_transitivity (f : U) (g : V) (h : W) :
    T.direct.effective f (WithLp.toLp 2 (g,h)) = T.successiveForcing f g h := by
  change f - row T.D T.E (T.direct.inverseC (WithLp.toLp 2 (g,h))) = _
  rw [T.direct_inverseC]
  simp only [Data.solution, row_apply, map_sub, successiveForcing, firstForcing,
    firstB, sub_apply, ContinuousLinearMap.comp_apply]
  abel

/-- The complete short agrees as an operator, not only on a solved vector. -/
theorem short_transitivity : T.direct.short = T.successiveShort := by
  ext u
  change T.A u - row T.D T.E
    (T.direct.inverseC ((row T.D T.E).adjoint u)) = _
  rw [row_adjoint_apply, T.direct_inverseC]
  simp only [Data.solution, row_apply, map_sub]
  simp only [successiveShort, firstA, sub_apply,
    ContinuousLinearMap.comp_apply]
  rw [T.firstB_adjoint]
  simp only [firstB, sub_apply, ContinuousLinearMap.comp_apply]
  change _ = T.A u - T.E (T.tail.inverseC (T.E.adjoint u)) -
    (T.D (T.tail.inverseShort (T.tail.effective (T.D.adjoint u) (T.E.adjoint u))) -
      T.E (T.tail.inverseC (T.tail.B.adjoint
        (T.tail.inverseShort (T.tail.effective (T.D.adjoint u) (T.E.adjoint u))))))
  abel

/-- Strict positivity of the successive short is inherited from the full problem. -/
theorem successiveShort_positive (u : U) (hu : u ≠ 0) :
    0 < (inner ℂ u (T.successiveShort u)).re := by
  rw [← T.short_transitivity]
  exact T.direct.short_positive u hu

/-- The actual inverse used by both eliminations. -/
def successiveInverse : U →L[ℂ] U :=
  (strictlyPositiveEquiv T.successiveShort T.successiveShort_positive).symm.toContinuousLinearMap

 theorem inverse_transitivity (f : U) : T.direct.inverseShort f = T.successiveInverse f := by
  apply strictlyPositive_injective T.successiveShort T.successiveShort_positive
  rw [← T.short_transitivity, T.direct.short_inverseShort, T.short_transitivity]
  exact ((strictlyPositiveEquiv T.successiveShort T.successiveShort_positive).apply_symm_apply f).symm

/-- Coordinates obtained by solving the twice-reduced equation and reconstructing
both complementary coordinates, in reverse elimination order. -/
def successiveSolution (f : U) (g : V) (h : W) : Space U (Space V W) :=
  let u := T.successiveInverse (T.successiveForcing f g h)
  let v := T.tail.inverseShort (T.tail.effective g h - T.firstB.adjoint u)
  let w := T.tail.inverseC (h - T.E.adjoint u - T.tail.B.adjoint v)
  WithLp.toLp 2 (u,WithLp.toLp 2 (v,w))

/-- Full reconstructed vectors coincide, including both complement blocks. -/
theorem solution_transitivity (f : U) (g : V) (h : W) :
    T.direct.solution f (WithLp.toLp 2 (g,h)) = T.successiveSolution f g h := by
  let u := T.successiveInverse (T.successiveForcing f g h)
  have hu : T.direct.inverseShort (T.direct.effective f (WithLp.toLp 2 (g,h))) = u := by
    rw [T.forcing_transitivity, T.inverse_transitivity]
  change WithLp.toLp 2 (_, T.direct.inverseC (_ - (row T.D T.E).adjoint _)) = _
  rw [hu, row_adjoint_apply]
  change WithLp.toLp 2 (u, T.direct.inverseC
    (WithLp.toLp 2 (g - T.D.adjoint u,h-T.E.adjoint u))) = _
  rw [T.direct_inverseC]
  have hv : T.tail.effective (g - T.D.adjoint u) (h - T.E.adjoint u) =
      T.tail.effective g h - T.firstB.adjoint u := by
    rw [T.firstB_adjoint]
    simp only [Data.effective, map_sub]
    abel
  simp only [Data.solution, hv, successiveSolution]
  rfl

/-- Any physical linear observation survives successive elimination exactly. -/
theorem observation_transitivity (f : U) (g : V) (h : W)
    (ell : Space U (Space V W) →L[ℂ] ℂ) :
    ell (T.direct.solution f (WithLp.toLp 2 (g,h))) = ell (T.successiveSolution f g h) := by
  rw [T.solution_transitivity]

end ThreeData
end Riemann.Basic.PositiveSchur
