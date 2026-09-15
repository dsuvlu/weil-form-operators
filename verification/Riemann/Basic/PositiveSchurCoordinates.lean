import Riemann.Basic.PositiveSchur

/-! Construct positive Schur data from an actual positive operator and its physical coordinates. -/
noncomputable section
open scoped InnerProductSpace
namespace Riemann.Basic.PositiveSchur
variable {U W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

def firstColumn : U →L[ℂ] Space U W :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ U W).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℂ U).prod (0 : U →L[ℂ] W))
def secondColumn : W →L[ℂ] Space U W :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ U W).symm.toContinuousLinearMap.comp
    ((0 : W →L[ℂ] U).prod (ContinuousLinearMap.id ℂ W))

omit [FiniteDimensional ℂ U] [FiniteDimensional ℂ W] in
@[simp] theorem firstColumn_apply (x : U) : firstColumn (W:=W) x = WithLp.toLp 2 (x,0) := rfl
omit [FiniteDimensional ℂ U] [FiniteDimensional ℂ W] in
@[simp] theorem secondColumn_apply (x : W) : secondColumn (U:=U) x = WithLp.toLp 2 (0,x) := rfl

theorem firstColumn_adjoint (x : Space U W) : firstColumn.adjoint x = x.fst := by
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp

theorem secondColumn_adjoint (x : Space U W) : secondColumn.adjoint x = x.snd := by
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp

def firstBlock (H : Space U W →L[ℂ] Space U W) : U →L[ℂ] U := galerkinGram H firstColumn
def crossBlock (H : Space U W →L[ℂ] Space U W) : W →L[ℂ] U :=
  firstColumn.adjoint.comp (H.comp secondColumn)
def secondBlock (H : Space U W →L[ℂ] Space U W) : W →L[ℂ] W := galerkinGram H secondColumn

/-- Hermitian block entries reconstruct the original physical operator. -/
theorem block_coordinates (H : Space U W →L[ℂ] Space U W) (hH : H.adjoint = H) :
    block (firstBlock H) (crossBlock H) (secondBlock H) = H := by
  ext z
  have hz : z = firstColumn z.fst + secondColumn z.snd := by
    apply (WithLp.equiv 2 (U × W)).injective
    apply Prod.ext <;> simp
  have hb : (crossBlock H).adjoint = secondColumn.adjoint.comp (H.comp firstColumn) := by
    simp [crossBlock, ContinuousLinearMap.adjoint_comp, hH, ContinuousLinearMap.comp_assoc]
  apply (WithLp.equiv 2 (U × W)).injective
  apply Prod.ext
  · change firstBlock H z.fst + crossBlock H z.snd = (H z).fst
    rw [hz, map_add]
    simp [firstBlock, crossBlock, galerkinGram, firstColumn_adjoint]
  · change (crossBlock H).adjoint z.fst + secondBlock H z.snd = (H z).snd
    rw [hb, hz, map_add]
    simp [secondBlock, galerkinGram, secondColumn_adjoint]

/-- A positive physical operator supplies all Schur data; no positive block or
inverse is separately assumed. -/
def Data.ofOperator (H : Space U W →L[ℂ] Space U W) (hH : H.adjoint = H)
    (hp : ∀ z, z ≠ 0 → 0 < (⟪z, H z⟫_ℂ).re) : Data U W where
  A := firstBlock H
  B := crossBlock H
  C := secondBlock H
  selfA := galerkinGram_selfAdjoint H firstColumn hH
  selfC := galerkinGram_selfAdjoint H secondColumn hH
  positive z hz := by rw [block_coordinates H hH]; exact hp z hz

@[simp] theorem Data.ofOperator_block (H : Space U W →L[ℂ] Space U W) (hH : H.adjoint = H)
    (hp : ∀ z, z ≠ 0 → 0 < (⟪z, H z⟫_ℂ).re) :
    block (Data.ofOperator H hH hp).A (Data.ofOperator H hH hp).B (Data.ofOperator H hH hp).C = H :=
  block_coordinates H hH

end Riemann.Basic.PositiveSchur
