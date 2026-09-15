import Riemann.Basic.PositiveCompression
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! Physical whitening of injective, nonorthonormal columns. -/
noncomputable section
open scoped InnerProductSpace
namespace Riemann.Basic
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- The raw physical mass is Z*Z. -/
def columnMass (Z : F →L[ℂ] E) : F →L[ℂ] F := Z.adjoint.comp Z

theorem columnMass_positive (Z : F →L[ℂ] E) (hZ : Function.Injective Z)
    (x : F) (hx : x ≠ 0) : 0 < (⟪x, columnMass Z x⟫_ℂ).re := by
  change 0 < (⟪x, Z.adjoint (Z x)⟫_ℂ).re
  rw [Z.adjoint_inner_right]
  exact (re_inner_self_pos (𝕜 := ℂ)).mpr (fun h => hx (hZ (by simpa using h)))

theorem columnMass_nonneg (Z : F →L[ℂ] E) : 0 ≤ columnMass Z := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  exact ContinuousLinearMap.isPositive_one.adjoint_conj Z

/-- The positive square root of the raw mass, defined by mathlib's functional calculus. -/
def columnMassSqrt (Z : F →L[ℂ] E) : F →L[ℂ] F := CFC.sqrt (columnMass Z)

theorem columnMassSqrt_square (Z : F →L[ℂ] E) :
    (columnMassSqrt Z).comp (columnMassSqrt Z) = columnMass Z :=
  CFC.sqrt_mul_sqrt_self _ (columnMass_nonneg Z)

theorem columnMassSqrt_adjoint (Z : F →L[ℂ] E) :
    (columnMassSqrt Z).adjoint = columnMassSqrt Z :=
  ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg _)).isSelfAdjoint

theorem columnMassSqrt_injective (Z : F →L[ℂ] E) (hZ : Function.Injective Z) :
    Function.Injective (columnMassSqrt Z) := by
  intro x y h
  apply strictlyPositive_injective (columnMass Z) (columnMass_positive Z hZ)
  have hh := congrArg (columnMassSqrt Z) h
  change ((columnMassSqrt Z).comp (columnMassSqrt Z)) x =
    ((columnMassSqrt Z).comp (columnMassSqrt Z)) y at hh
  simpa only [columnMassSqrt_square] using hh

def columnMassSqrtEquiv (Z : F →L[ℂ] E) (hZ : Function.Injective Z) : F ≃L[ℂ] F :=
  (LinearEquiv.ofBijective (columnMassSqrt Z).toLinearMap
    ⟨columnMassSqrt_injective Z hZ,
      LinearMap.injective_iff_surjective.mp (columnMassSqrt_injective Z hZ)⟩).toContinuousLinearEquiv

@[simp] theorem columnMassSqrtEquiv_apply (Z : F →L[ℂ] E) (hZ : Function.Injective Z) (x : F) :
    columnMassSqrtEquiv Z hZ x = columnMassSqrt Z x := rfl

/-- Physically whitened columns U=ZM⁻¹ᐟ². -/
def whitenedColumns (Z : F →L[ℂ] E) (hZ : Function.Injective Z) : F →L[ℂ] E :=
  Z.comp (columnMassSqrtEquiv Z hZ).symm.toContinuousLinearMap

theorem whitenedColumns_inner (Z : F →L[ℂ] E) (hZ : Function.Injective Z) (x y : F) :
    ⟪whitenedColumns Z hZ x, whitenedColumns Z hZ y⟫_ℂ = ⟪x,y⟫_ℂ := by
  let T := columnMassSqrtEquiv Z hZ
  change ⟪Z (T.symm x), Z (T.symm y)⟫_ℂ = _
  rw [← Z.adjoint_inner_right]
  change ⟪T.symm x, columnMass Z (T.symm y)⟫_ℂ = _
  rw [← columnMassSqrt_square]
  change ⟪T.symm x, columnMassSqrt Z (columnMassSqrt Z (T.symm y))⟫_ℂ = _
  rw [← columnMassSqrt_adjoint Z, ContinuousLinearMap.adjoint_inner_right, columnMassSqrt_adjoint]
  change ⟪T (T.symm x), T (T.symm y)⟫_ℂ = _
  rw [T.apply_symm_apply, T.apply_symm_apply]

theorem whitenedColumns_reconstruct (Z : F →L[ℂ] E) (hZ : Function.Injective Z) :
    (whitenedColumns Z hZ).comp (columnMassSqrt Z) = Z := by
  ext x
  change Z ((columnMassSqrtEquiv Z hZ).symm (columnMassSqrtEquiv Z hZ x)) = Z x
  rw [ContinuousLinearEquiv.symm_apply_apply]

/-- Raw and whitened pulled-back forms are related by the physical square-root congruence. -/
theorem raw_whitened_congruence (Z : F →L[ℂ] E) (hZ : Function.Injective Z) (H : E →L[ℂ] E) :
    galerkinGram H Z = (columnMassSqrt Z).comp
      ((galerkinGram H (whitenedColumns Z hZ)).comp (columnMassSqrt Z)) := by
  nth_rw 1 [← whitenedColumns_reconstruct Z hZ]
  simp only [galerkinGram, ContinuousLinearMap.adjoint_comp,
    columnMassSqrt_adjoint, ContinuousLinearMap.comp_assoc]

/-- The scalar parameter multiplies the physical mass in raw coordinates. -/
theorem raw_physical_pencil (Z : F →L[ℂ] E) (H : E →L[ℂ] E) (e : ℂ) :
    galerkinGram (H - e • ContinuousLinearMap.id ℂ E) Z =
      galerkinGram H Z - e • columnMass Z := by
  ext x
  simp [galerkinGram, columnMass]

/-- Whitening is a genuine linear isometry in the physical metric. -/
def whitenedIsometry (Z : F →L[ℂ] E) (hZ : Function.Injective Z) : F →ₗᵢ[ℂ] E :=
  (whitenedColumns Z hZ).toLinearMap.isometryOfInner (whitenedColumns_inner Z hZ)

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- Shortening commutes with the physical whitening congruence. The complementary
inverse and its sign are identical in both coordinate systems. -/
theorem raw_short_whitened (Z : F →L[ℂ] E) (hZ : Function.Injective Z)
    (H : E →L[ℂ] E) (J : F →L[ℂ] W) (Cinv : W →L[ℂ] W) :
    galerkinGram H Z - galerkinGram Cinv J =
      (columnMassSqrt Z).comp ((galerkinGram H (whitenedColumns Z hZ) -
        galerkinGram Cinv (J.comp (columnMassSqrtEquiv Z hZ).symm.toContinuousLinearMap)).comp
        (columnMassSqrt Z)) := by
  have hj : (J.comp (columnMassSqrtEquiv Z hZ).symm.toContinuousLinearMap).comp
      (columnMassSqrt Z) = J := by
    ext x
    change J ((columnMassSqrtEquiv Z hZ).symm (columnMassSqrtEquiv Z hZ x)) = J x
    rw [ContinuousLinearEquiv.symm_apply_apply]
  have hg : galerkinGram Cinv J = (columnMassSqrt Z).comp
      ((galerkinGram Cinv (J.comp (columnMassSqrtEquiv Z hZ).symm.toContinuousLinearMap)).comp
        (columnMassSqrt Z)) := by
    nth_rw 1 [← hj]
    simp only [galerkinGram, ContinuousLinearMap.adjoint_comp,
      columnMassSqrt_adjoint, ContinuousLinearMap.comp_assoc]
  rw [raw_whitened_congruence Z hZ H, hg, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_sub]

end Riemann.Basic
