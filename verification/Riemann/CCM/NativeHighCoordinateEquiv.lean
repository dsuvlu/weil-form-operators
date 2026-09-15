import Riemann.CCM.NativeInverseEnergy
import Riemann.CCM.NativeCapacity

/-!
# The complex odd high section in its physical paired coordinates

The coefficients are complex. The real BL matrices are complexified after the
physical coordinate equivalence is proved; no real-form restriction is imposed
on vectors in the native complex section.
-/
noncomputable section
open scoped InnerProductSpace BigOperators
namespace Riemann.CCM.Native
variable {N J : ℕ}

abbrev HighCoordinates (N J : ℕ) := EuclideanSpace ℂ (HighIndex N J)

/-- Complex synthesis in the unchanged physical paired columns. -/
def highSynthesisLinear (N J : ℕ) : HighCoordinates N J →ₗ[ℂ] Section N where
  toFun x := ∑ j, x j • oddHighVector j
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_smul, Finset.smul_sum]

@[simp] theorem highSynthesisLinear_apply (x : HighCoordinates N J) :
    highSynthesisLinear N J x = ∑ j, x j • oddHighVector j := rfl

@[simp] theorem highSynthesisLinear_single (j : HighIndex N J) :
    highSynthesisLinear N J (EuclideanSpace.single j 1) = oddHighVector j := by
  simp [highSynthesisLinear]

def highSynthesisIsometry (N J : ℕ) : HighCoordinates N J →ₗᵢ[ℂ] Section N :=
  (highSynthesisLinear N J).isometryOfInner (by
    intro x y
    change ⟪∑ j, x j • oddHighVector j, ∑ j, y j • oddHighVector j⟫_ℂ = ⟪x,y⟫_ℂ
    rw [sum_inner]
    simp only [inner_smul_left, (@oddHighVector_orthonormal N J).inner_right_fintype]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm])

@[simp] theorem highSynthesisIsometry_apply (x : HighCoordinates N J) :
    highSynthesisIsometry N J x = ∑ j, x j • oddHighVector j := rfl

lemma oddHighVector_mem (j : HighIndex N J) : oddHighVector j ∈ oddHighSection N J := by
  constructor
  · exact oddHighVector_odd j
  · intro i hi
    have hp : i ≠ highPositiveIndex j := by
      intro h
      subst i
      simp only [mode_highPositiveIndex, Int.natAbs_natCast] at hi
      omega
    have hn : i ≠ (highPositiveIndex j).rev := by
      intro h
      subst i
      simp only [mode_rev, mode_highPositiveIndex, Int.natAbs_neg, Int.natAbs_natCast] at hi
      omega
    simp [oddHighVector_apply, hp, hn]

lemma highSynthesis_mem (x : HighCoordinates N J) :
    highSynthesisIsometry N J x ∈ oddHighSection N J := by
  rw [highSynthesisIsometry_apply]
  apply Submodule.sum_mem
  intro j hj
  exact (oddHighSection N J).smul_mem (x j) (oddHighVector_mem j)

/-- The synthesized vector with its actual native high-space membership. -/
def highSynthesis (N J : ℕ) : HighCoordinates N J →ₗᵢ[ℂ] oddHighSection N J :=
  { toLinearMap := (highSynthesisIsometry N J).toLinearMap.codRestrict (oddHighSection N J) highSynthesis_mem
    norm_map' := (highSynthesisIsometry N J).norm_map }

@[simp] theorem highSynthesis_coe (x : HighCoordinates N J) :
    ((highSynthesis N J x : oddHighSection N J) : Section N) = ∑ j, x j • oddHighVector j := rfl

lemma highSynthesis_positive (x : HighCoordinates N J) (i : HighIndex N J) :
    (highSynthesis N J x : Section N) (highPositiveIndex i) =
      x i * ((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [highSynthesis_coe, highPositiveIndex_ne_rev, highPositiveIndex_injective.eq_iff]

lemma odd_high_ext {x y : oddHighSection N J}
    (h : ∀ j : HighIndex N J, (x : Section N) (highPositiveIndex j) =
      (y : Section N) (highPositiveIndex j)) : x = y := by
  apply Subtype.ext
  ext i
  by_cases hi : (mode i).natAbs ≤ J
  · rw [x.property.2 i hi, y.property.2 i hi]
  · have hab : (mode i).natAbs ≤ N := by
      simp only [mode]
      have := i.isLt
      omega
    let j : HighIndex N J := ⟨⟨(mode i).natAbs, by omega⟩, by change J < (mode i).natAbs; omega⟩
    have hj := h j
    have he : i = highPositiveIndex j ∨ i = (highPositiveIndex j).rev := by
      by_cases hs : 0 ≤ mode i
      · left
        apply mode_injective N
        simp only [mode_highPositiveIndex, j]
        exact (Int.natAbs_of_nonneg hs).symm
      · right
        apply mode_injective N
        simp only [mode_rev, mode_highPositiveIndex, j]
        omega
    rcases he with hp | hn
    · rw [hp]
      exact hj
    · rw [hn]
      have hx := congrArg (fun v : Section N => v (highPositiveIndex j)) x.property.1
      have hy := congrArg (fun v : Section N => v (highPositiveIndex j)) y.property.1
      simp only [reflection_apply, PiLp.neg_apply] at hx hy
      rw [hj] at hx
      exact hx.trans hy.symm

/-- The paired complex coefficients recover every native odd high vector. -/
theorem highSynthesis_surjective (N J : ℕ) : Function.Surjective (highSynthesis N J) := by
  intro x
  let c : HighCoordinates N J := WithLp.toLp 2 (fun j => (Real.sqrt 2 : ℂ) * (x : Section N) (highPositiveIndex j))
  refine ⟨c, odd_high_ext (fun j => ?_)⟩
  rw [highSynthesis_positive]
  change ((Real.sqrt 2 : ℂ) * (x : Section N) (highPositiveIndex j)) * (Real.sqrt 2 : ℂ)⁻¹ = _
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by norm_num
  field_simp

/-- Actual physical complex coordinate equivalence, valid also for empty high spaces. -/
def highCoordinateEquiv (N J : ℕ) : HighCoordinates N J ≃ₗᵢ[ℂ] oddHighSection N J :=
  LinearIsometryEquiv.ofSurjective (highSynthesis N J) (highSynthesis_surjective N J)

@[simp] theorem highCoordinateEquiv_apply (x : HighCoordinates N J) :
    ((highCoordinateEquiv N J x : oddHighSection N J) : Section N) = ∑ j, x j • oddHighVector j := rfl

@[simp] theorem highCoordinateEquiv_single (j : HighIndex N J) :
    ((highCoordinateEquiv N J (EuclideanSpace.single j 1) : oddHighSection N J) : Section N) =
      oddHighVector j := by simp [highCoordinateEquiv_apply]

lemma highCoordinateEquiv_symm_inner (x : oddHighSection N J) (j : HighIndex N J) :
    (highCoordinateEquiv N J).symm x j =
      ⟪highCoordinateEquiv N J (EuclideanSpace.single j 1), x⟫_ℂ := by
  have h := (highCoordinateEquiv N J).inner_map_map (𝕜 := ℂ) (E := HighCoordinates N J) (E' := oddHighSection N J) (EuclideanSpace.single j 1)
    ((highCoordinateEquiv N J).symm x)
  simpa only [LinearIsometryEquiv.apply_symm_apply, EuclideanSpace.inner_single_left,
    map_one, one_mul] using h.symm

lemma highCoordinateEquiv_symm_apply (x : oddHighSection N J) (j : HighIndex N J) :
    (highCoordinateEquiv N J).symm x j = ⟪oddHighVector j, (x : Section N)⟫_ℂ := by
  rw [highCoordinateEquiv_symm_inner]
  change ⟪(highCoordinateEquiv N J (EuclideanSpace.single j 1) : Section N), (x : Section N)⟫_ℂ = _
  rw [highCoordinateEquiv_single]

/-- The matrix operator in Euclidean complex high coordinates. -/
def highMatrixOperator (A : Matrix (HighIndex N J) (HighIndex N J) ℂ) :
    HighCoordinates N J →L[ℂ] HighCoordinates N J := A.toEuclideanLin.toContinuousLinearMap

@[simp] theorem highMatrixOperator_apply (A : Matrix (HighIndex N J) (HighIndex N J) ℂ)
    (x : HighCoordinates N J) (i : HighIndex N J) :
    highMatrixOperator A x i = ∑ j, A i j * x j := rfl

/-- The squared free operator is genuinely diagonal in the paired coordinates. -/
lemma highCoordinateEquiv_free (L : ℝ) (x : HighCoordinates N J) :
    oddHighFree L J (highCoordinateEquiv N J x) =
      highCoordinateEquiv N J (highMatrixOperator ((highRealFree L N J).map Complex.ofReal) x) := by
  apply Subtype.ext
  change derivative L (derivative L (highCoordinateEquiv N J x : Section N)) = _
  simp only [highCoordinateEquiv_apply, map_sum, map_smul, oddHighVector_squaredDerivative]
  apply Finset.sum_congr rfl
  intro j hj
  simp [highMatrixOperator_apply, highRealFree, Matrix.diagonal_apply]
  rw [smul_comm]
  change ((highFrequency L j ^ 2 : ℝ) : ℂ) • (x j • oddHighVector j) = _
  simp [smul_smul]

lemma highCoordinate_conjugate_apply (T : Section N →L[ℂ] Section N)
    (x : HighCoordinates N J) (i : HighIndex N J) :
    (highCoordinateEquiv N J).symm
      (Riemann.Capacity.columnEnergy T (oddHighInclusion N J) (highCoordinateEquiv N J x)) i =
      ∑ j, ⟪oddHighVector i, T (oddHighVector j)⟫_ℂ * x j := by
  rw [highCoordinateEquiv_symm_inner, Riemann.Capacity.columnEnergy_inner]
  change ⟪(highCoordinateEquiv N J (EuclideanSpace.single i 1) : Section N),
    T (highCoordinateEquiv N J x : Section N)⟫_ℂ = _
  rw [highCoordinateEquiv_single, highCoordinateEquiv_apply]
  simp [map_sum, map_smul, inner_sum, inner_smul_right, mul_comm]

/-- Exact complexification of the physical high mass. -/
lemma highCoordinateEquiv_mass (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (x : HighCoordinates N J) :
    (highCoordinateEquiv N J).symm (nativeHighMass C A J (highCoordinateEquiv N J x)) =
      highMatrixOperator ((highRealMass C L hL A J).map Complex.ofReal) x := by
  ext i
  rw [nativeHighMass, highCoordinate_conjugate_apply, highMatrixOperator_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.map_apply, highRealMass_complex_entry]
  rfl

/-- Exact complexification of the physical differentiated high energy. -/
lemma highCoordinateEquiv_energy (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (x : HighCoordinates N J) :
    (highCoordinateEquiv N J).symm (nativeHighEnergy C L A J (highCoordinateEquiv N J x)) =
      highMatrixOperator ((highRealEnergy C L hL A J).map Complex.ofReal) x := by
  ext i
  rw [highCoordinateEquiv_symm_inner, nativeHighEnergy, Riemann.Capacity.columnEnergy_inner]
  change ⟪derivative L (highCoordinateEquiv N J (EuclideanSpace.single i 1) : Section N),
    nativeShifted C A (derivative L (highCoordinateEquiv N J x : Section N))⟫_ℂ = _
  rw [highCoordinateEquiv_single, highCoordinateEquiv_apply, highMatrixOperator_apply]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.map_apply, highRealEnergy_complex_entry]
  exact mul_comm _ _

end Riemann.CCM.Native
