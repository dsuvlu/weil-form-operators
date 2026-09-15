import Riemann.CCM.NativeHighCoordinateEquiv
import Riemann.Basic.RealMatrixComplexification
import Riemann.Capacity.SoftMeanGeometry

/-! Exact operator and scalar dictionaries for the actual complex high section. -/
noncomputable section
open scoped InnerProductSpace BigOperators
namespace Riemann.CCM.Native
open Riemann.Basic Riemann.Capacity
variable {N J : ℕ}

lemma highMatrixOperator_mul (A B : Matrix (HighIndex N J) (HighIndex N J) ℂ) :
    highMatrixOperator (A * B) = (highMatrixOperator A).comp (highMatrixOperator B) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, highMatrixOperator_apply, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma highMatrixOperator_one : highMatrixOperator (1 : Matrix (HighIndex N J) (HighIndex N J) ℂ) =
    ContinuousLinearMap.id ℂ _ := by
  ext x i
  simp [highMatrixOperator_apply, Matrix.one_apply]

lemma highCoordinateEquiv_pencil (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (s : ℝ) (x : HighCoordinates N J) :
    (highCoordinateEquiv N J).symm ((nativeHighPencil C L hL A J).pencil s
      (highCoordinateEquiv N J x)) =
      highMatrixOperator (((highRealEnergy C L hL A J) + s • highRealMass C L hL A J).map
        Complex.ofReal) x := by
  change (highCoordinateEquiv N J).symm
    (nativeHighEnergy C L A J (highCoordinateEquiv N J x) +
      (s : ℂ) • nativeHighMass C A J (highCoordinateEquiv N J x)) = _
  rw [map_add, map_smul, highCoordinateEquiv_energy C L hL A,
    highCoordinateEquiv_mass C L hL A]
  ext i
  simp [highMatrixOperator_apply, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

lemma highCoordinateEquiv_inverse (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (s : ℝ) (hs : 0 < s) (x : HighCoordinates N J) :
    (highCoordinateEquiv N J).symm
      (positiveInverse ((nativeHighPencil C L hL A J).pencil s)
        ((nativeHighPencil C L hL A J).pencil_positive s hs) (highCoordinateEquiv N J x)) =
      highMatrixOperator (((highRealEnergy C L hL A J) + s • highRealMass C L hL A J)⁻¹.map
        Complex.ofReal) x := by
  let T := highRealEnergy C L hL A J + s • highRealMass C L hL A J
  have hT : T.det ≠ 0 := (Matrix.PosDef.add (highRealEnergy_pos C L hL A J)
    ((highRealMass_pos C L hL A J).smul hs)).det_pos.ne'
  apply (highCoordinateEquiv N J).injective
  apply strictlyPositive_injective ((nativeHighPencil C L hL A J).pencil s)
    ((nativeHighPencil C L hL A J).pencil_positive s hs)
  simp only [LinearIsometryEquiv.apply_symm_apply, positiveInverse_left]
  apply (highCoordinateEquiv N J).symm.injective
  rw [highCoordinateEquiv_pencil, LinearIsometryEquiv.symm_apply_apply]
  change x = highMatrixOperator (T.map Complex.ofReal)
    (highMatrixOperator (T⁻¹.map Complex.ofReal) x)
  rw [← ContinuousLinearMap.comp_apply, ← highMatrixOperator_mul]
  have hm : T.map Complex.ofReal * T⁻¹.map Complex.ofReal = 1 := by
    change Complex.ofRealHom.mapMatrix T * Complex.ofRealHom.mapMatrix T⁻¹ = 1
    rw [← map_mul, Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.mpr hT), map_one]
  rw [hm, highMatrixOperator_one]
  rfl

/-- The actual inverse-mass operator is similar to the complexified real matrix. -/
lemma highCoordinateEquiv_inverseMass (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (s : ℝ) (hs : 0 < s) (x : HighCoordinates N J) :
    (highCoordinateEquiv N J).symm
      (positiveInverse ((nativeHighPencil C L hL A J).pencil s)
        ((nativeHighPencil C L hL A J).pencil_positive s hs)
        (nativeHighMass C A J (highCoordinateEquiv N J x))) =
      highMatrixOperator ((((highRealEnergy C L hL A J + s • highRealMass C L hL A J)⁻¹) *
        highRealMass C L hL A J).map Complex.ofReal) x := by
  have hm := highCoordinateEquiv_mass C L hL A x
  have he := congrArg (highCoordinateEquiv N J) hm
  simp only [LinearIsometryEquiv.apply_symm_apply] at he
  rw [he, highCoordinateEquiv_inverse C L hL A s hs]
  rw [← ContinuousLinearMap.comp_apply, ← highMatrixOperator_mul]
  congr 1
  congr 1
  exact (map_mul (Complex.ofRealHom.mapMatrix : Matrix (HighIndex N J) (HighIndex N J) ℝ →+*
    Matrix (HighIndex N J) (HighIndex N J) ℂ) _ _).symm

/-- The complex trace and the real BL trace are equal under scalar extension. -/
theorem nativeHigh_inverseMassTrace (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (s : ℝ) (hs : 0 < s) :
    inverseMassTrace ((nativeHighPencil C L hL A J).pencil s)
      ((nativeHighPencil C L hL A J).pencil_positive s hs) (nativeHighMass C A J) =
      (((highRealEnergy C L hL A J + s • highRealMass C L hL A J)⁻¹ *
        highRealMass C L hL A J).trace : ℝ) := by
  let T := ((positiveInverse ((nativeHighPencil C L hL A J).pencil s)
    ((nativeHighPencil C L hL A J).pencil_positive s hs)).comp (nativeHighMass C A J)).toLinearMap
  have hc := LinearMap.trace_conj' T (highCoordinateEquiv N J).symm.toLinearEquiv
  have he : (highCoordinateEquiv N J).symm.toLinearEquiv.conj T =
      (highMatrixOperator (((highRealEnergy C L hL A J + s • highRealMass C L hL A J)⁻¹ *
        highRealMass C L hL A J).map Complex.ofReal)).toLinearMap := by
    apply LinearMap.ext
    intro x
    exact highCoordinateEquiv_inverseMass C L hL A s hs x
  rw [he] at hc
  change LinearMap.trace ℂ _ T = _
  rw [← hc]
  change LinearMap.trace ℂ _ (Matrix.toEuclideanLin _) = _
  rw [trace_toEuclideanLin]
  simp [Matrix.trace]

/-- BI high soft mean equals BL high mean for the actual native family. -/
theorem nativeHigh_softMean_eq (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (hJN : J < N) (s : ℝ) (hs : 0 < s) :
    (nativeHighPencil C L hL A J).softMean s hs =
      (nativeInverseEnergyData C L hL A J hJN).highMean s := by
  rw [PositivePencil.softMean]
  change s * (inverseMassTrace ((nativeHighPencil C L hL A J).pencil s)
    ((nativeHighPencil C L hL A J).pencil_positive s hs) (nativeHighMass C A J)).re = _
  rw [nativeHigh_inverseMassTrace C L hL A s hs]
  rfl

lemma highCoordinate_det_eq (T : oddHighSection N J →L[ℂ] oddHighSection N J)
    (R : Matrix (HighIndex N J) (HighIndex N J) ℝ)
    (hT : ∀ x, (highCoordinateEquiv N J).symm (T (highCoordinateEquiv N J x)) =
      highMatrixOperator (R.map Complex.ofReal) x) :
    LinearMap.det T.toLinearMap = (R.det : ℂ) := by
  have hc := LinearMap.det_conj T.toLinearMap (highCoordinateEquiv N J).symm.toLinearEquiv
  change LinearMap.det ((highCoordinateEquiv N J).symm.toLinearEquiv.conj T.toLinearMap) = _ at hc
  have he : (highCoordinateEquiv N J).symm.toLinearEquiv.conj T.toLinearMap =
      (highMatrixOperator (R.map Complex.ofReal)).toLinearMap := by
    apply LinearMap.ext
    exact hT
  rw [he] at hc
  rw [← hc]
  change LinearMap.det (Matrix.toEuclideanLin _) = _
  rw [det_toEuclideanLin]
  exact (RingHom.map_det Complex.ofRealHom R).symm

lemma nativeHigh_pencil_det (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (s : ℝ) :
    LinearMap.det ((nativeHighPencil C L hL A J).pencil s).toLinearMap =
      ((highRealEnergy C L hL A J + s • highRealMass C L hL A J).det : ℂ) :=
  highCoordinate_det_eq _ _ (highCoordinateEquiv_pencil C L hL A s)

lemma nativeHigh_mass_det (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) :
    LinearMap.det (nativeHighMass C A J).toLinearMap =
      ((highRealMass C L hL A J).det : ℂ) :=
  highCoordinate_det_eq _ _ (highCoordinateEquiv_mass C L hL A)

lemma highCoordinateEquiv_freePencil (L s : ℝ) (x : HighCoordinates N J) :
    (highCoordinateEquiv N J).symm
      ((oddHighFree (N := N) L J + (s : ℂ) • ContinuousLinearMap.id ℂ (oddHighSection N J)) (highCoordinateEquiv N J x)) =
      highMatrixOperator ((highRealFree L N J + s • 1).map Complex.ofReal) x := by
  change (highCoordinateEquiv N J).symm (oddHighFree L J (highCoordinateEquiv N J x) +
    (s : ℂ) • highCoordinateEquiv N J x) = _
  rw [highCoordinateEquiv_free, map_add, map_smul, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]
  have hm : (highRealFree L N J + s • 1).map Complex.ofReal =
      Matrix.diagonal (fun i : HighIndex N J => ((highFrequency L i ^ 2 + s : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j <;> simp [highRealFree, h]
  rw [hm]
  ext i
  simp [highMatrixOperator_apply, highRealFree, Matrix.diagonal_apply, add_mul]

lemma nativeHigh_freePencil_det (L s : ℝ) :
    LinearMap.det (oddHighFree L J + (s : ℂ) • ContinuousLinearMap.id ℂ (oddHighSection N J)).toLinearMap =
      ((highRealFree L N J + s • 1).det : ℂ) :=
  highCoordinate_det_eq _ _ (highCoordinateEquiv_freePencil L s)

/-- Actual native operator determinant quotient, equal to the BL real quotient. -/
theorem nativeHigh_determinantRatio_eq (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (hJN : J < N) (s : ℝ) :
    LinearMap.det ((nativeHighPencil C L hL A J).pencil s).toLinearMap /
      (LinearMap.det (nativeHighMass C A J).toLinearMap *
        LinearMap.det (oddHighFree L J + (s : ℂ) • ContinuousLinearMap.id ℂ (oddHighSection N J)).toLinearMap) =
      ((nativeInverseEnergyData C L hL A J hJN).determinantRatio s : ℂ) := by
  rw [nativeHigh_pencil_det, nativeHigh_mass_det C L hL A, nativeHigh_freePencil_det]
  simp only [InverseEnergyData.determinantRatio, InverseEnergyData.pencil,
    InverseEnergyData.freePencil, nativeInverseEnergyData, Complex.ofReal_div, Complex.ofReal_mul]

/-- The pre-existing real synthesis embeds as the real form of the complex coordinates. -/
lemma highCoordinateEquiv_realSynthesis (x : HighIndex N J → ℝ) :
    (highCoordinateEquiv N J (WithLp.toLp 2 (fun j => (x j : ℂ))) : Section N) =
      oddHighRealSynthesis x := by
  rw [highCoordinateEquiv_apply]
  rfl

/-- Being real is an additional coordinate condition, not a restriction on the complex carrier. -/
lemma highCoordinateEquiv_realForm (x : HighCoordinates N J) :
    (∀ i, ((highCoordinateEquiv N J x : Section N) i).im = 0) ↔
      ∀ j, (x j).im = 0 := by
  constructor
  · intro hx j
    have h := inner_real_of_coordinates (oddHighVector j) (highCoordinateEquiv N J x)
      (oddHighVector_real j) hx
    rw [← highCoordinateEquiv_symm_apply, LinearIsometryEquiv.symm_apply_apply] at h
    exact h
  · intro hx i
    rw [highCoordinateEquiv_apply]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
    rw [Complex.im_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Complex.mul_im, hx, oddHighVector_real]
    ring

end Riemann.CCM.Native
