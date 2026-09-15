import Riemann.CCM.NativeHighCoordinateDictionary

/-! The BL source response and inverse mass energy on the physical complex high
section. Real columns are embedded in the complex space; it is not restricted
to real coefficients. -/
noncomputable section
open scoped InnerProductSpace BigOperators
namespace Riemann.CCM.Native
open Riemann.Basic Riemann.Capacity Matrix
variable {N J : ℕ}

def realHighCoordinates (t : HighIndex N J → ℝ) : HighCoordinates N J :=
  WithLp.toLp 2 (fun j => (t j : ℂ))

lemma highMatrixOperator_real (R : Matrix (HighIndex N J) (HighIndex N J) ℝ)
    (t : HighIndex N J → ℝ) :
    highMatrixOperator (R.map Complex.ofReal) (realHighCoordinates t) =
      realHighCoordinates (R *ᵥ t) := by
  ext j
  simp [highMatrixOperator_apply, realHighCoordinates, Matrix.mulVec, dotProduct]

/-- The source is the physical projection of Dη, with its already proved
normalization √2 ω_j/√L. -/
def nativeHighSource (L : ℝ) (N J : ℕ) : oddHighSection N J :=
  oddHighProjection N J (derivative L (endpointVector N L))

lemma highCoordinateEquiv_source (L : ℝ) :
    (highCoordinateEquiv N J).symm (nativeHighSource L N J) =
      realHighCoordinates (highRealZeta L) := by
  ext j
  rw [highCoordinateEquiv_symm_inner]
  simp only [nativeHighSource, oddHighProjection, ContinuousLinearMap.adjoint_inner_right]
  change ⟪(highCoordinateEquiv N J (EuclideanSpace.single j 1) : Section N),
    derivative L (endpointVector N L)⟫_ℂ = (highRealZeta L j : ℂ)
  rw [highCoordinateEquiv_single, oddHighVector_zeta_pairing]

lemma highCoordinateEquiv_massInverse (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (x : HighCoordinates N J) :
    (highCoordinateEquiv N J).symm
      (positiveInverse (nativeHighMass C A J) (nativeHighMass_positive C L hL A J)
        (highCoordinateEquiv N J x)) =
      highMatrixOperator ((highRealMass C L hL A J)⁻¹.map Complex.ofReal) x := by
  let T := highRealMass C L hL A J
  have hT : T.det ≠ 0 := (highRealMass_pos C L hL A J).det_pos.ne'
  apply (highCoordinateEquiv N J).injective
  apply strictlyPositive_injective (nativeHighMass C A J) (nativeHighMass_positive C L hL A J)
  simp only [LinearIsometryEquiv.apply_symm_apply]
  have hleft := positiveInverse_left (E := oddHighSection N J) (nativeHighMass C A J)
    (nativeHighMass_positive C L hL A J) (highCoordinateEquiv N J x)
  rw [hleft]
  apply (highCoordinateEquiv N J).symm.injective
  rw [highCoordinateEquiv_mass C L hL A, LinearIsometryEquiv.symm_apply_apply]
  change x = highMatrixOperator (T.map Complex.ofReal)
    (highMatrixOperator (T⁻¹.map Complex.ofReal) x)
  rw [← ContinuousLinearMap.comp_apply, ← highMatrixOperator_mul]
  have hm : T.map Complex.ofReal * T⁻¹.map Complex.ofReal = 1 := by
    change Complex.ofRealHom.mapMatrix T * Complex.ofRealHom.mapMatrix T⁻¹ = 1
    rw [← map_mul, Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.mpr hT), map_one]
  rw [hm, highMatrixOperator_one]
  rfl

/-- The high free resolvent response, transported by the physical unitary chart.
The following theorem identifies its defining native resolvent equation. -/
def nativeHighSourceResponse (L : ℝ) (N J : ℕ) (s : ℝ) : oddHighSection N J :=
  highCoordinateEquiv N J (realHighCoordinates
    ((highRealFree L N J + s • 1)⁻¹ *ᵥ highRealZeta L))

lemma nativeHighSourceResponse_equation (L : ℝ) (hL : 0 < L) (N J : ℕ)
    {s : ℝ} (hs : 0 < s) :
    (oddHighFree (N := N) L J + (s : ℂ) • ContinuousLinearMap.id ℂ (oddHighSection N J))
      (nativeHighSourceResponse L N J s) = nativeHighSource L N J := by
  apply (highCoordinateEquiv N J).symm.injective
  rw [nativeHighSourceResponse, highCoordinateEquiv_freePencil,
    highMatrixOperator_real, highCoordinateEquiv_source]
  congr 1
  have hp : (highRealFree L N J + s • 1).det ≠ 0 :=
    ((highRealFree_pos hL).add ((Matrix.PosDef.one :
      (1 : Matrix (HighIndex N J) (HighIndex N J) ℝ).PosDef).smul hs)).det_pos.ne'
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp),
    Matrix.one_mulVec]

/-- The physical free response is the unique solution of its native resolvent equation. -/
lemma nativeHighSourceResponse_unique (L : ℝ) (hL : 0 < L) (N J : ℕ)
    {s : ℝ} (hs : 0 < s) (x : oddHighSection N J)
    (hx : (oddHighFree (N := N) L J + (s : ℂ) • ContinuousLinearMap.id ℂ (oddHighSection N J)) x =
      nativeHighSource L N J) : x = nativeHighSourceResponse L N J s := by
  let T := highRealFree L N J + s • 1
  have hT : T.det ≠ 0 := ((highRealFree_pos hL).add ((Matrix.PosDef.one :
      (1 : Matrix (HighIndex N J) (HighIndex N J) ℝ).PosDef).smul hs)).det_pos.ne'
  have ht : highMatrixOperator (T.map Complex.ofReal) ((highCoordinateEquiv N J).symm x) =
      realHighCoordinates (highRealZeta L) := by
    rw [← highCoordinateEquiv_freePencil, LinearIsometryEquiv.apply_symm_apply,
      hx, highCoordinateEquiv_source]
  have hc := congrArg (highMatrixOperator (T⁻¹.map Complex.ofReal)) ht
  rw [← ContinuousLinearMap.comp_apply, ← highMatrixOperator_mul] at hc
  have hm : T⁻¹.map Complex.ofReal * T.map Complex.ofReal = 1 := by
    change Complex.ofRealHom.mapMatrix T⁻¹ * Complex.ofRealHom.mapMatrix T = 1
    rw [← map_mul, Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hT), map_one]
  rw [hm, highMatrixOperator_one, highMatrixOperator_real] at hc
  apply (highCoordinateEquiv N J).symm.injective
  simpa only [nativeHighSourceResponse, LinearIsometryEquiv.symm_apply_apply,
    ContinuousLinearMap.id_apply, T] using hc

/-- The inverse mass energy is evaluated on the actual complex high section. -/
def nativeHighSourceEnergy (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (s : ℝ) : ℝ :=
  (⟪nativeHighSourceResponse L N J s,
    positiveInverse (nativeHighMass C A J) (nativeHighMass_positive C L hL A J)
      (nativeHighSourceResponse L N J s)⟫_ℂ).re

/-- The real BL source energy and the physical complex high energy coincide. -/
theorem nativeHigh_sourceEnergy_eq (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (hJN : J < N) (s : ℝ) :
    nativeHighSourceEnergy C L hL A J s =
      (nativeInverseEnergyData C L hL A J hJN).inverseEnergy s := by
  let t := (highRealFree L N J + s • 1)⁻¹ *ᵥ highRealZeta L
  have hi := highCoordinateEquiv_massInverse C L hL A (realHighCoordinates t)
  have hinner := LinearIsometryEquiv.inner_map_map (𝕜 := ℂ) (highCoordinateEquiv N J).symm
    (nativeHighSourceResponse L N J s)
    (positiveInverse (nativeHighMass C A J) (nativeHighMass_positive C L hL A J)
      (nativeHighSourceResponse L N J s))
  simp only [nativeHighSourceResponse, LinearIsometryEquiv.symm_apply_apply] at hinner
  change ⟪realHighCoordinates t, (highCoordinateEquiv N J).symm
    (positiveInverse (nativeHighMass C A J) (nativeHighMass_positive C L hL A J)
      (highCoordinateEquiv N J (realHighCoordinates t)))⟫_ℂ = _ at hinner
  rw [hi] at hinner
  have he := complexification_energy ((highRealMass C L hL A J)⁻¹) t
  have hr := congrArg Complex.re (hinner.symm.trans he)
  exact hr

lemma nativeHigh_sourceEnergy_pos (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (hJN : J < N) (s : ℝ) (hs : 0 < s) :
    0 < nativeHighSourceEnergy C L hL A J s := by
  rw [nativeHigh_sourceEnergy_eq C L hL A J hJN]
  exact (nativeInverseEnergyData C L hL A J hJN).inverseEnergy_pos hs

/-- BL's actual logarithmic derivative expressed with the physical native high mean and energy. -/
theorem nativeHigh_softMean_sourceEnergy_identity (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (hJN : J < N) (s : ℝ) (hs : 0 < s) :
    (nativeHighPencil C L hL A J).softMean s hs =
      (nativeInverseEnergyData C L hL A J hJN).freeMean s +
      (nativeInverseEnergyData C L hL A J hJN).boundaryCorrection s +
      s / 2 * deriv (fun t => Real.log (nativeHighSourceEnergy C L hL A J t)) s := by
  rw [nativeHigh_softMean_eq C L hL A J hJN s hs]
  simp only [nativeHigh_sourceEnergy_eq C L hL A J hJN]
  exact (nativeInverseEnergyData C L hL A J hJN).highMean_inverseEnergy_identity hs

/-- Exact BL anchors in the BI native high-capacity and physical source-energy notation. -/
theorem nativeHigh_fixed_anchor_capacity_energy_bounds (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (hJN : J < N) :
    Real.log 9 * ((nativeHighPencil C L hL A J).softMean (1/16) (by norm_num) - 1) ≤
      (nativeInverseEnergyData C L hL A J hJN).freeLogRatio (1/16) (9/16) +
        (1/2 : ℝ) * Real.log (nativeHighSourceEnergy C L hL A J (9/16) /
          nativeHighSourceEnergy C L hL A J (1/16)) ∧
    (nativeInverseEnergyData C L hL A J hJN).freeLogRatio (1/16) (9/16) +
        (1/2 : ℝ) * Real.log (nativeHighSourceEnergy C L hL A J (9/16) /
          nativeHighSourceEnergy C L hL A J (1/16)) ≤
      8 * (nativeHighPencil C L hL A J).softMean (1/16) (by norm_num) := by
  rw [nativeHigh_softMean_eq C L hL A J hJN (1/16) (by norm_num)]
  simp only [nativeHigh_sourceEnergy_eq C L hL A J hJN]
  exact (nativeInverseEnergyData C L hL A J hJN).fixed_anchor_capacity_energy_bounds

end Riemann.CCM.Native
