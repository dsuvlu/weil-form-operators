import Riemann.CCM.OddGroundResponse
import Riemann.CCM.FourierCharacteristic

/-! The existing entire characteristic and the full native odd inverse-energy
pencil have the same finite determinant factor. -/
noncomputable section
open scoped InnerProductSpace BigOperators
open Matrix
namespace Riemann.CCM.Native
variable {N J : ℕ}

lemma odd_pair_resolvent (L : ℝ) (hL : 0 < L) (j : HighIndex N J) {a : ℝ} (ha : 0 < a) :
    ((Real.sqrt L)⁻¹ : ℂ) * ∑ i, oddHighVector j i /
      ((frequency L i : ℂ) - Complex.I * (a : ℂ)) =
    (highRealZeta L j / (highFrequency L j ^ 2 + a ^ 2) : ℝ) := by
  have hw : ((highFrequency L j : ℂ) - Complex.I * (a : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hn : (-(highFrequency L j : ℂ) - Complex.I * (a : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hd : (highFrequency L j ^ 2 + a ^ 2 : ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  simp only [oddHighVector_apply, mul_sub, sub_div, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, ite_div, zero_div, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, frequency_rev, Complex.ofReal_neg]
  rw [← mul_sub]
  change ((Real.sqrt L)⁻¹ : ℂ) *
    (((Real.sqrt 2)⁻¹ : ℂ) / ((highFrequency L j : ℂ) - Complex.I * a) -
    ((Real.sqrt 2)⁻¹ : ℂ) / (-(highFrequency L j : ℂ) - Complex.I * a)) = _
  simp only [highRealZeta, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_pow]
  have hc : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast hs2
  have hLs : (Real.sqrt L : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hL).ne'
  have h2s : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast hs
  have hdc : (highFrequency L j : ℂ)^2 + (a : ℂ)^2 ≠ 0 := by exact_mod_cast hd
  field_simp [hw, hn, hLs, h2s, hdc]
  ring_nf
  simp only [Complex.I_sq, hc]
  ring

lemma odd_synthesis_resolvent (L : ℝ) (hL : 0 < L)
    (t : HighIndex N J → ℝ) {a : ℝ} (ha : 0 < a) :
    ((Real.sqrt L)⁻¹ : ℂ) * ∑ i, oddHighRealSynthesis t i /
      ((frequency L i : ℂ) - Complex.I * (a : ℂ)) =
    (∑ j, t j * (highRealZeta L j / (highFrequency L j ^ 2 + a ^ 2)) : ℝ) := by
  simp only [oddHighRealSynthesis, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_div, Finset.mul_sum, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum]
  have he : (∑ i, (t j : ℂ) * oddHighVector j i /
      ((frequency L i : ℂ) - Complex.I * (a : ℂ))) =
      (t j : ℂ) * ∑ i, oddHighVector j i /
      ((frequency L i : ℂ) - Complex.I * (a : ℂ)) := by
    simp only [mul_div_assoc, Finset.mul_sum]
  rw [he, mul_left_comm, odd_pair_resolvent L hL j ha]

lemma native_full_resolvent_diagonal (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (hJN : J < N) {s : ℝ} (hs : 0 < s) :
    (nativeInverseEnergyData C L hL A J hJN).resolvent s =
      Matrix.diagonal (fun j => (highFrequency L j ^ 2 + s)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  have he : (nativeInverseEnergyData C L hL A J hJN).freePencil s =
      Matrix.diagonal (fun j => highFrequency L j ^ 2 + s) := by
    ext i j
    by_cases h : i = j <;> simp [InverseEnergyData.freePencil,
      nativeInverseEnergyData, highRealFree, h]
  rw [he, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hs)]
  · simp [h]

lemma boundaryMatrix_derivative_ratio (L : ℝ) (v : Section N) (z : ℂ)
    (hz : (freeMatrix N L - z • 1).det ≠ 0) :
    (boundaryMatrix L v - z • 1).det / (freeMatrix N L - z • 1).det =
    1 - endpointRow N L ⬝ᵥ ((freeMatrix N L - z • 1)⁻¹ *ᵥ
      (fun i => derivative L v i)) := by
  have he : boundaryMatrix L v - z • 1 = (freeMatrix N L - z • 1) -
      Basic.columnRow (fun i => derivative L v i) (endpointRow N L) := by
    have hd : freeMatrix N L *ᵥ (fun i => v i) = (fun i => derivative L v i) := by
      ext i
      simp [freeMatrix, Matrix.mulVec_diagonal]
    simp only [boundaryMatrix, Basic.correctedMatrix, hd]
    abel
  rw [he, Basic.determinant_sub_columnRow _ hz, mul_div_cancel_left₀ _ hz]

/-- The full actual CCM determinant factor is the determinant ratio of its
positive full odd pencil. The zero even ground is already canceled. -/
theorem native_boundary_determinant_inverseEnergy (C : Coefficients N) (L : ℝ)
    (hL : 0 < L) (A : GroundAdmission C) (hN : 0 < N) {a : ℝ} (ha : 0 < a) :
    let v := (fullData C L hL A).groundVector
    (boundaryMatrix L v - (Complex.I * (a : ℂ)) • 1).det /
      (freeMatrix N L - (Complex.I * (a : ℂ)) • 1).det =
    ((nativeInverseEnergyData C L hL A 0 hN).determinantRatio (a^2) : ℂ) := by
  dsimp only
  have hz : (Complex.I * (a : ℂ)).im ≠ 0 := by simpa using ha.ne'
  rw [boundaryMatrix_derivative_ratio L _ _ (freeMatrix_det_ne_zero_of_nonreal L hz)]
  rw [ground_derivative_odd_inverse C L hL A]
  change 1 - endpointRow N L ⬝ᵥ ((freeMatrix N L - (Complex.I * (a : ℂ)) • 1)⁻¹ *ᵥ
    -(fun i => oddHighRealSynthesis ((highRealMass C L hL A 0)⁻¹ *ᵥ highRealBeta C L) i)) = _
  rw [Matrix.mulVec_neg, dotProduct_neg, sub_neg_eq_add]
  rw [freeMatrix_resolvent L _ _ ((freeMatrix_det_ne_zero_iff L _).mp
    (freeMatrix_det_ne_zero_of_nonreal L hz)), odd_synthesis_resolvent L hL _ ha]
  rw [InverseEnergyData.determinantRatio_eq _ (sq_pos_of_pos ha),
    native_full_resolvent_diagonal C L hL A 0 hN (sq_pos_of_pos ha)]
  simp [Matrix.mulVec_diagonal, dotProduct, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc, nativeInverseEnergyData]

/-- The existing entire characteristic, without a parallel definition, factors
at every positive imaginary anchor through the existing native BL determinant. -/
theorem native_characteristic_inverseEnergy (C : Coefficients N) (L : ℝ)
    (hL : 0 < L) (A : GroundAdmission C) (hN : 0 < N) {a : ℝ} (ha : 0 < a) :
    boundaryCharacteristic L (fullData C L hL A).groundVector (Complex.I * (a : ℂ)) =
      Basic.complexSinc ((L : ℂ) * (Complex.I * (a : ℂ)) / 2) *
      ((nativeInverseEnergyData C L hL A 0 hN).determinantRatio (a^2) : ℂ) := by
  rw [boundaryCharacteristic_off_lattice]
  · rw [native_boundary_determinant_inverseEnergy C L hL A hN ha]
  · intro i h
    have he := congrArg Complex.im h
    simp at he
    linarith

end Riemann.CCM.Native
