import Riemann.CCM.PositiveOddCapacity
import Riemann.CCM.InverseEnergyCapacity

/-!
# Actual real odd Fourier coordinates for the finite inverse-energy theorem

The positive modes J<j≤N are paired with their negative modes. All matrices are
formed from the original full admitted shifted Weil matrix in its physical
orthonormal coordinates.
-/
noncomputable section
open scoped InnerProductSpace BigOperators
open Matrix
namespace Riemann.CCM.Native

abbrev HighIndex (N J : ℕ) := {j : Fin (N+1) // J < j.val}
variable {N J : ℕ}

def highPositiveIndex (j : HighIndex N J) : Index N := ⟨N + j.val.val, by have := j.val.isLt; omega⟩
@[simp] theorem mode_highPositiveIndex (j : HighIndex N J) :
    mode (highPositiveIndex j) = j.val.val := by simp [mode, highPositiveIndex]

lemma highPositiveIndex_injective : Function.Injective (@highPositiveIndex N J) := by
  intro i j h
  apply Subtype.ext
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [highPositiveIndex] at this
  omega

lemma highPositiveIndex_ne_rev (i j : HighIndex N J) : highPositiveIndex i ≠ (highPositiveIndex j).rev := by
  intro h
  have hm := congrArg mode h
  simp only [mode_highPositiveIndex, mode_rev] at hm
  have := i.property
  have := j.property
  omega

def oddHighVector (j : HighIndex N J) : Section N :=
  ((Real.sqrt 2)⁻¹ : ℂ) •
    (EuclideanSpace.single (highPositiveIndex j) 1 - EuclideanSpace.single (highPositiveIndex j).rev 1)

@[simp] theorem oddHighVector_apply (j : HighIndex N J) (i : Index N) :
    oddHighVector j i = ((Real.sqrt 2)⁻¹ : ℂ) *
      ((if i = highPositiveIndex j then 1 else 0) - (if i = (highPositiveIndex j).rev then 1 else 0)) := by
  simp [oddHighVector]

@[simp] theorem oddHighVector_positive (i j : HighIndex N J) :
    oddHighVector j (highPositiveIndex i) = if i = j then ((Real.sqrt 2)⁻¹ : ℂ) else 0 := by
  simp [highPositiveIndex_ne_rev, highPositiveIndex_injective.eq_iff]

lemma oddHighVector_odd (j : HighIndex N J) : reflection N (oddHighVector j) = -oddHighVector j := by
  ext i
  have h1 : i.rev = highPositiveIndex j ↔ i = (highPositiveIndex j).rev := by
    constructor <;> intro h <;> simpa using congrArg Fin.rev h
  have h2 : i.rev = (highPositiveIndex j).rev ↔ i = highPositiveIndex j := Fin.rev_inj
  simp only [reflection_apply, oddHighVector_apply, PiLp.neg_apply, h1, h2]
  ring

def highFrequency (L : ℝ) (j : HighIndex N J) : ℝ := frequency L (highPositiveIndex j)
lemma highFrequency_pos {L : ℝ} (hL : 0 < L) (j : HighIndex N J) : 0 < highFrequency L j := by
  dsimp [highFrequency, frequency]
  rw [mode_highPositiveIndex]
  apply mul_pos (div_pos (by positivity) hL)
  exact_mod_cast (lt_of_le_of_lt (Nat.zero_le J) j.property)

lemma oddHighVector_squaredDerivative (L : ℝ) (j : HighIndex N J) :
    derivative L (derivative L (oddHighVector j)) = (highFrequency L j ^ 2 : ℝ) • oddHighVector j := by
  ext i
  by_cases hp : i = highPositiveIndex j
  · subst i
    simp [highFrequency, pow_two, mul_assoc]
  · by_cases hn : i = (highPositiveIndex j).rev
    · subst i
      simp [highFrequency, pow_two]
      ring
    · simp [oddHighVector_apply, hp, hn]

/-- Real coefficient synthesis in the physically normalized odd basis. -/
def oddHighRealSynthesis (x : HighIndex N J → ℝ) : Section N := ∑ j, (x j : ℂ) • oddHighVector j

lemma oddHighRealSynthesis_positive (x : HighIndex N J → ℝ) (i : HighIndex N J) :
    oddHighRealSynthesis x (highPositiveIndex i) = (x i : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [oddHighRealSynthesis, highPositiveIndex_ne_rev, highPositiveIndex_injective.eq_iff]

lemma oddHighRealSynthesis_injective : Function.Injective (@oddHighRealSynthesis N J) := by
  intro x y h
  funext i
  have hi := congrArg (fun v : Section N => v (highPositiveIndex i)) h
  simp only [oddHighRealSynthesis_positive] at hi
  have hr : ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by norm_num
  exact_mod_cast mul_right_cancel₀ hr hi

lemma oddHighRealSynthesis_odd (x : HighIndex N J → ℝ) :
    reflection N (oddHighRealSynthesis x) = -oddHighRealSynthesis x := by
  simp [oddHighRealSynthesis, map_sum, oddHighVector_odd, Finset.sum_neg_distrib]

/-- The actual real part of the physical form, in the prescribed columns. -/
def realColumnGram (T : Section N →L[ℂ] Section N) (w : HighIndex N J → Section N) :
    Matrix (HighIndex N J) (HighIndex N J) ℝ :=
  fun i j => (⟪w i, T (w j)⟫_ℂ).re

lemma realColumnGram_symmetric (T : Section N →L[ℂ] Section N) (hT : T.adjoint = T)
    (w : HighIndex N J → Section N) : (realColumnGram T w).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  change (⟪w j, T (w i)⟫_ℂ).re = (⟪w i, T (w j)⟫_ℂ).re
  have h := T.adjoint_inner_right (w j) (w i)
  rw [hT] at h
  rw [h]
  exact inner_re_symm (𝕜 := ℂ) (T (w j)) (w i)

lemma realColumnGram_quadratic (T : Section N →L[ℂ] Section N)
    (w : HighIndex N J → Section N) (x : HighIndex N J → ℝ) :
    x ⬝ᵥ (realColumnGram T w *ᵥ x) =
      (⟪∑ i, (x i : ℂ) • w i, T (∑ j, (x j : ℂ) • w j)⟫_ℂ).re := by
  simp only [realColumnGram, Matrix.mulVec, dotProduct, map_sum, map_smul,
    inner_sum, sum_inner, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma oddHighVector_inner (j : HighIndex N J) (x : Section N) :
    ⟪oddHighVector j, x⟫_ℂ = ((Real.sqrt 2)⁻¹ : ℂ) *
      (x (highPositiveIndex j) - x (highPositiveIndex j).rev) := by
  simp [oddHighVector, inner_smul_left, inner_sub_left, EuclideanSpace.inner_single_left]

lemma oddHighVector_negative (i j : HighIndex N J) :
    oddHighVector j (highPositiveIndex i).rev =
      -(if i = j then ((Real.sqrt 2)⁻¹ : ℂ) else 0) := by
  have h := congrArg (fun v : Section N => v (highPositiveIndex i)) (oddHighVector_odd j)
  simpa only [reflection_apply, PiLp.neg_apply, oddHighVector_positive] using h

/-- The paired columns are orthonormal in the physical complex inner product. -/
lemma oddHighVector_orthonormal : Orthonormal ℂ (@oddHighVector N J) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [oddHighVector_inner, oddHighVector_positive, oddHighVector_negative]
  by_cases h : i = j
  · subst j
    simp only [↓reduceIte, sub_neg_eq_add]
    have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by norm_cast; norm_num
    field_simp
    rw [hs]
    norm_num
  · simp [h]

lemma oddHighVector_real (j : HighIndex N J) (i : Index N) : (oddHighVector j i).im = 0 := by
  simp only [oddHighVector_apply]
  split_ifs <;> simp

lemma derivative_real (L : ℝ) (x : Section N) (hx : ∀ i, (x i).im = 0) :
    ∀ i, (derivative L x i).im = 0 := by
  intro i
  simp [derivative_apply, Complex.mul_im, hx]

lemma shifted_real (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (x : Section N) (hx : ∀ i, (x i).im = 0) :
    ∀ i, ((fullData C L hL A).shifted x i).im = 0 := by
  intro i
  change ((weilOperator C x) i - (A.e₀ : ℂ) * x i).im = 0
  simp only [weilOperator_apply, Complex.sub_im, Complex.im_sum, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, hx, mul_zero, zero_mul, add_zero, sub_zero]
  apply Finset.sum_eq_zero
  intro j hj
  have hm : (weilMatrix C i j).im = 0 := by
    unfold weilMatrix
    split_ifs <;> exact Complex.ofReal_im _
  simp only [hm, zero_mul, add_zero]

lemma inner_real_of_coordinates (x y : Section N)
    (hx : ∀ i, (x i).im = 0) (hy : ∀ i, (y i).im = 0) : (⟪x, y⟫_ℂ).im = 0 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Complex.im_sum,
    Complex.mul_im, hx, hy]

/-- The physical endpoint derivative has a strictly positive real coordinate. -/
def highRealZeta (L : ℝ) (j : HighIndex N J) : ℝ :=
  Real.sqrt 2 / Real.sqrt L * highFrequency L j

lemma highRealZeta_pos {L : ℝ} (hL : 0 < L) (j : HighIndex N J) : 0 < highRealZeta L j :=
  mul_pos (div_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_pos.mpr hL)) (highFrequency_pos hL j)

lemma oddHighVector_zeta_pairing (L : ℝ) (j : HighIndex N J) :
    ⟪oddHighVector j, derivative L (endpointVector N L)⟫_ℂ = (highRealZeta L j : ℂ) := by
  rw [oddHighVector_inner]
  simp only [derivative_apply, endpointVector_apply, frequency_rev, Complex.ofReal_neg]
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by norm_cast; norm_num
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by norm_num
  simp only [highRealZeta, highFrequency, Complex.ofReal_mul, Complex.ofReal_div]
  field_simp
  rw [hs]
  ring

lemma oddHighVector_endpointDerivative (L : ℝ) (j : HighIndex N J) :
    ⟪endpointVector N L, derivative L (oddHighVector j)⟫_ℂ = (highRealZeta L j : ℂ) := by
  have h := (derivative L).adjoint_inner_right (endpointVector N L) (oddHighVector j)
  rw [derivative_selfadjoint] at h
  rw [h]
  rw [← inner_conj_symm, oddHighVector_zeta_pairing]
  simp

/-- Actual real odd compression of the full shifted Weil form. -/
def highRealMass (C : Coefficients N) (L : ℝ) (hL : 0 < L) (A : GroundAdmission C) (J : ℕ) :
    Matrix (HighIndex N J) (HighIndex N J) ℝ :=
  realColumnGram (fullData C L hL A).shifted oddHighVector

/-- Actual differentiated odd compression, with the same admitted energy. -/
def highRealEnergy (C : Coefficients N) (L : ℝ) (hL : 0 < L) (A : GroundAdmission C) (J : ℕ) :
    Matrix (HighIndex N J) (HighIndex N J) ℝ :=
  realColumnGram (fullData C L hL A).shifted (fun j => derivative L (oddHighVector j))

def highRealFree (L : ℝ) (N J : ℕ) : Matrix (HighIndex N J) (HighIndex N J) ℝ :=
  Matrix.diagonal (fun j => highFrequency L j ^ 2)

def highRealBeta (C : Coefficients N) (L : ℝ) (j : HighIndex N J) : ℝ :=
  (⟪oddHighVector j, displacementVector C L⟫_ℂ).re

lemma highRealFree_pos {L : ℝ} (hL : 0 < L) : (highRealFree L N J).PosDef :=
  Matrix.PosDef.diagonal (fun j => sq_pos_of_pos (highFrequency_pos hL j))

lemma highRealMass_pos (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) : (highRealMass C L hL A J).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (realColumnGram_symmetric _ (fullData C L hL A).shifted_selfadjoint _)
  intro x hx
  simp only [star_trivial]
  rw [realColumnGram_quadratic]
  apply (fullData C L hL A).odd_shifted_positive (oddHighRealSynthesis_odd x)
  intro hz
  apply hx
  apply oddHighRealSynthesis_injective
  simpa [oddHighRealSynthesis] using hz

lemma highRealEnergy_pos (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) : (highRealEnergy C L hL A J).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (realColumnGram_symmetric _ (fullData C L hL A).shifted_selfadjoint _)
  intro x hx
  simp only [star_trivial]
  rw [realColumnGram_quadratic]
  have hn : oddHighRealSynthesis x ≠ 0 := by
    intro hz
    apply hx
    apply oddHighRealSynthesis_injective
    simpa [oddHighRealSynthesis] using hz
  have h := (fullData C L hL A).odd_differentiated_positive (oddHighRealSynthesis_odd x) hn
  simpa only [oddHighRealSynthesis, fullData, map_sum, map_smul] using h

lemma highRealBeta_complex_entry (C : Coefficients N) (L : ℝ) (j : HighIndex N J) :
    (highRealBeta C L j : ℂ) = ⟪oddHighVector j, displacementVector C L⟫_ℂ := by
  apply Complex.ext
  · rfl
  · exact (inner_real_of_coordinates _ _ (oddHighVector_real j)
      (fun i => by simp only [displacementVector_apply, Complex.ofReal_im])).symm

/-- The original full displacement gives the high-block rank-one identity. -/
lemma highReal_displacement (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) :
    highRealEnergy C L hL A J = highRealMass C L hL A J * highRealFree L N J +
      Matrix.of (fun i j => highRealBeta C L i * highRealZeta L j) := by
  let M := fullData C L hL A
  ext i j
  have he : M.reflection (M.D (oddHighVector j)) = M.D (oddHighVector j) := by
    change reflection N (derivative L (oddHighVector j)) = derivative L (oddHighVector j)
    rw [reflection_derivative, oddHighVector_odd, map_neg, neg_neg]
  have hd := M.shifted_displacement (M.D (oddHighVector j))
  rw [M.odd_inner_even he, zero_smul, sub_zero] at hd
  have hsq : M.D (M.D (oddHighVector j)) =
      ((highFrequency L j ^ 2 : ℝ) : ℂ) • oddHighVector j := by
    simpa only [M, fullData, Complex.coe_smul] using oddHighVector_squaredDerivative L j
  rw [hsq, map_smul] at hd
  have hsolve : M.D (M.shifted (M.D (oddHighVector j))) =
      ((highFrequency L j ^ 2 : ℝ) : ℂ) • M.shifted (oddHighVector j) +
      (highRealZeta L j : ℂ) • M.b := by
    have hz : ⟪M.eta, M.D (oddHighVector j)⟫_ℂ = (highRealZeta L j : ℂ) :=
      oddHighVector_endpointDerivative L j
    rw [hz] at hd
    exact (sub_eq_iff_eq_add.mp hd).trans (add_comm _ _)
  have hinner := M.D.adjoint_inner_right (oddHighVector i) (M.shifted (M.D (oddHighVector j)))
  rw [M.D_selfadjoint, hsolve, inner_add_right, inner_smul_right, inner_smul_right] at hinner
  change (⟪M.D (oddHighVector i), M.shifted (M.D (oddHighVector j))⟫_ℂ).re = _
  rw [← hinner]
  simp [highRealMass, realColumnGram, highRealFree, highRealBeta, Matrix.mul_diagonal,
    Complex.mul_re, mul_comm, M, fullData, pow_two]

/-- No imaginary component is discarded by the real mass matrix. -/
lemma highRealMass_complex_entry (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (i j : HighIndex N J) :
    (highRealMass C L hL A J i j : ℂ) =
      ⟪oddHighVector i, (fullData C L hL A).shifted (oddHighVector j)⟫_ℂ := by
  apply Complex.ext
  · rfl
  · exact (inner_real_of_coordinates _ _ (oddHighVector_real i)
      (shifted_real C L hL A _ (oddHighVector_real j))).symm

/-- The differentiated real matrix is likewise the actual complex compression. -/
lemma highRealEnergy_complex_entry (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (i j : HighIndex N J) :
    (highRealEnergy C L hL A J i j : ℂ) =
      ⟪derivative L (oddHighVector i),
        (fullData C L hL A).shifted (derivative L (oddHighVector j))⟫_ℂ := by
  apply Complex.ext
  · rfl
  · exact (inner_real_of_coordinates _ _ (derivative_real L _ (oddHighVector_real i))
      (shifted_real C L hL A _ (derivative_real L _ (oddHighVector_real j)))).symm

lemma highRealZeta_ne_zero {L : ℝ} (hL : 0 < L) (hJN : J < N) :
    (highRealZeta L : HighIndex N J → ℝ) ≠ 0 := by
  intro h
  let j : HighIndex N J := ⟨⟨N, Nat.lt_succ_self N⟩, hJN⟩
  have hz := congrFun h j
  exact (highRealZeta_pos hL j).ne' hz

/-- Native nonempty high data. Its only spectral admission is the original full
simple even least ground; all high positivity and endpoint data are derived. -/
def nativeInverseEnergyData (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (hJN : J < N) : InverseEnergyData (HighIndex N J) where
  A := highRealFree L N J
  B := highRealMass C L hL A J
  K := highRealEnergy C L hL A J
  beta := highRealBeta C L
  zeta := highRealZeta L
  A_pos := highRealFree_pos hL
  B_pos := highRealMass_pos C L hL A J
  K_pos := highRealEnergy_pos C L hL A J
  displacement := highReal_displacement C L hL A J
  zeta_ne_zero := highRealZeta_ne_zero hL hJN

/-- The native high mean has the actual real logarithmic inverse-energy derivative. -/
theorem native_highMean_inverseEnergy_identity (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (hJN : J < N) {s : ℝ} (hs : 0 < s) :
    let M := nativeInverseEnergyData C L hL A J hJN
    M.highMean s = M.freeMean s + M.boundaryCorrection s +
      s / 2 * deriv (fun t => Real.log (M.inverseEnergy t)) s :=
  (nativeInverseEnergyData C L hL A J hJN).highMean_inverseEnergy_identity hs

/-- Exact prescribed-anchor determinant/source-energy identity in native coordinates. -/
theorem native_fixed_anchor_log_identity (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (hJN : J < N) :
    let M := nativeInverseEnergyData C L hL A J hJN
    Real.log (M.determinantRatio (9/16) / M.determinantRatio (1/16)) =
      (1/2 : ℝ) * Real.log (M.inverseEnergy (9/16) / M.inverseEnergy (1/16)) +
        ∫ t in (1/16 : ℝ)..(9/16 : ℝ), M.boundaryCorrection t / t :=
  (nativeInverseEnergyData C L hL A J hJN).fixed_anchor_log_identity

/-- Native source-energy ratio controls the high capacity with the exact free term. -/
theorem native_fixed_anchor_capacity_energy_bounds (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (hJN : J < N) :
    let M := nativeInverseEnergyData C L hL A J hJN
    Real.log 9 * (M.highMean (1/16) - 1) ≤ M.freeLogRatio (1/16) (9/16) +
      (1/2 : ℝ) * Real.log (M.inverseEnergy (9/16) / M.inverseEnergy (1/16)) ∧
    M.freeLogRatio (1/16) (9/16) +
      (1/2 : ℝ) * Real.log (M.inverseEnergy (9/16) / M.inverseEnergy (1/16)) ≤
      8 * M.highMean (1/16) :=
  (nativeInverseEnergyData C L hL A J hJN).fixed_anchor_capacity_energy_bounds

end Riemann.CCM.Native
