import Riemann.Analysis.FiniteWindow.NativeShiftEntries
import Riemann.CCM.WeilMatrix

/-! # Actual Hermitian killed shifts in the native divided-difference class -/
noncomputable section
open scoped InnerProductSpace NNReal
namespace Riemann.Analysis.FiniteWindow
open Riemann.CCM.Native

/-- The literal cosine diagonal and sine divided difference of `S_y+S_y†`. -/
def hermitianShiftCoefficients (N : ℕ) (L y : ℝ) : Coefficients N where
  diagonal i := 2 * (1 - y / L) * Real.cos (frequency L i * y)
  beta i := -Real.sin (frequency L i * y) / Real.pi
  diagonal_even i := by simp
  beta_odd i := by simp [neg_div]

/-- At distinct native frequencies the terminal phase simplifies by periodicity. -/
theorem fourierShiftCompression_entry_offDiagonal {N : ℕ} {L : ℝ} (hL : 0 < L)
    (y : ℝ≥0) (hy : (y : ℝ) ≤ L) {i j : Index N} (hij : i ≠ j) :
    fourierShiftCompression N L y (EuclideanSpace.single j (1 : ℂ)) i =
      (Complex.exp (Complex.I * (frequency L i * (y : ℝ))) -
        Complex.exp (Complex.I * (frequency L j * (y : ℝ)))) /
      (Complex.I * (L : ℂ) * ((frequency L j : ℂ) - (frequency L i : ℂ))) := by
  rw [fourierShiftCompression_entry_explicit hL y hy, if_neg hij]
  have he : Complex.exp (Complex.I *
      ((frequency L j : ℂ) - (frequency L i : ℂ)) * ((L - (y : ℝ) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (frequency L i * (y : ℝ))) /
        Complex.exp (Complex.I * (frequency L j * (y : ℝ))) := by
    have hsplit : Complex.I * ((frequency L j : ℂ) - (frequency L i : ℂ)) *
        ((L - (y : ℝ) : ℝ) : ℂ) =
        (Complex.I * (frequency L j * L) - Complex.I * (frequency L i * L)) +
        (Complex.I * (frequency L i * (y : ℝ)) - Complex.I * (frequency L j * (y : ℝ))) := by
      push_cast
      ring
    rw [hsplit, Complex.exp_add, Complex.exp_sub, frequency_period hL j,
      frequency_period hL i, div_self one_ne_zero, one_mul, Complex.exp_sub]
  rw [he]
  have hfreq : (frequency L j : ℂ) - (frequency L i : ℂ) ≠ 0 := by
    intro he
    exact hij ((frequency_injective hL (Complex.ofReal_injective (sub_eq_zero.mp he))).symm)
  field_simp [Complex.ofReal_ne_zero.mpr hL.ne', Complex.I_ne_zero,
    hfreq, Complex.exp_ne_zero]

/-- The compressed killed shift is complex symmetric in the native Fourier basis. -/
theorem fourierShiftCompression_symmetric_entries {N : ℕ} {L : ℝ} (hL : 0 < L)
    (y : ℝ≥0) (hy : (y : ℝ) ≤ L) (i j : Index N) :
    fourierShiftCompression N L y (EuclideanSpace.single j (1 : ℂ)) i =
      fourierShiftCompression N L y (EuclideanSpace.single i (1 : ℂ)) j := by
  by_cases hij : i = j
  · subst j; rfl
  · rw [fourierShiftCompression_entry_offDiagonal hL y hy hij,
      fourierShiftCompression_entry_offDiagonal hL y hy (Ne.symm hij)]
    have hdiff : (frequency L i : ℂ) - (frequency L j : ℂ) =
        -((frequency L j : ℂ) - (frequency L i : ℂ)) := by ring
    rw [hdiff, mul_neg]
    rw [show Complex.exp (Complex.I * (frequency L j * (y : ℝ))) -
        Complex.exp (Complex.I * (frequency L i * (y : ℝ))) =
        -(Complex.exp (Complex.I * (frequency L i * (y : ℝ))) -
          Complex.exp (Complex.I * (frequency L j * (y : ℝ)))) by ring]
    exact (neg_div_neg_eq _ _).symm

/-- Matrix entries of an adjoint in the actual orthonormal coefficient basis. -/
theorem adjoint_single_entry {N : ℕ} (T : Section N →L[ℂ] Section N) (i j : Index N) :
    T.adjoint (EuclideanSpace.single j (1 : ℂ)) i =
      star (T (EuclideanSpace.single i (1 : ℂ)) j) := by
  have he := T.adjoint_inner_right (EuclideanSpace.single i (1 : ℂ))
    (EuclideanSpace.single j (1 : ℂ))
  simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using he

theorem re_div_I_real (z : ℂ) (d : ℝ) : (z / (Complex.I * (d : ℂ))).re = z.im / d := by
  by_cases hd : d = 0
  · simp [hd]
  · simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
    field_simp

theorem hermitianShift_entry {N : ℕ} {L : ℝ} (hL : 0 < L)
    (y : ℝ≥0) (hy : (y : ℝ) ≤ L) (i j : Index N) :
    (fourierShiftCompression N L y + (fourierShiftCompression N L y).adjoint)
      (EuclideanSpace.single j (1 : ℂ)) i =
      weilMatrix (hermitianShiftCoefficients N L y) i j := by
  change fourierShiftCompression N L y (EuclideanSpace.single j (1 : ℂ)) i +
    (fourierShiftCompression N L y).adjoint (EuclideanSpace.single j (1 : ℂ)) i = _
  rw [adjoint_single_entry, ← fourierShiftCompression_symmetric_entries hL y hy i j]
  change _ + (starRingEnd ℂ) _ = _
  rw [Complex.add_conj]
  by_cases hij : i = j
  · subst j
    rw [fourierShiftCompression_entry_explicit hL y hy, if_pos rfl]
    simp only [weilMatrix, ↓reduceIte, hermitianShiftCoefficients]
    apply congrArg Complex.ofReal
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.inv_re, Complex.inv_im, Complex.normSq_ofReal, Complex.exp_re,
      Complex.exp_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_add, add_zero, sub_zero, Complex.ofReal_sub, zero_sub]
    norm_num [Complex.sub_re, Complex.sub_im]
    field_simp
  · rw [fourierShiftCompression_entry_offDiagonal hL y hy hij]
    have hd : Complex.I * (L : ℂ) * ((frequency L j : ℂ) - (frequency L i : ℂ)) =
        Complex.I * ((L * (frequency L j - frequency L i) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hd, re_div_I_real]
    simp only [weilMatrix, if_neg hij, hermitianShiftCoefficients]
    apply congrArg Complex.ofReal
    simp only [Complex.sub_im, Complex.exp_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, zero_add, add_zero, sub_zero]
    norm_num
    have hden : L * (frequency L j - frequency L i) =
        -(2 * Real.pi) * ((mode i : ℝ) - mode j) := by
      unfold frequency
      field_simp
      ring
    rw [hden]
    field_simp [mode_difference_ne_zero hij, Real.pi_ne_zero]
    ring

/-- Standard physical basis entries determine a native finite operator. -/
theorem nativeOperator_ext_single {N : ℕ} {S T : Section N →L[ℂ] Section N}
    (h : ∀ i j, S (EuclideanSpace.single j (1 : ℂ)) i =
      T (EuclideanSpace.single j (1 : ℂ)) i) : S = T := by
  apply ContinuousLinearMap.ext
  intro x
  have hx : x = ∑ j, x j • EuclideanSpace.single j (1 : ℂ) := by
    ext i
    simp [Pi.single_apply]
  rw [hx, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, map_smul]
  congr 1
  ext i
  exact h i j

/-- The divided-difference operator is proved equal to the actual Hermitian shift. -/
theorem hermitianShift_weilOperator {N : ℕ} {L : ℝ} (hL : 0 < L)
    (y : ℝ≥0) (hy : (y : ℝ) ≤ L) :
    fourierShiftCompression N L y + (fourierShiftCompression N L y).adjoint =
      weilOperator (hermitianShiftCoefficients N L y) := by
  apply nativeOperator_ext_single
  intro i j
  rw [hermitianShift_entry hL y hy]
  simp [weilOperator_apply]

end Riemann.Analysis.FiniteWindow
