import Riemann.Analysis.FiniteWindow.NativeFourierIsometry

/-! # Literal killed-shift entries in native Fourier coordinates -/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace NNReal
namespace Riemann.Analysis.FiniteWindow
open Riemann.CCM.Native

/-- The terminal truncation shortens the integration interval by exactly the shift. -/
theorem inner_ofContinuous_killedShift {L : ℝ} (_hL : 0 ≤ L) (y : ℝ≥0)
    (hy : (y : ℝ) ≤ L) (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    ⟪ofContinuous L f hf, killedShift L y (ofContinuous L g hg)⟫_ℂ =
      ∫ t in 0..L - (y : ℝ), star (f t) * g (t + y) := by
  change ⟪(ofContinuous L f hf : Ambient),
    (killedShift L y (ofContinuous L g hg) : Ambient)⟫_ℂ = _
  rw [L2.inner_def]
  have hgt := (measurePreserving_add_left volume (y : ℝ)).quasiMeasurePreserving.ae
    (ofContinuous_ae L g hg)
  calc
    _ = ∫ t, (Ico 0 (L - (y : ℝ))).indicator (fun t => star (f t) * g (t + y)) t := by
      apply integral_congr_ae
      filter_upwards [ofContinuous_ae L f hf,
        killedShift_ae L y (ofContinuous L g hg), hgt] with t hf hs hg
      rw [hf, hs]
      by_cases ht : t ∈ Ico 0 (L - (y : ℝ))
      · have htL : t ∈ Ico 0 L := ⟨ht.1, lt_of_lt_of_le ht.2 (sub_le_self L y.2)⟩
        have hyt : (y : ℝ) + t < L := by linarith [ht.2]
        have hytL : (y : ℝ) + t ∈ Ico 0 L := ⟨add_nonneg y.2 ht.1, hyt⟩
        simp only [htL, hyt, and_self, ↓reduceIte, indicator_of_mem htL,
          indicator_of_mem ht, RCLike.inner_apply, hg, indicator_of_mem hytL]
        simp only [starRingEnd_apply, add_comm, mul_comm]
      · have hn : ¬(t ∈ Ico 0 L ∧ (y : ℝ) + t < L) := by
          intro h
          exact ht ⟨h.1.1, by linarith [h.2]⟩
        simp only [hn, ↓reduceIte, inner_zero_right, indicator_of_notMem ht]
    _ = _ := by
      rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
        intervalIntegral.integral_of_le (sub_nonneg.mpr hy)]

theorem fourierFunction_single {N : ℕ} (L : ℝ) (i : Index N) :
    fourierFunction L (EuclideanSpace.single i (1 : ℂ)) = fun t : ℝ =>
      ((Real.sqrt L)⁻¹ : ℂ) * Complex.exp (Complex.I * (frequency L i * t)) := by
  funext t
  simp [fourierFunction]

/-- Exact Fourier compression of the actual killed Hilbert shift. -/
def fourierShiftCompression (N : ℕ) (L : ℝ) (y : ℝ≥0) : Section N →L[ℂ] Section N :=
  (fourierInclusion N L).adjoint.comp ((killedShift L y).comp (fourierInclusion N L))

theorem fourierShiftCompression_entry {N : ℕ} (L : ℝ) (y : ℝ≥0) (i j : Index N) :
    fourierShiftCompression N L y (EuclideanSpace.single j (1 : ℂ)) i =
      ⟪fourierHilbert L (EuclideanSpace.single i (1 : ℂ)),
        killedShift L y (fourierHilbert L (EuclideanSpace.single j (1 : ℂ)))⟫_ℂ := by
  change _ = ⟪fourierInclusion N L (EuclideanSpace.single i (1 : ℂ)),
    killedShift L y (fourierInclusion N L (EuclideanSpace.single j (1 : ℂ)))⟫_ℂ
  rw [← (fourierInclusion N L).adjoint_inner_right]
  simp [EuclideanSpace.inner_single_left, fourierShiftCompression]

/-- The literal integral entry before evaluating the elementary exponential. -/
theorem fourierShiftCompression_entry_integral {N : ℕ} {L : ℝ} (hL : 0 < L)
    (y : ℝ≥0) (hy : (y : ℝ) ≤ L) (i j : Index N) :
    fourierShiftCompression N L y (EuclideanSpace.single j (1 : ℂ)) i =
      (L : ℂ)⁻¹ * Complex.exp (Complex.I * (frequency L j * (y : ℝ))) *
        ∫ t in 0..L - (y : ℝ), Complex.exp (Complex.I *
          ((frequency L j : ℂ) - (frequency L i : ℂ)) * (t : ℂ)) := by
  rw [fourierShiftCompression_entry, fourierHilbert, fourierHilbert,
    inner_ofContinuous_killedShift hL.le y hy]
  simp only [fourierFunction_single]
  have hs : (Real.sqrt L : ℂ) ^ 2 = (L : ℂ) := by exact_mod_cast Real.sq_sqrt hL.le
  have hn : (Real.sqrt L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hL)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [← starRingEnd_apply, map_mul, map_inv₀, Complex.conj_ofReal,
    ← Complex.exp_conj, Complex.conj_I]
  have he : Complex.exp (-Complex.I * (frequency L i * t)) *
      Complex.exp (Complex.I * (frequency L j * (t + y))) =
      Complex.exp (Complex.I * (frequency L j * (y : ℝ))) *
        Complex.exp (Complex.I * ((frequency L j : ℂ) - (frequency L i : ℂ)) * (t : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  calc
    _ = (((Real.sqrt L : ℂ)⁻¹) ^ 2) *
        (Complex.exp (-Complex.I * (frequency L i * t)) *
          Complex.exp (Complex.I * (frequency L j * (t + y)))) := by push_cast; ring
    _ = _ := by
      rw [he, ← hs]
      field_simp

/-- The closed-form matrix entry, with its removable diagonal written explicitly. -/
theorem fourierShiftCompression_entry_explicit {N : ℕ} {L : ℝ} (hL : 0 < L)
    (y : ℝ≥0) (hy : (y : ℝ) ≤ L) (i j : Index N) :
    fourierShiftCompression N L y (EuclideanSpace.single j (1 : ℂ)) i =
      (L : ℂ)⁻¹ * Complex.exp (Complex.I * (frequency L j * (y : ℝ))) *
        (if i = j then ((L - (y : ℝ) : ℝ) : ℂ) else
          (Complex.exp (Complex.I * ((frequency L j : ℂ) - (frequency L i : ℂ)) *
            ((L - (y : ℝ) : ℝ) : ℂ)) - 1) /
          (Complex.I * ((frequency L j : ℂ) - (frequency L i : ℂ)))) := by
  rw [fourierShiftCompression_entry_integral hL y hy]
  congr 1
  by_cases hij : i = j
  · subst j
    simp
  · rw [if_neg hij, integral_exp_mul_complex]
    · simp
    · apply mul_ne_zero Complex.I_ne_zero
      intro he
      exact hij ((frequency_injective hL (Complex.ofReal_injective (sub_eq_zero.mp he))).symm)

/-- After the physical terminal cutoff the entire compressed shift is zero. -/
theorem fourierShiftCompression_eq_zero (N : ℕ) (L : ℝ) (y : ℝ≥0)
    (hy : L ≤ (y : ℝ)) : fourierShiftCompression N L y = 0 := by
  simp [fourierShiftCompression, killedShift_eq_zero L y hy]

end Riemann.Analysis.FiniteWindow
