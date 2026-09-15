import Riemann.Analysis.FiniteWindow.NativeFourierHilbert
import Riemann.CCM.FourierIntegral

/-! # Exact physical Fourier isometry into the interval Hilbert space

The coefficient inner product is identified with the actual supported L² inner
product, including the normalization `L⁻¹ᐟ²` and every signed Fourier index.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace
namespace Riemann.Analysis.FiniteWindow
open Riemann.CCM.Native

/-- The physical inner product of supported continuous representatives. -/
theorem inner_ofContinuous {L : ℝ} (hL : 0 ≤ L) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    ⟪ofContinuous L f hf, ofContinuous L g hg⟫_ℂ =
      ∫ t in 0..L, star (f t) * g t := by
  change ⟪(ofContinuous L f hf : Ambient), (ofContinuous L g hg : Ambient)⟫_ℂ = _
  rw [L2.inner_def]
  calc
    _ = ∫ t, (Ico 0 L).indicator (fun t => star (f t) * g t) t := by
      apply integral_congr_ae
      filter_upwards [ofContinuous_ae L f hf, ofContinuous_ae L g hg] with t hf hg
      rw [hf, hg]
      by_cases ht : t ∈ Ico 0 L <;> simp [ht, RCLike.inner_apply, mul_comm]
    _ = _ := by
      rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
        intervalIntegral.integral_of_le hL]

/-- Orthogonality of the literal signed integer exponentials. -/
theorem integral_frequency_difference {N : ℕ} {L : ℝ} (hL : 0 < L)
    (i j : Index N) :
    (∫ t in 0..L, Complex.exp (Complex.I *
      ((frequency L j : ℂ) - (frequency L i : ℂ)) * (t : ℂ))) =
      if i = j then (L : ℂ) else 0 := by
  by_cases hij : i = j
  · subst j
    simp
  · have hfreq : (frequency L j : ℂ) - (frequency L i : ℂ) ≠ 0 := by
      intro he
      have he' : frequency L j = frequency L i := Complex.ofReal_injective (sub_eq_zero.mp he)
      exact hij ((frequency_injective hL he').symm)
    rw [if_neg hij, integral_exp_mul_complex (mul_ne_zero Complex.I_ne_zero hfreq)]
    have he : Complex.exp (Complex.I *
        ((frequency L j : ℂ) - (frequency L i : ℂ)) * (L : ℂ)) = 1 := by
      rw [show Complex.I * ((frequency L j : ℂ) - (frequency L i : ℂ)) * (L : ℂ) =
        Complex.I * (frequency L j * L) - Complex.I * (frequency L i * L) by ring,
        Complex.exp_sub, frequency_period hL j, frequency_period hL i]
      simp
    simp [he]

/-- A single pair of normalized Fourier summands has the physical delta pairing. -/
theorem integral_fourier_summands {N : ℕ} {L : ℝ} (hL : 0 < L)
    (i j : Index N) (a b : ℂ) :
    (∫ t in 0..L,
      star (a * ((Real.sqrt L)⁻¹ : ℂ) * Complex.exp (Complex.I * (frequency L i * t))) *
        (b * ((Real.sqrt L)⁻¹ : ℂ) * Complex.exp (Complex.I * (frequency L j * t)))) =
      if i = j then star a * b else 0 := by
  have hfun : (fun t : ℝ =>
      star (a * ((Real.sqrt L)⁻¹ : ℂ) * Complex.exp (Complex.I * (frequency L i * t))) *
        (b * ((Real.sqrt L)⁻¹ : ℂ) * Complex.exp (Complex.I * (frequency L j * t)))) =
      (fun t : ℝ => (star a * b * (((Real.sqrt L)⁻¹ : ℂ) ^ 2)) *
        Complex.exp (Complex.I * ((frequency L j : ℂ) - (frequency L i : ℂ)) * (t : ℂ))) := by
    funext t
    simp only [← starRingEnd_apply, ← Complex.exp_conj, map_mul, map_inv₀,
      Complex.conj_I, Complex.conj_ofReal]
    have he : Complex.exp (-Complex.I * (frequency L i * t)) *
        Complex.exp (Complex.I * (frequency L j * t)) =
        Complex.exp (Complex.I * ((frequency L j : ℂ) - (frequency L i : ℂ)) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc
      _ = ((starRingEnd ℂ) a * b * (((Real.sqrt L)⁻¹ : ℂ) ^ 2)) *
          (Complex.exp (-Complex.I * (frequency L i * t)) *
            Complex.exp (Complex.I * (frequency L j * t))) := by ring
      _ = _ := by rw [he]
  rw [hfun, intervalIntegral.integral_const_mul, integral_frequency_difference hL]
  split_ifs
  · have hs : (Real.sqrt L : ℂ) ^ 2 = (L : ℂ) := by exact_mod_cast Real.sq_sqrt hL.le
    have hn : (Real.sqrt L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hL)
    rw [← hs]
    field_simp
  · simp

/-- The full native polynomial has exactly the Euclidean coefficient inner product. -/
theorem integral_fourier_inner {N : ℕ} {L : ℝ} (hL : 0 < L) (x y : Section N) :
    (∫ t in 0..L, star (fourierFunction L x t) * fourierFunction L y t) = ⟪x, y⟫_ℂ := by
  simp only [fourierFunction, star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · have he (j : Index N) :
        (∫ t in 0..L, ∑ i : Index N,
          star (x i * ((Real.sqrt L)⁻¹ : ℂ) * Complex.exp (Complex.I * (frequency L i * t))) *
          (y j * ((Real.sqrt L)⁻¹ : ℂ) * Complex.exp (Complex.I * (frequency L j * t)))) =
        ∑ i : Index N, if i = j then star (x i) * y j else 0 := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        exact integral_fourier_summands hL i j (x i) (y j)
      · intro i _
        apply Continuous.intervalIntegrable
        fun_prop
    simp_rw [he]
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  · intro i _
    apply Continuous.intervalIntegrable
    fun_prop

/-- Isometry of the actual full signed native Fourier section. -/
theorem fourierHilbert_inner {N : ℕ} {L : ℝ} (hL : 0 < L) (x y : Section N) :
    ⟪fourierHilbert L x, fourierHilbert L y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [fourierHilbert, fourierHilbert, inner_ofContinuous hL.le]
  exact integral_fourier_inner hL x y

def fourierIsometry (N : ℕ) {L : ℝ} (hL : 0 < L) : Section N →ₗᵢ[ℂ] Hilbert L :=
  (fourierInclusionLinearMap N L).isometryOfInner (fourierHilbert_inner hL)

@[simp] theorem fourierIsometry_apply {N : ℕ} {L : ℝ} (hL : 0 < L) (x : Section N) :
    fourierIsometry N hL x = fourierHilbert L x := rfl

end Riemann.Analysis.FiniteWindow
