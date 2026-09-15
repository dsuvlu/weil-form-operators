import Riemann.Analysis.FiniteWindow.NativeHermitianShift
import Riemann.Analysis.FiniteWindow.PrimeHilbert

/-! # The actual prime current in native divided-difference coordinates

The prime current is `-Z⁻¹ Z′`, with positive von Mangoldt weights. Its negative
Hermitian form therefore has a negative cosine diagonal and positive sine beta.
-/
noncomputable section
open Finset
open scoped InnerProductSpace NNReal
namespace Riemann.Analysis.FiniteWindow
open Riemann.CCM.Native

/-- Actual Fourier compression, continuous and linear in the Hilbert operator. -/
def nativeCompression (N : ℕ) (L : ℝ) :
    (Hilbert L →L[ℂ] Hilbert L) →L[ℂ] (Section N →L[ℂ] Section N) :=
  LinearMap.mkContinuous
    { toFun (T : Hilbert L →L[ℂ] Hilbert L) := (fourierInclusion N L).adjoint.comp (T.comp (fourierInclusion N L))
      map_add' S T := by ext x; simp
      map_smul' c T := by ext x; simp }
    (‖(fourierInclusion N L).adjoint‖ * ‖fourierInclusion N L‖)
    (fun T => by
      calc
        _ ≤ ‖(fourierInclusion N L).adjoint‖ * ‖T.comp (fourierInclusion N L)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖(fourierInclusion N L).adjoint‖ * (‖T‖ * ‖fourierInclusion N L‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg (fourierInclusion N L).adjoint)
        _ = _ := by ring)

@[simp] theorem nativeCompression_apply (N : ℕ) (L : ℝ) (T : Hilbert L →L[ℂ] Hilbert L) :
    nativeCompression N L T =
      (fourierInclusion N L).adjoint.comp (T.comp (fourierInclusion N L)) := rfl

@[simp] theorem nativeCompression_killedShift (N : ℕ) (L : ℝ) (y : ℝ≥0) :
    nativeCompression N L (killedShift L y) = fourierShiftCompression N L y := rfl

/-- A finite-set version used by the literal arithmetic cutoff. -/
def sumCoefficients {N : ℕ} {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (C : ι → Coefficients N) : Coefficients N where
  diagonal i := ∑ a ∈ s, w a * (C a).diagonal i
  beta i := ∑ a ∈ s, w a * (C a).beta i
  diagonal_even i := by simp only [(C _).diagonal_even]
  beta_odd i := by simp only [(C _).beta_odd, mul_neg, sum_neg_distrib]

theorem weilMatrix_sumCoefficients {N : ℕ} {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (C : ι → Coefficients N) (i j : Index N) :
    weilMatrix (sumCoefficients s w C) i j = ∑ a ∈ s, (w a : ℂ) * weilMatrix (C a) i j := by
  by_cases hij : i = j
  · subst j
    simp [weilMatrix, sumCoefficients]
  · simp only [weilMatrix, if_neg hij, sumCoefficients]
    rw [← sum_sub_distrib, sum_div]
    push_cast
    apply sum_congr rfl
    intro a _
    ring

theorem weilOperator_sumCoefficients {N : ℕ} {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (C : ι → Coefficients N) :
    weilOperator (sumCoefficients s w C) = ∑ a ∈ s, (w a : ℂ) • weilOperator (C a) := by
  apply nativeOperator_ext_single
  intro i j
  simp [weilOperator_apply, weilMatrix_sumCoefficients]

/-- Only the physically surviving logarithmic shifts occur in the coefficient sum. -/
def primeSurvivors (L : ℝ) : Finset ℕ :=
  (Ioc 0 (primeCutoff L)).filter (fun n => Real.log n < L)

def primeRealWeight (σ : ℝ) (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n * Real.exp (-σ * Real.log n)

/-- Native coefficients of the negative Hermitian prime current. -/
def nativePrimeCoefficients (N : ℕ) (L σ : ℝ) : Coefficients N :=
  sumCoefficients (primeSurvivors L) (fun n => -primeRealWeight σ n)
    (fun n => hermitianShiftCoefficients N L (Real.log n))

theorem primeCurrent_sum_survivors (L σ : ℝ) :
    primeCurrent L σ = ∑ n ∈ primeSurvivors L,
      (primeRealWeight σ n : ℂ) • killedShift L (Arithmetic.natLog n) := by
  change ((Arithmetic.synthesis (primeCutoff L) (primeWeight L σ)
    ArithmeticFunction.vonMangoldt : primeAlgebra L) : Hilbert L →L[ℂ] Hilbert L) = _
  rw [prime_synthesis_sum]
  have hs : (∑ n ∈ Ioc 0 (primeCutoff L),
      (primeRealWeight σ n : ℂ) • killedShift L (Arithmetic.natLog n)) =
      ∑ n ∈ primeSurvivors L, (primeRealWeight σ n : ℂ) • killedShift L (Arithmetic.natLog n) := by
    rw [primeSurvivors, sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hlog : Real.log n < L
    · simp only [hlog, ↓reduceIte]
    · have hn0 : n ≠ 0 := ne_of_gt (mem_Ioc.mp hn).1
      have hk : killedShift L (Arithmetic.natLog n) = 0 :=
        killedShift_eq_zero L _ (by rw [Arithmetic.natLog_coe hn0]; exact le_of_not_gt hlog)
      simp only [hlog, ↓reduceIte, hk]
      exact @smul_zero ℂ (Hilbert L →L[ℂ] Hilbert L) _ _ (primeRealWeight σ n : ℂ)
  rw [← hs]
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := ne_of_gt (mem_Ioc.mp hn).1
  simp [primeShift, hn0, smul_smul, primeRealWeight,
    Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]

/-- Compression preserves the actual finite arithmetic current sum. -/
theorem nativeCompression_primeCurrent (N : ℕ) (L σ : ℝ) :
    nativeCompression N L (primeCurrent L σ) = ∑ n ∈ primeSurvivors L,
      (primeRealWeight σ n : ℂ) • fourierShiftCompression N L (Arithmetic.natLog n) := by
  rw [primeCurrent_sum_survivors, map_sum]
  apply sum_congr rfl
  intro n _
  rw [map_smul]
  rfl

/-- The native prime matrix is the negative Hermitian form of the actual current. -/
theorem nativePrime_weilOperator {N : ℕ} {L : ℝ} (hL : 0 < L) (σ : ℝ) :
    weilOperator (nativePrimeCoefficients N L σ) =
      -(nativeCompression N L (primeCurrent L σ) +
        (nativeCompression N L (primeCurrent L σ)).adjoint) := by
  rw [nativePrimeCoefficients, weilOperator_sumCoefficients, nativeCompression_primeCurrent]
  have ht : ∀ n ∈ primeSurvivors L,
      weilOperator (hermitianShiftCoefficients N L (Real.log n)) =
        fourierShiftCompression N L (Arithmetic.natLog n) +
        (fourierShiftCompression N L (Arithmetic.natLog n)).adjoint := by
    intro n hn
    have hn0 : n ≠ 0 := ne_of_gt (mem_Ioc.mp (mem_filter.mp hn).1).1
    have hh : (Arithmetic.natLog n : ℝ) ≤ L := by
      rw [Arithmetic.natLog_coe hn0]
      exact (mem_filter.mp hn).2.le
    simpa only [Arithmetic.natLog_coe hn0] using
      (hermitianShift_weilOperator (N := N) hL (Arithmetic.natLog n) hh).symm
  simp_rw [map_sum]
  simp only [map_smulₛₗ, Complex.conj_ofReal]
  rw [← sum_add_distrib, ← sum_neg_distrib]
  apply sum_congr rfl
  intro n hn
  rw [ht n hn]
  simp only [Complex.ofReal_neg, neg_smul, smul_add, neg_add_rev]
  abel

@[simp] theorem nativePrimeCoefficients_beta (N : ℕ) (L σ : ℝ) (i : Index N) :
    (nativePrimeCoefficients N L σ).beta i = ∑ n ∈ primeSurvivors L,
      primeRealWeight σ n * Real.sin (frequency L i * Real.log n) / Real.pi := by
  simp only [nativePrimeCoefficients, sumCoefficients, hermitianShiftCoefficients]
  apply sum_congr rfl
  intro n _
  ring

@[simp] theorem nativePrimeCoefficients_diagonal (N : ℕ) (L σ : ℝ) (i : Index N) :
    (nativePrimeCoefficients N L σ).diagonal i = -2 * ∑ n ∈ primeSurvivors L,
      primeRealWeight σ n * (1 - Real.log n / L) * Real.cos (frequency L i * Real.log n) := by
  simp only [nativePrimeCoefficients, sumCoefficients, hermitianShiftCoefficients, mul_sum]
  apply sum_congr rfl
  intro n _
  ring

end Riemann.Analysis.FiniteWindow
