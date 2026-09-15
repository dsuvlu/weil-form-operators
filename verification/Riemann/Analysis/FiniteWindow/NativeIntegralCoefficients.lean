import Riemann.Analysis.FiniteWindow.NativePrimeCoefficients
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Integration of native divided-difference coefficients

Integration takes place in scalar matrix entries. No operator-valued Bochner
measurability on the infinite-dimensional Hilbert space is required.
-/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Riemann.Analysis.FiniteWindow
open Riemann.CCM.Native

/-- Scalar integrals preserve the exact native parity conditions. -/
def integralCoefficients {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (C : Ω → Coefficients N) : Coefficients N where
  diagonal i := ∫ y, (C y).diagonal i ∂μ
  beta i := ∫ y, (C y).beta i ∂μ
  diagonal_even i := by simp only [(C _).diagonal_even]
  beta_odd i := by simp only [(C _).beta_odd, integral_neg]

/-- The scalar integral commutes with each actual native matrix entry. -/
theorem weilMatrix_integralCoefficients {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (C : Ω → Coefficients N)
    (hb : ∀ i, Integrable (fun y => (C y).beta i) μ) (i j : Index N) :
    weilMatrix (integralCoefficients μ C) i j =
      ∫ y, weilMatrix (C y) i j ∂μ := by
  by_cases hij : i = j
  · subst j
    simp [weilMatrix, integralCoefficients, integral_complex_ofReal]
  · simp only [weilMatrix, if_neg hij, integralCoefficients]
    rw [integral_complex_ofReal, integral_div, integral_sub (hb i) (hb j)]

/-- Every scalar native matrix entry is integrable when its coefficients are. -/
theorem integrable_weilMatrix {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (C : Ω → Coefficients N)
    (hd : ∀ i, Integrable (fun y => (C y).diagonal i) μ)
    (hb : ∀ i, Integrable (fun y => (C y).beta i) μ) (i j : Index N) :
    Integrable (fun y => weilMatrix (C y) i j) μ := by
  by_cases hij : i = j
  · subst j
    simp only [weilMatrix, ↓reduceIte]
    convert (hd i).ofReal using 1
    rfl
  · simp only [weilMatrix, if_neg hij]
    convert (((hb i).sub (hb j)).div_const ((mode i : ℝ) - mode j)).ofReal using 1
    rfl

/-- Integrability of actual matrix entries recovers normalized coefficient integrability. -/
theorem integrable_coefficients_of_entries {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (C : Ω → Coefficients N)
    (hzero : ∀ y, (C y).beta (zeroIndex N) = 0)
    (he : ∀ i j, Integrable (fun y => weilMatrix (C y) i j) μ) :
    (∀ i, Integrable (fun y => (C y).diagonal i) μ) ∧
      (∀ i, Integrable (fun y => (C y).beta i) μ) := by
  constructor
  · intro i
    have hh := (he i i).re
    convert hh using 1
    funext y
    simp [weilMatrix, RCLike.re_to_complex]
  · intro i
    by_cases hi : i = zeroIndex N
    · subst i
      simp only [hzero]
      convert (integrable_zero Ω ℝ μ) using 1 <;> rfl
    · have hm : (mode i : ℝ) ≠ 0 := by
        have hh := mode_difference_ne_zero hi
        simpa using hh
      have hh := (he i (zeroIndex N)).re.const_mul (mode i : ℝ)
      convert hh using 1
      funext y
      simp [weilMatrix, hi, hzero, RCLike.re_to_complex]
      field_simp

/-- A scalar identity contributes only its real constant diagonal. -/
def scalarCoefficients (N : ℕ) (c : ℝ) : Coefficients N where
  diagonal _ := c
  beta _ := 0
  diagonal_even _ := rfl
  beta_odd _ := by simp

@[simp] theorem weilOperator_scalarCoefficients (N : ℕ) (c : ℝ) :
    weilOperator (scalarCoefficients N c) = (c : ℂ) • ContinuousLinearMap.id ℂ (Section N) := by
  apply nativeOperator_ext_single
  intro i j
  by_cases hij : i = j <;> simp [weilOperator_apply, weilMatrix, scalarCoefficients, hij]

/-- Addition and real scaling of exact native coefficients. -/
def addCoefficients {N : ℕ} (C D : Coefficients N) : Coefficients N where
  diagonal i := C.diagonal i + D.diagonal i
  beta i := C.beta i + D.beta i
  diagonal_even i := by rw [C.diagonal_even, D.diagonal_even]
  beta_odd i := by rw [C.beta_odd, D.beta_odd]; ring

def scaleCoefficients {N : ℕ} (a : ℝ) (C : Coefficients N) : Coefficients N where
  diagonal i := a * C.diagonal i
  beta i := a * C.beta i
  diagonal_even i := by rw [C.diagonal_even]
  beta_odd i := by rw [C.beta_odd]; ring

@[simp] theorem weilMatrix_addCoefficients {N : ℕ} (C D : Coefficients N) (i j : Index N) :
    weilMatrix (addCoefficients C D) i j = weilMatrix C i j + weilMatrix D i j := by
  by_cases hij : i = j
  · simp [weilMatrix, addCoefficients, hij]
  · simp [weilMatrix, addCoefficients, hij]
    ring

@[simp] theorem weilMatrix_scaleCoefficients {N : ℕ} (a : ℝ) (C : Coefficients N) (i j : Index N) :
    weilMatrix (scaleCoefficients a C) i j = (a : ℂ) * weilMatrix C i j := by
  by_cases hij : i = j
  · simp [weilMatrix, scaleCoefficients, hij]
  · simp [weilMatrix, scaleCoefficients, hij]
    ring

@[simp] theorem weilOperator_addCoefficients {N : ℕ} (C D : Coefficients N) :
    weilOperator (addCoefficients C D) = weilOperator C + weilOperator D := by
  apply nativeOperator_ext_single
  intro i j
  simp [weilOperator_apply]

@[simp] theorem weilOperator_scaleCoefficients {N : ℕ} (a : ℝ) (C : Coefficients N) :
    weilOperator (scaleCoefficients a C) = (a : ℂ) • weilOperator C := by
  apply nativeOperator_ext_single
  intro i j
  simp [weilOperator_apply]

end Riemann.Analysis.FiniteWindow
