import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RemovableSingularity

/-! Elementary complex sinc for the finite CCM characteristic.
The removable value is defined explicitly and identified with mathlib's
extended difference quotient; no limiting spectral assertion is involved.
-/

noncomputable section

namespace Riemann.Basic

/-- The entire complex sine quotient with its removable value at zero. -/
def complexSinc (w : ℂ) : ℂ := if w = 0 then 1 else Complex.sin w / w

@[simp] theorem complexSinc_zero : complexSinc 0 = 1 := by simp [complexSinc]

theorem complexSinc_of_ne_zero {w : ℂ} (hw : w ≠ 0) :
    complexSinc w = Complex.sin w / w := by simp [complexSinc, hw]

/-- Its product with the argument is sine, including at the removable point. -/
@[simp] theorem mul_complexSinc (w : ℂ) : w * complexSinc w = Complex.sin w := by
  by_cases hw : w = 0
  · simp [hw]
  · rw [complexSinc_of_ne_zero hw]
    field_simp

/-- The extended difference quotient supplies the removable value exactly. -/
theorem complexSinc_eq_dslope : complexSinc = dslope Complex.sin 0 := by
  funext w
  by_cases hw : w = 0
  · subst w
    simp [Complex.deriv_sin]
  · rw [complexSinc_of_ne_zero hw, dslope_of_ne _ hw]
    simp [slope, div_eq_mul_inv, mul_comm]

/-- Complex sinc is differentiable on the whole complex plane. -/
theorem differentiable_complexSinc : Differentiable ℂ complexSinc := by
  rw [complexSinc_eq_dslope, ← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (Filter.univ_mem)).mpr
    Complex.differentiable_sin.differentiableOn

/-- A nonreal argument cannot be a zero of complex sinc. -/
theorem complexSinc_ne_zero_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) :
    complexSinc w ≠ 0 := by
  have hw0 : w ≠ 0 := by intro h; exact hw (by simp [h])
  rw [complexSinc_of_ne_zero hw0]
  apply div_ne_zero _ hw0
  intro hs
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
  exact hw (by simp [hk])

/-- Cardinal values on the integer multiples of π. -/
@[simp] theorem complexSinc_int_mul_pi (k : ℤ) :
    complexSinc ((k : ℂ) * (Real.pi : ℂ)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · have harg : (k : ℂ) * (Real.pi : ℂ) ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hk) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    simp [complexSinc_of_ne_zero harg, Complex.sin_int_mul_pi, hk]

/-- Integer shifts of sine, with the phase convention used in the CCM Fourier sum. -/
theorem complex_sin_add_int_mul_pi (w : ℂ) (k : ℤ) :
    Complex.sin (w + (k : ℂ) * (Real.pi : ℂ)) = (-1 : ℂ) ^ k * Complex.sin w :=
  k.cast_negOnePow ℂ ▸ Complex.sin_antiperiodic.add_int_mul_eq k

/-- The same phase occurs for subtraction of an integer multiple of π. -/
theorem complex_sin_sub_int_mul_pi (w : ℂ) (k : ℤ) :
    Complex.sin (w - (k : ℂ) * (Real.pi : ℂ)) = (-1 : ℂ) ^ k * Complex.sin w :=
  k.cast_negOnePow ℂ ▸ Complex.sin_antiperiodic.sub_int_mul_eq k

end Riemann.Basic
