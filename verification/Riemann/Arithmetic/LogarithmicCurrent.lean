import Riemann.Arithmetic.FiniteSynthesis

/-! The formal coefficient derivation of finite Dirichlet polynomials.
This does not equip the window-function carrier with a topology. -/

noncomputable section
open Finset
namespace Riemann.Arithmetic

/-- The coefficient rule d(n^{-s})/ds=−log(n)n^{-s}. -/
def coefficientDerivative (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := -Real.log n * f n
  map_zero' := by simp

@[simp] theorem coefficientDerivative_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    coefficientDerivative f n = -Real.log n * f n := rfl

/-- The coefficient rule is a derivation for Dirichlet convolution. -/
theorem coefficientDerivative_mul (f g : ArithmeticFunction ℝ) :
    coefficientDerivative (f*g) = coefficientDerivative f*g + f*coefficientDerivative g := by
  ext n
  simp only [coefficientDerivative_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := Nat.mem_divisorsAntidiagonal.mp hd
  have hd0 : d.1*d.2 ≠ 0 := by rw [hd'.1]; exact hd'.2
  have hm : (d.1 : ℝ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hd0
  have hn : (d.2 : ℝ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hd0
  rw [← hd'.1, Nat.cast_mul, Real.log_mul hm hn]
  ring

open scoped ArithmeticFunction.zeta

@[simp] theorem coefficientDerivative_zeta :
    coefficientDerivative (ζ : ArithmeticFunction ℝ) = -ArithmeticFunction.log := by
  ext n
  by_cases hn : n=0
  · subst n; simp
  simp [coefficientDerivative, ArithmeticFunction.neg_apply, ArithmeticFunction.log_apply, hn]

/-- The derivative used in logarithmicCurrent is exactly synthesized coefficient differentiation. -/
theorem eulerCoefficientDerivative_eq {R : Type*} [CommRing R] [Algebra ℝ R]
    (X : ℕ) (w : ℕ →*₀ R) :
    eulerCoefficientDerivative X w = synthesis X w (coefficientDerivative ζ) := by
  simp [eulerCoefficientDerivative]

end Riemann.Arithmetic
