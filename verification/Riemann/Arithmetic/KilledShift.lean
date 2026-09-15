import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
# Killed backward shifts on a finite interval

The carrier consists of actual complex functions on `[0,L)`. No norm,
completion, or finite-dimensionality is asserted. Translation parameters
are nonnegative. This is the algebraic model of manuscript §2.1 / RN34 §4.
-/

noncomputable section
open scoped NNReal
namespace Riemann.Arithmetic

abbrev Window (L : ℝ) := Set.Ico (0 : ℝ) L
abbrev WindowFunctions (L : ℝ) := Window L → ℂ

/-- Backward translation, killed at the right endpoint. -/
def killedShift (L : ℝ) (y : ℝ≥0) : Module.End ℂ (WindowFunctions L) where
  toFun f t := if h : (t : ℝ) + y < L then
    f ⟨t + y, add_nonneg t.property.1 y.property, h⟩ else 0
  map_add' f g := by ext t; dsimp; split_ifs <;> simp
  map_smul' c f := by ext t; dsimp; split_ifs <;> simp

@[simp] theorem killedShift_apply (L : ℝ) (y : ℝ≥0) (f : WindowFunctions L)
    (t : Window L) : killedShift L y f t =
      if h : (t : ℝ) + y < L then
        f ⟨t + y, add_nonneg t.property.1 y.property, h⟩ else 0 := rfl

@[simp] theorem killedShift_zero (L : ℝ) : killedShift L 0 = 1 := by
  ext f t
  simp [killedShift, t.property.2]

/-- The intermediate survival condition is redundant precisely because shifts are nonnegative. -/
theorem killedShift_mul (L : ℝ) (a b : ℝ≥0) :
    killedShift L a * killedShift L b = killedShift L (a + b) := by
  ext f t
  change killedShift L a (killedShift L b f) t = _
  simp only [killedShift_apply, NNReal.coe_add, add_assoc]
  split_ifs <;> try rfl
  all_goals exfalso; linarith [b.property]

/-- The boundary case y=L is killed as well. -/
theorem killedShift_eq_zero (L : ℝ) (y : ℝ≥0) (hy : L ≤ (y : ℝ)) :
    killedShift L y = 0 := by
  ext f t
  simp only [killedShift_apply, LinearMap.zero_apply, Pi.zero_apply]
  rw [dif_neg]
  linarith [t.property.1]

theorem killedShift_commute (L : ℝ) (a b : ℝ≥0) :
    Commute (killedShift L a) (killedShift L b) := by
  show killedShift L a * killedShift L b = killedShift L b * killedShift L a
  rw [killedShift_mul, killedShift_mul, add_comm]

end Riemann.Arithmetic
