import Riemann.Arithmetic.KilledShift
import Mathlib.Analysis.SpecialFunctions.Complex.Log

noncomputable section
open scoped NNReal
namespace Riemann.Arithmetic

/-- The real logarithm, regarded as nonnegative for positive natural input. -/
def natLog (n : ℕ) : ℝ≥0 := Real.toNNReal (Real.log n)

theorem natLog_coe {n : ℕ} (hn : n ≠ 0) :
    (natLog n : ℝ) = Real.log n := by
  apply Real.coe_toNNReal
  exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

@[simp] theorem natLog_one : natLog 1 = 0 := by simp [natLog]

theorem natLog_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    natLog (m*n) = natLog m + natLog n := by
  apply NNReal.eq
  simp only [natLog_coe (mul_ne_zero hm hn), NNReal.coe_add, natLog_coe hm, natLog_coe hn]
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)]

/-- Zero is an algebraic bookkeeping index; every positive index is its actual logarithmic shift. -/
def multiplicativeShift (L : ℝ) : ℕ →*₀ Module.End ℂ (WindowFunctions L) where
  toFun n := if n = 0 then 0 else killedShift L (natLog n)
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · subst m; simp
    by_cases hn : n = 0
    · subst n; simp
    simp [hm, hn, natLog_mul hm hn, killedShift_mul]

theorem multiplicativeShift_eq (L : ℝ) {n : ℕ} (hn : n ≠ 0) :
    multiplicativeShift L n = killedShift L (natLog n) := by simp [multiplicativeShift, hn]

theorem multiplicativeShift_killed (L : ℝ) {n : ℕ} (hn : n ≠ 0)
    (h : L ≤ Real.log n) : multiplicativeShift L n = 0 := by
  rw [multiplicativeShift_eq L hn]
  exact killedShift_eq_zero L _ (by rwa [natLog_coe hn])

theorem multiplicativeShift_killed_of_exp_le (L : ℝ) {n : ℕ}
    (h : Real.exp L ≤ (n : ℝ)) : multiplicativeShift L n = 0 := by
  have hn : 0 < (n : ℝ) := (Real.exp_pos L).trans_le h
  exact multiplicativeShift_killed L (by exact_mod_cast ne_of_gt hn)
    ((Real.le_log_iff_exp_le hn).mpr h)

/-- The generated commutative algebra consists of actual function endomorphisms. -/
def shiftAlgebra (L : ℝ) : Subalgebra ℂ (Module.End ℂ (WindowFunctions L)) :=
  Algebra.adjoin ℂ (Set.range (multiplicativeShift L))

instance shiftAlgebra_comm (L : ℝ) : IsMulCommutative (shiftAlgebra L) :=
  Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    rw [← map_mul, ← map_mul, Nat.mul_comm])

open scoped IsMulCommutative in
instance shiftAlgebra_commRing (L : ℝ) : CommRing (shiftAlgebra L) :=
  inferInstance

/-- The arithmetic representation in its proven commutative image algebra. -/
def shiftCharacter (L : ℝ) : ℕ →*₀ shiftAlgebra L where
  toFun n := ⟨multiplicativeShift L n, Algebra.subset_adjoin ⟨n, rfl⟩⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_mul' m n := by ext; simp

@[simp] theorem shiftCharacter_coe (L : ℝ) (n : ℕ) :
    (shiftCharacter L n : Module.End ℂ (WindowFunctions L)) = multiplicativeShift L n := rfl

/-- Scalar Dirichlet weights in exponential form, with zero reserved for bookkeeping. -/
def dirichletWeight (s : ℂ) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else Complex.exp (-s * (Real.log n : ℂ))
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · subst m; simp
    by_cases hn : n = 0
    · subst n; simp
    simp only [mul_eq_zero, hm, hn, or_self, ↓reduceIte, Nat.cast_mul]
    rw [Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn), Complex.ofReal_add,
      mul_add, Complex.exp_add]

/-- n ↦ n^{-s} V_n as a multiplicative character in the native shift algebra. -/
def weightedShift (L : ℝ) (s : ℂ) : ℕ →*₀ shiftAlgebra L :=
  ((algebraMap ℂ (shiftAlgebra L)).toMonoidWithZeroHom.comp (dirichletWeight s)) *
    shiftCharacter L

end Riemann.Arithmetic
