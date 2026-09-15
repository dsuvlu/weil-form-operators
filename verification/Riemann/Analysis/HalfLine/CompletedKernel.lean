import Riemann.Analysis.HalfLine.KernelTranslation
import Riemann.Analysis.HalfLine.RawEuler

/-! # Derivation of the completed operator on compact support

The arithmetic sum is finite. Each term is translated under a strong vector
integral, and the resulting scalar sum is the derived floor kernel.
-/
noncomputable section
open MeasureTheory Set Filter
namespace Riemann.Analysis.HalfLine

theorem smoothingOperator_rawPartialSum (N : ℕ) (f : Hilbert) :
    smoothingOperator (rawPartialSum N f) =
      ∫ y, ((∑ n ∈ Finset.Ioc 0 N, arithmeticKernelTerm n y) : ℂ) • shift y f := by
  rw [rawPartialSum_apply, map_sum]
  calc
    _ = ∑ n ∈ Finset.Ioc 0 N, ∫ y, (arithmeticKernelTerm n y : ℂ) • shift y f := by
      apply Finset.sum_congr rfl
      intro n hn
      exact smoothingOperator_raw_term (Finset.mem_Ioc.mp hn).1 f
    _ = ∫ y, ∑ n ∈ Finset.Ioc 0 N, (arithmeticKernelTerm n y : ℂ) • shift y f := by
      symm
      exact integral_finsetSum _ (fun n _ =>
        integrable_scalar_shift (integrable_arithmeticKernelTerm n) f)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [Finset.sum_smul]

/-- Finite support supplies the represented killing needed by the arithmetic cutoff. -/
theorem completedOperator_finite_kernel (L : ℝ) (f : FiniteWindow.Hilbert L) :
    smoothingOperator (rawPartialSum (FiniteWindow.primeCutoff L) (finiteInclusion L f)) =
      completedOperator (finiteInclusion L f) := by
  rw [smoothingOperator_rawPartialSum, completedOperator_apply]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y < L
  · have hc : arithmeticCount y ≤ FiniteWindow.primeCutoff L :=
      Nat.cast_le.mp ((arithmeticCount_le y).trans
        ((Real.exp_le_exp.mpr hy.le).trans (Nat.le_ceil (Real.exp L))))
    have hs := congrArg (fun t : ℝ => (t:ℂ))
      (sum_arithmeticKernelTerm_Ioc (FiniteWindow.primeCutoff L) y hc)
    push_cast at hs
    rw [hs]
  · rw [shift_finiteInclusion_eq_zero L (le_of_not_gt hy)]
    simp

/-- Equality on the actual dense raw domain, derived before taking the extension. -/
theorem completedOperator_eq_smoothed_rawEuler (f : compactSupport) :
    completedOperator f = smoothingOperator (rawEuler f) := by
  obtain ⟨L, hL, w, hw⟩ := compactSupport_representation f
  rw [hw, rawEuler_finiteInclusion]
  change completedOperator (finiteInclusion L w) =
    smoothingOperator (finiteInclusion L (FiniteWindow.primeOperator L (1/2) w))
  rw [← rawPartialSum_finiteInclusion]
  exact (completedOperator_finite_kernel L w).symm

end Riemann.Analysis.HalfLine
