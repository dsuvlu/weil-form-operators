import Riemann.Analysis.FiniteWindow.KilledShiftHilbert
import Riemann.Arithmetic.KilledShift

/-! # A.e. agreement with the preserved algebraic killed shifts

Restriction of a chosen L² representative is used only inside an a.e. equality.
It is not asserted to be a well-defined point-evaluation map on L² classes.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal
namespace Riemann.Analysis.FiniteWindow

/-- The actual Hilbert shift has precisely the representative action of the
preserved pointwise arithmetic shift. -/
theorem killedShift_agrees_algebraic_ae (L : ℝ) (y : ℝ≥0) (f : Hilbert L) :
    ∀ᵐ t : ℝ, ∀ ht : t ∈ Ico 0 L,
      ((killedShift L y f : Hilbert L) : Ambient) t =
        Riemann.Arithmetic.killedShift L y
          (fun u : Riemann.Arithmetic.Window L => (f : Ambient) u) ⟨t, ht⟩ := by
  filter_upwards [killedShift_ae L y f] with t ht hmem
  rw [ht, Riemann.Arithmetic.killedShift_apply]
  by_cases hy : t + (y : ℝ) < L
  · have hy' : (y : ℝ) + t < L := by simpa only [add_comm] using hy
    simp only [hmem, hy', and_self, ↓reduceIte, hy, ↓reduceDIte]
    congr 1
    exact add_comm _ _
  · have hy' : ¬(y : ℝ) + t < L := by simpa only [add_comm] using hy
    simp only [hmem, hy', and_false, ↓reduceIte, hy, ↓reduceDIte]

end Riemann.Analysis.FiniteWindow
