import Riemann.Analysis.HalfLine.Kernel
import Riemann.Analysis.HalfLine.Volterra

/-! # The bounded critical half-line completion

The scalar kernel is the one derived from the arithmetic integer and square
sums. Integration is strong integration on each Hilbert vector.
-/
noncomputable section
open MeasureTheory Set Filter
namespace Riemann.Analysis.HalfLine

/-- The single bounded critical completed half-line operator. -/
def completedOperator : Hilbert →L[ℂ] Hilbert :=
  shiftFamily.kernelOperator criticalKernelL1

theorem integrable_completed_orbit (f : Hilbert) :
    Integrable (fun y => (criticalKernel y : ℂ) • shift y f) := by
  apply (shiftFamily.integrable_kernel_orbit criticalKernelL1 f).congr
  filter_upwards [criticalKernelL1_ae] with y hy
  exact congrArg (· • shift y f) hy

theorem completedOperator_apply (f : Hilbert) :
    completedOperator f = ∫ y, (criticalKernel y : ℂ) • shift y f := by
  change (∫ y, criticalKernelL1 y • shift y f) = _
  apply integral_congr_ae
  filter_upwards [criticalKernelL1_ae] with y hy
  rw [hy]

theorem completedOperator_apply_nonneg (f : Hilbert) :
    completedOperator f = ∫ y in Ici (0 : ℝ), (criticalKernel y : ℂ) • shift y f := by
  rw [completedOperator_apply]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [criticalKernel_of_neg (lt_of_not_ge hy)]
  simp

theorem norm_completedOperator_le_kernel :
    ‖completedOperator‖ ≤ ‖criticalKernelL1‖ :=
  shiftFamily.norm_kernelOperator_le _

theorem norm_completedOperator_le : ‖completedOperator‖ ≤ 8 * Real.pi / 3 :=
  norm_completedOperator_le_kernel.trans norm_criticalKernelL1_le

end Riemann.Analysis.HalfLine
