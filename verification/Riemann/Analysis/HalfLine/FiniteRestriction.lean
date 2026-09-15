import Riemann.Analysis.HalfLine.CompletedKernel
import Riemann.Analysis.HalfLine.CompletedCore

/-! # The unique bounded extension and its exact physical restrictions

The truncations are support projections. No Fourier compression or reducing
subspace assertion is used.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Riemann.Analysis.HalfLine

/-- The kernel operator extends the original Gamma/polar completed raw domain. -/
theorem completedOperator_extends_core (f : compactSupport) :
    completedOperator f = completedCore f := by
  rw [completedCore_eq_smoothing]
  exact completedOperator_eq_smoothed_rawEuler f

/-- Density gives uniqueness among bounded extensions of the same core map. -/
theorem completedOperator_unique {T : Hilbert →L[ℂ] Hilbert}
    (hT : ∀ f : compactSupport, T f = completedCore f) : T = completedOperator := by
  apply operator_ext_finite
  intro L hL f
  exact (hT (finiteCoreInclusion L hL f)).trans
    (completedOperator_extends_core (finiteCoreInclusion L hL f)).symm

/-- Exact physical support restriction to the frozen finite-window completion. -/
theorem completedOperator_finiteInclusion (L : ℝ) (hL : 0 < L)
    (f : FiniteWindow.Hilbert L) :
    completedOperator (finiteInclusion L f) =
      finiteInclusion L (FiniteWindow.completedFrame L (1/2) f) := by
  exact (completedOperator_extends_core (finiteCoreInclusion L hL f)).trans
    (completedCore_finiteInclusion L hL f)

/-- Invariance of each finite physical support space. -/
theorem completedOperator_preserves_finiteSupport (L : ℝ) (hL : 0 < L)
    (f : Hilbert) (hf : (f : Ambient) ∈ FiniteWindow.supported L) :
    (completedOperator f : Ambient) ∈ FiniteWindow.supported L := by
  have he := completedOperator_finiteInclusion L hL ⟨f, hf⟩
  exact he ▸ (FiniteWindow.completedFrame L (1/2) ⟨f, hf⟩).property

/-- Only the one-sided invariant-space identity is asserted. -/
theorem supportProjection_completedOperator_supportProjection (L : ℝ) (hL : 0 < L)
    (f : Hilbert) :
    supportProjection L (completedOperator (supportProjection L f)) =
      completedOperator (supportProjection L f) := by
  change supportProjection L (completedOperator (finiteInclusion L (finiteProjection L f))) = _
  rw [completedOperator_finiteInclusion L hL]
  change finiteInclusion L (finiteProjection L
      (finiteInclusion L (FiniteWindow.completedFrame L (1/2) (finiteProjection L f)))) = _
  rw [finiteProjection_inclusion]
  exact (completedOperator_finiteInclusion L hL (finiteProjection L f)).symm

/-- Strong support truncation convergence; no operator-norm convergence is claimed. -/
theorem completedOperator_supportTruncation_tendsto (f : Hilbert) :
    Tendsto (fun n : ℕ => supportProjection (n:ℝ)
      (completedOperator (supportProjection (n:ℝ) f))) atTop (𝓝 (completedOperator f)) := by
  apply (completedOperator.continuous.continuousAt.tendsto.comp (supportProjection_tendsto f)).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact (supportProjection_completedOperator_supportProjection (n:ℝ) (by exact_mod_cast hn) f).symm

end Riemann.Analysis.HalfLine
