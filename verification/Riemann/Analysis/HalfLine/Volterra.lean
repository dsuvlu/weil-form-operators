import Riemann.Analysis.HalfLine.FiniteSupport
import Riemann.Analysis.FiniteWindow.StrongKernelIntegral
import Riemann.Analysis.FiniteWindow.DirectedGenerator
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Positive half-line Volterra factors

These are actual strong integrals on the supported half-line L² space. All
substantive resolvent assertions require a strictly positive real parameter.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace Riemann.Analysis.HalfLine

/-- Strong integration uses scalar kernels on the ambient real line. -/
def shiftFamily : StrongContractionFamily (volume : Measure ℝ) Hilbert where
  operator := shift
  measurable_orbit f := (continuous_shift_apply f).aestronglyMeasurable
  norm_le := norm_shift_le

/-- The positive Volterra kernel, zero extended to negative times. -/
def volterraKernel (b y : ℝ) : ℂ :=
  (Ici 0).indicator (fun y => (Real.exp (-b * y) : ℂ)) y

theorem integrable_volterraKernel {b : ℝ} (hb : 0 < b) : Integrable (volterraKernel b) := by
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  apply (integrableOn_Ici_iff_integrableOn_Ioi).mpr
  exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) 0).ofReal

def volterraKernelL1 (b : ℝ) : Lp ℂ 1 (volume : Measure ℝ) :=
  if hb : 0 < b then (memLp_one_iff_integrable.mpr (integrable_volterraKernel hb)).toLp
    (volterraKernel b) else 0

theorem volterraKernelL1_ae {b : ℝ} (hb : 0 < b) :
    (volterraKernelL1 b : ℝ → ℂ) =ᵐ[volume] volterraKernel b := by
  simp only [volterraKernelL1, dif_pos hb]
  exact MemLp.coeFn_toLp _

theorem norm_volterraKernelL1 {b : ℝ} (hb : 0 < b) :
    ‖volterraKernelL1 b‖ = b⁻¹ := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ y, (Ici (0 : ℝ)).indicator (fun y => Real.exp (-b * y)) y := by
      apply integral_congr_ae
      filter_upwards [volterraKernelL1_ae hb] with y hy
      rw [hy]
      by_cases hy0 : y ∈ Ici (0 : ℝ)
      · simp only [volterraKernel, indicator_of_mem hy0, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      · simp [volterraKernel, hy0]
    _ = b⁻¹ := by
      rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
        integral_exp_mul_Ioi (neg_neg_of_pos hb)]
      simp

/-- Positive real Volterra factors; the unused nonpositive branch is zero. -/
def volterra (b : ℝ) : Hilbert →L[ℂ] Hilbert :=
  shiftFamily.kernelOperator (volterraKernelL1 b)

theorem norm_volterra_le {b : ℝ} (hb : 0 < b) : ‖volterra b‖ ≤ b⁻¹ :=
  (shiftFamily.norm_kernelOperator_le _).trans_eq (norm_volterraKernelL1 hb)

theorem integrable_volterra_orbit {b : ℝ} (hb : 0 < b) (f : Hilbert) :
    Integrable (fun y => volterraKernel b y • shift y f) := by
  apply (shiftFamily.integrable_kernel_orbit (volterraKernelL1 b) f).congr
  filter_upwards [volterraKernelL1_ae hb] with y hy
  exact congrArg (· • shift y f) hy

theorem volterra_apply {b : ℝ} (hb : 0 < b) (f : Hilbert) :
    volterra b f = ∫ y in Ici (0 : ℝ), (Real.exp (-b * y) : ℂ) • shift y f := by
  change (∫ y, volterraKernelL1 b y • shift y f) = _
  calc
    _ = ∫ y, (Ici (0 : ℝ)).indicator
        (fun y => (Real.exp (-b * y) : ℂ) • shift y f) y := by
      apply integral_congr_ae
      filter_upwards [volterraKernelL1_ae hb] with y hy
      rw [hy]
      by_cases hy0 : y ∈ Ici (0 : ℝ) <;> simp [volterraKernel, hy0]
    _ = _ := integral_indicator measurableSet_Ici

/-- Exact finite-window restriction of every positive half-line factor. -/
theorem volterra_finiteInclusion (L : ℝ) (hL : 0 ≤ L) {b : ℝ} (hb : 0 < b)
    (f : FiniteWindow.Hilbert L) :
    volterra b (finiteInclusion L f) =
      finiteInclusion L (FiniteWindow.volterra L (b : ℂ) f) := by
  rw [volterra_apply hb, FiniteWindow.volterra_apply]
  calc
    _ = ∫ y in Icc (0 : ℝ) L,
        (Real.exp (-b * y) : ℂ) • shift y (finiteInclusion L f) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici
        (fun _ h => h.1)
      intro y hy
      have hLy : L ≤ y := by
        have hn : ¬ y ≤ L := fun h => hy.2 ⟨hy.1, h⟩
        exact (lt_of_not_ge hn).le
      rw [shift_finiteInclusion_eq_zero L hLy, smul_zero]
    _ = ∫ y in 0..L,
        (Real.exp (-b * y) : ℂ) • shift y (finiteInclusion L f) := by
      rw [intervalIntegral.integral_of_le hL, integral_Icc_eq_integral_Ioc]
    _ = ∫ y in 0..L, (finiteInclusion L).toContinuousLinearMap
        (FiniteWindow.weightedOrbit L (b : ℂ) f y) := by
      apply intervalIntegral.integral_congr
      intro y _
      simp only [FiniteWindow.weightedOrbit, LinearIsometry.coe_toContinuousLinearMap,
        map_smul, shift_finiteInclusion]
      congr 1
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    _ = _ := (finiteInclusion L).toContinuousLinearMap.intervalIntegral_comp_comm
      ((FiniteWindow.continuous_weightedOrbit L (b : ℂ) f).intervalIntegrable
        (μ := volume) 0 L)

/-- Equality of bounded maps is determined on the physical finite windows. -/
theorem operator_ext_finite {T U : Hilbert →L[ℂ] Hilbert}
    (h : ∀ (L : ℝ), 0 < L → ∀ f : FiniteWindow.Hilbert L,
      T (finiteInclusion L f) = U (finiteInclusion L f)) : T = U := by
  apply ContinuousLinearMap.ext
  have he : Set.EqOn T U (compactSupport : Set Hilbert) := by
    intro f hf
    obtain ⟨L, hL, hg⟩ := hf
    exact h L hL ⟨f, hg⟩
  intro f
  exact he.closure T.continuous U.continuous (compactSupport_dense f)

/-- The resolvent identity transfers from the exact finite restrictions. -/
theorem volterra_resolvent_identity {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    volterra b - volterra c = ((c - b : ℝ) : ℂ) • ((volterra b).comp (volterra c)) := by
  apply operator_ext_finite
  intro L hL f
  have he := congrArg (fun T : FiniteWindow.Hilbert L →L[ℂ] FiniteWindow.Hilbert L =>
    finiteInclusion L (T f)) (FiniteWindow.volterra_resolvent_identity L hL.le (b : ℂ) (c : ℂ))
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, map_sub, map_smul] at he ⊢
  rw [volterra_finiteInclusion L hL.le hb, volterra_finiteInclusion L hL.le hc,
    volterra_finiteInclusion L hL.le hb]
  simpa only [Complex.ofReal_sub] using he

theorem volterra_commute {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    (volterra b).comp (volterra c) = (volterra c).comp (volterra b) := by
  apply operator_ext_finite
  intro L hL f
  have he := congrArg (fun T : FiniteWindow.Hilbert L →L[ℂ] FiniteWindow.Hilbert L =>
    finiteInclusion L (T f)) (FiniteWindow.volterra_commute L hL.le (b : ℂ) (c : ℂ))
  simp only [ContinuousLinearMap.comp_apply] at he ⊢
  rw [volterra_finiteInclusion L hL.le hc, volterra_finiteInclusion L hL.le hb,
    volterra_finiteInclusion L hL.le hb, volterra_finiteInclusion L hL.le hc]
  exact he

end Riemann.Analysis.HalfLine
