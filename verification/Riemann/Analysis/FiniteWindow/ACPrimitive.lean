import Riemann.Analysis.FiniteWindow.Volterra
import Riemann.Basic.L2IntegralRepresentative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # Terminal primitives of supported L² functions

The primitive is an actual absolutely continuous complex-valued function,
with a specified zero terminal trace and the negative L² derivative.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace Riemann.Analysis

/-- Lipschitz maps preserve absolute continuity of interval paths. -/
theorem absolutelyContinuous_lipschitz_comp {E F : Type*} [PseudoMetricSpace E]
    [PseudoMetricSpace F] {f : ℝ → E} {T : E → F} {a b : ℝ} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b) (hT : LipschitzWith K T) :
    AbsolutelyContinuousOnInterval (fun t => T (f t)) a b := by
  apply squeeze_zero (fun t => Finset.sum_nonneg (fun _ _ => dist_nonneg))
    (fun t => ?_) (by simpa using Filter.Tendsto.const_mul (K : ℝ) hf)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hT.dist_le_mul _ _

/-- The complex primitive is absolutely continuous, by its two real components. -/
theorem complex_integral_absolutelyContinuous {f : ℝ → ℂ} {a b c : ℝ}
    (hf : Integrable f) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun t => ∫ u in c..t, f u) a b := by
  have hr := hf.re.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral hc
  have hi := hf.im.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral hc
  have hrC := absolutelyContinuous_lipschitz_comp hr Complex.isometry_ofReal.lipschitz
  have hiC := absolutelyContinuous_lipschitz_comp hi Complex.isometry_ofReal.lipschitz
  have h := hrC.add (hiC.const_smul Complex.I)
  have heq : (fun t => ∫ u in c..t, f u) =
      ((fun t => Complex.ofReal (∫ u in c..t, (f u).re)) +
        fun t => Complex.I • Complex.ofReal (∫ u in c..t, (f u).im)) := by
    funext t
    change (∫ u in c..t, f u) =
      Complex.ofReal (∫ u in c..t, Complex.reCLM (f u)) +
      Complex.I • Complex.ofReal (∫ u in c..t, Complex.imCLM (f u))
    rw [Complex.reCLM.intervalIntegral_comp_comm hf.intervalIntegrable,
      Complex.imCLM.intervalIntegral_comp_comm hf.intervalIntegrable]
    change (∫ u in c..t, f u) =
      Complex.ofReal (∫ u in c..t, f u).re +
      Complex.I * Complex.ofReal (∫ u in c..t, f u).im
    simpa only [mul_comm] using (Complex.re_add_im (∫ u in c..t, f u)).symm
  rw [heq]
  exact h

namespace FiniteWindow

lemma integrable_supported (L : ℝ) (f : Hilbert L) : Integrable (f : Ambient) := by
  have h := integrableOn_Lp_of_measure_ne_top (f : Ambient) (by norm_num)
    (s := Ico 0 L) (by simp)
  exact (h.integrable_indicator measurableSet_Ico).congr (supported_ae L f).symm

/-- An actual continuous representative of the terminal primitive. -/
def terminalPrimitive (L : ℝ) (f : Hilbert L) (t : ℝ) : ℂ :=
  ∫ u in t..L, (f : Ambient) u

@[simp] theorem terminalPrimitive_terminal (L : ℝ) (f : Hilbert L) :
    terminalPrimitive L f L = 0 := by simp [terminalPrimitive]

lemma terminalPrimitive_absolutelyContinuous (L : ℝ) (f : Hilbert L) :
    AbsolutelyContinuousOnInterval (terminalPrimitive L f) 0 L := by
  have h := complex_integral_absolutelyContinuous (integrable_supported L f)
    (show L ∈ uIcc 0 L from right_mem_uIcc)
  have heq : terminalPrimitive L f = -(fun t => ∫ u in L..t, (f : Ambient) u) := by
    funext t
    exact intervalIntegral.integral_symm _ _
  rw [heq]
  exact h.neg

lemma terminalPrimitive_ae_hasDerivAt (L : ℝ) (f : Hilbert L) :
    ∀ᵐ t, t ∈ uIcc 0 L → HasDerivAt (terminalPrimitive L f) (-(f : Ambient) t) t := by
  have h := (integrable_supported L f).intervalIntegrable (a := 0) (b := L)
  filter_upwards [h.ae_hasDerivAt_integral] with t ht hmem
  have hd := (ht hmem L right_mem_uIcc).neg
  have heq : terminalPrimitive L f = -(fun t => ∫ u in L..t, (f : Ambient) u) := by
    funext t
    exact intervalIntegral.integral_symm _ _
  rw [heq]
  exact hd

/-- The translated, spatially cut scalar representative is jointly integrable
on any finite shift-parameter measure. -/
lemma integrable_cut_translation {μ : Measure ℝ} [IsFiniteMeasure μ]
    (L : ℝ) (f : Hilbert L) :
    Integrable (fun p : ℝ × ℝ => (Ico 0 L).indicator
      (fun t => (f : Ambient) (p.1 + t)) p.2) (μ.prod volume) := by
  let φ := fun y t : ℝ => (Ico 0 L).indicator (fun t => (f : Ambient) (y+t)) t
  have hφ : StronglyMeasurable (Function.uncurry φ) := by
    exact ((Lp.stronglyMeasurable (f : Ambient)).comp_measurable
      (measurable_fst.add measurable_snd)).indicator
        (measurableSet_Ico.preimage measurable_snd)
  have hi (y : ℝ) : Integrable (fun t => (f : Ambient) (y+t)) :=
    (measurePreserving_add_left volume y).integrable_comp_of_integrable
      (integrable_supported L f)
  have hcut (y : ℝ) : Integrable (φ y) :=
    (hi y).indicator measurableSet_Ico
  apply (integrable_prod_iff hφ.aestronglyMeasurable).2
  refine ⟨Eventually.of_forall hcut, ?_⟩
  apply (integrable_const (∫ t, ‖(f : Ambient) t‖)).mono'
    hφ.norm.integral_prod_right.aestronglyMeasurable
  filter_upwards with y
  rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
  calc
    _ ≤ ∫ t, ‖(f : Ambient) (y+t)‖ := by
      apply integral_mono_ae (hcut y).norm (hi y).norm
      filter_upwards with t
      change ‖(Ico 0 L).indicator (fun t => (f : Ambient) (y+t)) t‖ ≤ _
      by_cases ht : t ∈ Ico 0 L
      · simp [ht]
      · simp [ht]
    _ = _ := (measurePreserving_add_left volume y).integral_comp
      (Homeomorph.addLeft y).measurableEmbedding (fun t => ‖(f : Ambient) t‖)

/-- The Hilbert primitive has the literal shifted scalar-integral representative. -/
theorem volterra_zero_ae_integral {L : ℝ} (hL : 0 ≤ L) (f : Hilbert L) :
    ((volterra L 0 f : Ambient) : ℝ → ℂ) =ᵐ[volume]
      fun t => ∫ y in Ioc 0 L,
        (Ico 0 L).indicator (fun t => (f : Ambient) (y+t)) t := by
  let F := fun y : ℝ => (shift L y f : Ambient)
  let μ : Measure ℝ := volume.restrict (Ioc 0 L)
  have hF : Integrable F μ :=
    (((supported L).subtypeL.continuous.comp (continuous_shift_apply L f)).intervalIntegrable
      (μ := volume) 0 L).1
  have hrep : ∀ᵐ y ∂μ, (F y : ℝ → ℂ) =ᵐ[volume]
      fun t => (Ico 0 L).indicator (fun t => (f : Ambient) (y+t)) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hy0 : 0 ≤ y := hy.1.le
    have he : F y = cut L (translate y f) := by
      change (cut L (translate (y.toNNReal : ℝ) f)) = _
      rw [Real.coe_toNNReal y hy0]
    rw [he]
    filter_upwards [cut_ae L (translate y f), translate_ae y f] with t ht hs
    rw [ht]
    by_cases hmem : t ∈ Ico 0 L <;> simp [hmem, hs]
  have hi := integral_L2_ae (φ := fun y t => (Ico 0 L).indicator
    (fun t => (f : Ambient) (y+t)) t) hF (integrable_cut_translation (μ := μ) L f) hrep
  have he : (volterra L 0 f : Ambient) = ∫ y, F y ∂μ := by
    change (supported L).subtypeL (∫ y in 0..L, weightedOrbit L 0 f y) = _
    rw [← (supported L).subtypeL.intervalIntegral_comp_comm
      ((continuous_weightedOrbit L 0 f).intervalIntegrable (μ := volume) 0 L)]
    simp only [weightedOrbit, neg_zero, zero_mul, Complex.exp_zero, one_smul]
    exact intervalIntegral.integral_of_le hL
  rw [he]
  exact hi

lemma translated_integral_eq_terminalPrimitive {L t : ℝ} (hL : 0 ≤ L)
    (f : Hilbert L) (ht : t ∈ Ico 0 L) :
    (∫ y in Ioc 0 L, (f : Ambient) (y+t)) = terminalPrimitive L f t := by
  have htail : (∫ u in L..L+t, (f : Ambient) u) = 0 := by
    calc
      _ = ∫ _u in L..L+t, (0 : ℂ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [supported_ae L f] with u hu hmem
        have hLu : L < u := (uIoc_of_le (show L ≤ L+t by linarith [ht.1]) ▸ hmem).1
        have hn : u ∉ Ico 0 L := fun h => (not_lt_of_ge hLu.le) h.2
        simpa only [indicator_of_notMem hn] using hu
      _ = 0 := by simp
  rw [← intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_comp_add_right, zero_add]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    ((integrable_supported L f).intervalIntegrable (a := t) (b := L))
    ((integrable_supported L f).intervalIntegrable (a := L) (b := L+t))
  rw [htail, add_zero] at hadd
  exact hadd.symm

/-- Literal Volterra formula at zero, with the actual terminal AC representative. -/
theorem volterra_zero_ae {L : ℝ} (hL : 0 ≤ L) (f : Hilbert L) :
    ((volterra L 0 f : Ambient) : ℝ → ℂ) =ᵐ[volume]
      (Ico 0 L).indicator (terminalPrimitive L f) := by
  filter_upwards [volterra_zero_ae_integral hL f] with t ht
  rw [ht]
  by_cases hmem : t ∈ Ico 0 L
  · simp only [indicator_of_mem hmem]
    exact translated_integral_eq_terminalPrimitive hL f hmem
  · simp only [indicator_of_notMem hmem, integral_zero]

/-- Every terminal-zero AC representative with this L² derivative is the
negative terminal primitive; this is the converse domain identification. -/
theorem ac_terminal_eq_neg_primitive {L : ℝ} (g : Hilbert L) {f : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f 0 L) (hL : f L = 0)
    (hd : ∀ᵐ t, t ∈ uIcc 0 L → HasDerivAt f ((g : Ambient) t) t) :
    ∀ t ∈ uIcc 0 L, f t = -terminalPrimitive L g t := by
  have hsum := hf.add (terminalPrimitive_absolutelyContinuous L g)
  have hd0 : ∀ᵐ t, t ∈ uIcc 0 L →
      HasDerivAt (f + terminalPrimitive L g) 0 t := by
    filter_upwards [hd, terminalPrimitive_ae_hasDerivAt L g] with t ht hg hmem
    simpa using (ht hmem).add (hg hmem)
  obtain ⟨c, hc⟩ := hsum.const_of_ae_hasDerivAt_zero hd0
  have hc0 : c = 0 := by simpa [hL] using (hc L right_mem_uIcc).symm
  intro t ht
  have h := hc t ht
  rw [hc0] at h
  exact eq_neg_of_add_eq_zero_left h

end FiniteWindow
end Riemann.Analysis
