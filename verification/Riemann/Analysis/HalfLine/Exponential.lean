import Riemann.Analysis.HalfLine.Hilbert
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Actual half-line exponential vectors

All vectors are genuine supported L² classes. Their shift eigenrelations use
nonnegative time and positive real decay, independently of arithmetic kernels.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace NNReal ENNReal
namespace Riemann.Analysis.HalfLine

def exponentialFunction (r : ℝ) : ℝ → ℂ :=
  (Ici 0).indicator (fun t => (Real.exp (-r * t) : ℂ))

lemma exponentialFunction_measurable (r : ℝ) : Measurable (exponentialFunction r) := by
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul continuous_id))).measurable.indicator measurableSet_Ici

lemma exponentialFunction_norm_sq (r t : ℝ) :
    ‖exponentialFunction r t‖ ^ 2 =
      (Ici 0).indicator (fun t => Real.exp ((-2 * r) * t)) t := by
  by_cases ht : t ∈ Ici (0 : ℝ)
  · simp only [exponentialFunction, indicator_of_mem ht, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  · simp [exponentialFunction, ht]

lemma exponentialFunction_memLp {r : ℝ} (hr : 0 < r) :
    MemLp (exponentialFunction r) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (exponentialFunction_measurable r).aestronglyMeasurable).2
  simp_rw [exponentialFunction_norm_sq]
  apply IntegrableOn.integrable_indicator _ measurableSet_Ici
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_mul_Ioi (by linarith) 0

/-- Unnormalized positive-decay exponential in the physical half-line carrier. -/
def exponential (r : ℝ) (hr : 0 < r) : Hilbert := by
  let f : Ambient := (exponentialFunction_memLp hr).toLp (exponentialFunction r)
  refine ⟨f, (mem_supported_iff f).2 ?_⟩
  apply Lp.ext
  filter_upwards [cut_ae f, MemLp.coeFn_toLp (exponentialFunction_memLp hr)] with t hc hf
  rw [hc]
  by_cases ht : t ∈ Ici (0 : ℝ)
  · simp [ht]
  · simp only [indicator_of_notMem ht]
    rw [hf]
    simp [exponentialFunction, ht]

theorem exponential_ae (r : ℝ) (hr : 0 < r) :
    ((exponential r hr : Ambient) : ℝ → ℂ) =ᵐ[volume] exponentialFunction r :=
  MemLp.coeFn_toLp (exponentialFunction_memLp hr)

theorem norm_exponential_sq (r : ℝ) (hr : 0 < r) :
    ‖exponential r hr‖ ^ 2 = 1 / (2 * r) := by
  have h : ⟪(exponential r hr : Ambient), (exponential r hr : Ambient)⟫_ℂ =
      ((1 / (2 * r) : ℝ) : ℂ) := by
    rw [L2.inner_def]
    calc
      _ = ∫ t, (((Ici (0 : ℝ)).indicator
          (fun t => Real.exp ((-2 * r) * t)) t : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [exponential_ae r hr] with t ht
        rw [ht, inner_self_eq_norm_sq_to_K]
        simp only [← RCLike.ofReal_pow, exponentialFunction_norm_sq]
        rfl
      _ = _ := by
        rw [integral_complex_ofReal, integral_indicator measurableSet_Ici,
          integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (by linarith)]
        simp
  have h' := congrArg Complex.re h
  change RCLike.re ⟪exponential r hr, exponential r hr⟫_ℂ = _ at h'
  simpa only [inner_self_eq_norm_sq, Complex.ofReal_re] using h'

theorem shift_exponential (r : ℝ) (hr : 0 < r) (y : ℝ) (hy : 0 ≤ y) :
    shift y (exponential r hr) = (Real.exp (-r * y) : ℂ) • exponential r hr := by
  apply Subtype.ext
  simp only [Submodule.coe_smul]
  apply Lp.ext
  have ht := (measurePreserving_add_left volume y).quasiMeasurePreserving.ae
    (exponential_ae r hr)
  filter_upwards [killedShift_ae y.toNNReal (exponential r hr), ht,
    exponential_ae r hr,
    Lp.coeFn_smul (Real.exp (-r*y) : ℂ) (exponential r hr : Ambient)] with t hs ht hf hm
  simp only [shift]
  rw [hs, hm]
  simp only [Real.coe_toNNReal _ hy] at *
  simp only [Pi.smul_apply]
  rw [hf]
  by_cases h : 0 ≤ t
  · rw [if_pos h, ht]
    simp only [exponentialFunction, indicator_of_mem (show t ∈ Ici (0 : ℝ) from h),
      indicator_of_mem (show y + t ∈ Ici (0 : ℝ) from add_nonneg hy h),
      smul_eq_mul, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · simp [h, exponentialFunction]

/-- The normalized exponential used to test a lower bound. -/
def unitExponential (r : ℝ) (hr : 0 < r) : Hilbert :=
  (Real.sqrt (2*r) : ℂ) • exponential r hr

theorem norm_unitExponential (r : ℝ) (hr : 0 < r) : ‖unitExponential r hr‖ = 1 := by
  have h : ‖unitExponential r hr‖ ^ 2 = 1 := by
    rw [unitExponential, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (by positivity), norm_exponential_sq]
    field_simp
  nlinarith [norm_nonneg (unitExponential r hr)]

theorem shift_unitExponential (r : ℝ) (hr : 0 < r) (y : ℝ) (hy : 0 ≤ y) :
    shift y (unitExponential r hr) = (Real.exp (-r*y) : ℂ) • unitExponential r hr := by
  simp only [unitExponential, map_smul, shift_exponential r hr y hy]
  exact smul_comm _ _ _

end Riemann.Analysis.HalfLine
