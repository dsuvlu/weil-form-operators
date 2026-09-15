import Riemann.Analysis.FiniteWindow.LiteralVolterra
import Riemann.Analysis.FiniteWindow.NativeFourierIsometry
import Riemann.Analysis.FiniteWindow.PolarOperator

/-! # The literal polar kernel

The two critical Volterra channels have a separable symmetric kernel. The
terminal-integral product identity is used to symmetrize the triangular
integrals without making an assertion about an unbounded adjoint.
-/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace Riemann.Analysis.FiniteWindow

theorem continuous_tailIntegral {f : ℝ → ℂ} (hf : Continuous f) (b : ℝ) :
    Continuous (fun t => ∫ u in t..b, f u) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (intervalIntegral.integral_hasDerivAt_left (hf.intervalIntegrable t b)
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).continuousAt

/-- The two triangular pieces of a separable square kernel. -/
theorem integral_tail_product {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) :
    (∫ t in a..b, f t * (∫ u in t..b, g u) + g t * (∫ u in t..b, f u)) =
      (∫ t in a..b, f t) * (∫ t in a..b, g t) := by
  have hd (t : ℝ) : HasDerivAt
      (fun t => -(∫ u in t..b, f u) * (∫ u in t..b, g u))
      (f t * (∫ u in t..b, g u) + g t * (∫ u in t..b, f u)) t := by
    have hF := intervalIntegral.integral_hasDerivAt_left (hf.intervalIntegrable t b)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
    have hG := intervalIntegral.integral_hasDerivAt_left (hg.intervalIntegrable t b)
      hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
    convert hF.neg.mul hG using 1
    all_goals try rfl
    simp only [Pi.neg_apply]
    ring
  have hi := ((hf.mul (continuous_tailIntegral hg b)).add
    (hg.mul (continuous_tailIntegral hf b))).intervalIntegrable (μ := volume) a b
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa only [intervalIntegral.integral_same, neg_zero, zero_mul, zero_sub, neg_mul, neg_neg] using he

def volterraRepresentative (L : ℝ) (b : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  Complex.exp (b * (t : ℂ)) * ∫ u in t..L, Complex.exp (-b * (u : ℂ)) * f u

theorem continuous_volterraRepresentative (L : ℝ) (b : ℂ) {f : ℝ → ℂ}
    (hf : Continuous f) : Continuous (volterraRepresentative L b f) := by
  exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp (b * (t : ℂ)))).mul
    (continuous_tailIntegral ((show Continuous (fun u : ℝ => Complex.exp (-b * (u : ℂ))) by fun_prop).mul hf) L)

theorem volterraRepresentative_eq (L t : ℝ) (b : ℂ) {f : ℝ → ℂ}
    (_hf : Continuous f) :
    volterraRepresentative L b f t =
      ∫ u in t..L, Complex.exp (-b * ((u-t : ℝ) : ℂ)) * f u := by
  rw [volterraRepresentative, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Continuous inputs have the literal continuous Volterra representative. -/
theorem volterra_ofContinuous {L : ℝ} (hL : 0 ≤ L) (b : ℂ) {f : ℝ → ℂ}
    (hf : Continuous f) :
    volterra L b (ofContinuous L f hf) =
      ofContinuous L (volterraRepresentative L b f) (continuous_volterraRepresentative L b hf) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [volterra_ae hL b (ofContinuous L f hf),
    ofContinuous_ae L (volterraRepresentative L b f) (continuous_volterraRepresentative L b hf)]
    with t ht hr
  rw [ht, hr]
  by_cases hm : t ∈ Ico 0 L
  · rw [indicator_of_mem hm, indicator_of_mem hm, volterraRepresentative_eq L t b hf]
    apply intervalIntegral.integral_congr_ae
    have hEnd : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ L := by simp [ae_iff]
    filter_upwards [ofContinuous_ae L f hf, hEnd] with u hu huEnd hmem
    have huL : u ∈ Ico 0 L := by
      rw [uIoc_of_le hm.2.le] at hmem
      exact ⟨le_trans hm.1 hmem.1.le, lt_of_le_of_ne hmem.2 huEnd⟩
    rw [hu, indicator_of_mem huL]
  · simp only [indicator_of_notMem hm]


theorem volterraRepresentative_real (L t b : ℝ) (f : ℝ → ℂ) :
    volterraRepresentative L (b : ℂ) f t =
      (Real.exp (b*t) : ℂ) * ∫ u in t..L, (Real.exp (-b*u) : ℂ) * f u := by
  simp only [volterraRepresentative, Complex.ofReal_exp, Complex.ofReal_mul,
    Complex.ofReal_neg]

/-- Pairing the opposite real resolvents fills a separable square kernel. -/
theorem inner_volterra_cross {L : ℝ} (hL : 0 ≤ L) (b : ℝ) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    ⟪ofContinuous L f hf, volterra L (b : ℂ) (ofContinuous L g hg)⟫_ℂ +
      ⟪volterra L (-b : ℂ) (ofContinuous L f hf), ofContinuous L g hg⟫_ℂ =
      (∫ t in 0..L, (Real.exp (b*t) : ℂ) * star (f t)) *
      (∫ t in 0..L, (Real.exp (-b*t) : ℂ) * g t) := by
  rw [volterra_ofContinuous hL (b : ℂ) hg, volterra_ofContinuous hL (-b : ℂ) hf,
    inner_ofContinuous hL _ _ hf (continuous_volterraRepresentative L (b : ℂ) hg),
    inner_ofContinuous hL _ _ (continuous_volterraRepresentative L (-b : ℂ) hf) hg]
  have hcf : Continuous (fun t : ℝ => (Real.exp (b*t) : ℂ) * star (f t)) := by fun_prop
  have hcg : Continuous (fun t : ℝ => (Real.exp (-b*t) : ℂ) * g t) := by fun_prop
  have hc1 := (hf.star.mul (continuous_volterraRepresentative L (b : ℂ) hg)).intervalIntegrable
    (μ := volume) 0 L
  have hc2 := ((continuous_volterraRepresentative L (-b : ℂ) hf).star.mul hg).intervalIntegrable
    (μ := volume) 0 L
  change IntervalIntegrable (fun t => star (f t) * volterraRepresentative L (b : ℂ) g t) volume 0 L at hc1
  change IntervalIntegrable (fun t => star (volterraRepresentative L (-b : ℂ) f t) * g t) volume 0 L at hc2
  rw [← intervalIntegral.integral_add hc1 hc2]
  calc
    _ = ∫ t in 0..L,
        ((Real.exp (b*t) : ℂ) * star (f t)) *
          (∫ u in t..L, (Real.exp (-b*u) : ℂ) * g u) +
        ((Real.exp (-b*t) : ℂ) * g t) *
          (∫ u in t..L, (Real.exp (b*u) : ℂ) * star (f u)) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [volterraRepresentative_real]
      rw [show (-b : ℂ) = ((-b : ℝ) : ℂ) by simp, volterraRepresentative_real]
      simp only [neg_neg, Complex.star_def, map_mul, Complex.conj_ofReal,
        ← intervalIntegral.intervalIntegral_conj]
      ring
    _ = _ := integral_tail_product hcf hcg 0 L

/-- The two critical channels occur exactly once in the full symmetric kernel. -/
def polarKernel (t u : ℝ) : ℂ :=
  (Real.exp ((t-u)/2) + Real.exp (-(t-u)/2) : ℝ)

theorem polarKernel_cosh (t u : ℝ) :
    polarKernel t u = (2 * Real.cosh ((t-u)/2) : ℝ) := by
  simp only [polarKernel, Real.cosh_eq, neg_div]
  norm_cast
  ring

theorem polarKernel_separable (t u : ℝ) :
    polarKernel t u = (Real.exp (t/2) : ℂ) * (Real.exp (-u/2) : ℂ) +
      (Real.exp (-t/2) : ℂ) * (Real.exp (u/2) : ℂ) := by
  simp only [polarKernel, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Real.exp_add]
  congr 2 <;> congr 1 <;> ring


/-- The Hermitian sum of the two actual critical Volterra channels has the
rank-two separable form associated with `polarKernel`. -/
theorem inner_polarVolterra {L : ℝ} (hL : 0 ≤ L) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    ⟪ofContinuous L f hf,
      (volterra L (1 / 2) + volterra L (-(1 / 2))) (ofContinuous L g hg)⟫_ℂ +
    ⟪(volterra L (1 / 2) + volterra L (-(1 / 2))) (ofContinuous L f hf),
      ofContinuous L g hg⟫_ℂ =
    (∫ t in 0..L, (Real.exp (t/2) : ℂ) * star (f t)) *
      (∫ t in 0..L, (Real.exp (-t/2) : ℂ) * g t) +
    (∫ t in 0..L, (Real.exp (-t/2) : ℂ) * star (f t)) *
      (∫ t in 0..L, (Real.exp (t/2) : ℂ) * g t) := by
  have hp := inner_volterra_cross hL (1 / 2) hf hg
  have hm := inner_volterra_cross hL (-(1 / 2)) hf hg
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_neg, neg_neg] at hp hm
  have he : ∀ t : ℝ, (1 / 2) * t = t / 2 := fun t => by ring
  have hn : ∀ t : ℝ, -(1 / 2) * t = -t / 2 := fun t => by ring
  simp only [he, hn] at hp hm
  simp only [add_apply, inner_add_right, inner_add_left]
  calc
    _ = (⟪ofContinuous L f hf, volterra L (1 / 2) (ofContinuous L g hg)⟫_ℂ +
          ⟪volterra L (-(1 / 2)) (ofContinuous L f hf), ofContinuous L g hg⟫_ℂ) +
        (⟪ofContinuous L f hf, volterra L (-(1 / 2)) (ofContinuous L g hg)⟫_ℂ +
          ⟪volterra L (1 / 2) (ofContinuous L f hf), ofContinuous L g hg⟫_ℂ) := by abel
    _ = _ := congrArg₂ (· + ·) hp hm

end Riemann.Analysis.FiniteWindow
