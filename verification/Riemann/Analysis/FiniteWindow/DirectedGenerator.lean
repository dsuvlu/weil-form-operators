import Riemann.Analysis.FiniteWindow.Volterra
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # The actual strong right generator of the killed semigroup

The graph is defined by the strong right derivative at zero. Its later
identification with the terminal-zero absolutely continuous domain is therefore
a theorem about this semigroup, rather than a replacement definition of it.
-/

noncomputable section
open MeasureTheory Set Filter
namespace Riemann.Analysis.FiniteWindow

/-- The actual strong right derivative at zero. -/
def HasGenerator (L : ℝ) (f g : Hilbert L) : Prop :=
  HasDerivWithinAt (fun h : ℝ => shift L h f) g (Ici 0) 0

/-- The right derivative propagates to every nonnegative orbit time. -/
theorem HasGenerator.orbit_right {L : ℝ} {f g : Hilbert L}
    (hfg : HasGenerator L f g) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun y : ℝ => shift L y f) (shift L t g) (Ici t) t := by
  have hsub : HasDerivWithinAt (fun y : ℝ => y - t) 1 (Ici t) t :=
    ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
  have hcomp := hfg.scomp_of_eq t hsub
    (show MapsTo (fun y : ℝ => y - t) (Ici t) (Ici 0) from
      fun y hy => (show 0 ≤ y - t from sub_nonneg.mpr hy)) (by simp)
  simp only [one_smul] at hcomp
  have hout := ((shift L t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hcomp
  apply hout.congr
  · intro y hy
    change shift L y f = shift L t (shift L (y - t) f)
    have he := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T f)
      (shift_add L ht (sub_nonneg.mpr hy))
    simpa only [ContinuousLinearMap.comp_apply, add_sub_cancel] using he.symm
  · simp

/-- The integrated orbit identity, proved from the actual right derivative. -/
theorem HasGenerator.orbit_integral {L : ℝ} {f g : Hilbert L}
    (hfg : HasGenerator L f g) {t : ℝ} (ht : 0 ≤ t) :
    (∫ y in 0..t, shift L y g) = shift L t f - f := by
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    (continuous_shift_apply L f).continuousOn
    (fun y hy => (hfg.orbit_right hy.1.le).Ioi_of_Ici)
    ((continuous_shift_apply L g).intervalIntegrable (μ := volume) 0 t)
  simpa only [shift_zero, ContinuousLinearMap.id_apply] using he

/-- Nilpotence identifies the graph with the inverse of the zero-parameter
Volterra operator; this is the converse domain inclusion. -/
theorem HasGenerator.eq_neg_volterra_zero {L : ℝ} (hL : 0 ≤ L)
    {f g : Hilbert L} (hfg : HasGenerator L f g) : f = -(volterra L 0 g) := by
  have he := hfg.orbit_integral hL
  simp [shift_eq_zero L le_rfl] at he
  have hv : volterra L 0 g = -f := by
    simpa only [volterra_apply, weightedOrbit, neg_zero, zero_mul, Complex.exp_zero,
      one_smul] using he
  rw [hv, neg_neg]

/-- Each Volterra output has its actual strong right derivative. -/
theorem hasGenerator_volterra (L : ℝ) (hL : 0 ≤ L) (b : ℂ) (f : Hilbert L) :
    HasGenerator L (volterra L b f) (b • volterra L b f - f) := by
  have hw := continuous_weightedOrbit L b f
  have hi := intervalIntegral.integral_hasDerivAt_right
    (hw.intervalIntegrable (μ := volume) 0 0) hw.stronglyMeasurable.stronglyMeasurableAtFilter
    hw.continuousAt
  have hc : HasDerivAt (fun h : ℝ => Complex.exp (b * (h : ℂ))) b 0 := by
    have hc := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul b).cexp
    simpa using (hc : HasDerivAt _ _ (0 : ℝ))
  have hd := hc.smul ((hasDerivAt_const (0 : ℝ) (volterra L b f)).sub hi)
  change HasDerivAt
    (fun h : ℝ => Complex.exp (b * (h : ℂ)) •
      (volterra L b f - ∫ y in 0..h, weightedOrbit L b f y))
    (Complex.exp (b * (0 : ℂ)) • (0 - weightedOrbit L b f 0) +
      b • (volterra L b f - ∫ y in 0..0, weightedOrbit L b f y)) 0 at hd
  have hd' : HasDerivWithinAt
      (fun h : ℝ => Complex.exp (b * (h : ℂ)) •
        (volterra L b f - ∫ y in 0..h, weightedOrbit L b f y))
      (b • volterra L b f - f) (Ici 0) 0 := by
    simpa only [mul_zero, Complex.exp_zero, zero_sub, weightedOrbit_zero,
      one_smul, intervalIntegral.integral_same, sub_zero, sub_eq_add_neg, add_comm, neg_zero, zero_add, add_zero]
      using (hd.hasDerivWithinAt (s := Ici 0))
  exact hd'.congr (fun h hh => shift_volterra L hL b f hh) (by simp)

/-- Exact characterization of the maximal strong generator graph. -/
theorem hasGenerator_iff_eq_neg_volterra_zero (L : ℝ) (hL : 0 ≤ L)
    (f g : Hilbert L) : HasGenerator L f g ↔ f = -(volterra L 0 g) := by
  constructor
  · exact HasGenerator.eq_neg_volterra_zero hL
  · intro h
    subst f
    have hd := (hasGenerator_volterra L hL 0 g).neg
    change HasDerivWithinAt (fun h : ℝ => shift L h (-(volterra L 0 g))) g (Ici 0) 0
    convert hd using 1
    · rfl
    · rfl
    · rfl
    · funext h
      exact map_neg (shift L h) _
    · simp

theorem HasGenerator.unique {L : ℝ} {f g g' : Hilbert L}
    (h : HasGenerator L f g) (h' : HasGenerator L f g') : g = g' :=
  (h.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
    (h'.derivWithin (uniqueDiffWithinAt_Ici 0))

/-- The second Volterra inverse, on the actual generator graph. -/
theorem HasGenerator.volterra_inverse {L : ℝ} (hL : 0 ≤ L) {f g : Hilbert L}
    (hfg : HasGenerator L f g) (b : ℂ) : volterra L b (b • f - g) = f := by
  have hd : ∀ t ∈ Ioo 0 L, HasDerivWithinAt (weightedOrbit L b f)
      (weightedOrbit L b (g - b • f) t) (Ioi t) t := by
    intro t ht
    have he : HasDerivAt (fun y : ℝ => Complex.exp (-b * (y : ℂ)))
        (Complex.exp (-b * (t : ℂ)) * (-b)) t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-b)).cexp
    have hd := he.hasDerivWithinAt.smul (hfg.orbit_right ht.1.le).Ioi_of_Ici
    convert hd using 1
    all_goals try rfl
    simp only [weightedOrbit, map_sub, map_smul, smul_sub, mul_smul, neg_smul]
    module
  have hw := continuous_weightedOrbit L b f
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hL hw.continuousOn hd
    ((continuous_weightedOrbit L b (g - b • f)).intervalIntegrable (μ := volume) 0 L)
  have hv : volterra L b (g - b • f) = -f := by
    simpa only [volterra_apply, weightedOrbit_eq_zero L b f le_rfl, weightedOrbit_zero, zero_sub] using he
  have hh : b • f - g = -(g - b • f) := by module
  rw [hh, map_neg, hv, neg_neg]

/-- The resolvent identity for every pair of complex parameters. -/
theorem volterra_resolvent_identity (L : ℝ) (hL : 0 ≤ L) (b c : ℂ) :
    volterra L b - volterra L c = (c - b) • ((volterra L b).comp (volterra L c)) := by
  apply ContinuousLinearMap.ext
  intro f
  have he := (hasGenerator_volterra L hL c f).volterra_inverse hL b
  change volterra L b f - volterra L c f = (c - b) • volterra L b (volterra L c f)
  simp only [map_sub, map_smul] at he
  calc
    _ = volterra L b f -
        (b • volterra L b (volterra L c f) -
          (c • volterra L b (volterra L c f) - volterra L b f)) :=
      congrArg (fun v : Hilbert L => volterra L b f - v) he.symm
    _ = _ := by module

theorem volterra_commute (L : ℝ) (hL : 0 ≤ L) (b c : ℂ) :
    (volterra L b).comp (volterra L c) = (volterra L c).comp (volterra L b) := by
  by_cases hbc : c = b
  · subst c; rfl
  apply smul_right_injective (Hilbert L →L[ℂ] Hilbert L) (sub_ne_zero.mpr hbc)
  dsimp only
  rw [← volterra_resolvent_identity L hL b c]
  have he := volterra_resolvent_identity L hL c b
  calc
    _ = -(volterra L c - volterra L b) := by module
    _ = -((b - c) • ((volterra L c).comp (volterra L b))) := congrArg Neg.neg he
    _ = _ := by module

theorem volterra_injective (L : ℝ) (hL : 0 ≤ L) (b : ℂ) :
    Function.Injective (volterra L b) := by
  intro f g h
  have hf := hasGenerator_volterra L hL b f
  have hg := hasGenerator_volterra L hL b g
  rw [h] at hf
  have he := hf.unique hg
  exact (sub_right_inj.mp he)

end Riemann.Analysis.FiniteWindow
