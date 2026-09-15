import Riemann.Analysis.FiniteWindow.GammaOperator
import Riemann.Analysis.FiniteWindow.GeneratorOperator

/-! # The explicit renormalized Gamma current and its domain

The domain is an intrinsic integrability condition on the difference of shift
orbits. It is not asserted to be invariant under the current, or to be a graph
core of any separately closed operator. The terminal-zero generator domain is
contained in it; finite Fourier vectors require a separate endpoint estimate.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Riemann.Analysis.FiniteWindow

/-- Singular shift weight of the one-sided Gamma current. -/
def gammaWeight (y : ℝ) : ℝ := Real.exp (-y / 2) / (1 - Real.exp (-2 * y))

/-- The regular scalar difference left after cancelling the singular identity term. -/
def gammaRemainder (y : ℝ) : ℝ :=
  (Real.exp (-y / 2) - Real.exp (-2 * y)) / (1 - Real.exp (-2 * y))

/-- The convergent difference integrand, with both subtraction terms retained. -/
def gammaIntegrand (L : ℝ) (f : Hilbert L) (y : ℝ) : Hilbert L :=
  (gammaWeight y : ℂ) • (shift L y f - f) + (gammaRemainder y : ℂ) • f

def gammaConstant (L : ℝ) : ℝ :=
  (Real.eulerMascheroniConstant + Real.log Real.pi) / 2 +
    Real.log (1 - Real.exp (-2 * L)) / 2

theorem gammaWeight_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ gammaWeight y :=
  div_nonneg (Real.exp_pos _).le (GammaCompletion.base_arg_pos hy).le

theorem gammaRemainder_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ gammaRemainder y := by
  apply div_nonneg _ (GammaCompletion.base_arg_pos hy).le
  apply sub_nonneg.mpr
  exact Real.exp_le_exp.mpr (by linarith)

theorem gammaRemainder_le_one {y : ℝ} (hy : 0 < y) : gammaRemainder y ≤ 1 := by
  apply (div_le_one (GammaCompletion.base_arg_pos hy)).mpr
  have he := Real.exp_le_one_iff.mpr (show -y / 2 ≤ 0 by linarith)
  linarith

theorem gammaWeight_mul_le {L y : ℝ} (_hL : 0 < L) (hy : y ∈ Ioo 0 L) :
    gammaWeight y * y ≤ (2 * Real.exp (-2 * L))⁻¹ := by
  have hc : 0 < 2 * Real.exp (-2 * L) := by positivity
  have hq := GammaCompletion.base_arg_pos hy.1
  have he : Real.exp (-y / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hy.1])
  have hl := GammaCompletion.base_arg_lower hy.1.le hy.2.le
  dsimp [gammaWeight]
  rw [div_mul_eq_mul_div, inv_eq_one_div, le_div_iff₀ hc, div_mul_eq_mul_div, div_le_one hq]
  nlinarith [mul_le_mul_of_nonneg_right he hy.1.le]

theorem gammaIntegrand_add (L : ℝ) (f g : Hilbert L) (y : ℝ) :
    gammaIntegrand L (f + g) y = gammaIntegrand L f y + gammaIntegrand L g y := by
  simp only [gammaIntegrand, map_add]
  module

theorem gammaIntegrand_smul (L : ℝ) (a : ℂ) (f : Hilbert L) (y : ℝ) :
    gammaIntegrand L (a • f) y = a • gammaIntegrand L f y := by
  simp only [gammaIntegrand, map_smul]
  module

def gammaCurrentDomain (L : ℝ) : Submodule ℂ (Hilbert L) where
  carrier := {f | IntegrableOn (gammaIntegrand L f) (Ioo 0 L)}
  zero_mem' := by
    change IntegrableOn (gammaIntegrand L 0) (Ioo 0 L) volume
    convert! (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : Hilbert L)) (Ioo 0 L) volume) using 1
    funext y
    simp [gammaIntegrand]
  add_mem' := by
    intro f g hf hg
    change IntegrableOn (gammaIntegrand L (f + g)) (Ioo 0 L) volume
    convert! hf.add hg using 1
    funext y
    exact gammaIntegrand_add L f g y
  smul_mem' := by
    intro a f hf
    change IntegrableOn (gammaIntegrand L (a • f)) (Ioo 0 L) volume
    have hh : IntegrableOn (fun y => a • gammaIntegrand L f y) (Ioo 0 L) volume :=
      (show Integrable (gammaIntegrand L f) (volume.restrict (Ioo 0 L)) from hf).smul a
    exact hh.congr (Eventually.of_forall fun y => (gammaIntegrand_smul L a f y).symm)

/-- The explicit renormalized current on its proved integrability domain. -/
def gammaCurrent (L : ℝ) : gammaCurrentDomain L →ₗ[ℂ] Hilbert L where
  toFun f := (gammaConstant L : ℂ) • (f : Hilbert L) +
    ∫ y in Ioo 0 L, gammaIntegrand L f y
  map_add' f g := by
    change (gammaConstant L : ℂ) • ((f : Hilbert L) + g) +
      ∫ y in Ioo 0 L, gammaIntegrand L ((f : Hilbert L) + g) y = _
    simp only [gammaIntegrand_add]
    rw [integral_add f.property g.property]
    module
  map_smul' a f := by
    change (gammaConstant L : ℂ) • (a • (f : Hilbert L)) +
      ∫ y in Ioo 0 L, gammaIntegrand L (a • (f : Hilbert L)) y = _
    simp only [gammaIntegrand_smul, integral_smul, RingHom.id_apply]
    module

theorem HasGenerator.norm_shift_sub_le {L : ℝ} {f g : Hilbert L}
    (hfg : HasGenerator L f g) {y : ℝ} (hy : 0 ≤ y) :
    ‖shift L y f - f‖ ≤ y * ‖g‖ := by
  rw [← hfg.orbit_integral hy]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := y) (C := ‖g‖)
    (fun t _ => norm_shift_apply_le L t g)
  simpa only [sub_zero, abs_of_nonneg hy, mul_comm] using hh

theorem continuousOn_gammaIntegrand (L : ℝ) (f : Hilbert L) :
    ContinuousOn (gammaIntegrand L f) (Ioo 0 L) := by
  have hq : ContinuousOn (fun y : ℝ => 1 - Real.exp (-2 * y)) (Ioo 0 L) := by fun_prop
  have hn : ∀ y ∈ Ioo 0 L, 1 - Real.exp (-2 * y) ≠ 0 :=
    fun y hy => (GammaCompletion.base_arg_pos hy.1).ne'
  have hw : ContinuousOn gammaWeight (Ioo 0 L) :=
    (show ContinuousOn (fun y : ℝ => Real.exp (-y / 2)) (Ioo 0 L) by fun_prop).div hq hn
  have hr : ContinuousOn gammaRemainder (Ioo 0 L) :=
    (show ContinuousOn (fun y : ℝ => Real.exp (-y / 2) - Real.exp (-2 * y)) (Ioo 0 L) by
      fun_prop).div hq hn
  exact (Complex.continuous_ofReal.comp_continuousOn hw).smul
    ((continuous_shift_apply L f).continuousOn.sub continuousOn_const) |>.add
      ((Complex.continuous_ofReal.comp_continuousOn hr).smul continuousOn_const)

theorem HasGenerator.mem_gammaCurrentDomain {L : ℝ} (hL : 0 < L)
    {f g : Hilbert L} (hfg : HasGenerator L f g) : f ∈ gammaCurrentDomain L := by
  have hc : 0 ≤ (2 * Real.exp (-2 * L))⁻¹ := by positivity
  apply (integrableOn_const (C := (2 * Real.exp (-2 * L))⁻¹ * ‖g‖ + ‖f‖)
    (s := Ioo 0 L) (hs := by simp [Real.volume_Ioo])).mono'
    ((continuousOn_gammaIntegrand L f).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have hw := gammaWeight_nonneg hy.1
  have hr := gammaRemainder_nonneg hy.1
  calc
    ‖gammaIntegrand L f y‖ ≤
      ‖(gammaWeight y : ℂ) • (shift L y f - f)‖ + ‖(gammaRemainder y : ℂ) • f‖ := norm_add_le _ _
    _ = gammaWeight y * ‖shift L y f - f‖ + gammaRemainder y * ‖f‖ := by
      rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg hr]
    _ ≤ gammaWeight y * (y * ‖g‖) + 1 * ‖f‖ := by
      gcongr
      · exact hfg.norm_shift_sub_le hy.1.le
      · exact gammaRemainder_le_one hy.1
    _ ≤ (2 * Real.exp (-2 * L))⁻¹ * ‖g‖ + ‖f‖ := by
      rw [← mul_assoc, one_mul]
      gcongr
      exact gammaWeight_mul_le hL hy

theorem generatorDomain_le_gammaCurrentDomain {L : ℝ} (hL : 0 < L) :
    generatorDomain L ≤ gammaCurrentDomain L := by
  intro f hf
  obtain ⟨g, hg⟩ := (mem_generatorDomain_iff L hL.le f).mp hf
  exact hg.mem_gammaCurrentDomain hL

/-- Endpoint-truncated current, before evaluating its scalar subtraction. -/
def gammaTruncated (L δ : ℝ) (f : Hilbert L) : Hilbert L :=
  (gammaConstant L : ℂ) • f + ∫ y in δ..L, gammaIntegrand L f y

theorem gammaTruncated_zero {L : ℝ} (hL : 0 ≤ L) (f : gammaCurrentDomain L) :
    gammaTruncated L 0 f = gammaCurrent L f := by
  change (gammaConstant L : ℂ) • (f : Hilbert L) +
    (∫ y in 0..L, gammaIntegrand L f y) = _
  rw [intervalIntegral.integral_of_le hL, integral_Ioc_eq_integral_Ioo]
  rfl

/-- Truncation converges in the Hilbert norm on the declared current domain. -/
theorem gammaTruncated_tendsto {L : ℝ} (hL : 0 < L) (f : gammaCurrentDomain L) :
    Tendsto (fun δ => gammaTruncated L δ f) (𝓝[Icc 0 L] 0) (𝓝 (gammaCurrent L f)) := by
  have hf : IntegrableOn (gammaIntegrand L f) (uIcc 0 L) volume := by
    rw [uIcc_of_le hL.le]
    exact f.property.congr_set_ae Ioo_ae_eq_Icc.symm
  have hc := intervalIntegral.continuousOn_primitive_interval_left hf
  rw [uIcc_of_le hL.le] at hc
  have hh := ((continuousWithinAt_const (b := (gammaConstant L : ℂ) • (f : Hilbert L))).add
    (hc 0 ⟨le_rfl, hL.le⟩)).tendsto
  change Tendsto (fun δ => gammaTruncated L δ f) (𝓝[Icc 0 L] 0)
    (𝓝 (gammaTruncated L 0 f)) at hh
  rwa [gammaTruncated_zero hL.le f] at hh

/-- The integrand is the original renormalized difference, with no separated
singular integral hidden in its definition. -/
theorem gammaIntegrand_eq (L y : ℝ) (f : Hilbert L) :
    gammaIntegrand L f y = ((1 - Real.exp (-2 * y) : ℝ) : ℂ)⁻¹ •
      ((Real.exp (-y / 2) : ℂ) • shift L y f - (Real.exp (-2 * y) : ℂ) • f) := by
  dsimp [gammaIntegrand, gammaWeight, gammaRemainder]
  generalize Real.exp (-y / 2) = a
  generalize Real.exp (-2 * y) = b
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  module

end Riemann.Analysis.FiniteWindow
