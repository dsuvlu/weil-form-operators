import Riemann.Analysis.FiniteWindow.GammaCurrent
import Riemann.Analysis.FiniteWindow.NativeFourierShiftBound

/-! The native Fourier test space belongs to the current domain, including
nonzero endpoint vectors. The proof uses its actual square-root shift modulus. -/
noncomputable section
open MeasureTheory Set
namespace Riemann.Analysis.FiniteWindow

theorem gammaWeight_sqrt_le {L y : ℝ} (hL : 0 < L) (hy : y ∈ Ioo 0 L) :
    gammaWeight y * Real.sqrt y ≤
      (2 * Real.exp (-2 * L))⁻¹ * y ^ (-(1 / 2 : ℝ)) := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy.1
  rw [Real.rpow_neg hy.1.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  apply (le_div_iff₀ hs).mpr
  rw [mul_assoc, Real.mul_self_sqrt hy.1.le]
  exact gammaWeight_mul_le hL hy

/-- Every vector with a square-root shift modulus lies in the literal current domain. -/
theorem mem_gammaCurrentDomain_of_sqrt_modulus {L : ℝ} (hL : 0 < L)
    (f : Hilbert L) (C : ℝ) (hC : 0 ≤ C)
    (hmod : ∀ y ∈ Ioo 0 L, ‖shift L y f - f‖ ≤ C * Real.sqrt y) :
    f ∈ gammaCurrentDomain L := by
  have hp : IntegrableOn (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) (Ioo 0 L) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hL).mpr (by norm_num)
  have hb := (hp.const_mul ((2 * Real.exp (-2 * L))⁻¹ * C)).add
    (integrableOn_const (C := ‖f‖) (s := Ioo 0 L) (hs := by simp [Real.volume_Ioo]))
  apply hb.mono' ((continuousOn_gammaIntegrand L f).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have hw := gammaWeight_nonneg hy.1
  have hr := gammaRemainder_nonneg hy.1
  calc
    ‖gammaIntegrand L f y‖ ≤
        ‖(gammaWeight y : ℂ) • (shift L y f - f)‖ +
          ‖(gammaRemainder y : ℂ) • f‖ := norm_add_le _ _
    _ = gammaWeight y * ‖shift L y f - f‖ + gammaRemainder y * ‖f‖ := by
      rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg hr]
    _ ≤ gammaWeight y * (C * Real.sqrt y) + ‖f‖ := by
      nlinarith [mul_le_mul_of_nonneg_left (hmod y hy) hw,
        mul_le_mul_of_nonneg_right (gammaRemainder_le_one hy.1) (norm_nonneg f)]
    _ ≤ ((2 * Real.exp (-2 * L))⁻¹ * C) * y ^ (-(1 / 2 : ℝ)) + ‖f‖ := by
      nlinarith [mul_le_mul_of_nonneg_right (gammaWeight_sqrt_le hL hy) hC]

/-- The original full Fourier section is admitted without imposing its endpoint to vanish. -/
theorem fourierHilbert_mem_gammaCurrentDomain {N : ℕ} {L : ℝ} (hL : 0 < L)
    (x : Riemann.CCM.Native.Section N) :
    fourierHilbert L x ∈ gammaCurrentDomain L := by
  apply mem_gammaCurrentDomain_of_sqrt_modulus hL _ (fourierShiftConstant L x)
    (fourierShiftConstant_nonneg L x)
  intro y hy
  exact norm_shift_fourier_sub_le_sqrt hL hy.1.le hy.2.le x

end Riemann.Analysis.FiniteWindow
