import Riemann.Analysis.FiniteWindow.GammaOperator
import Riemann.Analysis.FiniteWindow.PrimeHilbert
import Riemann.Analysis.FiniteWindow.PolarOperator
import Riemann.Analysis.FiniteWindow.NativeFourierHilbert

/-! # The completed finite-window frame and its exact range

The bounded frame is the ordered product of the normalized polar, Gamma and
prime factors. At the critical parameter its only smoothing factor is the
Volterra resolvent. Its inverse is constructed only on the generator domain;
no bounded inverse on the ambient Hilbert space is asserted.
-/

noncomputable section
namespace Riemann.Analysis.FiniteWindow

local instance (L : ℝ) : ContinuousSMul ℝ (Hilbert L →L[ℂ] Hilbert L) :=
  IsScalarTower.continuousSMul ℂ

def completedFrame (L σ : ℝ) : Hilbert L →L[ℂ] Hilbert L :=
  polarOperator L σ * gammaOperator L σ * primeOperator L σ

def completedDerivative (L : ℝ) : Hilbert L →L[ℂ] Hilbert L :=
  (polarDerivative L (1 / 2) * gammaOperator L (1 / 2) +
    polarOperator L (1 / 2) * gammaDerivative L) * primeOperator L (1 / 2) +
    (polarOperator L (1 / 2) * gammaOperator L (1 / 2)) * primeDerivative L (1 / 2)

theorem hasDerivAt_completedFrame_half {L : ℝ} (hL : 0 < L) :
    HasDerivAt (completedFrame L) (completedDerivative L) (1 / 2) := by
  exact Riemann.Basic.hasDerivAt_operator_mul
    (Riemann.Basic.hasDerivAt_operator_mul (hasDerivAt_polarOperator L (1 / 2))
      (hasDerivAt_gammaOperator_half hL)) (hasDerivAt_primeOperator L (1 / 2))

theorem completedFrame_hasDerivAt {L σ : ℝ} (hL : 0 < L) (hσ : σ ∈ Set.Ioo 0 1) :
    ∃ T : Hilbert L →L[ℂ] Hilbert L, HasDerivAt (completedFrame L) T σ := by
  obtain ⟨T, hT⟩ := gammaOperator_hasDerivAt hL hσ
  exact ⟨_, Riemann.Basic.hasDerivAt_operator_mul
    (Riemann.Basic.hasDerivAt_operator_mul (hasDerivAt_polarOperator L σ) hT)
    (hasDerivAt_primeOperator L σ)⟩

theorem polarOperator_commute_volterra (L : ℝ) (hL : 0 ≤ L) (σ : ℝ) (b : ℂ) :
    polarOperator L σ * volterra L b = volterra L b * polarOperator L σ := by
  dsimp [polarOperator]
  rw [mul_assoc, resolventFactor_commute_resolvent L hL, ← mul_assoc,
    resolventFactor_commute_resolvent L hL, mul_assoc]

/-- At the critical parameter the bounded factors follow the single Volterra
resolvent. This factorization is the range argument. -/
theorem completedFrame_half {L : ℝ} (hL : 0 < L) :
    completedFrame L (1 / 2) = (2 * Real.pi : ℂ) •
      (volterra L (1 / 2) * (polarOperator L (1 / 2) * primeOperator L (1 / 2))) := by
  have hc := polarOperator_commute_volterra L hL.le (1 / 2) (1 / 2)
  rw [completedFrame, gammaOperator_half hL]
  apply ContinuousLinearMap.ext
  intro u
  change polarOperator L (1 / 2) ((2 * Real.pi : ℂ) •
    volterra L (1 / 2) (primeOperator L (1 / 2) u)) = _
  rw [map_smul]
  exact congrArg (fun T : Hilbert L →L[ℂ] Hilbert L =>
    (2 * Real.pi : ℂ) • T (primeOperator L (1 / 2) u)) hc

private theorem criticalScalar_ne_zero : (2 * Real.pi : ℂ) ≠ 0 := by
  exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

theorem completedFrame_injective {L : ℝ} (hL : 0 < L) :
    Function.Injective (completedFrame L (1 / 2)) := by
  intro u v huv
  rw [completedFrame_half hL] at huv
  change (2 * Real.pi : ℂ) • volterra L (1 / 2) (polarOperator L (1 / 2)
    (primeOperator L (1 / 2) u)) = (2 * Real.pi : ℂ) • volterra L (1 / 2)
      (polarOperator L (1 / 2) (primeOperator L (1 / 2) v)) at huv
  have h := (volterra_injective L hL.le (1 / 2))
    ((smul_right_injective _ criticalScalar_ne_zero) huv)
  have hp := congrArg (polarInverse L (1 / 2)) h
  have hpi (w : Hilbert L) : polarInverse L (1 / 2) (polarOperator L (1 / 2) w) = w :=
    by
      have hh := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T w) (polarInverse_mul L hL.le (1 / 2))
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using hh
  rw [hpi, hpi] at hp
  have hi := congrArg (primeInverse L (1 / 2)) hp
  have hzi (w : Hilbert L) : primeInverse L (1 / 2) (primeOperator L (1 / 2) w) = w :=
    by
      have hh := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T w) (primeInverse_mul L (1 / 2))
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using hh
  simpa only [hzi] using hi

/-- The completed range equals the maximal terminal generator domain. -/
theorem range_completedFrame {L : ℝ} (hL : 0 < L) :
    (completedFrame L (1 / 2)).range = generatorDomain L := by
  rw [← range_volterra_eq_generatorDomain L hL.le (1 / 2)]
  ext f
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨(2 * Real.pi : ℂ) • (polarOperator L (1 / 2)
      (primeOperator L (1 / 2) u)), ?_⟩
    rw [completedFrame_half hL]
    change volterra L (1 / 2) ((2 * Real.pi : ℂ) • _) =
      (2 * Real.pi : ℂ) • volterra L (1 / 2) _
    exact map_smul _ _ _
  · rintro ⟨u, rfl⟩
    refine ⟨primeInverse L (1 / 2) (polarInverse L (1 / 2)
      ((2 * Real.pi : ℂ)⁻¹ • u)), ?_⟩
    rw [completedFrame_half hL]
    change (2 * Real.pi : ℂ) • volterra L (1 / 2)
      (polarOperator L (1 / 2) (primeOperator L (1 / 2)
        (primeInverse L (1 / 2) (polarInverse L (1 / 2)
          ((2 * Real.pi : ℂ)⁻¹ • u))))) = _
    have hzi (w : Hilbert L) : primeOperator L (1 / 2) (primeInverse L (1 / 2) w) = w :=
      by
      have hh := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T w) (primeOperator_mul_inverse L (1 / 2))
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using hh
    have hpi (w : Hilbert L) : polarOperator L (1 / 2) (polarInverse L (1 / 2) w) = w :=
      by
      have hh := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T w) (polarOperator_mul_inverse L hL.le (1 / 2))
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using hh
    rw [hzi, hpi, map_smul, smul_smul, mul_inv_cancel₀ criticalScalar_ne_zero, one_smul]
    rfl

/-- The range equivalence is linear. It is deliberately not an ambient bounded
inverse: its codomain is the actual generator domain. -/
def completedRangeEquiv (L : ℝ) (hL : 0 < L) : Hilbert L ≃ₗ[ℂ] generatorDomain L :=
  (LinearEquiv.ofInjective (completedFrame L (1 / 2)).toLinearMap
    (completedFrame_injective hL)).trans (LinearEquiv.ofEq _ _ (range_completedFrame hL))

@[simp] theorem completedRangeEquiv_coe (L : ℝ) (hL : 0 < L) (u : Hilbert L) :
    (completedRangeEquiv L hL u : Hilbert L) = completedFrame L (1 / 2) u := rfl

/-- The unique literal source of an eligible terminal-zero vector. -/
def completedSource (L : ℝ) (hL : 0 < L) : generatorDomain L →ₗ[ℂ] Hilbert L :=
  (completedRangeEquiv L hL).symm.toLinearMap

@[simp] theorem completedFrame_completedSource (L : ℝ) (hL : 0 < L)
    (w : generatorDomain L) : completedFrame L (1 / 2) (completedSource L hL w) = w :=
  congrArg Subtype.val ((completedRangeEquiv L hL).apply_symm_apply w)

theorem completedSource_unique (L : ℝ) (hL : 0 < L) (w : generatorDomain L)
    {u : Hilbert L} (hu : completedFrame L (1 / 2) u = w) :
    u = completedSource L hL w :=
  completedFrame_injective hL (hu.trans (completedFrame_completedSource L hL w).symm)

/-- The range statement with the representative and boundary trace explicit. -/
theorem mem_completedFrame_range_iff_ac {L : ℝ} (hL : 0 < L) (f : Hilbert L) :
    f ∈ (completedFrame L (1 / 2)).range ↔ ∃ g, HasACDerivative L f g := by
  rw [range_completedFrame hL]
  exact mem_generatorDomain_iff_ac hL.le f

/-- Every endpoint-zero native Fourier polynomial has its unique literal source. -/
def nativeCompletedSource {N : ℕ} {L : ℝ} (hL : 0 < L)
    (x : Riemann.CCM.Native.Section N) (hx : Riemann.CCM.Native.endpoint N L x = 0) :
    Hilbert L :=
  completedSource L hL ⟨fourierHilbert L x, (mem_generatorDomain_iff L hL.le _).2
    ⟨_, nativeFourier_hasGenerator hL x hx⟩⟩

@[simp] theorem completedFrame_nativeCompletedSource {N : ℕ} {L : ℝ} (hL : 0 < L)
    (x : Riemann.CCM.Native.Section N) (hx : Riemann.CCM.Native.endpoint N L x = 0) :
    completedFrame L (1 / 2) (nativeCompletedSource hL x hx) = fourierHilbert L x :=
  completedFrame_completedSource L hL _

end Riemann.Analysis.FiniteWindow
