import Riemann.Analysis.FiniteWindow.CompletedCurrent
import Riemann.Analysis.FiniteWindow.GammaCurrentIdentity

/-! # Differentiating the completed frame on its explicit current domain

The three factors are differentiated in their original order. Every singular
current commutation uses the proved preservation of its integrability domain.
-/
noncomputable section
namespace Riemann.Analysis.FiniteWindow

theorem completed_polar_derivative {L : ℝ} (hL : 0 < L) :
    polarDerivative L (1/2) * gammaOperator L (1/2) * primeOperator L (1/2) =
      completedFrame L (1/2) * (volterra L (1/2) + volterra L (-(1/2))) := by
  have hp := polarDerivative_eq L hL.le (1/2)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hp
  have he : Commute (gammaOperator L (1/2)) (volterra L (1/2) + volterra L (-(1/2))) :=
    (gammaOperator_commute_volterra L hL.le (1/2) (1/2)).add_right
      (gammaOperator_commute_volterra L hL.le (1/2) (-(1/2)))
  have hz : Commute (primeOperator L (1/2)) (volterra L (1/2) + volterra L (-(1/2))) :=
    (primeOperator_commute_volterra L hL.le (1/2) (1/2)).add_right
      (primeOperator_commute_volterra L hL.le (1/2) (-(1/2)))
  rw [hp, mul_assoc, mul_assoc, (he.mul_left hz).symm.eq]
  simp only [completedFrame, mul_assoc]

/-- The differentiated frame equals minus the frame applied to the literal
completed current on its declared integrability domain. -/
theorem completedDerivative_eq_neg_frame_current {L : ℝ} (hL : 0 < L)
    (f : gammaCurrentDomain L) :
    completedDerivative L f = -completedFrame L (1/2) (completedCurrent L f) := by
  let zf : gammaCurrentDomain L :=
    ⟨primeOperator L (1/2) f,
      map_mem_gammaCurrentDomain (primeOperator L (1/2)) (primeOperator_commute_shift L (1/2)) f⟩
  have hg := gammaOperator_half_gammaCurrent hL zf
  have hc := gammaCurrent_commute (primeOperator L (1/2)) (primeOperator_commute_shift L (1/2)) f
  change gammaCurrent L zf = primeOperator L (1/2) (gammaCurrent L f) at hc
  rw [hc] at hg
  have hgg : gammaDerivative L (primeOperator L (1/2) f) =
      -gammaOperator L (1/2) (primeOperator L (1/2) (gammaCurrent L f)) := by
    simpa only [neg_neg] using (congrArg Neg.neg hg).symm
  have hgp := congrArg (polarOperator L (1/2)) hgg
  rw [map_neg] at hgp
  have hzp := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L =>
    polarOperator L (1/2) (gammaOperator L (1/2) (T f))) (primeDerivative_eq L (1/2))
  simp only [neg_apply, mul_apply_eq_comp, map_neg] at hzp
  have hpp := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T (f : Hilbert L))
    (completed_polar_derivative hL)
  simp only [mul_apply_eq_comp, add_apply, map_add] at hpp
  change polarDerivative L (1/2) (gammaOperator L (1/2) (primeOperator L (1/2) f)) +
      polarOperator L (1/2) (gammaDerivative L (primeOperator L (1/2) f)) +
      polarOperator L (1/2) (gammaOperator L (1/2) (primeDerivative L (1/2) f)) = _
  rw [hpp, hgp, hzp, completedCurrent_apply]
  change completedFrame L (1/2) (volterra L (1/2) f) +
      completedFrame L (1/2) (volterra L (-(1/2)) f) +
      -(completedFrame L (1/2) (gammaCurrent L f)) +
      -(completedFrame L (1/2) (primeCurrent L (1/2) f)) = _
  rw [map_sub, map_sub, map_add]
  module


theorem completedFrame_commute_volterra {L : ℝ} (hL : 0 < L) (b : ℂ) :
    Commute (completedFrame L (1/2)) (volterra L b) := by
  have hp : Commute (polarOperator L (1/2)) (volterra L b) :=
    polarOperator_commute_volterra L hL.le (1/2) b
  exact (hp.mul_left (gammaOperator_commute_volterra L hL.le (1/2) b)).mul_left
    (primeOperator_commute_volterra L hL.le (1/2) b)

theorem completedFrame_commute_primeCurrent {L : ℝ} (hL : 0 < L) :
    Commute (completedFrame L (1/2)) (primeCurrent L (1/2)) := by
  have hp := primeAlgebra_commute (polarOperator L (1/2))
    (polarOperator_commute_shift L hL.le (1/2))
    (Arithmetic.synthesis (primeCutoff L) (primeWeight L (1/2)) ArithmeticFunction.vonMangoldt)
  have he := primeAlgebra_commute (gammaOperator L (1/2))
    (gammaOperator_commute_shift L (1/2))
    (Arithmetic.synthesis (primeCutoff L) (primeWeight L (1/2)) ArithmeticFunction.vonMangoldt)
  exact (hp.mul_left he).mul_left (primeOperator_commute_current L (1/2))

/-- Left current transport holds for every fixed Hilbert source. The input
source is not required to belong to the current domain. -/
theorem completedCurrent_frame_eq_neg_derivative {L : ℝ} (hL : 0 < L) (u : Hilbert L) :
    completedCurrent L ⟨completedFrame L (1/2) u, completedFrame_mem_currentDomain hL u⟩ =
      -completedDerivative L u := by
  let ef : gammaCurrentDomain L :=
    ⟨gammaOperator L (1/2) (primeOperator L (1/2) u),
      gammaOperator_half_mem_gammaCurrentDomain hL (primeOperator L (1/2) u)⟩
  have hg := gammaCurrent_commute (polarOperator L (1/2))
    (polarOperator_commute_shift L hL.le (1/2)) ef
  rw [show gammaCurrent L ef = -gammaDerivative L (primeOperator L (1/2) u) from
    gammaCurrent_gammaOperator_half hL (primeOperator L (1/2) u), map_neg] at hg
  have hj := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T u)
    (completedFrame_commute_primeCurrent hL).symm.eq
  simp only [mul_apply_eq_comp] at hj
  have hzp := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L =>
    polarOperator L (1/2) (gammaOperator L (1/2) (T u))) (primeDerivative_eq L (1/2))
  simp only [neg_apply, mul_apply_eq_comp, map_neg] at hzp
  have hpp := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T u)
    (completed_polar_derivative hL)
  simp only [mul_apply_eq_comp, add_apply, map_add] at hpp
  have hr (b : ℂ) := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T u)
    (completedFrame_commute_volterra hL b).symm.eq
  simp only [mul_apply_eq_comp] at hr
  rw [completedCurrent_apply, hj, hr, hr]
  change completedFrame L (1/2) (primeCurrent L (1/2) u) +
      gammaCurrent L ⟨polarOperator L (1/2) (ef : Hilbert L), _⟩ -
      completedFrame L (1/2) (volterra L (1/2) u) -
      completedFrame L (1/2) (volterra L (-(1/2)) u) = _
  rw [hg]
  change completedFrame L (1/2) (primeCurrent L (1/2) u) +
      -(polarOperator L (1/2) (gammaDerivative L (primeOperator L (1/2) u))) -
      completedFrame L (1/2) (volterra L (1/2) u) -
      completedFrame L (1/2) (volterra L (-(1/2)) u) =
    -(polarDerivative L (1/2) (gammaOperator L (1/2) (primeOperator L (1/2) u)) +
      polarOperator L (1/2) (gammaDerivative L (primeOperator L (1/2) u)) +
      polarOperator L (1/2) (gammaOperator L (1/2) (primeDerivative L (1/2) u)))
  rw [hpp, hzp]
  change _ = -(completedFrame L (1/2) (volterra L (1/2) u) +
    completedFrame L (1/2) (volterra L (-(1/2)) u) +
    polarOperator L (1/2) (gammaDerivative L (primeOperator L (1/2) u)) +
    -(completedFrame L (1/2) (primeCurrent L (1/2) u)))
  module

end Riemann.Analysis.FiniteWindow
