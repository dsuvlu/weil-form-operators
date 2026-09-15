import Riemann.Analysis.HalfLine.RawEuler
import Riemann.Analysis.HalfLine.KernelTranslation
import Riemann.Analysis.FiniteWindow.CompletedFrame

/-! # Critical completion on the raw dense domain

The two positive resolvent factors are retained before their algebraic
cancellation. This is a fixed critical construction, not a parameter family.
-/
noncomputable section
namespace Riemann.Analysis.HalfLine

/-- The two critical polar factors in their original order. -/
def criticalPolar : Hilbert →L[ℂ] Hilbert :=
  (1 - (2 : ℂ) • volterra (5/2)) * (1 - (2 : ℂ) • volterra (3/2))

/-- Completion is first defined only on the raw compact-support domain. -/
def completedCore : compactSupport →ₗ[ℂ] Hilbert :=
  criticalPolar.toLinearMap.comp
    (((2*Real.pi : ℂ) • volterra (1/2)).toLinearMap.comp rawEuler)

theorem critical_first_cancellation :
    (1 - (2 : ℂ) • volterra (5/2)) * volterra (1/2) = volterra (5/2) := by
  apply ContinuousLinearMap.ext
  intro f
  have he := congrArg (fun T : Hilbert →L[ℂ] Hilbert => T f)
    (volterra_resolvent_identity (by norm_num : (0:ℝ)<5/2) (by norm_num : (0:ℝ)<1/2))
  norm_num only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    show (((1/2-5/2 : ℝ) : ℂ)) = -2 by norm_num] at he
  change volterra (1/2) f - (2:ℂ) • volterra (5/2) (volterra (1/2) f) = _
  calc
    _ = volterra (1/2) f + (volterra (5/2) f - volterra (1/2) f) := by rw [he]; module
    _ = _ := by module

theorem critical_second_cancellation :
    volterra (5/2) * (1 - (2 : ℂ) • volterra (3/2)) =
      (3 : ℂ) • volterra (5/2) - (2 : ℂ) • volterra (3/2) := by
  apply ContinuousLinearMap.ext
  intro f
  have he := congrArg (fun T : Hilbert →L[ℂ] Hilbert => T f)
    (volterra_resolvent_identity (by norm_num : (0:ℝ)<5/2) (by norm_num : (0:ℝ)<3/2))
  norm_num only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    show (((3/2-5/2 : ℝ) : ℂ)) = -1 by norm_num, neg_smul, one_smul] at he
  change volterra (5/2) (f - (2:ℂ) • volterra (3/2) f) = _
  rw [map_sub, map_smul]
  change _ = (3:ℂ) • volterra (5/2) f - (2:ℂ) • volterra (3/2) f
  calc
    _ = volterra (5/2) f + (2:ℂ) • (volterra (5/2) f - volterra (3/2) f) := by
      rw [he]; module
    _ = _ := by module

theorem critical_factor_reduction :
    criticalPolar * volterra (1/2) =
      (3 : ℂ) • volterra (5/2) - (2 : ℂ) • volterra (3/2) := by
  have hc : (1 - (2 : ℂ) • volterra (3/2)) * volterra (1/2) =
      volterra (1/2) * (1 - (2 : ℂ) • volterra (3/2)) := by
    have hh := volterra_commute (by norm_num : (0:ℝ)<3/2) (by norm_num : (0:ℝ)<1/2)
    change volterra (3/2) * volterra (1/2) = volterra (1/2) * volterra (3/2) at hh
    apply ContinuousLinearMap.ext
    intro f
    change volterra (1/2) f - (2:ℂ) • volterra (3/2) (volterra (1/2) f) =
      volterra (1/2) (f - (2:ℂ) • volterra (3/2) f)
    rw [map_sub, map_smul]
    exact congrArg (fun x : Hilbert => volterra (1/2) f - (2:ℂ) • x)
      (congrArg (fun T : Hilbert →L[ℂ] Hilbert => T f) hh)
  rw [criticalPolar, mul_assoc, hc, ← mul_assoc, critical_first_cancellation,
    critical_second_cancellation]

/-- The original ordered completion equals the bounded smoothing of raw synthesis. -/
theorem completedCore_eq_smoothing (f : compactSupport) :
    completedCore f = smoothingOperator (rawEuler f) := by
  change criticalPolar ((2*Real.pi : ℂ) • volterra (1/2) (rawEuler f)) = _
  rw [map_smul]
  have he := congrArg (fun T : Hilbert →L[ℂ] Hilbert =>
    (2*Real.pi : ℂ) • T (rawEuler f)) critical_factor_reduction
  exact he

/-- Literal restriction to the previously formalized finite critical frame. -/
theorem completedCore_finiteInclusion (L : ℝ) (hL : 0 < L) (f : FiniteWindow.Hilbert L) :
    completedCore (finiteCoreInclusion L hL f) =
      finiteInclusion L (FiniteWindow.completedFrame L (1/2) f) := by
  change criticalPolar ((2*Real.pi : ℂ) • volterra (1/2)
    (rawEuler (finiteCoreInclusion L hL f))) = _
  rw [rawEuler_finiteInclusion, volterra_finiteInclusion L hL.le (by norm_num)]
  simp only [criticalPolar, mul_apply_eq_comp, sub_apply, smul_apply,
    one_apply_eq_self, map_sub, map_smul]
  simp only [volterra_finiteInclusion L hL.le (by norm_num : (0:ℝ)<3/2),
    volterra_finiteInclusion L hL.le (by norm_num : (0:ℝ)<5/2)]
  rw [FiniteWindow.completedFrame, FiniteWindow.gammaOperator_half hL]
  simp only [FiniteWindow.polarOperator, FiniteWindow.resolventFactor,
    mul_apply_eq_comp, add_apply, smul_apply, one_apply_eq_self,
    map_add, map_smul]
  norm_num
  module

end Riemann.Analysis.HalfLine
