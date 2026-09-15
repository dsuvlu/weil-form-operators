import Riemann.Basic.FiniteOperatorParameter
import Riemann.Analysis.FiniteWindow.DirectedGenerator
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # The independently normalized polar factor

All resolvents are the actual finite-window Volterra operators. Inverses of
I+dR_b are constructed from R_(b+d), for every complex b,d. No half-plane
restriction or bounded inverse of the completed Gamma factor is introduced.
-/

noncomputable section
open MeasureTheory
namespace Riemann.Analysis.FiniteWindow

local instance (L : ℝ) : ContinuousSMul ℝ (Hilbert L →L[ℂ] Hilbert L) :=
  IsScalarTower.continuousSMul ℂ

def resolventFactor (L : ℝ) (b d : ℂ) : Hilbert L →L[ℂ] Hilbert L :=
  1 + d • volterra L b

theorem resolventFactor_inverse (L : ℝ) (hL : 0 ≤ L) (b d : ℂ) :
    resolventFactor L b d * resolventFactor L (b + d) (-d) = 1 := by
  have hh := volterra_resolvent_identity L hL b (b + d)
  have hd : volterra L b - volterra L (b + d) =
      d • (volterra L b).comp (volterra L (b + d)) := by
    simpa only [add_sub_cancel_left] using hh
  apply ContinuousLinearMap.ext
  intro u
  have he := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T u) hd
  change volterra L b u - volterra L (b + d) u =
    d • volterra L b (volterra L (b + d) u) at he
  change resolventFactor L b d (resolventFactor L (b + d) (-d) u) = u
  simp only [resolventFactor, add_apply, one_apply_eq_self,
    smul_apply, map_add, map_smul]
  calc
    _ = u + d • (volterra L b u - volterra L (b + d) u -
      d • volterra L b (volterra L (b + d) u)) := by module
    _ = u := by rw [he, sub_self, smul_zero, add_zero]

theorem resolventFactor_inverse_left (L : ℝ) (hL : 0 ≤ L) (b d : ℂ) :
    resolventFactor L (b + d) (-d) * resolventFactor L b d = 1 := by
  simpa only [add_neg_cancel_right, neg_neg] using resolventFactor_inverse L hL (b + d) (-d)

/-- The finite-window polar polynomial, normalized at s₀=5/2. -/
def polarOperator (L σ : ℝ) : Hilbert L →L[ℂ] Hilbert L :=
  resolventFactor L (5 / 2) ((σ : ℂ) - 5 / 2) *
    resolventFactor L (3 / 2) ((σ : ℂ) - 5 / 2)

/-- Explicit bounded inverse of the polar factor. -/
def polarInverse (L σ : ℝ) : Hilbert L →L[ℂ] Hilbert L :=
  resolventFactor L ((3 / 2) + ((σ : ℂ) - 5 / 2)) (-((σ : ℂ) - 5 / 2)) *
    resolventFactor L ((5 / 2) + ((σ : ℂ) - 5 / 2)) (-((σ : ℂ) - 5 / 2))

theorem polarOperator_mul_inverse (L : ℝ) (hL : 0 ≤ L) (σ : ℝ) :
    polarOperator L σ * polarInverse L σ = 1 := by
  dsimp [polarOperator, polarInverse]
  rw [mul_assoc, ← mul_assoc (resolventFactor L (3 / 2) _),
    resolventFactor_inverse L hL, one_mul, resolventFactor_inverse L hL]

theorem polarInverse_mul (L : ℝ) (hL : 0 ≤ L) (σ : ℝ) :
    polarInverse L σ * polarOperator L σ = 1 := by
  dsimp [polarOperator, polarInverse]
  rw [mul_assoc, ← mul_assoc (resolventFactor L (5 / 2 + _) _),
    resolventFactor_inverse_left L hL, one_mul, resolventFactor_inverse_left L hL]

def polarDerivative (L σ : ℝ) : Hilbert L →L[ℂ] Hilbert L :=
  volterra L (5 / 2) * resolventFactor L (3 / 2) ((σ : ℂ) - 5 / 2) +
    resolventFactor L (5 / 2) ((σ : ℂ) - 5 / 2) * volterra L (3 / 2)

theorem hasDerivAt_polarOperator (L σ : ℝ) :
    HasDerivAt (polarOperator L) (polarDerivative L σ) σ := by
  exact Riemann.Basic.hasDerivAt_operator_mul
    (Riemann.Basic.hasDerivAt_operator_affine (volterra L (5 / 2)) (5 / 2) σ)
    (Riemann.Basic.hasDerivAt_operator_affine (volterra L (3 / 2)) (5 / 2) σ)

/-- Multiplication by a relative factor moves the resolvent parameter. -/
theorem resolventFactor_mul_resolvent (L : ℝ) (hL : 0 ≤ L) (b d : ℂ) :
    resolventFactor L b d * volterra L (b + d) = volterra L b := by
  have hh := volterra_resolvent_identity L hL b (b + d)
  have hd : volterra L b - volterra L (b + d) =
      d • (volterra L b).comp (volterra L (b + d)) := by
    simpa only [add_sub_cancel_left] using hh
  apply ContinuousLinearMap.ext
  intro u
  have he := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T u) hd
  change volterra L b u - volterra L (b + d) u =
    d • volterra L b (volterra L (b + d) u) at he
  change volterra L (b + d) u + d • volterra L b (volterra L (b + d) u) = _
  rw [← he]
  abel

theorem resolventFactor_commute_resolvent (L : ℝ) (hL : 0 ≤ L) (b d c : ℂ) :
    resolventFactor L b d * volterra L c = volterra L c * resolventFactor L b d := by
  apply ContinuousLinearMap.ext
  intro u
  have hh := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T u) (volterra_commute L hL b c)
  change volterra L b (volterra L c u) = volterra L c (volterra L b u) at hh
  change volterra L c u + d • volterra L b (volterra L c u) =
    volterra L c (u + d • volterra L b u)
  rw [map_add, map_smul, hh]

/-- The derivative has the factored form that identifies the polar current. -/
theorem polarDerivative_eq (L : ℝ) (hL : 0 ≤ L) (σ : ℝ) :
    polarDerivative L σ = polarOperator L σ *
      (volterra L (σ : ℂ) + volterra L ((σ : ℂ) - 1)) := by
  let d : ℂ := (σ : ℂ) - 5 / 2
  have h0 : 5 / 2 + d = (σ : ℂ) := by dsimp [d]; ring
  have h1 : 3 / 2 + d = (σ : ℂ) - 1 := by dsimp [d]; ring
  have hr0 := resolventFactor_mul_resolvent L hL (5 / 2) d
  have hr1 := resolventFactor_mul_resolvent L hL (3 / 2) d
  rw [h0] at hr0
  rw [h1] at hr1
  change volterra L (5 / 2) * resolventFactor L (3 / 2) d +
    resolventFactor L (5 / 2) d * volterra L (3 / 2) =
    (resolventFactor L (5 / 2) d * resolventFactor L (3 / 2) d) * _
  rw [mul_add, mul_assoc, resolventFactor_commute_resolvent L hL (3 / 2) d (σ : ℂ),
    ← mul_assoc, hr0, mul_assoc, hr1]

theorem polar_negative_logarithmic_derivative (L : ℝ) (hL : 0 ≤ L) (σ : ℝ) :
    -(polarInverse L σ * polarDerivative L σ) =
      -(volterra L (σ : ℂ)) - volterra L ((σ : ℂ) - 1) := by
  rw [polarDerivative_eq L hL, ← mul_assoc, polarInverse_mul L hL, one_mul, neg_add_rev]
  abel

/-- Each classical polar channel occurs exactly once at the critical parameter. -/
theorem polar_current_half (L : ℝ) (hL : 0 ≤ L) :
    -(polarInverse L (1 / 2) * polarDerivative L (1 / 2)) =
      -(volterra L (1 / 2)) - volterra L (-(1 / 2)) := by
  have hh := polar_negative_logarithmic_derivative L hL (1 / 2)
  norm_num at hh ⊢
  exact hh

end Riemann.Analysis.FiniteWindow
