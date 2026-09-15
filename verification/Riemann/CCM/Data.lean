import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Full simple-even finite CCM data

Fresh formalization from CCM, *Zeta Spectral Triples*, arXiv:2511.22755v1,
§5.2, and manuscript v0.1.0-draft.4 §4. No prior project Lean source was read.

The carrier is the full finite complex Hilbert space. The lower-bound hypothesis
states variational leastness on **every** vector of that carrier. Together with
the exhibited eigenvector it identifies the actual least eigenvalue; it is not a
minimum taken in an even subspace. Inner products are conjugate-linear first.
-/

open scoped InnerProductSpace

namespace Riemann.CCM

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The source hypotheses for the original full simple-even construction.
The free constant mode and boundary vector are separate pieces of data. -/
structure FullSimpleEvenData where
  finite_dimensional : FiniteDimensional ℂ E
  H : E →L[ℂ] E
  D : E →L[ℂ] E
  reflection : E →L[ℂ] E
  eta : E
  b : E
  ground : E
  constant : E
  e₀ : ℝ
  H_selfadjoint : H.adjoint = H
  D_selfadjoint : D.adjoint = D
  reflection_selfadjoint : reflection.adjoint = reflection
  reflection_involutive : ∀ x, reflection (reflection x) = x
  reflection_H : ∀ x, reflection (H x) = H (reflection x)
  reflection_D : ∀ x, reflection (D x) = -D (reflection x)
  eta_even : reflection eta = eta
  b_odd : reflection b = -b
  ground_even : reflection ground = ground
  ground_ne_zero : ground ≠ 0
  ground_eigen : H ground = (e₀ : ℂ) • ground
  least : ∀ x, e₀ * ‖x‖ ^ 2 ≤ (⟪x, H x⟫_ℂ).re
  simple : ∀ x, H x = (e₀ : ℂ) • x ↔ ∃ a : ℂ, x = a • ground
  constant_kernel : ∀ x, D x = 0 ↔ ∃ a : ℂ, x = a • constant
  constant_bright : ⟪eta, constant⟫_ℂ ≠ 0
  displacement : ∀ x, D (H x) - H (D x) =
    ⟪eta, x⟫_ℂ • b - ⟪b, x⟫_ℂ • eta

namespace FullSimpleEvenData

variable {E} (M : FullSimpleEvenData E)

/-- Shift by the full least eigenvalue, preserving the physical inner product. -/
def shifted : E →L[ℂ] E := M.H - (M.e₀ : ℂ) • ContinuousLinearMap.id ℂ E

/-- Native endpoint observation. -/
def boundary (x : E) : ℂ := ⟪M.eta, x⟫_ℂ

@[simp] theorem shifted_apply (x : E) :
    M.shifted x = M.H x - (M.e₀ : ℂ) • x := rfl

@[simp] theorem shifted_ground : M.shifted M.ground = 0 := by
  simp [M.ground_eigen]

/-- Simplicity concerns the kernel of the full shifted form. -/
theorem shifted_eq_zero_iff (x : E) :
    M.shifted x = 0 ↔ ∃ a : ℂ, x = a • M.ground := by
  simpa only [shifted_apply, sub_eq_zero] using M.simple x

/-- The scalar shift leaves the displacement unchanged. -/
theorem shifted_displacement (x : E) :
    M.D (M.shifted x) - M.shifted (M.D x) =
      ⟪M.eta, x⟫_ℂ • M.b - ⟪M.b, x⟫_ℂ • M.eta := by
  simpa only [shifted_apply, map_sub, map_smul, sub_sub_sub_cancel_right] using
    M.displacement x

/-- The full variational lower bound gives positivity of the shifted form. -/
theorem shifted_nonneg (x : E) : 0 ≤ (⟪x, M.shifted x⟫_ℂ).re := by
  rw [shifted_apply, inner_sub_right, inner_smul_right, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    show (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 from
      (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm]
  exact sub_nonneg.mpr (M.least x)

/-- Subtracting a real scalar preserves self-adjointness. -/
theorem shifted_selfadjoint : M.shifted.adjoint = M.shifted := by
  simp only [shifted, map_sub, map_smulₛₗ]
  simp [M.H_selfadjoint]

end FullSimpleEvenData
end Riemann.CCM
