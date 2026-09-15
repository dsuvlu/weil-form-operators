import Riemann.CCM.Correction
import Riemann.Basic.MetricSpectrum

/-! Positive-metric consequences for the finite corrected CCM operator. -/

open scoped InnerProductSpace

namespace Riemann.CCM.FullSimpleEvenData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (M : FullSimpleEvenData E)

/-- Native mathlib positivity of the shifted full form. -/
theorem shifted_positive : M.shifted.IsPositive := by
  refine ContinuousLinearMap.isPositive_def'.mpr ⟨M.shifted_selfadjoint, ?_⟩
  intro x
  change 0 ≤ (⟪M.shifted x, x⟫_ℂ).re
  rw [show (⟪M.shifted x, x⟫_ℂ).re = (⟪x, M.shifted x⟫_ℂ).re from inner_re_symm (𝕜 := ℂ) (M.shifted x) x]
  exact M.shifted_nonneg x

/-- The correction kills the whole shifted radical, not only a chosen phase. -/
theorem corrected_kills_kernel (x : E) (hx : M.shifted x = 0) :
    M.corrected x = 0 := by
  obtain ⟨a, rfl⟩ := (M.shifted_eq_zero_iff x).mp hx
  have hg : M.corrected M.ground = 0 := by
    simp [corrected_apply, M.groundVector_eq_normalizedGround, normalizedGround,
      map_smul, smul_smul, M.ground_bright]
  simp [map_smul, hg]

/-- The shifted form is positive definite on the physical complement of its kernel. -/
theorem shifted_positive_on_complement {x : E}
    (hx : x ∈ (LinearMap.ker M.shifted.toLinearMap)ᗮ) (hne : x ≠ 0) :
    0 < (⟪x, M.shifted x⟫_ℂ).re :=
  Riemann.positive_energy_pos_on_kernel_orthogonal M.shifted M.shifted_positive hx hne

/-- Every eigenvalue of the full corrected finite operator is real, including zero. -/
theorem corrected_eigenvalue_real {x : E} {z : ℂ}
    (hx : x ≠ 0) (heigen : M.corrected x = z • x) : z.im = 0 :=
  Riemann.metricSymmetric_eigenvalue_real M.shifted M.corrected M.shifted_positive
    M.weighted_symmetry M.corrected_kills_kernel hx heigen

end Riemann.CCM.FullSimpleEvenData
