import Riemann.CCM.Data
import Mathlib.Tactic

/-! Boundary brightness is proved from parity and displacement, not assumed. -/

open scoped InnerProductSpace

namespace Riemann.CCM.FullSimpleEvenData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable (M : FullSimpleEvenData E)

/-- Odd displacement data are orthogonal to every even vector. -/
theorem odd_inner_even {x : E} (hx : M.reflection x = x) :
    ⟪M.b, x⟫_ℂ = 0 := by
  have h := ContinuousLinearMap.adjoint_inner_left M.reflection x M.b
  rw [M.reflection_selfadjoint, M.b_odd, hx, inner_neg_left] at h
  have htwo : (2 : ℂ) * ⟪M.b, x⟫_ℂ = 0 := by linear_combination -h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Every vector in the shifted radical is even because that radical is the
single original even ground line. -/
theorem kernel_even {x : E} (hx : M.shifted x = 0) :
    M.reflection x = x := by
  obtain ⟨a, rfl⟩ := (M.shifted_eq_zero_iff x).mp hx
  simp only [map_smul, M.ground_even]

/-- Boundary brightness of the original ground; no visibility floor is assumed. -/
theorem ground_bright : ⟪M.eta, M.ground⟫_ℂ ≠ 0 := by
  intro hdark
  have hb := M.odd_inner_even M.ground_even
  have hrad : M.shifted (M.D M.ground) = 0 := by
    simpa only [M.shifted_ground, map_zero, zero_sub, hdark, hb,
      zero_smul, sub_self, neg_eq_zero] using M.shifted_displacement M.ground
  have heven := M.kernel_even hrad
  have hodd : M.reflection (M.D M.ground) = -M.D M.ground := by
    rw [M.reflection_D, M.ground_even]
  have htwo : (2 : ℂ) • M.D M.ground = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp (heven.symm.trans hodd)
  have hD : M.D M.ground = 0 :=
    (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  obtain ⟨a, ha⟩ := (M.constant_kernel M.ground).mp hD
  have hz : a * ⟪M.eta, M.constant⟫_ℂ = 0 := by
    simpa only [ha, inner_smul_right] using hdark
  have ha0 : a = 0 := (mul_eq_zero.mp hz).resolve_right M.constant_bright
  exact M.ground_ne_zero (by simpa [ha0] using ha)

/-- Normalization by the endpoint eliminates the scalar ambiguity of the ground. -/
noncomputable def normalizedGround : E := (⟪M.eta, M.ground⟫_ℂ)⁻¹ • M.ground

@[simp] theorem boundary_normalizedGround :
    ⟪M.eta, M.normalizedGround⟫_ℂ = 1 := by
  simp [normalizedGround, inner_smul_right, M.ground_bright]

@[simp] theorem shifted_normalizedGround : M.shifted M.normalizedGround = 0 := by
  rw [normalizedGround, map_smul, M.shifted_ground, smul_zero]

@[simp] theorem reflection_normalizedGround :
    M.reflection M.normalizedGround = M.normalizedGround := by
  simp [normalizedGround, M.ground_even]

/-- Displacement applied to the normalized original ground gives the correction
vector with its source sign. -/
theorem shifted_D_normalizedGround :
    M.shifted (M.D M.normalizedGround) = -M.b := by
  have h := M.shifted_displacement M.normalizedGround
  have hb := M.odd_inner_even M.reflection_normalizedGround
  simp only [M.shifted_normalizedGround, map_zero, zero_sub,
    M.boundary_normalizedGround, one_smul, hb, zero_smul, sub_zero] at h
  exact neg_eq_iff_eq_neg.mp h

end Riemann.CCM.FullSimpleEvenData
