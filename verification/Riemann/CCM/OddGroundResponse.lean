import Riemann.CCM.NativeHighCoordinateEquiv
import Riemann.Basic.RealMatrixComplexification

/-! The actual ground's derivative is reconstructed by the full odd mass
inverse. The ground itself is never replaced by an odd state. -/
noncomputable section
open scoped InnerProductSpace BigOperators
open Matrix
namespace Riemann.CCM.Native
variable {N : ℕ}

/-- Zero is the only Fourier coefficient excluded by cutoff zero, and oddness
already forces that coefficient to vanish. -/
theorem mem_oddHigh_zero {x : Section N} (hx : reflection N x = -x) :
    x ∈ oddHighSection N 0 := by
  refine ⟨hx, ?_⟩
  intro i hi
  have hm : mode i = 0 := by omega
  have hr : i.rev = i := mode_injective N (by rw [mode_rev, hm, neg_zero])
  have h := congrArg (fun y : Section N => y i) hx
  simp only [reflection_apply, PiLp.neg_apply, hr] at h
  linear_combination (1 / 2 : ℂ) * h

/-- The full positive paired coordinates detect every odd vector. -/
theorem odd_eq_zero_of_pairings {x : Section N} (hx : reflection N x = -x)
    (hpair : ∀ j : HighIndex N 0, ⟪oddHighVector j, x⟫_ℂ = 0) : x = 0 := by
  obtain ⟨c, hc⟩ := highSynthesis_surjective N 0 ⟨x, mem_oddHigh_zero hx⟩
  have hs : (∑ j, c j • oddHighVector j) = x := congrArg Subtype.val hc
  have hz : c = 0 := by
    ext j
    have h := hpair j
    rw [← hs, (@oddHighVector_orthonormal N 0).inner_right_fintype] at h
    exact h
  simpa [hz] using hs.symm

/-- Coordinates of the derivative source of the actual full normalized ground. -/
theorem ground_derivative_odd_inverse (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) :
    derivative L (fullData C L hL A).groundVector =
      -oddHighRealSynthesis ((highRealMass C L hL A 0)⁻¹ *ᵥ highRealBeta C L) := by
  let M := fullData C L hL A
  let B := highRealMass C L hL A 0
  let t := B⁻¹ *ᵥ highRealBeta C L
  let y := oddHighRealSynthesis t
  have hy : M.reflection y = -y := oddHighRealSynthesis_odd t
  have hDy : M.reflection (M.D M.groundVector) = -M.D M.groundVector := by
    change reflection N (derivative L M.groundVector) = -derivative L M.groundVector
    have he : reflection N M.groundVector = M.groundVector := M.reflection_groundVector
    rw [reflection_derivative, he]
  have hsolve : B *ᵥ t = highRealBeta C L := by
    dsimp [t]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (highRealMass_pos C L hL A 0).det_pos.ne'), Matrix.one_mulVec]
  have hGy : M.shifted y = M.b := by
    apply sub_eq_zero.mp
    apply odd_eq_zero_of_pairings
    · change M.reflection (M.shifted y - M.b) = -(M.shifted y - M.b)
      rw [map_sub, M.shifted_odd hy, M.b_odd]
      abel
    · intro j
      rw [inner_sub_right]
      change ⟪oddHighVector j, M.shifted (∑ k, (t k : ℂ) • oddHighVector k)⟫_ℂ -
        ⟪oddHighVector j, M.b⟫_ℂ = 0
      rw [map_sum, inner_sum]
      have hm (i k : HighIndex N 0) :
          ⟪oddHighVector i, M.shifted (oddHighVector k)⟫_ℂ = (B i k : ℂ) :=
        (highRealMass_complex_entry C L hL A i k).symm
      have hb : ⟪oddHighVector j, M.b⟫_ℂ = (highRealBeta C L j : ℂ) :=
        (highRealBeta_complex_entry C L j).symm
      simp only [map_smul, inner_smul_right, hm, hb]
      have hj := congrFun hsolve j
      have hjc := congrArg (fun r : ℝ => (r : ℂ)) hj
      simpa [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul,
        mul_comm] using sub_eq_zero.mpr hjc
  have hz : M.D M.groundVector + y = 0 := by
    apply M.odd_shifted_kernel
    · rw [map_add, hDy, hy, neg_add]
    · rw [map_add, M.shifted_D_groundVector, hGy, neg_add_cancel]
  exact eq_neg_of_add_eq_zero_left hz

end Riemann.CCM.Native
