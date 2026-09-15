import Riemann.CCM.InverseEnergy
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Literal determinant derivative and the finite high soft spectral mean. -/
noncomputable section
open Matrix
namespace Riemann.CCM.InverseEnergyData
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (M : InverseEnergyData ι)

/-- The direct rank-one solve complements the adjoint boundary solve. -/
theorem inversePencil_beta {s : ℝ} (hs : 0 < s) :
    M.inversePencil s *ᵥ M.beta = (M.determinantRatio s)⁻¹ •
      (M.resolvent s *ᵥ (M.B⁻¹ *ᵥ M.beta)) := by
  have hB : IsUnit M.B.det := isUnit_iff_ne_zero.mpr M.B_pos.det_pos.ne'
  have hF : IsUnit (M.freePencil s).det := isUnit_iff_ne_zero.mpr (M.freePencil_pos hs).det_pos.ne'
  have hP : IsUnit (M.pencil s).det := isUnit_iff_ne_zero.mpr (M.pencil_pos hs).det_pos.ne'
  have hv : M.pencil s *ᵥ (M.resolvent s *ᵥ (M.B⁻¹ *ᵥ M.beta)) =
      M.determinantRatio s • M.beta := by
    rw [M.pencil_split s, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      rankOne_mulVec, M.determinantRatio_eq hs]
    have hfree : M.B *ᵥ (M.freePencil s *ᵥ (M.resolvent s *ᵥ (M.B⁻¹ *ᵥ M.beta))) = M.beta := by
      simp [resolvent, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hF,
        Matrix.mul_nonsing_inv _ hB]
    rw [hfree, add_smul, one_smul]
  have hv' := congrArg (fun v => M.inversePencil s *ᵥ v) hv
  have hscaled : M.resolvent s *ᵥ (M.B⁻¹ *ᵥ M.beta) =
      M.determinantRatio s • (M.inversePencil s *ᵥ M.beta) := by
    simpa [inversePencil, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP,
      Matrix.mulVec_smul] using hv'
  rw [hscaled, smul_smul, inv_mul_cancel₀ (M.determinantRatio_pos hs).ne', one_smul]

/-- Sherman–Morrison in the exact inverse-mass order. -/
theorem inversePencil_mass {s : ℝ} (hs : 0 < s) :
    M.inversePencil s * M.B = M.resolvent s -
      (M.determinantRatio s)⁻¹ • Matrix.vecMulVec
        (M.resolvent s *ᵥ (M.B⁻¹ *ᵥ M.beta)) (M.zeta ᵥ* M.resolvent s) := by
  have hF : IsUnit (M.freePencil s).det := isUnit_iff_ne_zero.mpr (M.freePencil_pos hs).det_pos.ne'
  have hP : IsUnit (M.pencil s).det := isUnit_iff_ne_zero.mpr (M.pencil_pos hs).det_pos.ne'
  have h := congrArg (fun C => M.inversePencil s * C * M.resolvent s) (M.pencil_split s)
  have hl : M.inversePencil s * M.pencil s * M.resolvent s = M.resolvent s := by
    simp [inversePencil, Matrix.nonsing_inv_mul _ hP]
  have ht : M.inversePencil s * (M.B * M.freePencil s) * M.resolvent s =
      M.inversePencil s * M.B := by
    simp [resolvent, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hF]
  rw [hl, Matrix.mul_add, Matrix.add_mul, ht] at h
  change M.resolvent s = M.inversePencil s * M.B +
    M.inversePencil s * Matrix.vecMulVec M.beta M.zeta * M.resolvent s at h
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, M.inversePencil_beta hs,
    Matrix.smul_vecMulVec] at h
  exact eq_sub_iff_add_eq.mpr h.symm

/-- The trace of the inverse is the derivative of the literal perturbation determinant. -/
theorem highMean_eq {s : ℝ} (hs : 0 < s) :
    M.highMean s = M.freeMean s + s * deriv M.determinantRatio s / M.determinantRatio s := by
  rw [highMean, M.inversePencil_mass hs, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_vecMulVec, (M.hasDerivAt_determinantRatio hs).deriv, freeMean]
  have hp : (M.resolvent s *ᵥ (M.B⁻¹ *ᵥ M.beta)) ⬝ᵥ (M.zeta ᵥ* M.resolvent s) =
      M.zeta ⬝ᵥ ((M.resolvent s * M.resolvent s) *ᵥ (M.B⁻¹ *ᵥ M.beta)) := by
    rw [dotProduct_comm]
    simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rw [hp]
  ring

/-- BL's finite inverse-energy identity, including the actual real logarithmic derivative. -/
theorem highMean_inverseEnergy_identity {s : ℝ} (hs : 0 < s) :
    M.highMean s = M.freeMean s + M.boundaryCorrection s +
      s / 2 * deriv (fun t => Real.log (M.inverseEnergy t)) s := by
  rw [M.highMean_eq hs, M.logarithmicEnergy_identity hs]
  ring

end Riemann.CCM.InverseEnergyData
