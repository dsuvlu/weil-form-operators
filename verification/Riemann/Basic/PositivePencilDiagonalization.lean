import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-! Simultaneous congruence diagonalization of two positive real forms. -/
noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace Riemann.Basic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive real pair has a genuine invertible change of coordinates making
its mass the identity and its energy a positive diagonal matrix. -/
theorem positivePair_diagonalization (K B : Matrix ι ι ℝ) (hK : K.PosDef) (hB : B.PosDef) :
    ∃ (T : Matrix ι ι ℝ) (lambda : ι → ℝ), IsUnit T ∧
      (∀ i, 0 < lambda i) ∧ star T * B * T = 1 ∧ star T * K * T = Matrix.diagonal lambda := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.posSemidef.nonneg
  have hCdet : C.det ≠ 0 := by
    have h := hB.det_pos.ne'
    rw [hC, Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose] at h
    exact (mul_ne_zero_iff.mp h).2
  have hCu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hCdet)
  have hCi : IsUnit C⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hCu
  let F := star C⁻¹ * K * C⁻¹
  have hF : F.PosDef := hCi.posDef_star_left_conjugate_iff.mpr hK
  let U := hF.isHermitian.eigenvectorUnitary
  have hU : IsUnit (U : Matrix ι ι ℝ) := Unitary.isUnit_coe
  have hUU : (star (U : Matrix ι ι ℝ)) * U = 1 := Unitary.coe_star_mul_self U
  refine ⟨C⁻¹ * U, hF.isHermitian.eigenvalues, hCi.mul hU,
    hF.eigenvalues_pos, ?_, ?_⟩
  · calc
      _ = star (C * (C⁻¹ * (U : Matrix ι ι ℝ))) * (C * (C⁻¹ * U)) := by
        rw [hC]
        simp only [star_mul]
        noncomm_ring
      _ = 1 := by
        have hCU : C * (C⁻¹ * (U : Matrix ι ι ℝ)) = U := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hCdet), Matrix.one_mul]
        rw [hCU, hUU]
  · have hspec := hF.isHermitian.spectral_theorem
    change F = (U : Matrix ι ι ℝ) * Matrix.diagonal hF.isHermitian.eigenvalues * star (U : Matrix ι ι ℝ) at hspec
    rw [star_mul]
    change star (U : Matrix ι ι ℝ) * star C⁻¹ * K * (C⁻¹ * U) = _
    calc
      _ = star (U : Matrix ι ι ℝ) * F * U := by simp [F, Matrix.mul_assoc]
      _ = Matrix.diagonal hF.isHermitian.eigenvalues := by
        conv_lhs => rw [hspec]
        simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
        rw [Matrix.mul_assoc, hUU, Matrix.mul_one]

/-- Spectral sums and determinant products obtained from the constructed
congruence, not postulated as a spectral representation. -/
theorem positivePair_spectral_representation (K B : Matrix ι ι ℝ)
    (hK : K.PosDef) (hB : B.PosDef) :
    ∃ lambda : ι → ℝ, (∀ i, 0 < lambda i) ∧
      (∀ s : ℝ, 0 < s → Matrix.trace ((K + s • B)⁻¹ * B) =
        ∑ i, (lambda i + s)⁻¹) ∧
      (∀ a b : ℝ, 0 < a → 0 < b →
        (K + b • B).det / (K + a • B).det =
          ∏ i, (lambda i + b) / (lambda i + a)) := by
  obtain ⟨T, lambda, hT, hl, hTB, hTK⟩ := positivePair_diagonalization K B hK hB
  have hTd : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT
  have hTsd : IsUnit (star T).det := (Matrix.isUnit_iff_isUnit_det (star T)).mp hT.star
  have hdiag (s : ℝ) : star T * (K + s • B) * T = Matrix.diagonal (fun i => lambda i + s) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hTK, hTB]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  have hpd (s : ℝ) (hs : 0 < s) : 0 < (K + s • B).det := (hK.add (hB.smul hs)).det_pos
  refine ⟨lambda, hl, ?_, ?_⟩
  · intro s hs
    have hdinv : (Matrix.diagonal (fun i => lambda i + s))⁻¹ =
        Matrix.diagonal (fun i => (lambda i + s)⁻¹) := by
      apply Matrix.inv_eq_left_inv
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      simp [Matrix.diagonal_apply, Matrix.one_apply, (add_pos (hl _) hs).ne']
    have hinv : Matrix.trace ((star T * (K + s • B) * T)⁻¹ * (star T * B * T)) =
        Matrix.trace ((K + s • B)⁻¹ * B) := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
      have hm : (T⁻¹ * ((K + s • B)⁻¹ * (star T)⁻¹)) * (star T * B * T) =
          T⁻¹ * ((K + s • B)⁻¹ * B) * T := by
        calc
          _ = T⁻¹ * (K + s • B)⁻¹ * ((star T)⁻¹ * star T) * B * T := by noncomm_ring
          _ = _ := by rw [Matrix.nonsing_inv_mul _ hTsd]; noncomm_ring
      rw [hm, Matrix.trace_mul_cycle]
      rw [Matrix.mul_nonsing_inv _ hTd, Matrix.one_mul]
    rw [hdiag, hTB, Matrix.mul_one, hdinv, Matrix.trace_diagonal] at hinv
    exact hinv.symm
  · intro a b ha hb
    have hda := congrArg Matrix.det (hdiag a)
    have hdb := congrArg Matrix.det (hdiag b)
    simp only [Matrix.det_mul, Matrix.det_diagonal] at hda hdb
    rw [Finset.prod_div_distrib, ← hda, ← hdb]
    field_simp [hTd.ne_zero, hTsd.ne_zero, (hpd a ha).ne']


end Riemann.Basic
