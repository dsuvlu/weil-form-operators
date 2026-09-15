import Riemann.Basic.MatrixPencilCalculus
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.Star.Real

/-!
# The finite inverse-energy pencil

Real native high-block coefficients are held fixed while the real parameter s
varies. Positivity is assumed only for the three named finite matrices; a later
native specialization must derive these hypotheses from its admitted ground.
-/
noncomputable section
open Matrix
namespace Riemann.CCM
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive high-block data with the ordered native displacement identity. -/
structure InverseEnergyData (ι : Type*) [Fintype ι] [DecidableEq ι] where
  A : Matrix ι ι ℝ
  B : Matrix ι ι ℝ
  K : Matrix ι ι ℝ
  beta : ι → ℝ
  zeta : ι → ℝ
  A_pos : A.PosDef
  B_pos : B.PosDef
  K_pos : K.PosDef
  displacement : K = B * A + Matrix.of (fun i j => beta i * zeta j)
  zeta_ne_zero : zeta ≠ 0

namespace InverseEnergyData
variable (M : InverseEnergyData ι)

def freePencil (s : ℝ) : Matrix ι ι ℝ := M.A + s • 1
def pencil (s : ℝ) : Matrix ι ι ℝ := M.K + s • M.B
def resolvent (s : ℝ) : Matrix ι ι ℝ := (M.freePencil s)⁻¹
def inversePencil (s : ℝ) : Matrix ι ι ℝ := (M.pencil s)⁻¹
def boundaryVector (s : ℝ) : ι → ℝ := M.resolvent s *ᵥ M.zeta
def inverseEnergy (s : ℝ) : ℝ :=
  M.boundaryVector s ⬝ᵥ (M.B⁻¹ *ᵥ M.boundaryVector s)
def determinantRatio (s : ℝ) : ℝ :=
  (M.pencil s).det / (M.B.det * (M.freePencil s).det)
def boundaryResponse (s : ℝ) : ℝ := M.zeta ⬝ᵥ (M.inversePencil s *ᵥ M.zeta)
def highMean (s : ℝ) : ℝ := s * Matrix.trace (M.inversePencil s * M.B)
def freeMean (s : ℝ) : ℝ := s * Matrix.trace (M.resolvent s)
def boundaryCorrection (s : ℝ) : ℝ :=
  s * (M.boundaryVector s ⬝ᵥ (M.inversePencil s *ᵥ M.boundaryVector s)) /
    M.inverseEnergy s

lemma freePencil_pos {s : ℝ} (hs : 0 < s) : (M.freePencil s).PosDef :=
  M.A_pos.add ((Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).smul hs)
lemma pencil_pos {s : ℝ} (hs : 0 < s) : (M.pencil s).PosDef :=
  M.K_pos.add (M.B_pos.smul hs)
lemma determinantRatio_pos {s : ℝ} (hs : 0 < s) : 0 < M.determinantRatio s :=
  div_pos (M.pencil_pos hs).det_pos (mul_pos M.B_pos.det_pos (M.freePencil_pos hs).det_pos)
lemma boundaryVector_ne_zero {s : ℝ} (hs : 0 < s) : M.boundaryVector s ≠ 0 := by
  intro h
  apply M.zeta_ne_zero
  have h' := congrArg (fun v => M.freePencil s *ᵥ v) h
  simpa [boundaryVector, resolvent, mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (M.freePencil_pos hs).det_pos.ne')] using h'
lemma inverseEnergy_pos {s : ℝ} (hs : 0 < s) : 0 < M.inverseEnergy s := by
  simpa [inverseEnergy] using M.B_pos.inv.dotProduct_mulVec_pos (M.boundaryVector_ne_zero hs)

lemma pencil_split (s : ℝ) :
    M.pencil s = M.B * M.freePencil s + Matrix.of (fun i j => M.beta i * M.zeta j) := by
  simp only [pencil, freePencil, M.displacement, mul_add, Matrix.mul_smul, Matrix.mul_one]
  abel

/-- The determinant ratio is the literal rank-one perturbation determinant. -/
theorem determinantRatio_eq {s : ℝ} (hs : 0 < s) :
    M.determinantRatio s =
      1 + M.zeta ⬝ᵥ (M.resolvent s *ᵥ (M.B⁻¹ *ᵥ M.beta)) := by
  have hB := (isUnit_iff_ne_zero.mpr M.B_pos.det_pos.ne')
  have hF := (isUnit_iff_ne_zero.mpr (M.freePencil_pos hs).det_pos.ne')
  have hBF : IsUnit (M.B * M.freePencil s).det := by
    rw [Matrix.det_mul]; exact hB.mul hF
  have hrank : Matrix.of (fun i j => M.beta i * M.zeta j) =
      Matrix.replicateCol Unit M.beta * Matrix.replicateRow Unit M.zeta := by
    ext i j; simp [Matrix.mul_apply]
  have hd := Matrix.det_add_replicateCol_mul_replicateRow (ι := Unit) hBF
    M.beta M.zeta
  rw [← hrank, ← M.pencil_split s] at hd
  have hinv : (M.B * M.freePencil s)⁻¹ = M.resolvent s * M.B⁻¹ := by
    simp [resolvent, Matrix.mul_inv_rev]
  rw [Matrix.det_mul, hinv, Matrix.det_unique (n := Unit)] at hd
  have hentry : ((1 : Matrix Unit Unit ℝ) + Matrix.replicateRow Unit M.zeta *
      (M.resolvent s * M.B⁻¹) * Matrix.replicateCol Unit M.beta) () () =
      1 + M.zeta ⬝ᵥ (M.resolvent s *ᵥ (M.B⁻¹ *ᵥ M.beta)) := by
    simp [Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    funext y
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hentry] at hd
  rw [determinantRatio, hd, mul_div_cancel_left₀]
  exact mul_ne_zero M.B_pos.det_pos.ne' (M.freePencil_pos hs).det_pos.ne'

omit [DecidableEq ι] in
lemma symmetric_pairing {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (x y : ι → ℝ) :
    x ⬝ᵥ (C *ᵥ y) = y ⬝ᵥ (C *ᵥ x) := by
  have ht : Cᵀ = C := (Matrix.isHermitian_iff_isSymm.mp hC).eq
  simpa only [ht] using Matrix.dotProduct_transpose_mulVec C x y

lemma pencil_split_adjoint (s : ℝ) :
    M.pencil s = M.freePencil s * M.B + Matrix.of (fun i j => M.zeta i * M.beta j) := by
  have h := congrArg Matrix.transpose (M.pencil_split s)
  have hp : (M.pencil s)ᵀ = M.pencil s := by
    apply (Matrix.isHermitian_iff_isSymm.mp _).eq
    exact M.K_pos.isHermitian.add (M.B_pos.isHermitian.smul (star_trivial s))
  have hf : (M.freePencil s)ᵀ = M.freePencil s := by
    apply (Matrix.isHermitian_iff_isSymm.mp _).eq
    exact M.A_pos.isHermitian.add (Matrix.isHermitian_one.smul (star_trivial s))
  have hb : M.Bᵀ = M.B := (Matrix.isHermitian_iff_isSymm.mp M.B_pos.isHermitian).eq
  rw [Matrix.transpose_add, Matrix.transpose_mul, hp, hf, hb] at h
  convert h using 1
  ext i j
  simp [Matrix.transpose, mul_comm]

/-- The literal determinant ratio has an ordinary real derivative. -/
theorem hasDerivAt_determinantRatio {s : ℝ} (hs : 0 < s) :
    HasDerivAt M.determinantRatio
      (-(M.zeta ⬝ᵥ ((M.resolvent s * M.resolvent s) *ᵥ (M.B⁻¹ *ᵥ M.beta)))) s := by
  have hd := Riemann.Basic.hasDerivAt_inverseContraction M.A 1 s
    (M.freePencil_pos hs).isUnit M.zeta (M.B⁻¹ *ᵥ M.beta)
  have h := hd.const_add 1
  have heq : M.determinantRatio =ᶠ[nhds s]
      (fun t => 1 + M.zeta ⬝ᵥ ((M.A + t • 1)⁻¹ *ᵥ (M.B⁻¹ *ᵥ M.beta))) := by
    filter_upwards [eventually_gt_nhds hs] with t ht
    exact M.determinantRatio_eq ht
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  simpa [resolvent, freePencil] using h

/-- Actual derivative of the boundary response h(s)=ζᵀP(s)⁻¹ζ. -/
theorem hasDerivAt_boundaryResponse {s : ℝ} (hs : 0 < s) :
    HasDerivAt M.boundaryResponse
      (-(M.zeta ⬝ᵥ ((M.inversePencil s * M.B * M.inversePencil s) *ᵥ M.zeta))) s := by
  exact Riemann.Basic.hasDerivAt_inverseContraction M.K M.B s
      (M.pencil_pos hs).isUnit M.zeta M.zeta

omit [DecidableEq ι] in
lemma rankOne_mulVec (x y z : ι → ℝ) :
    Matrix.of (fun i j => x i * y j) *ᵥ z = (y ⬝ᵥ z) • x := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Ordered boundary solve; no commutation of B⁻¹ and R is used. -/
theorem inversePencil_boundary_scaled {s : ℝ} (hs : 0 < s) :
    M.B⁻¹ *ᵥ M.boundaryVector s =
      M.determinantRatio s • (M.inversePencil s *ᵥ M.zeta) := by
  have hB : IsUnit M.B.det := isUnit_iff_ne_zero.mpr M.B_pos.det_pos.ne'
  have hF : IsUnit (M.freePencil s).det :=
    isUnit_iff_ne_zero.mpr (M.freePencil_pos hs).det_pos.ne'
  have hP : IsUnit (M.pencil s).det :=
    isUnit_iff_ne_zero.mpr (M.pencil_pos hs).det_pos.ne'
  have hscalar : M.beta ⬝ᵥ (M.B⁻¹ *ᵥ M.boundaryVector s) =
      M.zeta ⬝ᵥ (M.resolvent s *ᵥ (M.B⁻¹ *ᵥ M.beta)) := by
    rw [symmetric_pairing M.B_pos.inv.isHermitian, dotProduct_comm]
    exact symmetric_pairing (M.freePencil_pos hs).inv.isHermitian _ _
  have hsolve : M.pencil s *ᵥ (M.B⁻¹ *ᵥ M.boundaryVector s) =
      M.determinantRatio s • M.zeta := by
    rw [M.pencil_split_adjoint s, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec (M.boundaryVector s), Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec,
      rankOne_mulVec, hscalar, M.determinantRatio_eq hs]
    have hfree : M.freePencil s *ᵥ M.boundaryVector s = M.zeta := by
      simp [boundaryVector, resolvent, mulVec_mulVec, Matrix.mul_nonsing_inv _ hF]
    rw [hfree, add_smul, one_smul]
  have hsolve' := congrArg (fun v => M.inversePencil s *ᵥ v) hsolve
  simpa [inversePencil, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hP,
    Matrix.mulVec_smul, ← Matrix.mul_assoc] using hsolve'

theorem inversePencil_boundary {s : ℝ} (hs : 0 < s) :
    M.inversePencil s *ᵥ M.zeta =
      (M.determinantRatio s)⁻¹ • (M.B⁻¹ *ᵥ M.boundaryVector s) := by
  rw [M.inversePencil_boundary_scaled hs, smul_smul,
    inv_mul_cancel₀ (M.determinantRatio_pos hs).ne', one_smul]

/-- The inverse energy is the squared determinant times the positive response energy. -/
theorem inverseEnergy_eq {s : ℝ} (hs : 0 < s) :
    M.inverseEnergy s = M.determinantRatio s ^ 2 *
      (M.zeta ⬝ᵥ ((M.inversePencil s * M.B * M.inversePencil s) *ᵥ M.zeta)) := by
  have hB : IsUnit M.B.det := isUnit_iff_ne_zero.mpr M.B_pos.det_pos.ne'
  have hb : M.boundaryVector s =
      M.determinantRatio s • (M.B *ᵥ (M.inversePencil s *ᵥ M.zeta)) := by
    have h := congrArg (fun v => M.B *ᵥ v) (M.inversePencil_boundary_scaled hs)
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.mulVec_smul] using h
  rw [inverseEnergy, M.inversePencil_boundary_scaled hs, hb,
    smul_dotProduct, dotProduct_smul]
  have hpair : (M.B *ᵥ (M.inversePencil s *ᵥ M.zeta)) ⬝ᵥ
      (M.inversePencil s *ᵥ M.zeta) =
      M.zeta ⬝ᵥ ((M.inversePencil s * M.B * M.inversePencil s) *ᵥ M.zeta) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact symmetric_pairing (M.pencil_pos hs).inv.isHermitian _ _
  rw [hpair]
  ring

/-- Positive first response energy, equal to minus the derivative of h. -/
def responseEnergy (s : ℝ) : ℝ :=
  M.zeta ⬝ᵥ ((M.inversePencil s * M.B * M.inversePencil s) *ᵥ M.zeta)
/-- The next positive response moment. -/
def responseMoment (s : ℝ) : ℝ :=
  M.zeta ⬝ᵥ ((M.inversePencil s * M.B * M.inversePencil s * M.B * M.inversePencil s) *ᵥ M.zeta)

theorem responseEnergy_pos {s : ℝ} (hs : 0 < s) : 0 < M.responseEnergy s := by
  have h := M.inverseEnergy_pos hs
  rw [M.inverseEnergy_eq hs] at h
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (M.determinantRatio_pos hs))).mp h

/-- The second response derivative is an actual real derivative. -/
theorem hasDerivAt_responseEnergy {s : ℝ} (hs : 0 < s) :
    HasDerivAt M.responseEnergy (-2 * M.responseMoment s) s := by
  have hd := Riemann.Basic.hasDerivAt_doubleInverseContraction M.K M.B M.B s
    (M.pencil_pos hs).isUnit M.zeta M.zeta
  convert! hd using 1
  simp [responseMoment, inversePencil, pencil, neg_mul, mul_neg, Matrix.mul_assoc,
    Matrix.add_mulVec, Matrix.neg_mulVec, dotProduct_add, dotProduct_neg]
  ring

/-- Energy differentiation obtained from E=D² times the positive response energy. -/
theorem hasDerivAt_inverseEnergy {s : ℝ} (hs : 0 < s) :
    HasDerivAt M.inverseEnergy
      (2 * M.determinantRatio s * deriv M.determinantRatio s * M.responseEnergy s -
        2 * M.determinantRatio s ^ 2 * M.responseMoment s) s := by
  have hd := (M.hasDerivAt_determinantRatio hs).differentiableAt.hasDerivAt
  have hw := M.hasDerivAt_responseEnergy hs
  have hp := (hd.pow 2).mul hw
  have heq : M.inverseEnergy =ᶠ[nhds s]
      (fun t => M.determinantRatio t ^ 2 * M.responseEnergy t) := by
    filter_upwards [eventually_gt_nhds hs] with t ht
    exact M.inverseEnergy_eq ht
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert! hp using 1
  simp only [Pi.pow_apply]
  ring

/-- The boundary numerator is the same second moment with its determinant scale. -/
theorem boundaryNumerator_eq {s : ℝ} (hs : 0 < s) :
    M.boundaryVector s ⬝ᵥ (M.inversePencil s *ᵥ M.boundaryVector s) =
      M.determinantRatio s ^ 2 * M.responseMoment s := by
  have hB : IsUnit M.B.det := isUnit_iff_ne_zero.mpr M.B_pos.det_pos.ne'
  have hb : M.boundaryVector s =
      M.determinantRatio s • (M.B *ᵥ (M.inversePencil s *ᵥ M.zeta)) := by
    have h := congrArg (fun v => M.B *ᵥ v) (M.inversePencil_boundary_scaled hs)
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.mulVec_smul] using h
  rw [hb, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  have hpair : (M.B *ᵥ (M.inversePencil s *ᵥ M.zeta)) ⬝ᵥ
      (M.inversePencil s *ᵥ (M.B *ᵥ (M.inversePencil s *ᵥ M.zeta))) =
      M.responseMoment s := by
    rw [dotProduct_comm, symmetric_pairing M.B_pos.isHermitian, dotProduct_comm]
    change _ ⬝ᵥ ((M.pencil s)⁻¹ *ᵥ _) = _
    rw [symmetric_pairing (M.pencil_pos hs).inv.isHermitian]
    simp only [responseMoment, inversePencil, ← Matrix.mulVec_mulVec]
  rw [hpair]
  ring

/-- Exact logarithmic-energy identity, with the derivative interpreted analytically. -/
theorem logarithmicEnergy_identity {s : ℝ} (hs : 0 < s) :
    s * deriv M.determinantRatio s / M.determinantRatio s =
      M.boundaryCorrection s + s / 2 * deriv (fun t => Real.log (M.inverseEnergy t)) s := by
  have he := M.inverseEnergy_pos hs
  have hd := M.determinantRatio_pos hs
  have hlog := (M.hasDerivAt_inverseEnergy hs).log he.ne'
  rw [hlog.deriv, boundaryCorrection, M.boundaryNumerator_eq hs]
  have heq : M.inverseEnergy s = M.determinantRatio s ^ 2 * M.responseEnergy s :=
    M.inverseEnergy_eq hs
  rw [heq]
  field_simp [hd.ne', (M.responseEnergy_pos hs).ne']
  ring

lemma inversePencil_boundaryVector_ne_zero {s : ℝ} (hs : 0 < s) :
    M.inversePencil s *ᵥ M.boundaryVector s ≠ 0 := by
  intro h
  have h' := congrArg (fun v => M.pencil s *ᵥ v) h
  apply M.boundaryVector_ne_zero hs
  simpa [inversePencil, mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (M.pencil_pos hs).det_pos.ne')] using h'

theorem boundaryCorrection_pos {s : ℝ} (hs : 0 < s) : 0 < M.boundaryCorrection s := by
  apply div_pos _ (M.inverseEnergy_pos hs)
  apply mul_pos hs
  simpa [inversePencil] using (M.pencil_pos hs).inv.dotProduct_mulVec_pos (M.boundaryVector_ne_zero hs)

/-- Algebraic inverse-order estimate, proved without commuting positive matrices. -/
theorem boundaryCorrection_lt_one {s : ℝ} (hs : 0 < s) : M.boundaryCorrection s < 1 := by
  let y := M.inversePencil s *ᵥ M.boundaryVector s
  have hy : y ≠ 0 := M.inversePencil_boundaryVector_ne_zero hs
  have hB : IsUnit M.B.det := isUnit_iff_ne_zero.mpr M.B_pos.det_pos.ne'
  have hP : IsUnit (M.pencil s).det := isUnit_iff_ne_zero.mpr (M.pencil_pos hs).det_pos.ne'
  have hby : M.boundaryVector s = M.K *ᵥ y + s • (M.B *ᵥ y) := by
    have h : M.pencil s *ᵥ y = M.boundaryVector s := by
      simp [y, inversePencil, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP]
    rw [← h]
    simp only [pencil, Matrix.add_mulVec, Matrix.smul_mulVec]
  have hinvb : M.B⁻¹ *ᵥ (M.B *ᵥ y) = y := by
    simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB]
  have hcross : (M.B *ᵥ y) ⬝ᵥ (M.B⁻¹ *ᵥ (M.K *ᵥ y)) = y ⬝ᵥ (M.K *ᵥ y) := by
    rw [symmetric_pairing M.B_pos.inv.isHermitian, hinvb, dotProduct_comm]
  have hcross' : (M.K *ᵥ y) ⬝ᵥ y = y ⬝ᵥ (M.K *ᵥ y) := dotProduct_comm _ _
  have hbpair : (M.B *ᵥ y) ⬝ᵥ y = y ⬝ᵥ (M.B *ᵥ y) := dotProduct_comm _ _
  have henergy : M.inverseEnergy s =
      (M.K *ᵥ y) ⬝ᵥ (M.B⁻¹ *ᵥ (M.K *ᵥ y)) +
      2 * s * (y ⬝ᵥ (M.K *ᵥ y)) + s^2 * (y ⬝ᵥ (M.B *ᵥ y)) := by
    rw [inverseEnergy, hby]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, hinvb, hcross, hcross', hbpair, smul_eq_mul]
    ring
  have hnum : M.boundaryVector s ⬝ᵥ (M.inversePencil s *ᵥ M.boundaryVector s) =
      y ⬝ᵥ (M.K *ᵥ y) + s * (y ⬝ᵥ (M.B *ᵥ y)) := by
    change M.boundaryVector s ⬝ᵥ y = _
    rw [hby, add_dotProduct, smul_dotProduct, hcross', hbpair]
    rfl
  have hnonneg : 0 ≤ (M.K *ᵥ y) ⬝ᵥ (M.B⁻¹ *ᵥ (M.K *ᵥ y)) := by
    simpa using M.B_pos.inv.posSemidef.dotProduct_mulVec_nonneg (M.K *ᵥ y)
  have hpositive : 0 < y ⬝ᵥ (M.K *ᵥ y) := by
    simpa using M.K_pos.dotProduct_mulVec_pos hy
  rw [boundaryCorrection, div_lt_one (M.inverseEnergy_pos hs), henergy, hnum]
  nlinarith [mul_pos hs hpositive]

/-- First and second ordinary derivatives of the scalar boundary response. -/
theorem boundaryResponse_deriv {s : ℝ} (hs : 0 < s) :
    deriv M.boundaryResponse s = -M.responseEnergy s :=
  (M.hasDerivAt_boundaryResponse hs).deriv

theorem hasDerivAt_boundaryResponse_deriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt (deriv M.boundaryResponse) (2 * M.responseMoment s) s := by
  have hd := (M.hasDerivAt_responseEnergy hs).neg
  have heq : deriv M.boundaryResponse =ᶠ[nhds s] (fun t => -M.responseEnergy t) := by
    filter_upwards [eventually_gt_nhds hs] with t ht
    exact M.boundaryResponse_deriv ht
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert! hd using 1
  ring

/-- The boundary correction is the logarithmic derivative of the response energy. -/
theorem boundaryCorrection_second_derivative {s : ℝ} (hs : 0 < s) :
    M.boundaryCorrection s =
      s * deriv (deriv M.boundaryResponse) s / (2 * (-deriv M.boundaryResponse s)) := by
  rw [boundaryCorrection, M.boundaryNumerator_eq hs, M.inverseEnergy_eq hs,
    (M.hasDerivAt_boundaryResponse_deriv hs).deriv, M.boundaryResponse_deriv hs]
  change s * (M.determinantRatio s ^ 2 * M.responseMoment s) /
      (M.determinantRatio s ^ 2 * M.responseEnergy s) = _
  field_simp [(M.determinantRatio_pos hs).ne', (M.responseEnergy_pos hs).ne']

end InverseEnergyData
end Riemann.CCM

