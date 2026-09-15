import Riemann.Capacity.FullDecomposition

/-! Explicit scalar formula for a positive rank-one block coupling. -/
noncomputable section
namespace Riemann.Capacity
open scoped InnerProductSpace
open Riemann.Basic Riemann.Basic.PositiveSchur InnerProductSpace
variable {U W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

namespace RankOneBlocks
variable (M : Data U W) (beta : U) (zeta : W)

def lowResponse : U := positiveInverse M.A M.A_positive beta
def highResponse : W := M.inverseC zeta
def theta : ℝ := (inner ℂ beta (lowResponse M beta)).re
def height : ℝ := (inner ℂ zeta (highResponse M zeta)).re
def denominator : ℝ := 1 - height M zeta * theta M beta

 theorem theta_real : ((theta M beta : ℝ) : ℂ) = inner ℂ beta (lowResponse M beta) :=
  positiveInverse_energy_real M.A M.A_positive
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp M.selfA) beta

 theorem height_real : ((height M zeta : ℝ) : ℂ) = inner ℂ zeta (highResponse M zeta) :=
  positiveInverse_energy_real M.C M.C_positive
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp M.selfC) zeta

 theorem theta_pos (hb : beta ≠ 0) : 0 < theta M beta :=
  positiveInverse_positive M.A M.A_positive
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp M.selfA) beta hb

 theorem short_lowResponse (hB : M.B = rankOne ℂ beta zeta) :
    M.short (lowResponse M beta) = (denominator M beta zeta : ℂ) • beta := by
  rw [M.short_apply, hB]
  simp only [lowResponse, positiveInverse_left, adjoint_rankOne, rankOne_apply, map_smul,
    smul_smul]
  change beta - (inner ℂ beta (lowResponse M beta) *
    inner ℂ zeta (highResponse M zeta)) • beta = _
  rw [← theta_real, ← height_real]
  simp only [denominator, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
    sub_smul, one_smul]
  rw [mul_comm]

 theorem denominator_pos (hB : M.B = rankOne ℂ beta zeta) (hb : beta ≠ 0) :
    0 < denominator M beta zeta := by
  have hu : lowResponse M beta ≠ 0 := by
    intro h
    have hi := positiveInverse_left M.A M.A_positive beta
    change M.A (lowResponse M beta) = beta at hi
    rw [h, map_zero] at hi
    exact hb hi.symm
  have hp := M.short_positive (lowResponse M beta) hu
  rw [short_lowResponse M beta zeta hB, inner_smul_right] at hp
  have ht : inner ℂ (lowResponse M beta) beta = (theta M beta : ℂ) := by
    rw [← inner_conj_symm, ← theta_real, Complex.conj_ofReal]
  rw [ht] at hp
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hp
  exact (mul_pos_iff_of_pos_right (theta_pos M beta hb)).mp hp

/-- The actual full inverse applied to the low coupling normal. -/
theorem inverse_normal (hB : M.B = rankOne ℂ beta zeta) (hb : beta ≠ 0) :
    positiveInverse (block M.A M.B M.C) M.positive (lowIncl beta) =
      WithLp.toLp 2 (((denominator M beta zeta : ℝ) : ℂ)⁻¹ • lowResponse M beta,
        -((theta M beta / denominator M beta zeta : ℝ) : ℂ) • highResponse M zeta) := by
  let d := denominator M beta zeta
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (denominator_pos M beta zeta hB hb))
  apply strictlyPositive_injective (block M.A M.B M.C) M.positive
  rw [positiveInverse_left, block_apply, hB]
  apply (WithLp.equiv 2 (U × W)).injective
  apply Prod.ext
  · change beta = M.A ((d:ℂ)⁻¹ • lowResponse M beta) +
      (rankOne ℂ beta zeta) (-((theta M beta / d : ℝ) : ℂ) • highResponse M zeta)
    simp only [map_smul, lowResponse, positiveInverse_left, rankOne_apply,
      smul_smul]
    change beta = (d:ℂ)⁻¹ • beta +
      (-((theta M beta / d : ℝ) : ℂ) * inner ℂ zeta (highResponse M zeta)) • beta
    rw [← height_real, ← add_smul]
    have hc : (d:ℂ)⁻¹ + -((theta M beta / d : ℝ) : ℂ) * (height M zeta : ℂ) = 1 := by
      simp only [Complex.ofReal_div]
      field_simp
      simp only [d, denominator, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul]
      ring
    rw [hc, one_smul]
  · change (0:W) = (rankOne ℂ beta zeta).adjoint ((d:ℂ)⁻¹ • lowResponse M beta) +
      M.C (-((theta M beta / d : ℝ) : ℂ) • highResponse M zeta)
    simp only [adjoint_rankOne, rankOne_apply, map_smul]
    rw [← theta_real, smul_smul]
    change (0:W) = ((d:ℂ)⁻¹ * (theta M beta : ℂ)) • zeta +
      -((theta M beta / d : ℝ) : ℂ) • M.C (M.inverseC zeta)
    rw [M.C_inverseC, ← add_smul]
    simp [div_eq_mul_inv, mul_comm]

 theorem inverse_normal_pairing (hB : M.B = rankOne ℂ beta zeta) (hb : beta ≠ 0) :
    (inner ℂ (lowIncl beta)
      (positiveInverse (block M.A M.B M.C) M.positive (lowIncl beta))).re =
      theta M beta / denominator M beta zeta := by
  rw [inverse_normal M beta zeta hB hb]
  simp only [lowIncl_apply, WithLp.prod_inner_apply, inner_zero_left, inner_smul_right]
  rw [← theta_real, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  ring_nf
  simp only [Complex.ofReal_re]

/-- The squared inverse denominator appears in the physical mass energy. -/
theorem inverse_normal_mass (hB : M.B = rankOne ℂ beta zeta) (hb : beta ≠ 0)
    (R : U →L[ℂ] U) (T : W →L[ℂ] W) :
    (inner ℂ (positiveInverse (block M.A M.B M.C) M.positive (lowIncl beta))
      (block R 0 T (positiveInverse (block M.A M.B M.C) M.positive (lowIncl beta)))).re =
    ((inner ℂ (lowResponse M beta) (R (lowResponse M beta))).re +
      (theta M beta)^2 * (inner ℂ (highResponse M zeta) (T (highResponse M zeta))).re) /
        (denominator M beta zeta)^2 := by
  rw [inverse_normal M beta zeta hB hb, ← Complex.ofReal_inv, ← Complex.ofReal_neg]
  rw [diagonal_apply]
  simp only [WithLp.prod_inner_apply, WithLp.toLp_fst, WithLp.toLp_snd,
    map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  ring

end RankOneBlocks

/-- Inverse of a diagonal block on a low normal, with positivity explicit. -/
theorem diagonal_inverse_low (A : U →L[ℂ] U) (C : W →L[ℂ] W)
    (hA : ∀ u, u ≠ 0 → 0 < (inner ℂ u (A u)).re)
    (hD : ∀ z : Space U W, z ≠ 0 → 0 < (inner ℂ z (block A 0 C z)).re) (beta : U) :
    positiveInverse (block A 0 C) hD (lowIncl beta) = lowIncl (positiveInverse A hA beta) := by
  apply strictlyPositive_injective (block A 0 C) hD
  rw [positiveInverse_left]
  simp

namespace GraphData
variable (P : GraphData U W)

/-- Explicit complementary resolvent energy h. -/
def couplingHeight (s : ℝ) (hs : 0 < s) : ℝ :=
  RankOneBlocks.height (P.pencilBlocks s hs) P.zeta.snd
/-- Explicit graph resolvent energy theta. -/
def couplingTheta (s : ℝ) (hs : 0 < s) : ℝ :=
  RankOneBlocks.theta (P.pencilBlocks s hs) P.betaGraph
/-- The mass-weighted high inverse energy (the negative height derivative). -/
def couplingHighMass (s : ℝ) (hs : 0 < s) : ℝ :=
  let u := RankOneBlocks.highResponse (P.pencilBlocks s hs) P.zeta.snd
  (inner ℂ u (P.metric.C u)).re
/-- The mass-weighted graph inverse energy (the negative theta derivative). -/
def couplingGraphMass (s : ℝ) (hs : 0 < s) : ℝ :=
  let u := RankOneBlocks.lowResponse (P.pencilBlocks s hs) P.betaGraph
  (inner ℂ u (P.graphMetric u)).re

 theorem coupling_denominator_pos (s : ℝ) (hs : 0 < s) :
    0 < 1 - P.couplingHeight s hs * P.couplingTheta s hs := by
  by_cases hb : P.betaGraph = 0
  · simp [couplingTheta, RankOneBlocks.theta, RankOneBlocks.lowResponse, hb]
  · exact RankOneBlocks.denominator_pos (P.pencilBlocks s hs) P.betaGraph P.zeta.snd rfl hb

/-- Explicit algebraic coupling, with the denominator proved positive.
Here h_B and theta_B are the positive mass-weighted inverse energies. -/
theorem coupling_formula (s : ℝ) (hs : 0 < s) :
    P.coupling s hs = s *
      (P.couplingHeight s hs * P.couplingGraphMass s hs +
        P.couplingTheta s hs * P.couplingHighMass s hs) /
      (1 - P.couplingHeight s hs * P.couplingTheta s hs) := by
  by_cases hb : P.betaGraph = 0
  · rw [P.coupling_eq_zero hb]
    simp [couplingTheta, couplingGraphMass, RankOneBlocks.theta,
      RankOneBlocks.lowResponse, hb]
  · let M := P.pencilBlocks s hs
    let b := P.betaGraph
    let z := P.zeta.snd
    let d := RankOneBlocks.denominator M b z
    let t := RankOneBlocks.theta M b
    let h := RankOneBlocks.height M z
    let tb := P.couplingGraphMass s hs
    let hb' := P.couplingHighMass s hs
    let eta : Space U W := lowIncl b
    have heta : eta ≠ 0 := by
      intro hz
      exact hb (congrArg (fun x : Space U W => x.fst) hz)
    have ht : 0 < t := RankOneBlocks.theta_pos M b hb
    have hd : 0 < d := RankOneBlocks.denominator_pos M b z rfl hb
    have hmass := RankOneBlocks.inverse_normal_mass M b z rfl hb P.graphMetric P.metric.C
    have hpair := RankOneBlocks.inverse_normal_pairing M b z rfl hb
    have hf := P.liftedPencil.softMean_hyperplane_difference s hs eta heta
    simp only [P.lifted_pencil, P.lifted_mass, eta] at hf
    dsimp only [M, pencilBlocks, b, z] at hmass hpair
    have hf' : P.liftedPencil.softMean s hs -
        (P.liftedPencil.compress (vectorHyperplane eta)).softMean s hs =
          s * ((tb + t^2 * hb') / d^2) / (t/d) := by
      rw [hmass, hpair] at hf
      exact hf
    have hinv : positiveInverse (P.decoupledPencil.pencil s)
        (P.decoupledPencil.pencil_positive s hs) eta =
        lowIncl (RankOneBlocks.lowResponse M b) := by
      have hi := diagonal_inverse_low (P.graphPencil.pencil s) (P.highPencil.pencil s)
        (P.graphPencil.pencil_positive s hs)
        (by simpa only [decoupledPencil, PositivePencil.orthogonalSum_pencil] using
          P.decoupledPencil.pencil_positive s hs) b
      simpa only [decoupledPencil, PositivePencil.orthogonalSum_pencil, eta,
        RankOneBlocks.lowResponse, M, pencilBlocks] using hi
    have hpdiag : (inner ℂ eta (positiveInverse (P.decoupledPencil.pencil s)
        (P.decoupledPencil.pencil_positive s hs) eta)).re = t := by
      rw [hinv]
      simp only [eta, lowIncl_apply, WithLp.prod_inner_apply, inner_zero_left, add_zero]
      rfl
    have hmdiag : (inner ℂ (positiveInverse (P.decoupledPencil.pencil s)
        (P.decoupledPencil.pencil_positive s hs) eta)
        (P.decoupledPencil.mass (positiveInverse (P.decoupledPencil.pencil s)
          (P.decoupledPencil.pencil_positive s hs) eta))).re = tb := by
      rw [hinv]
      change (inner ℂ (lowIncl (RankOneBlocks.lowResponse M b))
        (block P.graphMetric 0 P.metric.C (lowIncl (RankOneBlocks.lowResponse M b)))).re = tb
      simp only [lowIncl_apply, diagonal_apply, WithLp.prod_inner_apply]
      simp only [WithLp.toLp_fst, WithLp.toLp_snd, map_zero, inner_zero_left, add_zero]
      rfl
    have hdg := P.decoupledPencil.softMean_hyperplane_difference s hs eta heta
    rw [hmdiag, hpdiag] at hdg
    have hc : P.liftedPencil.compress (vectorHyperplane eta) =
        P.decoupledPencil.compress (vectorHyperplane eta) := by
      apply PositivePencil.ext P.common_coupling_hyperplane
      change physicalCompression _ P.liftedPencil.mass = physicalCompression _ P.decoupledPencil.mass
      rw [P.common_coupling_mass]
    rw [hc] at hf'
    have he : P.coupling s hs = s * ((tb+t^2*hb')/d^2)/(t/d) - s*tb/t := by
      rw [P.coupling_eq_lifted_difference]
      linarith
    rw [he]
    change s * ((tb+t^2*hb')/d^2)/(t/d) - s*tb/t = s*(h*tb+t*hb')/d
    have hddef : d = 1-h*t := rfl
    field_simp [ne_of_gt hd, ne_of_gt ht]
    rw [hddef]
    ring

end GraphData

end Riemann.Capacity
