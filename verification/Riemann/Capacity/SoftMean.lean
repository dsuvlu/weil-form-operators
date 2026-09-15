import Riemann.Basic.PositiveCompression

/-! Finite soft spectral means and the sharp hyperplane compression bound. -/
noncomputable section
open scoped InnerProductSpace
namespace Riemann.Capacity
open Riemann.Basic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Trace of the inverse against the physical mass operator. -/
def inverseMassTrace (H : E →L[ℂ] E)
    (hH : ∀ x, x ≠ 0 → 0 < (⟪x, H x⟫_ℂ).re) (B : E →L[ℂ] E) : ℂ :=
  LinearMap.trace ℂ E ((positiveInverse H hH).comp B).toLinearMap

/-- The rank-one defect formula after taking the trace against any mass. -/
theorem inverseMassTrace_hyperplane (H : E →L[ℂ] E)
    (hH : ∀ x, x ≠ 0 → 0 < (⟪x, H x⟫_ℂ).re) (hs : H.toLinearMap.IsSymmetric)
    (B : E →L[ℂ] E) (eta : E) (heta : eta ≠ 0) :
    inverseMassTrace H hH B -
      inverseMassTrace (physicalCompression (vectorHyperplane eta) H)
        (physicalCompression_positive _ H hH) (physicalCompression (vectorHyperplane eta) B) =
    ⟪positiveInverse H hH eta, B (positiveInverse H hH eta)⟫_ℂ /
      ⟪eta, positiveInverse H hH eta⟫_ℂ := by
  let V := vectorHyperplane eta
  let T := positiveInverse (physicalCompression V H) (physicalCompression_positive V H hH)
  have hc : LinearMap.trace ℂ E ((V.subtypeL.comp (T.comp V.orthogonalProjectionOnto)).comp B).toLinearMap =
      inverseMassTrace (physicalCompression V H) (physicalCompression_positive V H hH)
        (physicalCompression V B) := by
    change LinearMap.trace ℂ E (V.subtypeL.toLinearMap.comp
      ((T.comp (V.orthogonalProjectionOnto.comp B)).toLinearMap)) = _
    rw [LinearMap.trace_comp_comm']
    rfl
  rw [inverseMassTrace, ← hc, ← map_sub]
  have hd := congrArg (fun A : E →L[ℂ] E => LinearMap.trace ℂ E (A.comp B).toLinearMap)
    (hyperplane_inverse_defect H hH hs eta heta)
  simpa only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.toLinearMap_smul, map_smul,
    InnerProductSpace.rankOne_comp, InnerProductSpace.trace_rankOne,
    ContinuousLinearMap.adjoint_inner_left, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd

/-- A positive mass and a nonnegative energy form on a finite physical space. -/
structure PositivePencil (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  energy : E →L[ℂ] E
  mass : E →L[ℂ] E
  energy_symmetric : energy.toLinearMap.IsSymmetric
  mass_symmetric : mass.toLinearMap.IsSymmetric
  energy_nonneg : ∀ x, 0 ≤ (⟪x, energy x⟫_ℂ).re
  mass_positive : ∀ x, x ≠ 0 → 0 < (⟪x, mass x⟫_ℂ).re

namespace PositivePencil
variable (P : PositivePencil E)

def pencil (s : ℝ) : E →L[ℂ] E := P.energy + (s : ℂ) • P.mass

omit [FiniteDimensional ℂ E] in
@[simp] theorem pencil_apply (s : ℝ) (x : E) : P.pencil s x = P.energy x + (s : ℂ) • P.mass x := rfl

omit [FiniteDimensional ℂ E] in
theorem pencil_positive (s : ℝ) (hs : 0 < s) (x : E) (hx : x ≠ 0) :
    0 < (⟪x, P.pencil s x⟫_ℂ).re := by
  simp only [pencil_apply, inner_add_right, inner_smul_right, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact add_pos_of_nonneg_of_pos (P.energy_nonneg x) (mul_pos hs (P.mass_positive x hx))

omit [FiniteDimensional ℂ E] in
theorem pencil_symmetric (s : ℝ) : (P.pencil s).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪P.energy x + (s : ℂ) • P.mass x, y⟫_ℂ =
    ⟪x, P.energy y + (s : ℂ) • P.mass y⟫_ℂ
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  congr 1
  · exact P.energy_symmetric x y
  · congr 1
    exact P.mass_symmetric x y

/-- Physical restriction of both forms by compression. -/
def compress (V : Submodule ℂ E) : PositivePencil V where
  energy := physicalCompression V P.energy
  mass := physicalCompression V P.mass
  energy_symmetric := physicalCompression_symmetric V _ P.energy_symmetric
  mass_symmetric := physicalCompression_symmetric V _ P.mass_symmetric
  energy_nonneg x := by
    change 0 ≤ (⟪x, physicalCompression V P.energy x⟫_ℂ).re
    rw [physicalCompression_inner]
    exact P.energy_nonneg x
  mass_positive := physicalCompression_positive V _ P.mass_positive

@[simp] theorem compress_pencil (V : Submodule ℂ E) (s : ℝ) :
    (P.compress V).pencil s = physicalCompression V (P.pencil s) := by
  ext x
  simp [compress, pencil, physicalCompression]

/-- The finite soft spectral mean, with a constructed inverse. -/
def softMean (s : ℝ) (hs : 0 < s) : ℝ := s * (inverseMassTrace (P.pencil s) (P.pencil_positive s hs) P.mass).re

/-- Exact one-normal contribution lost by physical hyperplane compression. -/
theorem softMean_hyperplane_difference (s : ℝ) (hs : 0 < s) (eta : E) (heta : eta ≠ 0) :
    P.softMean s hs - (P.compress (vectorHyperplane eta)).softMean s hs =
    s * (⟪positiveInverse (P.pencil s) (P.pencil_positive s hs) eta,
      P.mass (positiveInverse (P.pencil s) (P.pencil_positive s hs) eta)⟫_ℂ).re /
      (⟪eta, positiveInverse (P.pencil s) (P.pencil_positive s hs) eta⟫_ℂ).re := by
  have h := inverseMassTrace_hyperplane (P.pencil s) (P.pencil_positive s hs)
    (P.pencil_symmetric s) P.mass eta heta
  have hr := congrArg Complex.re h
  rw [← positiveInverse_energy_real (P.pencil s) (P.pencil_positive s hs)
    (P.pencil_symmetric s) eta] at hr
  simp only [Complex.sub_re, Complex.div_ofReal_re] at hr
  simp only [softMean, compress_pencil]
  change s * (inverseMassTrace (P.pencil s) _ P.mass).re -
    s * (inverseMassTrace (physicalCompression (vectorHyperplane eta) (P.pencil s)) _
      (physicalCompression (vectorHyperplane eta) P.mass)).re = _
  rw [← mul_sub, hr]
  ring

/-- Codimension one removes between zero and one unit of soft spectral mean.
The energy is allowed to be singular, including on the hyperplane. -/
theorem softMean_hyperplane_bounds (s : ℝ) (hs : 0 < s) (eta : E) (heta : eta ≠ 0) :
    0 ≤ P.softMean s hs - (P.compress (vectorHyperplane eta)).softMean s hs ∧
    P.softMean s hs - (P.compress (vectorHyperplane eta)).softMean s hs ≤ 1 := by
  rw [P.softMean_hyperplane_difference s hs eta heta]
  let u := positiveInverse (P.pencil s) (P.pencil_positive s hs) eta
  let q := (⟪eta, u⟫_ℂ).re
  have hq : 0 < q := positiveInverse_positive _ _ (P.pencil_symmetric s) eta heta
  have hu : u ≠ 0 := by
    intro h
    have hi := positiveInverse_left (P.pencil s) (P.pencil_positive s hs) eta
    change P.pencil s u = eta at hi
    rw [h, map_zero] at hi
    exact heta hi.symm
  have hb := P.mass_positive u hu
  have he : q = (⟪u, P.energy u⟫_ℂ).re + s * (⟪u, P.mass u⟫_ℂ).re := by
    have hh := P.pencil_symmetric s u u
    change ⟪P.pencil s u, u⟫_ℂ = ⟪u, P.pencil s u⟫_ℂ at hh
    have hi : P.pencil s u = eta := positiveInverse_left _ _ eta
    rw [hi] at hh
    change (⟪eta, u⟫_ℂ).re = _
    rw [hh, ← hi]
    change (⟪u, P.energy u + (s : ℂ) • P.mass u⟫_ℂ).re = _
    simp only [inner_add_right, inner_smul_right, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change 0 ≤ s * (⟪u, P.mass u⟫_ℂ).re / q ∧ s * (⟪u, P.mass u⟫_ℂ).re / q ≤ 1
  constructor
  · exact le_of_lt (div_pos (mul_pos hs hb) hq)
  · apply (div_le_one hq).mpr
    linarith [P.energy_nonneg u]

/-- Strict energy positivity makes the one-normal contribution strictly below one. -/
theorem softMean_hyperplane_lt_one (hK : ∀ x, x ≠ 0 → 0 < (⟪x, P.energy x⟫_ℂ).re)
    (s : ℝ) (hs : 0 < s) (eta : E) (heta : eta ≠ 0) :
    P.softMean s hs - (P.compress (vectorHyperplane eta)).softMean s hs < 1 := by
  rw [P.softMean_hyperplane_difference s hs eta heta]
  let u := positiveInverse (P.pencil s) (P.pencil_positive s hs) eta
  have hq := positiveInverse_positive (P.pencil s) (P.pencil_positive s hs) (P.pencil_symmetric s) eta heta
  have hi : P.pencil s u = eta := positiveInverse_left _ _ eta
  have hu : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hi
    exact heta hi.symm
  have hh := P.pencil_symmetric s u u
  change ⟪P.pencil s u, u⟫_ℂ = ⟪u, P.pencil s u⟫_ℂ at hh
  have he : (⟪eta, u⟫_ℂ).re = (⟪u, P.energy u⟫_ℂ).re + s * (⟪u, P.mass u⟫_ℂ).re := by
    rw [← hi, hh]
    change (⟪u, P.energy u + (s : ℂ) • P.mass u⟫_ℂ).re = _
    simp only [inner_add_right, inner_smul_right, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply (div_lt_one hq).mpr
  change s * (⟪u, P.mass u⟫_ℂ).re < (⟪eta, u⟫_ℂ).re
  linarith [hK u hu]

omit [FiniteDimensional ℂ E] in
@[ext] theorem ext {P Q : PositivePencil E} (hK : P.energy = Q.energy) (hB : P.mass = Q.mass) : P = Q := by
  cases P
  cases Q
  cases hK
  cases hB
  rfl

/-- Common hyperplane compression gives the sharp one-unit comparison. -/
theorem softMean_common_hyperplane (Q : PositivePencil E) (eta : E) (heta : eta ≠ 0)
    (hK : physicalCompression (vectorHyperplane eta) P.energy =
      physicalCompression (vectorHyperplane eta) Q.energy)
    (hB : P.mass = Q.mass) (s : ℝ) (hs : 0 < s) :
    |P.softMean s hs - Q.softMean s hs| ≤ 1 := by
  have hc : P.compress (vectorHyperplane eta) = Q.compress (vectorHyperplane eta) := by
    apply PositivePencil.ext hK
    change physicalCompression _ P.mass = physicalCompression _ Q.mass
    rw [hB]
  have hp := P.softMean_hyperplane_bounds s hs eta heta
  have hq := Q.softMean_hyperplane_bounds s hs eta heta
  rw [hc] at hp
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end PositivePencil
end Riemann.Capacity
