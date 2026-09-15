import Riemann.CCM.FourierResolvent
import Riemann.CCM.FourierIntegral
import Riemann.CCM.NativeDeterminant

/-!
# The finite boundary characteristic

The determinant quotient is completed at its free poles by the Fourier
coefficient values. This definition never evaluates a singular matrix inverse
as if it were a resolvent.
-/
noncomputable section
open scoped InnerProductSpace BigOperators
open Matrix
open Riemann.Basic
namespace Riemann.CCM.Native
variable {N : ℕ}

/-- The whole free lattice, including modes outside the retained section. -/
def latticeFrequency (L : ℝ) (k : ℤ) : ℝ := (2 * Real.pi / L) * k

lemma frequency_eq_lattice (L : ℝ) (i : Index N) :
    frequency L i = latticeFrequency L (mode i) := rfl

lemma half_frequency {L : ℝ} (hL : 0 < L) (k : ℤ) :
    (L : ℂ) * (latticeFrequency L k : ℂ) / 2 = (k : ℂ) * (Real.pi : ℂ) := by
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  unfold latticeFrequency
  push_cast
  field_simp

lemma shifted_argument {L : ℝ} (hL : 0 < L) (z : ℂ) (i : Index N) :
    (L : ℂ) * (z - (frequency L i : ℂ)) / 2 =
      (L : ℂ) * z / 2 - (mode i : ℂ) * (Real.pi : ℂ) := by
  rw [← half_frequency hL (mode i)]
  change _ = (L : ℂ) * z / 2 - (L : ℂ) * (frequency L i : ℂ) / 2
  ring

lemma phase_sq (k : ℤ) : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
  rw [← mul_zpow]
  norm_num

/-- One Fourier coefficient's completed sine quotient, away from its free node. -/
lemma phased_sinc {L : ℝ} (hL : 0 < L) (z : ℂ) (i : Index N)
    (hz : z ≠ (frequency L i : ℂ)) :
    (-1 : ℂ) ^ mode i * complexSinc ((L : ℂ) * (z - (frequency L i : ℂ)) / 2) =
      2 * Complex.sin ((L : ℂ) * z / 2) / ((L : ℂ) * (z - (frequency L i : ℂ))) := by
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have ha : (L : ℂ) * (z - (frequency L i : ℂ)) / 2 ≠ 0 := by
    exact div_ne_zero (mul_ne_zero hLc (sub_ne_zero.mpr hz)) (by norm_num)
  rw [complexSinc_of_ne_zero ha]
  rw [shifted_argument hL z i, complex_sin_sub_int_mul_pi]
  rw [← mul_div_assoc, ← mul_assoc, phase_sq, one_mul]
  rw [← shifted_argument hL z i]
  field_simp

/-- The determinant ratio completed by its prescribed removable Fourier values. -/
def boundaryCharacteristic (L : ℝ) (v : Section N) (z : ℂ) : ℂ :=
  if h : ∃ i : Index N, z = (frequency L i : ℂ) then
    (-1 : ℂ) ^ mode h.choose * v h.choose / (Real.sqrt L : ℂ)
  else
    complexSinc ((L : ℂ) * z / 2) *
      ((boundaryMatrix L v - z • 1).det / (freeMatrix N L - z • 1).det)

lemma boundaryCharacteristic_off_lattice (L : ℝ) (v : Section N) (z : ℂ)
    (hz : ∀ i : Index N, z ≠ (frequency L i : ℂ)) :
    boundaryCharacteristic L v z = complexSinc ((L : ℂ) * z / 2) *
      ((boundaryMatrix L v - z • 1).det / (freeMatrix N L - z • 1).det) := by
  simp only [boundaryCharacteristic, not_exists.mpr hz, ↓reduceDIte]

lemma boundaryCharacteristic_at_mode {L : ℝ} (hL : 0 < L) (v : Section N) (j : Index N) :
    boundaryCharacteristic L v (frequency L j) = (-1 : ℂ)^mode j * v j / (Real.sqrt L : ℂ) := by
  have h : ∃ i : Index N, (frequency L j : ℂ) = (frequency L i : ℂ) := ⟨j, rfl⟩
  rw [boundaryCharacteristic, dif_pos h]
  have he : h.choose = j := by
    apply frequency_injective hL
    exact_mod_cast h.choose_spec.symm
  rw [he]

lemma sinc_at_lattice {L : ℝ} (hL : 0 < L) (k : ℤ) (i : Index N) :
    complexSinc ((L : ℂ) * ((latticeFrequency L k : ℂ) - (frequency L i : ℂ)) / 2) =
      if mode i = k then 1 else 0 := by
  rw [shifted_argument hL, half_frequency hL]
  rw [← sub_mul, ← Int.cast_sub, complexSinc_int_mul_pi]
  simp only [sub_eq_zero, eq_comm (a := k)]

lemma centeredFourierObservation_at_mode {L : ℝ} (hL : 0 < L)
    (v : Section N) (j : Index N) :
    centeredFourierObservation L v (frequency L j) =
      (Real.sqrt L : ℂ) * (v j * (-1 : ℂ)^mode j) := by
  unfold centeredFourierObservation
  congr 1
  change (∑ i, v i * (-1 : ℂ)^mode i *
    complexSinc ((L : ℂ) * ((latticeFrequency L (mode j) : ℂ) - (frequency L i : ℂ)) / 2)) = _
  simp only [sinc_at_lattice hL]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    have hm : mode i ≠ mode j := fun h => hij (mode_injective N h)
    simp [hm]
  · simp

lemma centeredFourierObservation_outside {L : ℝ} (hL : 0 < L)
    (v : Section N) (k : ℤ) (hk : ∀ i : Index N, mode i ≠ k) :
    centeredFourierObservation L v (latticeFrequency L k) = 0 := by
  simp [centeredFourierObservation, sinc_at_lattice hL, hk]

/-- The finite Fourier observation as a scalar free resolvent away from its poles. -/
theorem centeredFourierObservation_resolvent {L : ℝ} (hL : 0 < L)
    (v : Section N) (z : ℂ) (hz : ∀ i : Index N, z ≠ (frequency L i : ℂ)) :
    centeredFourierObservation L v z =
      -2 * Complex.sin ((L : ℂ) * z / 2) * (((Real.sqrt L)⁻¹ : ℂ) *
        ∑ i, v i / ((frequency L i : ℂ) - z)) := by
  have hs : (Real.sqrt L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL).ne'
  have hsq : (Real.sqrt L : ℂ)^2 = (L : ℂ) := by exact_mod_cast Real.sq_sqrt hL.le
  unfold centeredFourierObservation
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc (v i), phased_sinc hL z i (hz i)]
  have hf : (frequency L i : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz i).symm
  have hf' : z - (frequency L i : ℂ) ≠ 0 := sub_ne_zero.mpr (hz i)
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  field_simp
  rw [← hsq]
  ring

/-- The completed determinant is exactly the centered Fourier observation divided by L. -/
theorem boundaryCharacteristic_eq_fourier {L : ℝ} (hL : 0 < L) (v : Section N)
    (hv : ⟪endpointVector N L, v⟫_ℂ = 1) (z : ℂ) :
    boundaryCharacteristic L v z = centeredFourierObservation L v z / (L : ℂ) := by
  have hs : (Real.sqrt L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL).ne'
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hsq : (Real.sqrt L : ℂ)^2 = (L : ℂ) := by exact_mod_cast Real.sq_sqrt hL.le
  by_cases hz : ∃ i : Index N, z = (frequency L i : ℂ)
  · obtain ⟨j, rfl⟩ := hz
    rw [boundaryCharacteristic_at_mode hL, centeredFourierObservation_at_mode hL]
    field_simp
    rw [← hsq]
  · have hfree : ∀ i : Index N, z ≠ (frequency L i : ℂ) := not_exists.mp hz
    have hz0 : z ≠ 0 := by
      simpa [frequency] using hfree (zeroIndex N)
    have ha : (L : ℂ) * z / 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero hLc hz0) (by norm_num)
    rw [boundaryCharacteristic_off_lattice L v z hfree,
      boundaryMatrix_determinant_ratio L v hv z hfree,
      centeredFourierObservation_resolvent hL v z hfree,
      complexSinc_of_ne_zero ha]
    field_simp

/-- The completion has the entire-function topology, not merely an off-pole identity. -/
theorem differentiable_boundaryCharacteristic {L : ℝ} (hL : 0 < L) (v : Section N)
    (hv : ⟪endpointVector N L, v⟫_ℂ = 1) : Differentiable ℂ (boundaryCharacteristic L v) := by
  have he : boundaryCharacteristic L v = fun z => centeredFourierObservation L v z / (L : ℂ) :=
    funext (boundaryCharacteristic_eq_fourier hL v hv)
  rw [he]
  exact (differentiable_centeredFourierObservation L v).div_const _

/-- All other points on the free lattice have value zero. -/
theorem boundaryCharacteristic_outside {L : ℝ} (hL : 0 < L) (v : Section N)
    (hv : ⟪endpointVector N L, v⟫_ℂ = 1) (k : ℤ)
    (hk : ∀ i : Index N, mode i ≠ k) :
    boundaryCharacteristic L v (latticeFrequency L k) = 0 := by
  rw [boundaryCharacteristic_eq_fourier hL v hv,
    centeredFourierObservation_outside hL v k hk, zero_div]

/-- The entire native characteristic has no nonreal zeros. -/
theorem native_boundaryCharacteristic_nonreal (C : Coefficients N) (L : ℝ)
    (hL : 0 < L) (A : GroundAdmission C) {z : ℂ} (hz : z.im ≠ 0) :
    boundaryCharacteristic L (fullData C L hL A).groundVector z ≠ 0 := by
  have hfree : ∀ i : Index N, z ≠ (frequency L i : ℂ) :=
    (freeMatrix_det_ne_zero_iff L z).mp (freeMatrix_det_ne_zero_of_nonreal L hz)
  rw [boundaryCharacteristic_off_lattice L _ z hfree]
  apply mul_ne_zero
  · apply complexSinc_ne_zero_of_im_ne_zero
    have him : ((L : ℂ) * z / 2).im = L * z.im / 2 := by simp
    rw [him]
    exact div_ne_zero (mul_ne_zero hL.ne' hz) (by norm_num)
  · exact div_ne_zero (native_boundary_det_ne_zero C L hL A hz)
      (freeMatrix_det_ne_zero_of_nonreal L hz)

/-- The native characteristic equals the actual centered Fourier integral, with factor L. -/
theorem native_boundaryCharacteristic_eq_integral (C : Coefficients N) (L : ℝ)
    (hL : 0 < L) (A : GroundAdmission C) (z : ℂ) :
    boundaryCharacteristic L (fullData C L hL A).groundVector z =
      (∫ t in (0 : ℝ)..L, fourierFunction L (fullData C L hL A).groundVector t *
        Complex.exp (-Complex.I * z * ((t : ℂ) - (L : ℂ) / 2))) / (L : ℂ) := by
  rw [integral_fourierFunction_centered hL,
    boundaryCharacteristic_eq_fourier hL _ (fullData C L hL A).boundary_groundVector]

/-- The admitted native boundary characteristic is entire. -/
theorem native_boundaryCharacteristic_entire (C : Coefficients N) (L : ℝ)
    (hL : 0 < L) (A : GroundAdmission C) :
    Differentiable ℂ (boundaryCharacteristic L (fullData C L hL A).groundVector) :=
  differentiable_boundaryCharacteristic hL _ (fullData C L hL A).boundary_groundVector

/-- The transform itself has no nonreal zero. -/
theorem native_fourierObservation_nonreal (C : Coefficients N) (L : ℝ)
    (hL : 0 < L) (A : GroundAdmission C) {z : ℂ} (hz : z.im ≠ 0) :
    centeredFourierObservation L (fullData C L hL A).groundVector z ≠ 0 := by
  intro hzero
  have h := native_boundaryCharacteristic_nonreal C L hL A hz
  rw [boundaryCharacteristic_eq_fourier hL _ (fullData C L hL A).boundary_groundVector,
    hzero, zero_div] at h
  exact h rfl

end Riemann.CCM.Native
