import Riemann.CCM.BoundaryResolvent
import Riemann.CCM.FourierCharacteristic

/-! Exact finite boundary-response observations and their native Fourier ratios.
The nonreal anchor is legitimate by the proved finite real-zero theorem;
no lower bound uniform in a family is asserted.
-/

noncomputable section
open scoped InnerProductSpace BigOperators

namespace Riemann.CCM.FullSimpleEvenData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (M : FullSimpleEvenData E)

/-- Every linear observation retains the complete inverse-weighted boundary response. -/
theorem boundary_observation (ell : E →ₗ[ℂ] ℂ) :
    ell M.groundVector = ell M.boundarySection - ell (M.boundaryResponse : E) := by
  rw [M.groundVector_boundary_resolvent, map_sub]

/-- The signed dual response uses the physical adjoint of the actual inverse. -/
theorem boundary_observation_inner (k : E) :
    ⟪k, M.groundVector⟫_ℂ = ⟪k, M.boundarySection⟫_ℂ -
      ⟪M.boundaryInverse (M.boundaryProjection k), M.boundaryCoupling⟫_ℂ := by
  rw [M.groundVector_boundary_resolvent, inner_sub_right]
  congr 1
  have hp := M.boundaryHyperplane.inner_orthogonalProjectionOnto_eq_of_mem_right
    M.boundaryResponse k
  change ⟪M.boundaryProjection k, M.boundaryResponse⟫_ℂ =
    ⟪k, (M.boundaryResponse : E)⟫_ℂ at hp
  rw [← hp]
  exact (M.boundaryInverse_symmetric (M.boundaryProjection k) M.boundaryCoupling).symm

/-- Anchor normalization keeps the entire signed denominator; nonvanishing is explicit. -/
theorem normalized_boundary_observation (ell anchor : E →ₗ[ℂ] ℂ)
    (_ha : anchor M.groundVector ≠ 0) :
    ell M.groundVector / anchor M.groundVector =
      (ell M.boundarySection - ell (M.boundaryResponse : E)) /
      (anchor M.boundarySection - anchor (M.boundaryResponse : E)) := by
  rw [M.boundary_observation ell, M.boundary_observation anchor]

/-- The reconstructed denominator equals the actual anchor and is nonzero. -/
theorem boundary_observation_anchor_ne_zero (anchor : E →ₗ[ℂ] ℂ)
    (ha : anchor M.groundVector ≠ 0) :
    anchor M.boundarySection - anchor (M.boundaryResponse : E) ≠ 0 := by
  rw [← M.boundary_observation anchor]
  exact ha

end Riemann.CCM.FullSimpleEvenData

namespace Riemann.CCM.Native

variable {N : ℕ}

/-- The already-integrated finite Fourier observation as a linear functional of its coefficients. -/
def centeredFourierRow (L : ℝ) (z : ℂ) : Section N →ₗ[ℂ] ℂ where
  toFun v := centeredFourierObservation L v z
  map_add' v w := by
    simp [centeredFourierObservation, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' a v := by
    simp only [centeredFourierObservation, PiLp.smul_apply, smul_eq_mul,
      mul_assoc, ← Finset.mul_sum, RingHom.id_apply]
    ring

@[simp] theorem centeredFourierRow_apply (L : ℝ) (z : ℂ) (v : Section N) :
    centeredFourierRow L z v = centeredFourierObservation L v z := rfl

/-- Native finite Fourier response, in the original full admitted ground. -/
theorem native_fourier_boundary_response (C : Coefficients N) (L : ℝ)
    (hL : 0 < L) (A : GroundAdmission C) (z : ℂ) :
    centeredFourierObservation L (fullData C L hL A).groundVector z =
      centeredFourierObservation L (fullData C L hL A).boundarySection z -
      centeredFourierObservation L
        ((fullData C L hL A).boundaryResponse : Section N) z :=
  (fullData C L hL A).boundary_observation (centeredFourierRow L z)

/-- The fixed nonreal anchor is nonzero for the actual admitted native ground. -/
theorem native_fourier_anchor_ne_zero (C : Coefficients N) (L : ℝ)
    (hL : 0 < L) (A : GroundAdmission C) :
    centeredFourierObservation L (fullData C L hL A).groundVector (Complex.I / 4) ≠ 0 := by
  apply native_fourierObservation_nonreal C L hL A
  norm_num

/-- The normalized finite Fourier observation equals its signed boundary-resolvent ratio. -/
theorem native_normalized_fourier_boundary_ratio (C : Coefficients N) (L : ℝ)
    (hL : 0 < L) (A : GroundAdmission C) (z : ℂ) :
    centeredFourierObservation L (fullData C L hL A).groundVector z /
      centeredFourierObservation L (fullData C L hL A).groundVector (Complex.I / 4) =
    (centeredFourierObservation L (fullData C L hL A).boundarySection z -
      centeredFourierObservation L ((fullData C L hL A).boundaryResponse : Section N) z) /
    (centeredFourierObservation L (fullData C L hL A).boundarySection (Complex.I / 4) -
      centeredFourierObservation L ((fullData C L hL A).boundaryResponse : Section N) (Complex.I / 4)) :=
  (fullData C L hL A).normalized_boundary_observation (centeredFourierRow L z)
    (centeredFourierRow L (Complex.I / 4)) (native_fourier_anchor_ne_zero C L hL A)

/-- The signed response denominator is the same nonzero native Fourier anchor. -/
theorem native_boundary_ratio_denominator_ne_zero (C : Coefficients N) (L : ℝ)
    (hL : 0 < L) (A : GroundAdmission C) :
    centeredFourierObservation L (fullData C L hL A).boundarySection (Complex.I / 4) -
      centeredFourierObservation L ((fullData C L hL A).boundaryResponse : Section N) (Complex.I / 4) ≠ 0 :=
  (fullData C L hL A).boundary_observation_anchor_ne_zero
    (centeredFourierRow L (Complex.I / 4)) (native_fourier_anchor_ne_zero C L hL A)

end Riemann.CCM.Native
