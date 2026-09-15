import Riemann.CCM.PositiveOddCapacity

/-! Actual native odd Fourier cutoffs and their positive structured pencils. -/
noncomputable section
open scoped InnerProductSpace
namespace Riemann.CCM.Native
open Riemann.Capacity
variable {N : ℕ}

/-- Native odd high carrier: the Fourier coefficients at |n|≤J vanish.
Taking J=0 retains the full odd carrier; J≥N gives the empty high carrier. -/
def oddHighSection (N J : ℕ) : Submodule ℂ (Section N) where
  carrier := {x | reflection N x = -x ∧ ∀ i, (mode i).natAbs ≤ J → x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    constructor
    · rw [map_add, hx.1, hy.1, neg_add]
    · intro i hi
      simp [hx.2 i hi, hy.2 i hi]
  smul_mem' := by
    intro a x hx
    constructor
    · rw [map_smul, hx.1, smul_neg]
    · intro i hi
      simp [hx.2 i hi]

/-- The physical inclusion of the native high cutoff. -/
def oddHighInclusion (N J : ℕ) : oddHighSection N J →L[ℂ] Section N :=
  (oddHighSection N J).subtypeL

theorem oddHighInclusion_injective (N J : ℕ) : Function.Injective (oddHighInclusion N J) :=
  Subtype.val_injective

theorem oddHighInclusion_parity (N J : ℕ) (x : oddHighSection N J) :
    reflection N (oddHighInclusion N J x) = -oddHighInclusion N J x := x.property.1

def oddHighProjection (N J : ℕ) : Section N →L[ℂ] oddHighSection N J :=
  ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := oddHighSection N J) (F := Section N) (oddHighInclusion N J)

/-- The diagonal squared physical derivative preserves every native cutoff. -/
theorem squaredDerivative_mem_oddHigh (L : ℝ) (J : ℕ) (x : oddHighSection N J) :
    derivative L (derivative L (x : Section N)) ∈ oddHighSection N J := by
  constructor
  · rw [reflection_derivative, reflection_derivative, x.property.1, map_neg, map_neg, neg_neg, map_neg]
  · intro i hi
    simp [x.property.2 i hi]

def oddHighFree (L : ℝ) (J : ℕ) : oddHighSection N J →L[ℂ] oddHighSection N J :=
  ((derivative L).comp ((derivative L).comp (oddHighInclusion N J))).codRestrict
    (oddHighSection N J) (squaredDerivative_mem_oddHigh L J)

@[simp] theorem oddHighFree_coe (L : ℝ) (J : ℕ) (x : oddHighSection N J) :
    ((oddHighFree L J x : oddHighSection N J) : Section N) = derivative L (derivative L x) := rfl

/-- Actual shifted finite Weil form, at its admitted full eigenvalue. -/
def nativeShifted (C : Coefficients N) (A : GroundAdmission C) : Section N →L[ℂ] Section N :=
  weilOperator C - (A.e₀ : ℂ) • ContinuousLinearMap.id ℂ (Section N)

def nativeHighMass (C : Coefficients N) (A : GroundAdmission C) (J : ℕ) :
    oddHighSection N J →L[ℂ] oddHighSection N J :=
  columnEnergy (F := oddHighSection N J) (nativeShifted C A) (oddHighInclusion N J)

def nativeHighEnergy (C : Coefficients N) (L : ℝ) (A : GroundAdmission C) (J : ℕ) :
    oddHighSection N J →L[ℂ] oddHighSection N J :=
  columnEnergy (F := oddHighSection N J) (nativeShifted C A) ((derivative L).comp (oddHighInclusion N J))

theorem nativeHighMass_positive (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (x : oddHighSection N J) (hx : x ≠ 0) :
    0 < (⟪x, nativeHighMass C A J x⟫_ℂ).re := by
  rw [nativeHighMass, columnEnergy_inner]
  exact (fullData C L hL A).odd_shifted_positive x.property.1
    (fun h => hx (Subtype.ext h))

theorem nativeHigh_energy_positive (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (x : oddHighSection N J) (hx : x ≠ 0) :
    0 < (⟪x, nativeHighEnergy C L A J x⟫_ℂ).re := by
  rw [nativeHighEnergy, columnEnergy_inner]
  exact (fullData C L hL A).odd_differentiated_positive x.property.1
    (fun h => hx (Subtype.ext h))

/-- Native high rank-one identity, derived from the full CCM displacement. -/
theorem nativeHigh_displacement (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) :
    nativeHighEnergy C L A J = (nativeHighMass C A J).comp (oddHighFree L J) +
      InnerProductSpace.rankOne ℂ
        (oddHighProjection N J (displacementVector C L))
        (oddHighProjection N J (derivative L (endpointVector N L))) := by
  have h := (fullData C L hL A).oddColumn_displacement (E := Section N) (F := oddHighSection N J)
    (oddHighInclusion N J) (by
      intro x
      change reflection N (oddHighInclusion N J x) = -oddHighInclusion N J x
      exact x.property.1) (oddHighFree L J)
    (by
      intro x
      change derivative L (derivative L (oddHighInclusion N J x)) = oddHighInclusion N J (oddHighFree L J x)
      rfl)
  convert! h using 1

/-- Real scalar shifting preserves the native Hermitian form. -/
theorem nativeShifted_adjoint (C : Coefficients N) (A : GroundAdmission C) :
    (nativeShifted C A).adjoint = nativeShifted C A := by
  simp only [nativeShifted, map_sub, map_smulₛₗ]
  simp only [weilOperator_selfadjoint, ContinuousLinearMap.adjoint_id, Complex.conj_ofReal]

theorem nativeHighMass_symmetric (C : Coefficients N) (A : GroundAdmission C) (J : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := oddHighSection N J) (nativeHighMass C A J).toLinearMap := by
  unfold nativeHighMass
  apply columnEnergy_symmetric
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric (𝕜 := ℂ) (E := Section N) (A := nativeShifted C A)).mp (nativeShifted_adjoint C A)

theorem nativeHighEnergy_symmetric (C : Coefficients N) (L : ℝ) (A : GroundAdmission C) (J : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := oddHighSection N J) (nativeHighEnergy C L A J).toLinearMap := by
  unfold nativeHighEnergy
  apply columnEnergy_symmetric
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric (𝕜 := ℂ) (E := Section N) (A := nativeShifted C A)).mp (nativeShifted_adjoint C A)

/-- The actual positive high pencil; all positivity is derived from full admission. -/
def nativeHighPencil (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) : PositivePencil (oddHighSection N J) where
  energy := nativeHighEnergy C L A J
  mass := nativeHighMass C A J
  energy_symmetric := nativeHighEnergy_symmetric C L A J
  mass_symmetric := nativeHighMass_symmetric C A J
  energy_nonneg x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (nativeHigh_energy_positive C L hL A J x hx).le
  mass_positive := nativeHighMass_positive C L hL A J

end Riemann.CCM.Native
