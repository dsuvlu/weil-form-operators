import Riemann.CCM.CharacteristicSlope
import Riemann.CCM.NativeInverseEnergy
import Riemann.CCM.InverseEnergyCharacteristic

/-! The retained positive Fourier modes are exactly the free odd-pencil mean. -/
noncomputable section
open scoped BigOperators
namespace Riemann.CCM.Native
variable {N J : ℕ}

/-- The nonzero positive modes of the full odd carrier, enumerated without duplication. -/
def fullHighIndexEquiv (N : ℕ) : Fin N ≃ HighIndex N 0 where
  toFun j := ⟨⟨j.val+1, by have := j.isLt; omega⟩, by exact Nat.succ_pos _⟩
  invFun j := ⟨j.val.val-1, by have := j.val.isLt; have := j.property; omega⟩
  left_inv j := by ext; simp
  right_inv j := by ext; have := j.property; simp; omega

lemma native_freeMean_eq_positive_sum (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (hJN : J < N) (s : ℝ) (hs : 0 < s) :
    (nativeInverseEnergyData C L hL A J hJN).freeMean s =
      ∑ j : HighIndex N J, positiveLatticeWeight L s j.val.val := by
  let M := nativeInverseEnergyData C L hL A J hJN
  have hp : M.freePencil s = Matrix.diagonal (fun j => highFrequency L j ^ 2 + s) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [M, InverseEnergyData.freePencil, nativeInverseEnergyData, highRealFree]
    · simp [M, InverseEnergyData.freePencil, nativeInverseEnergyData, highRealFree, h]
  change s * Matrix.trace ((M.freePencil s)⁻¹) = _
  have hi : (M.freePencil s)⁻¹ = Matrix.diagonal (fun j => (highFrequency L j ^ 2 + s)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [hp, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [(add_pos_of_nonneg_of_pos (sq_nonneg (highFrequency L i)) hs).ne']
    · simp [hij]
  rw [hi]
  simp only [Matrix.trace_diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← div_eq_mul_inv]
  simp [positiveLatticeWeight, latticeFrequency, highFrequency, frequency, mode_highPositiveIndex]

lemma native_full_freeMean_eq_retained (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (hN : 0 < N) (s : ℝ) (hs : 0 < s) :
    (nativeInverseEnergyData C L hL A 0 hN).freeMean s =
      ∑ j ∈ Finset.range N, positiveLatticeWeight L s (j+1) := by
  rw [native_freeMean_eq_positive_sum C L hL A 0 hN s hs]
  rw [← (fullHighIndexEquiv N).sum_comp]
  change (∑ j : Fin N, positiveLatticeWeight L s (j.val+1)) = _
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => positiveLatticeWeight L s (j+1)) N

/-- Cancelling the retained free modes leaves precisely the omitted positive tail. -/
lemma native_freeMean_tail_cancellation (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (hN : 0 < N) {a : ℝ} (ha : 0 < a) :
    -(nativeInverseEnergyData C L hL A 0 hN).freeMean (a^2) + latticeTail L 0 (a^2) =
      latticeTail L N (a^2) := by
  rw [native_full_freeMean_eq_retained C L hL A hN (a^2) (sq_pos_of_pos ha)]
  linarith [latticeTail_split hL ha N]

/-- The existing native characteristic has the positive finite-pencil mean plus
exactly one term for each omitted pair of free modes. -/
theorem native_boundarySoftMean_eq_highMean_add_lattice (C : Coefficients N)
    (L : ℝ) (hL : 0 < L) (A : GroundAdmission C) (hN : 0 < N)
    {a : ℝ} (ha : 0 < a) :
    boundarySoftMean L (fullData C L hL A).groundVector a =
      (((nativeInverseEnergyData C L hL A 0 hN).highMean (a^2) +
        latticeTail L N (a^2) : ℝ) : ℂ) := by
  rw [boundarySoftMean_of_axis_factorization
    (nativeInverseEnergyData C L hL A 0 hN) hL ha _
    (native_boundaryCharacteristic_entire C L hL A)
    (fun t ht => native_characteristic_inverseEnergy C L hL A hN ht)]
  congr 1
  linarith [native_freeMean_tail_cancellation C L hL A hN ha]

end Riemann.CCM.Native
