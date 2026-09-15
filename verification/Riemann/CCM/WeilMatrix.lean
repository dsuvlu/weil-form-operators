import Riemann.CCM.FourierSection

/-! The real divided-difference matrix of CCM Lemma 5.1 and its exact native
rank-two displacement. Diagonal and odd off-diagonal data remain independent. -/

noncomputable section
open scoped InnerProductSpace BigOperators

namespace Riemann.CCM.Native

structure Coefficients (N : ℕ) where
  diagonal : Index N → ℝ
  beta : Index N → ℝ
  diagonal_even : ∀ i, diagonal i.rev = diagonal i
  beta_odd : ∀ i, beta i.rev = -beta i

variable {N : ℕ}

def weilMatrix (C : Coefficients N) : Matrix (Index N) (Index N) ℂ := fun i j =>
  if i = j then (C.diagonal i : ℂ)
  else (((C.beta i - C.beta j) / ((mode i : ℝ) - mode j) : ℝ) : ℂ)

theorem mode_difference_ne_zero {i j : Index N} (h : i ≠ j) :
    (mode i : ℝ) - mode j ≠ 0 := by
  intro hz
  have hh : mode i = mode j := by exact_mod_cast sub_eq_zero.mp hz
  exact h (mode_injective N hh)

theorem weilMatrix_symmetric (C : Coefficients N) (i j : Index N) :
    weilMatrix C j i = weilMatrix C i j := by
  by_cases h : i = j
  · subst j; rfl
  · simp only [weilMatrix, if_neg h, if_neg (Ne.symm h)]
    congr 1
    field_simp [mode_difference_ne_zero h, mode_difference_ne_zero (Ne.symm h)]
    ring

theorem weilMatrix_hermitian (C : Coefficients N) : (weilMatrix C).IsHermitian := by
  ext i j
  change (starRingEnd ℂ) (weilMatrix C j i) = weilMatrix C i j
  rw [weilMatrix_symmetric]
  unfold weilMatrix
  split_ifs <;> simp

theorem weilMatrix_reflect (C : Coefficients N) (i j : Index N) :
    weilMatrix C i.rev j.rev = weilMatrix C i j := by
  by_cases h : i = j
  · subst j; simp [weilMatrix, C.diagonal_even]
  · have hr : i.rev ≠ j.rev := fun hh => h (Fin.rev_injective hh)
    simp only [weilMatrix, if_neg h, if_neg hr, C.beta_odd, mode_rev, Int.cast_neg]
    congr 1
    rw [show -C.beta i - -C.beta j = -(C.beta i - C.beta j) by ring,
      show -(mode i : ℝ) - -(mode j : ℝ) = -((mode i : ℝ) - mode j) by ring,
      neg_div_neg_eq]

/-- The full native matrix, with no spectral or parity-block truncation. -/
def weilOperator (C : Coefficients N) : Section N →L[ℂ] Section N := ofMatrix (weilMatrix C)

@[simp] theorem weilOperator_apply (C : Coefficients N) (x : Section N) (i : Index N) :
    weilOperator C x i = ∑ j, weilMatrix C i j * x j := rfl

theorem weilOperator_selfadjoint (C : Coefficients N) :
    (weilOperator C).adjoint = weilOperator C :=
  ofMatrix_selfadjoint _ (weilMatrix_hermitian C)

set_option maxHeartbeats 800000 in
theorem reflection_weilOperator (C : Coefficients N) (x : Section N) :
    reflection N (weilOperator C x) = weilOperator C (reflection N x) := by
  ext i
  simp only [reflection_apply, weilOperator_apply]
  calc
    ∑ j, weilMatrix C i.rev j * x j =
      ∑ j : Index N, weilMatrix C i.rev j.rev * x j.rev :=
        (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Index N))
          (fun j => weilMatrix C i.rev j * x j)).symm
    _ = ∑ j : Index N, weilMatrix C i j * x j.rev := by
      apply Finset.sum_congr rfl
      intro j _
      rw [weilMatrix_reflect]

/-- The physical displacement column, with normalization 2π/√L. -/
def displacementVector (C : Coefficients N) (L : ℝ) : Section N :=
  WithLp.toLp 2 (fun i => ((2 * Real.pi / Real.sqrt L * C.beta i : ℝ) : ℂ))

@[simp] theorem displacementVector_apply (C : Coefficients N) (L : ℝ) (i : Index N) :
    displacementVector C L i = ((2 * Real.pi / Real.sqrt L * C.beta i : ℝ) : ℂ) := rfl

theorem displacementVector_odd (C : Coefficients N) (L : ℝ) :
    reflection N (displacementVector C L) = -displacementVector C L := by
  ext i
  simp [C.beta_odd]

theorem displacement_entry (C : Coefficients N) (L : ℝ) (i j : Index N) :
    ((frequency L i : ℂ) - frequency L j) * weilMatrix C i j =
      ((2 * Real.pi / L * (C.beta i - C.beta j) : ℝ) : ℂ) := by
  by_cases h : i = j
  · subst j; simp
  · have hcancel : ((mode i : ℝ) - mode j) *
        ((C.beta i - C.beta j) / ((mode i : ℝ) - mode j)) = C.beta i - C.beta j := by
      field_simp [mode_difference_ne_zero h]
    have hr : ((2 * Real.pi / L) * (mode i : ℝ) -
        (2 * Real.pi / L) * (mode j : ℝ)) *
        ((C.beta i - C.beta j) / ((mode i : ℝ) - mode j)) =
        (2 * Real.pi / L) * (C.beta i - C.beta j) := by
      calc
        _ = (2 * Real.pi / L) * (((mode i : ℝ) - mode j) *
          ((C.beta i - C.beta j) / ((mode i : ℝ) - mode j))) := by ring
        _ = _ := by rw [hcancel]
    simp only [weilMatrix, if_neg h, frequency]
    exact_mod_cast hr

theorem displacement_pairing (C : Coefficients N) (L : ℝ) (x : Section N) :
    ⟪displacementVector C L, x⟫_ℂ =
      ∑ i, ((2 * Real.pi / Real.sqrt L * C.beta i : ℝ) : ℂ) * x i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, displacementVector_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.conj_ofReal]
  ring

/-- The complete rank-two identity is proved from matrix entries, not assumed. -/
theorem native_displacement (C : Coefficients N) {L : ℝ} (hL : 0 < L)
    (x : Section N) :
    derivative L (weilOperator C x) - weilOperator C (derivative L x) =
      ⟪endpointVector N L, x⟫_ℂ • displacementVector C L -
        ⟪displacementVector C L, x⟫_ℂ • endpointVector N L := by
  have hs : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  have hsquare : (Real.sqrt L : ℂ) ^ 2 = (L : ℂ) := by
    exact_mod_cast Real.sq_sqrt hL.le
  ext i
  simp only [PiLp.sub_apply, derivative_apply, weilOperator_apply,
    PiLp.smul_apply, smul_eq_mul, displacementVector_apply, endpointVector_apply,
    endpoint_pairing, displacement_pairing]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hleft : ∑ j, ((frequency L i : ℂ) * (weilMatrix C i j * x j) -
      weilMatrix C i j * ((frequency L j : ℂ) * x j)) =
      ∑ j, ((2 * Real.pi / L * (C.beta i - C.beta j) : ℝ) : ℂ) * x j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← displacement_entry C L i j]
    ring
  rw [hleft]
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  have hsC : (Real.sqrt L : ℂ) ≠ 0 := by exact_mod_cast hs
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL
  rw [← hsquare]
  field_simp

end Riemann.CCM.Native
