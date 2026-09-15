import Riemann.CCM.BoundaryWeyl
import Riemann.Capacity.BoundaryCorrection

/-! Positive differentiated energy on the native odd carrier and its column pencils. -/
noncomputable section
open scoped InnerProductSpace
namespace Riemann.CCM.FullSimpleEvenData
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
variable (M : FullSimpleEvenData E)

/-- Every odd vector has zero endpoint. -/
theorem boundary_odd {x : E} (hx : M.reflection x = -x) : ⟪M.eta, x⟫_ℂ = 0 := by
  have h := M.reflection.adjoint_inner_right M.eta x
  rw [M.reflection_selfadjoint, M.eta_even, hx, inner_neg_right] at h
  have ht : (2 : ℂ) * ⟪M.eta, x⟫_ℂ = 0 := by linear_combination -h
  exact (mul_eq_zero.mp ht).resolve_left (by norm_num)

theorem odd_shifted_kernel {x : E} (hx : M.reflection x = -x) (hg : M.shifted x = 0) : x = 0 := by
  have he := M.kernel_even hg
  have ht : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp (he.symm.trans hx)
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

theorem shifted_odd {x : E} (hx : M.reflection x = -x) :
    M.reflection (M.shifted x) = -M.shifted x := by
  simp only [shifted_apply, map_sub, map_smul, M.reflection_H, hx, map_neg, smul_neg, sub_neg_eq_add, neg_sub]
  abel

theorem derivative_constant : M.D M.constant = 0 :=
  (M.constant_kernel M.constant).mpr ⟨1, (one_smul ℂ M.constant).symm⟩

/-- Differentiated odd energy has no radical. The displacement and bright
constant rule out an odd vector whose derivative lies on the actual ground line. -/
theorem odd_differentiated_kernel {x : E} (hx : M.reflection x = -x)
    (hg : M.shifted (M.D x) = 0) : x = 0 := by
  have hd : M.D (M.shifted x) = -⟪M.b, x⟫_ℂ • M.eta := by
    have h := M.shifted_displacement x
    rw [hg, M.boundary_odd hx, zero_smul, zero_sub, sub_zero] at h
    simpa only [neg_smul] using h
  have hpair := M.D.adjoint_inner_left (M.shifted x) M.constant
  rw [M.D_selfadjoint, M.derivative_constant, inner_zero_left, hd, inner_smul_right] at hpair
  have heta : ⟪M.constant, M.eta⟫_ℂ ≠ 0 := fun h => M.constant_bright (inner_eq_zero_symm.mp h)
  have hb : ⟪M.b, x⟫_ℂ = 0 := by
    have hz := (mul_eq_zero.mp hpair.symm).resolve_right heta
    exact neg_eq_zero.mp hz
  rw [hb, neg_zero, zero_smul] at hd
  obtain ⟨a, ha⟩ := (M.constant_kernel (M.shifted x)).mp hd
  have he := M.boundary_odd (M.shifted_odd hx)
  rw [ha, inner_smul_right] at he
  have ha0 := (mul_eq_zero.mp he).resolve_right M.constant_bright
  apply M.odd_shifted_kernel hx
  simpa [ha0] using ha

/-- Positive mass on every nonzero odd vector. -/
theorem odd_shifted_positive {x : E} (hx : M.reflection x = -x) (hne : x ≠ 0) :
    0 < (⟪x, M.shifted x⟫_ℂ).re :=
  Riemann.positive_energy_pos M.shifted M.shifted_positive
    (fun h => hne (M.odd_shifted_kernel hx h))

/-- Strict differentiated energy follows from the full simple-even CCM data. -/
theorem odd_differentiated_positive {x : E} (hx : M.reflection x = -x) (hne : x ≠ 0) :
    0 < (⟪M.D x, M.shifted (M.D x)⟫_ℂ).re :=
  Riemann.positive_energy_pos M.shifted M.shifted_positive
    (fun h => hne (M.odd_differentiated_kernel hx h))

/-- Native physical mass on an injective odd column family. -/
def oddColumnPencil (W : F →L[ℂ] E) (hW : Function.Injective W)
    (hodd : ∀ x, M.reflection (W x) = -W x) : Riemann.Capacity.PositivePencil F := by
  letI := M.finite_dimensional
  exact Riemann.Capacity.columnPencil M.shifted
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp M.shifted_selfadjoint)
    M.shifted_nonneg (M.D.comp W) (Riemann.Capacity.columnEnergy M.shifted W)
    (Riemann.Capacity.columnEnergy_symmetric M.shifted W
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp M.shifted_selfadjoint))
    (fun x hx => by
      rw [Riemann.Capacity.columnEnergy_inner]
      exact M.odd_shifted_positive (hodd x) (fun h => hx (hW (by simpa using h))))

/-- Strict energy of the native differentiated odd pencil. -/
theorem oddColumnPencil_energy_positive (W : F →L[ℂ] E) (hW : Function.Injective W)
    (hodd : ∀ x, M.reflection (W x) = -W x) (x : F) (hx : x ≠ 0) :
    0 < (⟪x, (M.oddColumnPencil W hW hodd).energy x⟫_ℂ).re := by
  letI := M.finite_dimensional
  change 0 < (⟪x, Riemann.Capacity.columnEnergy M.shifted (M.D.comp W) x⟫_ℂ).re
  rw [Riemann.Capacity.columnEnergy_inner]
  exact M.odd_differentiated_positive (hodd x) (fun h => hx (hW (by simpa using h)))

/-- Endpoint-corrected native pencil, with the same physical mass as the full one. -/
def oddCorrectedColumnPencil (W : F →L[ℂ] E) (hW : Function.Injective W)
    (hodd : ∀ x, M.reflection (W x) = -W x) (p : E) : Riemann.Capacity.PositivePencil F := by
  letI := M.finite_dimensional
  let P := M.oddColumnPencil W hW hodd
  exact Riemann.Capacity.columnPencil M.shifted
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp M.shifted_selfadjoint)
    M.shifted_nonneg
    (Riemann.Capacity.endpointCorrectedColumns (M.D.comp W) M.eta p)
    P.mass P.mass_symmetric P.mass_positive

/-- Native one-unit correction for every injective odd family and every section.
Endpoint-one is needed for endpoint cancellation, but not for this bound. -/
theorem oddColumn_softMean_boundaryCorrection (W : F →L[ℂ] E) (hW : Function.Injective W)
    (hodd : ∀ x, M.reflection (W x) = -W x) (p : E) (s : ℝ) (hs : 0 < s) :
    |(M.oddColumnPencil W hW hodd).softMean s hs -
      (M.oddCorrectedColumnPencil W hW hodd p).softMean s hs| ≤ 1 := by
  letI := M.finite_dimensional
  let P := M.oddColumnPencil W hW hodd
  exact Riemann.Capacity.softMean_endpointCorrection_le_one M.shifted
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp M.shifted_selfadjoint)
    M.shifted_nonneg (M.D.comp W) P.mass P.mass_symmetric P.mass_positive M.eta p s hs

/-- Squared derivative preserves an odd column space supplied in native Fourier
coordinates; its pulled-back pair has the exact rank-one displacement. -/
theorem oddColumn_displacement [FiniteDimensional ℂ E] (W : F →L[ℂ] E)
    (hodd : ∀ x, M.reflection (W x) = -W x) (A : F →L[ℂ] F)
    (hA : ∀ x, M.D (M.D (W x)) = W (A x)) :
    Riemann.Capacity.columnEnergy M.shifted (M.D.comp W) =
      (Riemann.Capacity.columnEnergy M.shifted W).comp A +
      InnerProductSpace.rankOne ℂ (W.adjoint M.b) (W.adjoint (M.D M.eta)) := by
  letI := M.finite_dimensional
  ext x
  have he : M.reflection (M.D (W x)) = M.D (W x) := by
    rw [M.reflection_D, hodd, map_neg, neg_neg]
  have hd := M.shifted_displacement (M.D (W x))
  rw [M.odd_inner_even he, zero_smul, sub_zero, hA] at hd
  have hsolve : M.D (M.shifted (M.D (W x))) =
      M.shifted (W (A x)) + ⟪M.eta, M.D (W x)⟫_ℂ • M.b := by
    exact (sub_eq_iff_eq_add.mp hd).trans (add_comm _ _)
  have hrow : ⟪W.adjoint (M.D M.eta), x⟫_ℂ = ⟪M.eta, M.D (W x)⟫_ℂ := by
    rw [W.adjoint_inner_left, ← M.D_selfadjoint, M.D.adjoint_inner_left, M.D_selfadjoint]
  change ((M.D.comp W).adjoint (M.shifted (M.D (W x)))) =
    W.adjoint (M.shifted (W (A x))) + ⟪W.adjoint (M.D M.eta), x⟫_ℂ • W.adjoint M.b
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, M.D_selfadjoint,
    hsolve, map_add, map_smul, hrow]

end Riemann.CCM.FullSimpleEvenData
