import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Positive energies and metric-symmetric eigenvectors

The null space of a positive operator is exactly its zero-energy space.
A metric-symmetric operator that kills that null space has real eigenvalues.
These generic bounded-operator statements do not assert spectral convergence.
-/

open scoped InnerProductSpace

namespace Riemann

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Zero energy for a positive semidefinite operator is equivalent to its kernel. -/
theorem positive_energy_eq_zero_iff (G : E →L[ℂ] E) (hG : G.IsPositive) (x : E) :
    (⟪x, G x⟫_ℂ).re = 0 ↔ G x = 0 := by
  obtain ⟨S, hS, _, hSS⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
      hG.isSelfAdjoint hG.spectrumRestricts
  have hs : S.adjoint = S := hS.star_eq
  have energy : ⟪x, G x⟫_ℂ = ⟪S x, S x⟫_ℂ := by
    rw [← hSS]
    change ⟪x, S (S x)⟫_ℂ = _
    simpa only [hs] using S.adjoint_inner_right x (S x)
  constructor
  · intro hx
    have hn : ‖S x‖ ^ 2 = 0 := by
      simpa [energy, inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re] using hx
    have hz : S x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    rw [← hSS]
    change S (S x) = 0
    simp [hz]
  · intro hx
    simp [hx]

/-- Positive energy away from the null space; no coercivity constant is asserted. -/
theorem positive_energy_pos (G : E →L[ℂ] E) (hG : G.IsPositive)
    {x : E} (hx : G x ≠ 0) : 0 < (⟪x, G x⟫_ℂ).re := by
  exact lt_of_le_of_ne (hG.re_inner_nonneg_right x)
    (Ne.symm (fun h => hx ((positive_energy_eq_zero_iff G hG x).mp h)))

/-- The metric is positive definite on the physical orthogonal complement of its kernel. -/
theorem positive_energy_pos_on_kernel_orthogonal (G : E →L[ℂ] E)
    (hG : G.IsPositive) {x : E}
    (hx : x ∈ (LinearMap.ker G.toLinearMap)ᗮ) (hne : x ≠ 0) :
    0 < (⟪x, G x⟫_ℂ).re := by
  apply positive_energy_pos G hG
  intro hzero
  have hmem : x ∈ LinearMap.ker G.toLinearMap := hzero
  have hi := (Submodule.mem_orthogonal' _ x).mp hx x hmem
  exact hne (inner_self_eq_zero.mp hi)

/-- Weighted symmetry plus annihilation of the metric kernel forces real eigenvalues. -/
theorem metricSymmetric_eigenvalue_real
    (G B : E →L[ℂ] E) (hG : G.IsPositive)
    (hmetric : ∀ x y, ⟪B x, G y⟫_ℂ = ⟪x, G (B y)⟫_ℂ)
    (hnull : ∀ x, G x = 0 → B x = 0)
    {x : E} {z : ℂ} (hx : x ≠ 0) (heigen : B x = z • x) : z.im = 0 := by
  by_cases hz : z = 0
  · simp [hz]
  have hgx : G x ≠ 0 := by
    intro h
    have he : z • x = 0 := heigen.symm.trans (hnull x h)
    exact (smul_eq_zero.mp he).elim hz hx
  have henergy : ⟪x, G x⟫_ℂ ≠ 0 := by
    intro h
    have := positive_energy_pos G hG hgx
    simp [h] at this
  have heq := hmetric x x
  rw [heigen, map_smul, inner_smul_left, inner_smul_right] at heq
  exact Complex.conj_eq_iff_im.mp (mul_right_cancel₀ henergy heq)

end Riemann
