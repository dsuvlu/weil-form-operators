import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Parameter derivatives in L¹

Dominated difference quotients give an actual derivative in the L¹ norm.
The representatives are supplied separately from their equivalence classes;
no simultaneous pointwise choice of representatives is assumed.
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped Topology

namespace Riemann.Basic

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An integrable local Lipschitz majorant and pointwise derivatives imply
an L¹-norm derivative. The representatives need agree only locally in the parameter. -/
theorem hasDerivAt_L1_of_dominated_lip
    (F : ℝ → α →₁[μ] E) (g : α →₁[μ] E)
    (f : ℝ → α → E) (g₀ : α → E) (x₀ : ℝ) (s : Set ℝ) (b : α → ℝ)
    (hs : s ∈ 𝓝 x₀)
    (hrep : ∀ x ∈ s, (F x : α → E) =ᵐ[μ] f x)
    (hgrep : (g : α → E) =ᵐ[μ] g₀)
    (hb : Integrable b μ) (hbpos : ∀ᵐ a ∂μ, 0 ≤ b a)
    (hlip : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖f x a - f x₀ a‖ ≤ b a * ‖x - x₀‖)
    (hdiff : ∀ᵐ a ∂μ, HasDerivAt (fun x => f x a) (g₀ a) x₀) :
    HasDerivAt F g x₀ := by
  have hx₀ : x₀ ∈ s := mem_of_mem_nhds hs
  have hfmeas (x : ℝ) (hx : x ∈ s) : AEStronglyMeasurable (f x) μ :=
    (Lp.aestronglyMeasurable (F x)).congr (hrep x hx)
  have hgint : Integrable g₀ μ := (L1.integrable_coeFn g).congr hgrep
  let q : ℝ → α → ℝ := fun x a =>
    ‖x - x₀‖⁻¹ * ‖f x a - f x₀ a - (x - x₀) • g₀ a‖
  have hq : Tendsto (fun x => ∫ a, q x a ∂μ) (𝓝 x₀) (𝓝 0) := by
    have hz : (∫ a, q x₀ a ∂μ) = 0 := by simp [q]
    rw [← hz]
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun a => b a + ‖g₀ a‖)
    · filter_upwards [hs] with x hx
      exact (((hfmeas x hx).sub (hfmeas x₀ hx₀)).sub
        (hgint.aestronglyMeasurable.const_smul (x - x₀))).norm.const_mul _
    · filter_upwards [hs] with x hx
      filter_upwards [hlip, hbpos] with a ha hba
      have hnn : 0 ≤ ‖x - x₀‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
      rw [Real.norm_of_nonneg (mul_nonneg hnn (norm_nonneg _))]
      calc
        q x a ≤ ‖x - x₀‖⁻¹ *
            (‖f x a - f x₀ a‖ + ‖(x - x₀) • g₀ a‖) := by
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hnn
        _ ≤ ‖x - x₀‖⁻¹ *
            (b a * ‖x - x₀‖ + ‖x - x₀‖ * ‖g₀ a‖) := by
          rw [norm_smul]
          gcongr
          exact ha x hx
        _ ≤ b a + ‖g₀ a‖ := by
          by_cases hzero : x = x₀
          · simp [hzero, add_nonneg hba (norm_nonneg _)]
          · have hn : ‖x - x₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzero)
            field_simp
            ring_nf
            exact le_rfl
    · exact hb.add hgint.norm
    · filter_upwards [hdiff] with a ha
      simpa [q] using (hasDerivAt_iff_tendsto.mp ha)
  have heq : ∀ᶠ x in 𝓝 x₀,
      ‖x - x₀‖⁻¹ * ‖F x - F x₀ - (x - x₀) • g‖ = ∫ a, q x a ∂μ := by
    filter_upwards [hs] with x hx
    rw [L1.norm_eq_integral_norm, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (F x - F x₀) ((x - x₀) • g),
      Lp.coeFn_sub (F x) (F x₀), Lp.coeFn_smul (x - x₀) g,
      hrep x hx, hrep x₀ hx₀, hgrep] with a hsub hsub' hsmul hfx hfx₀ hg
    simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsub' hsmul
    change ‖x - x₀‖⁻¹ * ‖(F x - F x₀ - (x - x₀) • g : α →₁[μ] E) a‖ = q x a
    rw [hsub, hsub', hsmul, hfx, hfx₀, hg]
  exact hasDerivAt_iff_tendsto.mpr (hq.congr' (heq.mono fun _ h => h.symm))

/-- A derivative majorant on a convex parameter neighborhood supplies the
local Lipschitz hypothesis of `hasDerivAt_L1_of_dominated_lip`. -/
theorem hasDerivAt_L1_of_dominated_deriv
    (F : ℝ → α →₁[μ] E) (g : α →₁[μ] E)
    (f f₁ : ℝ → α → E) (x₀ : ℝ) (s : Set ℝ) (b : α → ℝ)
    (hs : s ∈ 𝓝 x₀) (hconv : Convex ℝ s)
    (hrep : ∀ x ∈ s, (F x : α → E) =ᵐ[μ] f x)
    (hgrep : (g : α → E) =ᵐ[μ] f₁ x₀)
    (hb : Integrable b μ) (hbpos : ∀ᵐ a ∂μ, 0 ≤ b a)
    (hbound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖f₁ x a‖ ≤ b a)
    (hdiff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (fun x => f x a) (f₁ x a) x) :
    HasDerivAt F g x₀ := by
  have hx₀ : x₀ ∈ s := mem_of_mem_nhds hs
  apply hasDerivAt_L1_of_dominated_lip F g f (f₁ x₀) x₀ s b hs hrep hgrep hb hbpos
  · filter_upwards [hbound, hdiff, hbpos] with a hba hda hpos
    have hLip : LipschitzOnWith (Real.nnabs (b a)) (fun x => f x a) s := by
      apply hconv.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (fun x hx => (hda x hx).hasDerivWithinAt)
      intro x hx
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, abs_of_nonneg hpos]
      exact hba x hx
    intro x hx
    simpa [Real.coe_nnabs, abs_of_nonneg hpos] using hLip.norm_sub_le hx hx₀
  · exact hdiff.mono fun a ha => ha x₀ hx₀

end Riemann.Basic
