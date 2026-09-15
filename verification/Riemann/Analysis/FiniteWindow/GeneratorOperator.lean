import Riemann.Analysis.FiniteWindow.DirectedGenerator

/-! # The closed, densely defined terminal generator

The linear operator is constructed on the range of the injective zero-parameter
Volterra map. The proved strong-generator characterization identifies this range
with the maximal semigroup-generator domain. No bounded inverse on the whole
Hilbert space is introduced.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Riemann.Analysis.FiniteWindow

/-- The operator domain, subsequently identified with the strong generator graph. -/
def generatorDomain (L : ℝ) : Submodule ℂ (Hilbert L) := (volterra L 0).range

def generatorCoordinate (L : ℝ) (hL : 0 ≤ L) : Hilbert L ≃ₗ[ℂ] generatorDomain L :=
  LinearEquiv.ofInjective (volterra L 0).toLinearMap (volterra_injective L hL 0)

/-- The directed derivative as an unbounded linear operator on its domain. -/
def generator (L : ℝ) (hL : 0 ≤ L) : generatorDomain L →ₗ[ℂ] Hilbert L :=
  -(generatorCoordinate L hL).symm.toLinearMap

theorem mem_generatorDomain_iff (L : ℝ) (hL : 0 ≤ L) (f : Hilbert L) :
    f ∈ generatorDomain L ↔ ∃ g, HasGenerator L f g := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨-u, (hasGenerator_iff_eq_neg_volterra_zero L hL _ _).2 (by rw [map_neg, neg_neg]; rfl)⟩
  · rintro ⟨g, hg⟩
    refine ⟨-g, ?_⟩
    rw [map_neg]
    exact (hg.eq_neg_volterra_zero hL).symm

theorem generator_hasGenerator (L : ℝ) (hL : 0 ≤ L) (f : generatorDomain L) :
    HasGenerator L f (generator L hL f) := by
  apply (hasGenerator_iff_eq_neg_volterra_zero L hL _ _).2
  change (f : Hilbert L) = -(volterra L 0 (-(generatorCoordinate L hL).symm f))
  rw [map_neg, neg_neg]
  exact congrArg Subtype.val ((generatorCoordinate L hL).apply_symm_apply f).symm

theorem generator_eq_of_hasGenerator (L : ℝ) (hL : 0 ≤ L)
    (f : generatorDomain L) {g : Hilbert L} (hg : HasGenerator L f g) :
    generator L hL f = g := (generator_hasGenerator L hL f).unique hg

/-- Closedness of the maximal generator graph follows from its bounded Volterra equation. -/
theorem isClosed_generator_graph (L : ℝ) (hL : 0 ≤ L) :
    IsClosed {p : Hilbert L × Hilbert L | HasGenerator L p.1 p.2} := by
  have he : {p : Hilbert L × Hilbert L | HasGenerator L p.1 p.2} =
      {p | p.1 = -(volterra L 0 p.2)} := by
    ext p
    exact hasGenerator_iff_eq_neg_volterra_zero L hL p.1 p.2
  rw [he]
  exact isClosed_eq continuous_fst ((volterra L 0).continuous.comp continuous_snd).neg

/-- Every resolvent has exactly the same operator range. -/
theorem range_volterra_eq_generatorDomain (L : ℝ) (hL : 0 ≤ L) (b : ℂ) :
    (volterra L b).range = generatorDomain L := by
  ext f
  constructor
  · rintro ⟨u, rfl⟩
    exact (mem_generatorDomain_iff L hL _).2 ⟨_, hasGenerator_volterra L hL b u⟩
  · intro hf
    obtain ⟨g, hg⟩ := (mem_generatorDomain_iff L hL f).1 hf
    exact ⟨b • f - g, hg.volterra_inverse hL b⟩

/-- A resolvent with its codomain restricted to the actual generator domain. -/
def volterraToDomain (L : ℝ) (hL : 0 ≤ L) (b : ℂ) :
    Hilbert L →ₗ[ℂ] generatorDomain L :=
  (volterra L b).toLinearMap.codRestrict (generatorDomain L) fun f =>
    (mem_generatorDomain_iff L hL _).2 ⟨_, hasGenerator_volterra L hL b f⟩

@[simp] theorem volterraToDomain_coe (L : ℝ) (hL : 0 ≤ L) (b : ℂ) (f : Hilbert L) :
    (volterraToDomain L hL b f : Hilbert L) = volterra L b f := rfl

set_option maxHeartbeats 800000 in
/-- `(b-A)R_b = I`, with the domain inclusion visible in the type. -/
theorem generator_volterra_inverse (L : ℝ) (hL : 0 ≤ L) (b : ℂ) (f : Hilbert L) :
    b • volterra L b f - generator L hL (volterraToDomain L hL b f) = f := by
  have hg := generator_eq_of_hasGenerator L hL (volterraToDomain L hL b f)
    (hasGenerator_volterra L hL b f)
  rw [hg]
  module

/-- `R_b(b-A) = I` on the full actual generator domain. -/
theorem volterra_generator_inverse (L : ℝ) (hL : 0 ≤ L) (b : ℂ)
    (f : generatorDomain L) : volterra L b (b • (f : Hilbert L) - generator L hL f) = f :=
  (generator_hasGenerator L hL f).volterra_inverse hL b

/-- Each nonnegative shift commutes with every finite-window resolvent. -/
theorem shift_volterra_commute (L : ℝ) (hL : 0 ≤ L) (b : ℂ)
    {h : ℝ} (hh : 0 ≤ h) :
    (shift L h).comp (volterra L b) = (volterra L b).comp (shift L h) := by
  apply ContinuousLinearMap.ext
  intro f
  change shift L h (∫ y in 0..L, weightedOrbit L b f y) =
    ∫ y in 0..L, weightedOrbit L b (shift L h f) y
  rw [← (shift L h).intervalIntegral_comp_comm
    ((continuous_weightedOrbit L b f).intervalIntegrable 0 L)]
  apply intervalIntegral.integral_congr
  intro y hy
  have hy0 : 0 ≤ y := (uIcc_of_le hL ▸ hy).1
  have he : shift L h (shift L y f) = shift L y (shift L h f) := by
    have h₁ := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T f) (shift_add L hh hy0)
    have h₂ := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T f) (shift_add L hy0 hh)
    exact h₁.trans ((by simpa only [ContinuousLinearMap.comp_apply, add_comm] using h₂.symm))
  simpa only [weightedOrbit, map_smul] using congrArg
    (fun v : Hilbert L => Complex.exp (-b * (y : ℂ)) • v) he

/-- Every finite orbit integral is in the generator domain. -/
theorem orbitIntegral_eq_volterra_zero (L : ℝ) (hL : 0 ≤ L)
    (f : Hilbert L) {h : ℝ} (hh : 0 ≤ h) :
    (∫ y in 0..h, shift L y f) = volterra L 0 (f - shift L h f) := by
  have hs := shift_volterra L hL 0 f hh
  simp only [zero_mul, Complex.exp_zero, one_smul, weightedOrbit,
    neg_zero, zero_mul, Complex.exp_zero, one_smul] at hs
  have hc := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T f)
    (shift_volterra_commute L hL 0 hh)
  change shift L h (volterra L 0 f) = volterra L 0 (shift L h f) at hc
  rw [map_sub, ← hc, hs]
  module

/-- Density follows from actual strong orbit averages, without imposing a
periodic Fourier core on the absorbing generator. -/
theorem dense_generatorDomain (L : ℝ) (hL : 0 ≤ L) :
    Dense (generatorDomain L : Set (Hilbert L)) := by
  intro f
  have hc := continuous_shift_apply L f
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (μ := volume) 0 0)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have ht : Tendsto (fun h : ℝ => h⁻¹ • ∫ y in 0..h, shift L y f)
      (𝓝[>] 0) (𝓝 f) := by
    simpa only [zero_add, intervalIntegral.integral_same, sub_zero,
      shift_zero, ContinuousLinearMap.id_apply] using hd.tendsto_slope_zero_right
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [orbitIntegral_eq_volterra_zero L hL f (le_of_lt hh)]
  have hm : volterra L 0 (f - shift L h f) ∈ generatorDomain L :=
    ⟨f - shift L h f, rfl⟩
  exact ((generatorDomain L).restrictScalars ℝ).smul_mem (h⁻¹ : ℝ) hm

end Riemann.Analysis.FiniteWindow
