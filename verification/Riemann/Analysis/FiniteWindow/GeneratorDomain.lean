import Riemann.Analysis.FiniteWindow.GeneratorOperator
import Riemann.Analysis.FiniteWindow.ACPrimitive

/-! # Exact AC/L² domain of the directed generator

The derivative is positive and the zero trace is at the right endpoint.
`HasACDerivative` specifies representatives and their actual almost-everywhere
complex derivative, rather than merely naming a range space “Sobolev”.
-/
noncomputable section
open MeasureTheory Filter Set

namespace Riemann.Analysis.FiniteWindow

/-- An absorbing absolutely continuous representative with the given L² derivative. -/
def HasACDerivative (L : ℝ) (f g : Hilbert L) : Prop :=
  ∃ F : ℝ → ℂ,
    AbsolutelyContinuousOnInterval F 0 L ∧ F L = 0 ∧
    ((f : Ambient) : ℝ → ℂ) =ᵐ[volume] (Ico 0 L).indicator F ∧
    ∀ᵐ t, t ∈ uIcc 0 L → HasDerivAt F ((g : Ambient) t) t

/-- The actual right-semigroup generator has exactly the terminal AC/L² domain. -/
theorem hasGenerator_iff_hasACDerivative {L : ℝ} (hL : 0 ≤ L) (f g : Hilbert L) :
    HasGenerator L f g ↔ HasACDerivative L f g := by
  rw [hasGenerator_iff_eq_neg_volterra_zero L hL f g]
  constructor
  · intro he
    refine ⟨-terminalPrimitive L g, (terminalPrimitive_absolutelyContinuous L g).neg,
      by simp, ?_, ?_⟩
    · rw [he]
      filter_upwards [Lp.coeFn_neg (volterra L 0 g : Ambient), volterra_zero_ae hL g]
        with t ht hp
      have heNeg : ((-volterra L 0 g : Hilbert L) : Ambient) =
          -(volterra L 0 g : Ambient) := rfl
      rw [heNeg]
      rw [ht, Pi.neg_apply, hp]
      by_cases hmem : t ∈ Ico 0 L <;> simp [hmem]
    · filter_upwards [terminalPrimitive_ae_hasDerivAt L g] with t ht hmem
      simpa only [neg_neg] using (ht hmem).neg
  · rintro ⟨F, hF, hFL, hrep, hd⟩
    have he := ac_terminal_eq_neg_primitive g hF hFL hd
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hrep, volterra_zero_ae hL g,
      Lp.coeFn_neg (volterra L 0 g : Ambient)] with t hf hp hn
    have heNeg : ((-volterra L 0 g : Hilbert L) : Ambient) =
        -(volterra L 0 g : Ambient) := rfl
    rw [heNeg]
    rw [hf, hn, Pi.neg_apply, hp]
    by_cases ht : t ∈ Ico 0 L
    · simp only [indicator_of_mem ht]
      exact he t ((uIcc_of_le hL).symm ▸ ⟨ht.1, ht.2.le⟩)
    · simp [ht]

/-- The linear operator domain is exactly the absorbing AC/L² domain. -/
theorem mem_generatorDomain_iff_ac {L : ℝ} (hL : 0 ≤ L) (f : Hilbert L) :
    f ∈ generatorDomain L ↔ ∃ g, HasACDerivative L f g := by
  rw [mem_generatorDomain_iff L hL]
  exact exists_congr fun g => hasGenerator_iff_hasACDerivative hL f g

/-- The unbounded generator is the actual positive derivative of its AC representative. -/
theorem generator_hasACDerivative {L : ℝ} (hL : 0 ≤ L) (f : generatorDomain L) :
    HasACDerivative L f (generator L hL f) :=
  (hasGenerator_iff_hasACDerivative hL _ _).1 (generator_hasGenerator L hL f)

end Riemann.Analysis.FiniteWindow
