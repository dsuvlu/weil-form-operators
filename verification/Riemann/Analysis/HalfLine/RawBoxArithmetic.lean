import Riemann.Analysis.HalfLine.CompactBox
import Riemann.Analysis.HalfLine.RawBoxScalar
import Riemann.Analysis.HalfLine.RawEuler

/-! # Exact arithmetic values on the compact box representatives -/
noncomputable section
open MeasureTheory Set Filter Finset
namespace Riemann.Analysis.HalfLine

lemma rawWeight_inv_sqrt {n : ℕ} (hn : 0 < n) :
    rawWeight n = ((Real.sqrt n)⁻¹ : ℝ) := by
  unfold rawWeight
  have he : Real.exp (-Real.log n/2) = (Real.sqrt n)⁻¹ := by
    rw [show -Real.log n/2 = -(Real.log n/2) by ring,
      Real.exp_neg, Real.exp_half, Real.exp_log (by positivity : (0:ℝ)<n)]
  exact congrArg Complex.ofReal he

lemma mem_box_indices_iff (T t : ℝ) (n : ℕ) :
    n ∈ Finset.Icc ⌈max 1 (Real.exp (T-t))⌉₊ ⌊Real.exp (T+1-t)⌋₊ ↔
      0 < n ∧ Real.log n+t ∈ Set.Icc T (T+1) := by
  constructor
  · intro hn
    obtain ⟨hp,hq⟩ := Finset.mem_Icc.mp hn
    have hn1 : (1:ℝ) ≤ n := (le_max_left _ _).trans
      ((Nat.le_ceil _).trans (by exact_mod_cast hp))
    have hn0 : 0 < n := by exact_mod_cast (show (0:ℝ)<n by linarith)
    have hnR : (0:ℝ)<n := by positivity
    have ha : Real.exp (T-t) ≤ n := (le_max_right _ _).trans
      ((Nat.le_ceil _).trans (by exact_mod_cast hp))
    have hb : (n:ℝ) ≤ Real.exp (T+1-t) :=
      (by exact_mod_cast hq : (n:ℝ) ≤ ⌊Real.exp (T+1-t)⌋₊).trans
        (Nat.floor_le (Real.exp_pos _).le)
    have hl := (Real.le_log_iff_exp_le hnR).mpr ha
    have hu := (Real.log_le_iff_le_exp hnR).mpr hb
    exact ⟨hn0, by constructor <;> linarith⟩
  · rintro ⟨hn0, hl, hu⟩
    have hnR : (0:ℝ)<n := by positivity
    apply Finset.mem_Icc.mpr
    constructor
    · apply Nat.ceil_le.mpr
      apply max_le
      · exact_mod_cast hn0
      · exact (Real.le_log_iff_exp_le hnR).mp (by linarith)
    · apply Nat.le_floor
      exact (Real.log_le_iff_le_exp hnR).mp (by linarith)

lemma box_indices_subset_cutoff {T t : ℝ} (ht : 0 ≤ t) :
    Finset.Icc ⌈max 1 (Real.exp (T-t))⌉₊ ⌊Real.exp (T+1-t)⌋₊ ⊆
      Finset.Ioc 0 (FiniteWindow.primeCutoff (T+2)) := by
  intro n hn
  obtain ⟨hn0, hl, hu⟩ := (mem_box_indices_iff T t n).mp hn
  apply Finset.mem_Ioc.mpr
  refine ⟨hn0, ?_⟩
  have hnR : (0:ℝ)<n := by positivity
  have hlog : Real.log n ≤ T+2 := by linarith
  have hle := (Real.log_le_iff_le_exp hnR).mp hlog
  exact_mod_cast hle.trans (Nat.le_ceil (Real.exp (T+2)))

/-- The finite arithmetic sum on the closed box is the inclusive scalar sum. -/
theorem raw_box_sum (T t : ℝ) (ht : 0 ≤ t) :
    (∑ n ∈ Finset.Ioc 0 (FiniteWindow.primeCutoff (T+2)),
      rawWeight n * boxFunction T (Real.log n+t)) = (rawBoxScalar T t : ℂ) := by
  let S := Finset.Icc ⌈max 1 (Real.exp (T-t))⌉₊ ⌊Real.exp (T+1-t)⌋₊
  have hsub := box_indices_subset_cutoff (T := T) ht
  have hs : (∑ n ∈ Finset.Ioc 0 (FiniteWindow.primeCutoff (T+2)),
      rawWeight n * boxFunction T (Real.log n+t)) =
      ∑ n ∈ S, rawWeight n * boxFunction T (Real.log n+t) := by
    symm
    apply Finset.sum_subset hsub
    intro n hn hnS
    have hnot : Real.log n+t ∉ Set.Icc T (T+1) := by
      intro h
      exact hnS ((mem_box_indices_iff T t n).mpr ⟨(Finset.mem_Ioc.mp hn).1,h⟩)
    simp [boxFunction,hnot]
  rw [hs]
  simp only [rawBoxScalar, if_pos ht, Complex.ofReal_mul, Complex.ofReal_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn0,hm⟩ := (mem_box_indices_iff T t n).mp hn
  rw [rawWeight_inv_sqrt hn0, boxFunction, indicator_of_mem hm]
  ring

/-- Literal a.e. action of the raw Euler map on the constructed box. -/
theorem rawEuler_box_ae (T : ℝ) (hT : 0 ≤ T) :
    ((rawEuler (box T hT) : Ambient) : ℝ → ℂ) =ᵐ[volume]
      fun t => (rawBoxScalar T t : ℂ) := by
  rw [rawEuler_eq_partialSum (box T hT) (T+2) (boxVector_supported T hT)]
  have hall : ∀ᵐ t : ℝ, ∀ n : ℕ,
      (boxVector T hT : Ambient) (Real.log n+t) = boxFunction T (Real.log n+t) := by
    apply ae_all_iff.mpr
    intro n
    exact (measurePreserving_add_left volume (Real.log n)).quasiMeasurePreserving.ae
      (boxVector_ae T hT)
  filter_upwards [rawPartialSum_ae (FiniteWindow.primeCutoff (T+2)) (box T hT),hall]
    with t hp hb
  rw [hp]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht]
    calc
      _ = ∑ n ∈ Finset.Ioc 0 (FiniteWindow.primeCutoff (T+2)),
          rawWeight n * boxFunction T (Real.log n+t) := by
        apply Finset.sum_congr rfl
        intro n _
        change rawWeight n * (boxVector T hT : Ambient) (Real.log n+t) = _
        rw [hb n]
      _ = _ := raw_box_sum T t ht
  · simp [ht,rawBoxScalar]

end Riemann.Analysis.HalfLine
