import Riemann.Analysis.HalfLine.FiniteSupport
import Riemann.Analysis.FiniteWindow.PrimeHilbert

/-! # Raw Euler synthesis on the dense compact-support domain

The map is defined by finite sums and proved independent of the support witness.
No unrestricted infinite sum or bounded extension is used in this definition.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace Riemann.Analysis.HalfLine

/-- The critical arithmetic coefficient at a positive integer. -/
def rawWeight (n : ℕ) : ℂ := (Real.exp (-Real.log n / 2) : ℂ)

theorem rawWeight_eq_complexExp (n : ℕ) :
    rawWeight n = Complex.exp (-((1 / 2 : ℝ) : ℂ) * (Real.log n : ℂ)) := by
  rw [rawWeight, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- A genuinely finite operator sum, used only with a sufficient physical cutoff. -/
def rawPartialSum (X : ℕ) : Hilbert →L[ℂ] Hilbert :=
  ∑ n ∈ Finset.Ioc 0 X, rawWeight n • shift (Real.log n)

theorem rawPartialSum_apply (X : ℕ) (f : Hilbert) :
    rawPartialSum X f = ∑ n ∈ Finset.Ioc 0 X, rawWeight n • shift (Real.log n) f := by
  simp [rawPartialSum]

theorem rawPartialSum_finiteInclusion (L : ℝ) (f : FiniteWindow.Hilbert L) :
    rawPartialSum (FiniteWindow.primeCutoff L) (finiteInclusion L f) =
      finiteInclusion L (FiniteWindow.primeOperator L (1/2) f) := by
  rw [rawPartialSum_apply, FiniteWindow.primeOperator_sum]
  simp only [sum_apply, smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := ne_of_gt (Finset.mem_Ioc.mp hn).1
  rw [rawWeight_eq_complexExp, shift_finiteInclusion]
  congr 2
  simp [FiniteWindow.primeShift, hn0, FiniteWindow.shift, Arithmetic.natLog]

/-- Every extra term after a physical support cutoff vanishes on that vector. -/
theorem rawPartialSum_stable (L : ℝ) (f : FiniteWindow.Hilbert L) {X : ℕ}
    (hX : FiniteWindow.primeCutoff L ≤ X) :
    rawPartialSum X (finiteInclusion L f) =
      rawPartialSum (FiniteWindow.primeCutoff L) (finiteInclusion L f) := by
  rw [rawPartialSum_apply, rawPartialSum_apply]
  symm
  apply Finset.sum_subset (Finset.Ioc_subset_Ioc_right hX)
  intro n hn hncut
  have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
  have hcut : FiniteWindow.primeCutoff L < n := by
    simpa only [Finset.mem_Ioc, hnpos, true_and, not_le] using hncut
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hlog : L ≤ Real.log n := (Real.le_log_iff_exp_le hnreal).mpr
    ((Nat.le_ceil (Real.exp L)).trans (by exact_mod_cast hcut.le))
  rw [shift_finiteInclusion_eq_zero L hlog, smul_zero]

/-- Any two valid support witnesses give the same arithmetic value. -/
theorem rawPartialSum_witness_independent {L M : ℝ}
    (f : FiniteWindow.Hilbert L) (g : FiniteWindow.Hilbert M)
    (heq : finiteInclusion L f = finiteInclusion M g) :
    rawPartialSum (FiniteWindow.primeCutoff L) (finiteInclusion L f) =
      rawPartialSum (FiniteWindow.primeCutoff M) (finiteInclusion M g) := by
  rw [← rawPartialSum_stable L f (le_max_left _ _), heq,
    rawPartialSum_stable M g (le_max_right _ _)]

private def supportWitness (f : compactSupport) : ℝ := f.property.choose
private theorem supportWitness_pos (f : compactSupport) : 0 < supportWitness f :=
  f.property.choose_spec.1
private def supportRepresentative (f : compactSupport) : FiniteWindow.Hilbert (supportWitness f) :=
  ⟨f, f.property.choose_spec.2⟩

private def rawValue (f : compactSupport) : Hilbert :=
  rawPartialSum (FiniteWindow.primeCutoff (supportWitness f)) f

private theorem rawValue_eq (f : compactSupport) (L : ℝ)
    (hf : (f : Ambient) ∈ FiniteWindow.supported L) :
    rawValue f = rawPartialSum (FiniteWindow.primeCutoff L) f :=
  rawPartialSum_witness_independent (supportRepresentative f) ⟨f, hf⟩ rfl

/-- The raw synthesis is an algebraic linear map on its dense physical domain. -/
def rawEuler : compactSupport →ₗ[ℂ] Hilbert where
  toFun := rawValue
  map_add' f g := by
    let L := max (supportWitness f) (supportWitness g)
    have hf := finite_support_mono (le_max_left (supportWitness f) (supportWitness g)) (f : Ambient) (supportRepresentative f).property
    have hg := finite_support_mono (le_max_right (supportWitness f) (supportWitness g)) (g : Ambient) (supportRepresentative g).property
    rw [rawValue_eq (f+g) L ((FiniteWindow.supported L).add_mem hf hg),
      rawValue_eq f L hf, rawValue_eq g L hg]
    exact (rawPartialSum (FiniteWindow.primeCutoff L)).map_add f g
  map_smul' c f := by
    let L := supportWitness f
    have hf := (supportRepresentative f).property
    rw [rawValue_eq (c • f) L ((FiniteWindow.supported L).smul_mem c hf), rawValue_eq f L hf]
    exact (rawPartialSum (FiniteWindow.primeCutoff L)).map_smul c f

theorem rawEuler_eq_partialSum (f : compactSupport) (L : ℝ)
    (hf : (f : Ambient) ∈ FiniteWindow.supported L) :
    rawEuler f = rawPartialSum (FiniteWindow.primeCutoff L) f := rawValue_eq f L hf

set_option maxHeartbeats 1000000 in
/-- Literal agreement with the preserved finite Euler operator at s=1/2. -/
theorem rawEuler_finiteInclusion (L : ℝ) (hL : 0 < L) (f : FiniteWindow.Hilbert L) :
    rawEuler (finiteCoreInclusion L hL f) =
      finiteInclusion L (FiniteWindow.primeOperator L (1/2) f) := by
  rw [rawEuler_eq_partialSum _ L f.property]
  exact rawPartialSum_finiteInclusion L f

/-- Representatives commute with a finite L² sum almost everywhere. -/
theorem ambient_finset_sum_ae {ι : Type*} (s : Finset ι) (F : ι → Ambient) :
    ((∑ i ∈ s, F i : Ambient) : ℝ → ℂ) =ᵐ[volume] fun t => ∑ i ∈ s, F i t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 volume] with t ht
    exact ht
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), ih] with t ha hs
    simpa only [Pi.add_apply, hs] using ha

/-- The finite arithmetic action on actual representatives, with the half-line cutoff. -/
theorem rawPartialSum_ae (X : ℕ) (f : Hilbert) :
    ((rawPartialSum X f : Ambient) : ℝ → ℂ) =ᵐ[volume]
      fun t => if 0 ≤ t then ∑ n ∈ Finset.Ioc 0 X,
        rawWeight n * (f : Ambient) (Real.log n + t) else 0 := by
  have hcoe : (rawPartialSum X f : Ambient) =
      ∑ n ∈ Finset.Ioc 0 X, rawWeight n • (shift (Real.log n) f : Ambient) := by
    change supported.subtypeL (rawPartialSum X f) = _
    rw [rawPartialSum_apply, map_sum]
    simp only [map_smul]
    rfl
  rw [hcoe]
  have hall : ∀ᵐ t, ∀ n ∈ Finset.Ioc 0 X,
      ((rawWeight n • (shift (Real.log n) f : Ambient) : Ambient) : ℝ → ℂ) t =
        if 0 ≤ t then rawWeight n * (f : Ambient) (Real.log n + t) else 0 := by
    apply (Finset.eventually_all _).mpr
    intro n hn
    have hn0 : n ≠ 0 := ne_of_gt (Finset.mem_Ioc.mp hn).1
    have ha := killedShift_ae (Arithmetic.natLog n) f
    rw [Arithmetic.natLog_coe hn0] at ha
    filter_upwards [Lp.coeFn_smul (rawWeight n) (shift (Real.log n) f : Ambient), ha]
      with t hm hs
    rw [hm]
    change rawWeight n * ((killedShift (Arithmetic.natLog n) f : Ambient) : ℝ → ℂ) t = _
    rw [hs]
    split_ifs <;> simp
  filter_upwards [ambient_finset_sum_ae (Finset.Ioc 0 X)
    (fun n => rawWeight n • (shift (Real.log n) f : Ambient)), hall] with t hs ht
  rw [hs]
  by_cases h : 0 ≤ t
  · rw [if_pos h]
    apply Finset.sum_congr rfl
    intro n hn
    simpa only [if_pos h] using ht n hn
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro n hn
    simpa only [if_neg h] using ht n hn

end Riemann.Analysis.HalfLine
