import Riemann.Analysis.HalfLine.RawBoxArithmetic
import Riemann.Analysis.HalfLine.RawBoxConvergence

/-! # The raw Euler graph is not the graph of a closable operator

The domain and arithmetic action are the actual compact-support construction.
Closed width-one box representatives give an explicit nonzero vertical vector
in the closure of its graph. No completed-operator kernel is asserted here.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Riemann.Analysis.HalfLine

/-- The raw outputs converge in the unchanged physical L² norm. -/
theorem rawEuler_box_tendsto :
    Tendsto (fun n : ℕ => rawEuler (box n (Nat.cast_nonneg n))) atTop (𝓝 rawGraphDefect) :=
  rawBoxVectors_tendsto _ (fun n => rawEuler_box_ae n (Nat.cast_nonneg n))

/-- Explicit graph witness for nonclosability of the densely defined raw map. -/
theorem rawEuler_nonclosability_witness :
    ∃ f : ℕ → compactSupport,
      Tendsto (fun n => (f n : Hilbert)) atTop (𝓝 0) ∧
      Tendsto (fun n => rawEuler (f n)) atTop (𝓝 rawGraphDefect) ∧
      rawGraphDefect ≠ 0 :=
  ⟨fun n => box n (Nat.cast_nonneg n), boxVector_tendsto_zero,
    rawEuler_box_tendsto, rawGraphDefect_ne_zero⟩

/-- The actual graph, viewed in the product of the ambient Hilbert space with itself. -/
def rawEulerGraph : Set (Hilbert × Hilbert) :=
  Set.range (fun f : compactSupport => ((f : Hilbert), rawEuler f))

theorem rawEuler_graphClosure_defect :
    ((0 : Hilbert), rawGraphDefect) ∈ closure rawEulerGraph := by
  apply mem_closure_of_tendsto (boxVector_tendsto_zero.prodMk_nhds rawEuler_box_tendsto)
  exact Eventually.of_forall fun n => ⟨box n (Nat.cast_nonneg n), rfl⟩

/-- The closure of the actual graph fails the defining uniqueness of an operator graph. -/
theorem rawEuler_graphClosure_not_singleValued :
    ¬ ∀ p ∈ closure rawEulerGraph, ∀ q ∈ closure rawEulerGraph,
      p.1 = q.1 → p.2 = q.2 := by
  intro h
  have hz : ((0 : Hilbert),(0 : Hilbert)) ∈ closure rawEulerGraph := by
    apply subset_closure
    refine ⟨(0 : compactSupport), ?_⟩
    simp
  exact rawGraphDefect_ne_zero
    (h (0,rawGraphDefect) rawEuler_graphClosure_defect (0,0) hz rfl)

/-- The graph closure contains a nonzero vertical vector and hence cannot be
contained in the graph of any everywhere-defined linear map. -/
theorem rawEuler_graphClosure_not_linearGraph :
    ¬ ∃ T : Hilbert →ₗ[ℂ] Hilbert,
      ∀ p ∈ closure rawEulerGraph, T p.1 = p.2 := by
  rintro ⟨T,hT⟩
  have h := hT (0,rawGraphDefect) rawEuler_graphClosure_defect
  simp only [map_zero] at h
  exact rawGraphDefect_ne_zero h.symm

/-- In particular no bounded operator agrees with the raw map on its domain. -/
theorem rawEuler_no_bounded_extension :
    ¬ ∃ T : Hilbert →L[ℂ] Hilbert, ∀ f : compactSupport, T f = rawEuler f := by
  rintro ⟨T,hT⟩
  have ht := T.continuous.continuousAt.tendsto.comp boxVector_tendsto_zero
  have he : Tendsto (fun n : ℕ => rawEuler (box n (Nat.cast_nonneg n))) atTop (𝓝 0) := by
    have heq (n : ℕ) : T (boxVector n (Nat.cast_nonneg n)) =
        rawEuler (box n (Nat.cast_nonneg n)) := hT (box n (Nat.cast_nonneg n))
    simpa only [Function.comp_def, map_zero, heq] using ht
  exact rawGraphDefect_ne_zero (tendsto_nhds_unique rawEuler_box_tendsto he)

end Riemann.Analysis.HalfLine
