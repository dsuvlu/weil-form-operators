import Riemann.Basic.PositiveSchurCoordinates
import Riemann.CCM.PositiveOddCapacity
import Riemann.Capacity.FullDecomposition

/-! The full native CCM form supplies the BI metric graph and its capacity bounds. -/
noncomputable section
open scoped InnerProductSpace
namespace Riemann.CCM.FullSimpleEvenData
open Riemann.Basic Riemann.Basic.PositiveSchur Riemann.Capacity
variable {E U W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
variable (M : FullSimpleEvenData E)

/-- Actual odd columns in a free-invariant low/high split. The full physical
mass supplies the graph; no graph metric or coupling estimate is assumed. -/
def oddGraphData (Z : Space U W →L[ℂ] E) (hZ : Function.Injective Z)
    (hodd : ∀ x, M.reflection (Z x) = -Z x) (A₁ : U →L[ℂ] U) (A₂ : W →L[ℂ] W)
    (hfree : ∀ x, M.D (M.D (Z x)) = Z (block A₁ 0 A₂ x)) : GraphData U W := by
  let B := columnEnergy M.shifted Z
  have hB : B.adjoint = B :=
    (columnEnergy_symmetric M.shifted Z
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp M.shifted_selfadjoint)).clm_adjoint_eq
  have hpB : ∀ x, x ≠ 0 → 0 < (⟪x, B x⟫_ℂ).re := by
    intro x hx
    rw [show B = columnEnergy M.shifted Z from rfl, columnEnergy_inner]
    exact M.odd_shifted_positive (hodd x) (fun h => hx (hZ (by simpa using h)))
  refine {
    metric := Data.ofOperator B hB hpB
    K := columnEnergy M.shifted (M.D.comp Z)
    selfK := (columnEnergy_symmetric M.shifted (M.D.comp Z)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp M.shifted_selfadjoint)).clm_adjoint_eq
    positiveK := ?_
    A₁ := A₁
    A₂ := A₂
    beta := Z.adjoint M.b
    zeta := Z.adjoint (M.D M.eta)
    displacement := ?_ }
  · intro x hx
    rw [columnEnergy_inner]
    exact M.odd_differentiated_positive (hodd x) (fun h => hx (hZ (by simpa using h)))
  · rw [Data.ofOperator_block]
    exact M.oddColumn_displacement Z hodd (block A₁ 0 A₂) hfree

/-- The full metric used for graph elimination is exactly the actual pulled-back shifted form. -/
theorem oddGraphData_metric (Z : Space U W →L[ℂ] E) (hZ : Function.Injective Z)
    (hodd : ∀ x, M.reflection (Z x) = -Z x) (A₁ : U →L[ℂ] U) (A₂ : W →L[ℂ] W)
    (hfree : ∀ x, M.D (M.D (Z x)) = Z (block A₁ 0 A₂ x)) :
    (M.oddGraphData Z hZ hodd A₁ A₂ hfree).fullMetric = columnEnergy M.shifted Z := by
  simp only [oddGraphData, GraphData.fullMetric, Data.ofOperator_block]

/-- Native odd data inherit the exact bounded graph coupling. -/
theorem oddGraphData_coupling_bounds (Z : Space U W →L[ℂ] E) (hZ : Function.Injective Z)
    (hodd : ∀ x, M.reflection (Z x) = -Z x) (A₁ : U →L[ℂ] U) (A₂ : W →L[ℂ] W)
    (hfree : ∀ x, M.D (M.D (Z x)) = Z (block A₁ 0 A₂ x)) (s : ℝ) (hs : 0 < s) :
    0 ≤ (M.oddGraphData Z hZ hodd A₁ A₂ hfree).coupling s hs ∧
      (M.oddGraphData Z hZ hodd A₁ A₂ hfree).coupling s hs < 1 :=
  ⟨(M.oddGraphData Z hZ hodd A₁ A₂ hfree).coupling_nonneg s hs,
    (M.oddGraphData Z hZ hodd A₁ A₂ hfree).coupling_lt_one s hs⟩

/-- The generic full pencil is the actual odd-column pencil, with its physical mass. -/
theorem oddGraphData_fullPencil (Z : Space U W →L[ℂ] E) (hZ : Function.Injective Z)
    (hodd : ∀ x, M.reflection (Z x) = -Z x) (A₁ : U →L[ℂ] U) (A₂ : W →L[ℂ] W)
    (hfree : ∀ x, M.D (M.D (Z x)) = Z (block A₁ 0 A₂ x)) :
    (M.oddGraphData Z hZ hodd A₁ A₂ hfree).fullPencil = M.oddColumnPencil Z hZ hodd := by
  apply PositivePencil.ext
  · rfl
  · exact M.oddGraphData_metric Z hZ hodd A₁ A₂ hfree

/-- Full/high/graph pointwise control on the actual admitted odd-column family. -/
theorem oddGraphData_mean_bounds (Z : Space U W →L[ℂ] E) (hZ : Function.Injective Z)
    (hodd : ∀ x, M.reflection (Z x) = -Z x) (A₁ : U →L[ℂ] U) (A₂ : W →L[ℂ] W)
    (hfree : ∀ x, M.D (M.D (Z x)) = Z (block A₁ 0 A₂ x)) (s : ℝ) (hs : 0 < s) :
    (M.oddGraphData Z hZ hodd A₁ A₂ hfree).highPencil.softMean s hs +
      (M.oddGraphData Z hZ hodd A₁ A₂ hfree).graphPencil.softMean s hs ≤
        (M.oddColumnPencil Z hZ hodd).softMean s hs ∧
    (M.oddColumnPencil Z hZ hodd).softMean s hs <
      (M.oddGraphData Z hZ hodd A₁ A₂ hfree).highPencil.softMean s hs +
      (M.oddGraphData Z hZ hodd A₁ A₂ hfree).graphPencil.softMean s hs + 1 := by
  rw [← M.oddGraphData_fullPencil Z hZ hodd A₁ A₂ hfree]
  exact (M.oddGraphData Z hZ hodd A₁ A₂ hfree).full_high_graph_bounds s hs

end Riemann.CCM.FullSimpleEvenData
