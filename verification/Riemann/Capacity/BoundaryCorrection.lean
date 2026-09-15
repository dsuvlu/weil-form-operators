import Riemann.Capacity.SoftMean

/-! Endpoint correction of a column family and its sharp soft-mean comparison. -/
noncomputable section
open scoped InnerProductSpace
namespace Riemann.Capacity
open Riemann.Basic InnerProductSpace
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Energy form pulled back by the columns. -/
def columnEnergy (G : E →L[ℂ] E) (D : F →L[ℂ] E) : F →L[ℂ] F :=
  D.adjoint.comp (G.comp D)

@[simp] theorem columnEnergy_inner (G : E →L[ℂ] E) (D : F →L[ℂ] E) (x y : F) :
    ⟪x, columnEnergy G D y⟫_ℂ = ⟪D x, G (D y)⟫_ℂ := D.adjoint_inner_right x (G (D y))

theorem columnEnergy_symmetric (G : E →L[ℂ] E) (D : F →L[ℂ] E)
    (hG : G.toLinearMap.IsSymmetric) : (columnEnergy G D).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪columnEnergy G D x, y⟫_ℂ = ⟪x, columnEnergy G D y⟫_ℂ
  rw [columnEnergy_inner]
  change ⟪D.adjoint (G (D x)), y⟫_ℂ = _
  rw [D.adjoint_inner_left]
  exact hG (D x) (D y)

/-- Corrected columns `(I-pδ)D`, with `δ=⟨eta,·⟩`. -/
def endpointCorrectedColumns (D : F →L[ℂ] E) (eta p : E) : F →L[ℂ] E :=
  D - rankOne ℂ p (D.adjoint eta)

@[simp] theorem endpointCorrectedColumns_apply (D : F →L[ℂ] E) (eta p : E) (x : F) :
    endpointCorrectedColumns D eta p x = D x - ⟪eta, D x⟫_ℂ • p := by
  change D x - ⟪D.adjoint eta, x⟫_ℂ • p = _
  rw [D.adjoint_inner_left]

/-- The corrected columns have zero endpoint. -/
theorem endpointCorrectedColumns_boundary (D : F →L[ℂ] E) (eta p : E)
    (hp : ⟪eta, p⟫_ℂ = 1) (x : F) : ⟪eta, endpointCorrectedColumns D eta p x⟫_ℂ = 0 := by
  simp [inner_sub_right, inner_smul_right, hp]

/-- Correction vanishes on the kernel of the endpoint row. -/
theorem endpointCorrectedColumns_on_hyperplane (D : F →L[ℂ] E) (eta p : E)
    (x : vectorHyperplane (D.adjoint eta)) : endpointCorrectedColumns D eta p x = D x := by
  have hx : ⟪D.adjoint eta, (x : F)⟫_ℂ = 0 := x.property
  change D x - ⟪D.adjoint eta, (x : F)⟫_ℂ • p = D x
  rw [hx, zero_smul, sub_zero]

/-- The two energies have exactly the same hyperplane compression. -/
theorem endpointCorrectedColumns_common_compression (G : E →L[ℂ] E)
    (D : F →L[ℂ] E) (eta p : E) :
    physicalCompression (vectorHyperplane (D.adjoint eta)) (columnEnergy G D) =
    physicalCompression (vectorHyperplane (D.adjoint eta))
      (columnEnergy G (endpointCorrectedColumns D eta p)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [physicalCompression_inner, physicalCompression_inner,
    columnEnergy_inner, columnEnergy_inner,
    endpointCorrectedColumns_on_hyperplane, endpointCorrectedColumns_on_hyperplane]

/-- A column pencil with an independently specified positive physical mass. -/
def columnPencil (G : E →L[ℂ] E) (hG : G.toLinearMap.IsSymmetric)
    (hpos : ∀ x, 0 ≤ (⟪x, G x⟫_ℂ).re) (D : F →L[ℂ] E)
    (B : F →L[ℂ] F) (hB : B.toLinearMap.IsSymmetric)
    (hBp : ∀ x, x ≠ 0 → 0 < (⟪x, B x⟫_ℂ).re) : PositivePencil F where
  energy := columnEnergy G D
  mass := B
  energy_symmetric := columnEnergy_symmetric G D hG
  mass_symmetric := hB
  energy_nonneg x := by rw [columnEnergy_inner]; exact hpos (D x)
  mass_positive := hBp

/-- Sharp one-unit bound from the common endpoint-zero compression.
The vanishing row, one-dimensional source, and zero-dimensional source are included. -/
theorem softMean_endpointCorrection_le_one
    (G : E →L[ℂ] E) (hG : G.toLinearMap.IsSymmetric)
    (hpos : ∀ x, 0 ≤ (⟪x, G x⟫_ℂ).re) (D : F →L[ℂ] E)
    (B : F →L[ℂ] F) (hB : B.toLinearMap.IsSymmetric)
    (hBp : ∀ x, x ≠ 0 → 0 < (⟪x, B x⟫_ℂ).re)
    (eta p : E) (s : ℝ) (hs : 0 < s) :
    |(columnPencil G hG hpos D B hB hBp).softMean s hs -
      (columnPencil G hG hpos (endpointCorrectedColumns D eta p) B hB hBp).softMean s hs| ≤ 1 := by
  by_cases hc : D.adjoint eta = 0
  · have hd : endpointCorrectedColumns D eta p = D := by
      simp [endpointCorrectedColumns, hc]
    rw [hd, sub_self, abs_zero]
    norm_num
  · let P : PositivePencil F := columnPencil G hG hpos D B hB hBp
    let Q : PositivePencil F := columnPencil G hG hpos (endpointCorrectedColumns D eta p) B hB hBp
    have hK : physicalCompression (vectorHyperplane (D.adjoint eta)) P.energy =
        physicalCompression (vectorHyperplane (D.adjoint eta)) Q.energy :=
      endpointCorrectedColumns_common_compression G D eta p
    exact P.softMean_common_hyperplane Q (D.adjoint eta) hc hK rfl s hs

/-- Exact rank-two boundary correction, with the cross vector formed from D₀. -/
theorem columnEnergy_boundaryCorrection (G : E →L[ℂ] E)
    (hG : G.adjoint = G) (D : F →L[ℂ] E) (eta p : E) :
    columnEnergy G D - columnEnergy G (endpointCorrectedColumns D eta p) =
    rankOne ℂ ((endpointCorrectedColumns D eta p).adjoint (G p)) (D.adjoint eta) +
    rankOne ℂ (D.adjoint eta) ((endpointCorrectedColumns D eta p).adjoint (G p)) +
    ⟪p, G p⟫_ℂ • rankOne ℂ (D.adjoint eta) (D.adjoint eta) := by
  let D0 := endpointCorrectedColumns D eta p
  let c := D.adjoint eta
  have hd : D = D0 + rankOne ℂ p c := by
    dsimp [D0, c, endpointCorrectedColumns]
    abel
  change columnEnergy G D - columnEnergy G D0 =
    rankOne ℂ (D0.adjoint (G p)) c + rankOne ℂ c (D0.adjoint (G p)) +
      ⟪p, G p⟫_ℂ • rankOne ℂ c c
  conv_lhs => rw [hd]
  simp only [columnEnergy, map_add, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_add, adjoint_rankOne,
    comp_rankOne, rankOne_comp, ContinuousLinearMap.adjoint_comp,
    hG]
  ext x
  simp only [add_apply, sub_apply,
    rankOne_apply, smul_smul, smul_apply]
  simp only [ContinuousLinearMap.comp_apply]
  module

end Riemann.Capacity
