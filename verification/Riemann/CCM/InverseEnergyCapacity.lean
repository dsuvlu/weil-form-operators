import Riemann.CCM.InverseEnergyIntegration
import Riemann.Basic.PositivePencilDiagonalization
import Riemann.Capacity.ScalarLogBounds

/-! Exact finite capacity comparison with the inverse-energy ratio. -/
noncomputable section
open Matrix
namespace Riemann.CCM.InverseEnergyData
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (M : InverseEnergyData ι)

/-- The free logarithmic determinant increment, with both endpoints positive. -/
def freeLogRatio (a b : ℝ) : ℝ := Real.log ((M.freePencil b).det / (M.freePencil a).det)

/-- The high logarithmic increment retains the free determinant contribution. -/
theorem pencil_log_ratio_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log ((M.pencil b).det / (M.pencil a).det) =
      M.freeLogRatio a b + Real.log (M.determinantRatio b / M.determinantRatio a) := by
  have hratio : (M.pencil b).det / (M.pencil a).det =
      ((M.freePencil b).det / (M.freePencil a).det) *
      (M.determinantRatio b / M.determinantRatio a) := by
    unfold determinantRatio
    field_simp [M.B_pos.det_pos.ne', (M.freePencil_pos ha).det_pos.ne',
      (M.freePencil_pos hb).det_pos.ne', (M.pencil_pos ha).det_pos.ne']
  rw [hratio, Real.log_mul]
  · rfl
  · exact (div_pos (M.freePencil_pos hb).det_pos (M.freePencil_pos ha).det_pos).ne'
  · exact (div_pos (M.determinantRatio_pos hb) (M.determinantRatio_pos ha)).ne'

/-- Actual positive generalized eigenvalues simultaneously describe the trace
and logarithmic determinant increment. -/
theorem high_spectral_representation :
    ∃ lambda : ι → ℝ, (∀ i, 0 < lambda i) ∧
      (∀ s : ℝ, 0 < s → M.highMean s = ∑ i, s / (lambda i + s)) ∧
      (∀ a b : ℝ, 0 < a → 0 < b →
        M.freeLogRatio a b + Real.log (M.determinantRatio b / M.determinantRatio a) =
          ∑ i, Real.log ((lambda i + b) / (lambda i + a))) := by
  obtain ⟨lambda, hl, ht, hd⟩ := Riemann.Basic.positivePair_spectral_representation M.K M.B M.K_pos M.B_pos
  refine ⟨lambda, hl, ?_, ?_⟩
  · intro s hs
    rw [highMean, inversePencil, pencil, ht s hs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (div_eq_mul_inv _ _).symm
  · intro a b ha hb
    rw [← M.pencil_log_ratio_eq ha hb]
    change Real.log ((M.K + b • M.B).det / (M.K + a • M.B).det) = _
    rw [hd a b ha hb, Real.log_prod]
    intro i hi
    exact (div_pos (add_pos (hl i) hb) (add_pos (hl i) ha)).ne'

/-- BL G6: the actual finite high capacity controls the full logarithmic increment. -/
theorem capacity_log_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (b/a) * M.highMean a ≤
      M.freeLogRatio a b + Real.log (M.determinantRatio b / M.determinantRatio a) ∧
    M.freeLogRatio a b + Real.log (M.determinantRatio b / M.determinantRatio a) ≤
      (b/a-1) * M.highMean a := by
  obtain ⟨lambda, hl, hm, hd⟩ := M.high_spectral_representation
  rw [hm a ha, hd a b ha (lt_of_lt_of_le ha hab)]
  exact Riemann.Capacity.finite_log_ratio_bounds lambda hl ha hab

/-- The bounded one-normal correction converts capacity directly into a
source-energy ratio comparison. No free-tail bound is assumed. -/
theorem capacity_energy_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (b/a) * (M.highMean a - 1) ≤
      M.freeLogRatio a b + (1/2 : ℝ) * Real.log (M.inverseEnergy b / M.inverseEnergy a) ∧
    M.freeLogRatio a b + (1/2 : ℝ) * Real.log (M.inverseEnergy b / M.inverseEnergy a) ≤
      (b/a-1) * M.highMean a := by
  have hc := M.capacity_log_bounds ha hab
  rw [M.log_determinantRatio ha hab] at hc
  have hi := M.boundaryCorrection_integral_bounds ha hab
  constructor <;> nlinarith

/-- The exact fixed-anchor capacity/source-energy comparison. -/
theorem fixed_anchor_capacity_energy_bounds :
    Real.log 9 * (M.highMean (1/16) - 1) ≤
      M.freeLogRatio (1/16) (9/16) +
        (1/2 : ℝ) * Real.log (M.inverseEnergy (9/16) / M.inverseEnergy (1/16)) ∧
    M.freeLogRatio (1/16) (9/16) +
        (1/2 : ℝ) * Real.log (M.inverseEnergy (9/16) / M.inverseEnergy (1/16)) ≤
      8 * M.highMean (1/16) := by
  convert M.capacity_energy_bounds (a := 1/16) (b := 9/16) (by norm_num) (by norm_num) using 1 <;> norm_num

/-- An explicit inverse-energy ratio bound gives the prescribed-anchor capacity
bound, with its exact free determinant term still visible. -/
theorem fixed_anchor_capacity_of_energy_ratio {C : ℝ}
    (hC : M.inverseEnergy (9/16) / M.inverseEnergy (1/16) ≤ C) :
    M.highMean (1/16) ≤ 1 +
      (M.freeLogRatio (1/16) (9/16) + (1/2 : ℝ) * Real.log C) / Real.log 9 := by
  have he : 0 < M.inverseEnergy (9/16) / M.inverseEnergy (1/16) :=
    div_pos (M.inverseEnergy_pos (by norm_num)) (M.inverseEnergy_pos (by norm_num))
  have hl := Real.log_le_log he hC
  have hc := M.fixed_anchor_capacity_energy_bounds.1
  have hlog : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hm : M.highMean (1/16) - 1 ≤
      (M.freeLogRatio (1/16) (9/16) + (1/2 : ℝ) * Real.log C) / Real.log 9 := by
    apply (le_div_iff₀ hlog).mpr
    nlinarith
  linarith

end Riemann.CCM.InverseEnergyData
