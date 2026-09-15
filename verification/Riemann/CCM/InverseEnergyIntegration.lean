import Riemann.CCM.InverseEnergyTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fixed-parameter integration of the inverse-energy identity

All matrix data, including the actual ground energy in a native application,
are fixed throughout these real parameter intervals. No family bound is assumed.
-/
noncomputable section
open Matrix Set MeasureTheory
namespace Riemann.CCM.InverseEnergyData
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (M : InverseEnergyData ι)

lemma continuousAt_responseMoment {s : ℝ} (hs : 0 < s) :
    ContinuousAt M.responseMoment s :=
  Riemann.Basic.continuousAt_tripleInverseContraction M.K M.B M.B M.B s
    (M.pencil_pos hs).isUnit M.zeta M.zeta

lemma continuousAt_boundaryCorrection {s : ℝ} (hs : 0 < s) :
    ContinuousAt M.boundaryCorrection s := by
  have hc := ((continuousAt_id.mul
      ((M.hasDerivAt_determinantRatio hs).continuousAt.pow 2)).mul
      (M.continuousAt_responseMoment hs)).div
      (M.hasDerivAt_inverseEnergy hs).continuousAt (M.inverseEnergy_pos hs).ne'
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with t ht
  simp only [boundaryCorrection, M.boundaryNumerator_eq ht, Pi.div_apply, Pi.mul_apply,
    Pi.pow_apply, id_eq]
  ring

/-- The normalized logarithmic determinant-energy difference. -/
def logarithmicBalance (s : ℝ) : ℝ :=
  Real.log (M.determinantRatio s) - (1 / 2 : ℝ) * Real.log (M.inverseEnergy s)

theorem hasDerivAt_logarithmicBalance {s : ℝ} (hs : 0 < s) :
    HasDerivAt M.logarithmicBalance (M.boundaryCorrection s / s) s := by
  have hd := (M.hasDerivAt_determinantRatio hs).differentiableAt.hasDerivAt
  have he := (M.hasDerivAt_inverseEnergy hs).differentiableAt.hasDerivAt
  have hdl := hd.log (M.determinantRatio_pos hs).ne'
  have hel := he.log (M.inverseEnergy_pos hs).ne'
  have hf := hdl.sub (hel.const_mul (1 / 2 : ℝ))
  apply HasDerivAt.congr_deriv hf
  have hid := M.logarithmicEnergy_identity hs
  rw [hel.deriv] at hid
  apply (eq_div_iff hs.ne').mpr
  ring_nf at hid ⊢
  linarith

lemma boundaryCorrection_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => M.boundaryCorrection t / t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le ha ht.1
  exact ((M.continuousAt_boundaryCorrection htpos).div continuousAt_id htpos.ne').continuousWithinAt

/-- Integrated exact identity on any fixed positive finite interval. -/
theorem logarithmicBalance_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, M.boundaryCorrection t / t) =
      M.logarithmicBalance b - M.logarithmicBalance a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact M.hasDerivAt_logarithmicBalance (lt_of_lt_of_le ha ht.1)
  · exact M.boundaryCorrection_intervalIntegrable ha hab

/-- The scalar determinant ratio is recovered from the energy ratio and the
integrated boundary correction. This logarithmic form avoids branch choices. -/
theorem log_determinantRatio {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (M.determinantRatio b / M.determinantRatio a) =
      (1 / 2 : ℝ) * Real.log (M.inverseEnergy b / M.inverseEnergy a) +
        ∫ t in a..b, M.boundaryCorrection t / t := by
  have hb := lt_of_lt_of_le ha hab
  rw [M.logarithmicBalance_integral ha hab,
    Real.log_div (M.determinantRatio_pos hb).ne' (M.determinantRatio_pos ha).ne',
    Real.log_div (M.inverseEnergy_pos hb).ne' (M.inverseEnergy_pos ha).ne']
  simp only [logarithmicBalance]
  ring

/-- The correction integral lies between zero and the logarithmic parameter ratio. -/
theorem boundaryCorrection_integral_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ (∫ t in a..b, M.boundaryCorrection t / t) ∧
    (∫ t in a..b, M.boundaryCorrection t / t) ≤ Real.log (b / a) := by
  constructor
  · apply intervalIntegral.integral_nonneg hab
    intro t ht
    have htpos := lt_of_lt_of_le ha ht.1
    exact div_nonneg (M.boundaryCorrection_pos htpos).le htpos.le
  · have hb := lt_of_lt_of_le ha hab
    rw [← integral_one_div_of_pos ha hb]
    apply intervalIntegral.integral_mono_on hab
      (M.boundaryCorrection_intervalIntegrable ha hab)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab]
      intro t ht
      exact (continuousAt_const.div continuousAt_id (ne_of_gt (lt_of_lt_of_le ha ht.1))).continuousWithinAt
    · intro t ht
      have htpos := lt_of_lt_of_le ha ht.1
      exact (div_le_div_iff_of_pos_right htpos).mpr (M.boundaryCorrection_lt_one htpos).le

/-- Exact BL anchors; their ratio is nine. -/
theorem fixed_anchor_log_identity :
    Real.log (M.determinantRatio (9/16) / M.determinantRatio (1/16)) =
      (1/2 : ℝ) * Real.log (M.inverseEnergy (9/16) / M.inverseEnergy (1/16)) +
        ∫ t in (1/16 : ℝ)..(9/16 : ℝ), M.boundaryCorrection t / t :=
  M.log_determinantRatio (by norm_num) (by norm_num)

theorem fixed_anchor_correction_bounds :
    0 ≤ (∫ t in (1/16 : ℝ)..(9/16 : ℝ), M.boundaryCorrection t / t) ∧
    (∫ t in (1/16 : ℝ)..(9/16 : ℝ), M.boundaryCorrection t / t) ≤ Real.log 9 := by
  convert M.boundaryCorrection_integral_bounds (a := 1/16) (b := 9/16)
    (by norm_num) (by norm_num) using 1
  norm_num

/-- Positive determinant/energy ratio identity, with the ordinary positive square root. -/
theorem determinantRatio_energy_ratio {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    M.determinantRatio b / M.determinantRatio a =
      Real.sqrt (M.inverseEnergy b / M.inverseEnergy a) *
        Real.exp (∫ t in a..b, M.boundaryCorrection t / t) := by
  have hb := lt_of_lt_of_le ha hab
  have he : 0 < M.inverseEnergy b / M.inverseEnergy a :=
    div_pos (M.inverseEnergy_pos hb) (M.inverseEnergy_pos ha)
  have hd : 0 < M.determinantRatio b / M.determinantRatio a :=
    div_pos (M.determinantRatio_pos hb) (M.determinantRatio_pos ha)
  have hhalf : (1/2 : ℝ) * Real.log (M.inverseEnergy b / M.inverseEnergy a) =
      Real.log (Real.sqrt (M.inverseEnergy b / M.inverseEnergy a)) := by
    rw [Real.log_sqrt he.le]
    ring
  have h := congrArg Real.exp (M.log_determinantRatio ha hab)
  rw [Real.exp_log hd, hhalf, Real.exp_add, Real.exp_log (Real.sqrt_pos.mpr he)] at h
  exact h

/-- Two-sided fixed-data ratio bounds. -/
theorem determinantRatio_energy_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.sqrt (M.inverseEnergy b / M.inverseEnergy a) ≤
      M.determinantRatio b / M.determinantRatio a ∧
    M.determinantRatio b / M.determinantRatio a ≤
      (b/a) * Real.sqrt (M.inverseEnergy b / M.inverseEnergy a) := by
  have hb := lt_of_lt_of_le ha hab
  have hi := M.boundaryCorrection_integral_bounds ha hab
  have hlo : 1 ≤ Real.exp (∫ t in a..b, M.boundaryCorrection t / t) :=
    Real.one_le_exp_iff.mpr hi.1
  have hhi : Real.exp (∫ t in a..b, M.boundaryCorrection t / t) ≤ b/a := by
    simpa only [Real.exp_log (div_pos hb ha)] using Real.exp_le_exp.mpr hi.2
  rw [M.determinantRatio_energy_ratio ha hab]
  constructor
  · nlinarith [Real.sqrt_nonneg (M.inverseEnergy b / M.inverseEnergy a)]
  · nlinarith [Real.sqrt_nonneg (M.inverseEnergy b / M.inverseEnergy a)]

/-- BL's prescribed anchors give precisely the factor nine. -/
theorem fixed_anchor_energy_bounds :
    Real.sqrt (M.inverseEnergy (9/16) / M.inverseEnergy (1/16)) ≤
      M.determinantRatio (9/16) / M.determinantRatio (1/16) ∧
    M.determinantRatio (9/16) / M.determinantRatio (1/16) ≤
      9 * Real.sqrt (M.inverseEnergy (9/16) / M.inverseEnergy (1/16)) := by
  convert M.determinantRatio_energy_bounds (a := 1/16) (b := 9/16)
    (by norm_num) (by norm_num) using 1
  norm_num

/-- The logarithmic derivative of the determinant ratio is the excess high mean. -/
theorem hasDerivAt_log_determinantRatio {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => Real.log (M.determinantRatio t))
      ((M.highMean s - M.freeMean s) / s) s := by
  have hd := (M.hasDerivAt_determinantRatio hs).differentiableAt.hasDerivAt
  apply (hd.log (M.determinantRatio_pos hs).ne').congr_deriv
  rw [M.highMean_eq hs]
  field_simp
  ring

/-- Empty high blocks have determinant ratio one and high mean zero. Energy
logarithms are deliberately reserved for a nonzero boundary source. -/
theorem empty_high_block {κ : Type*} [Fintype κ] [DecidableEq κ] [IsEmpty κ]
    (A B K : Matrix κ κ ℝ) (s : ℝ) :
    (K + s • B).det / (B.det * (A + s • 1).det) = 1 ∧
      s * Matrix.trace ((K + s • B)⁻¹ * B) = 0 := by
  simp [Matrix.trace]

end Riemann.CCM.InverseEnergyData
