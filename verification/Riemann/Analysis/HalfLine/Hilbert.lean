import Riemann.Analysis.FiniteWindow.KilledShiftHilbert

/-! # Backward shifts on the actual half-line Hilbert space

The carrier is the closed subspace of the existing ambient complex L² space
supported in `[0,∞)`. Translation is followed by the physical half-line
projection. Nonnegative translations form a strongly continuous contraction
semigroup; no operator-norm continuity is asserted.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal
namespace Riemann.Analysis.HalfLine

abbrev Ambient : Type := FiniteWindow.Ambient

def cut (f : Ambient) : Ambient :=
  ((Lp.memLp f).indicator measurableSet_Ici).toLp ((Ici 0).indicator f)

theorem cut_ae (f : Ambient) :
    (cut f : ℝ → ℂ) =ᵐ[volume] (Ici 0).indicator f := MemLp.coeFn_toLp _

theorem cut_add (f g : Ambient) : cut (f + g) = cut f + cut g := by
  apply Lp.ext
  filter_upwards [cut_ae (f + g), cut_ae f, cut_ae g,
    Lp.coeFn_add f g, Lp.coeFn_add (cut f) (cut g)] with t h h₁ h₂ h₃ h₄
  rw [h, h₄]
  simp only [Pi.add_apply]
  rw [h₁, h₂]
  by_cases ht : t ∈ Ici 0
  · simpa only [indicator_of_mem ht, Pi.add_apply] using h₃
  · simp only [indicator_of_notMem ht, add_zero]

theorem cut_smul (c : ℂ) (f : Ambient) : cut (c • f) = c • cut f := by
  apply Lp.ext
  filter_upwards [cut_ae (c • f), cut_ae f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (cut f)] with t h h₁ h₂ h₃
  rw [h, h₃]
  simp only [Pi.smul_apply]
  rw [h₁]
  by_cases ht : t ∈ Ici 0 <;> simp [ht, h₂]

theorem norm_cut_le (f : Ambient) : ‖cut f‖ ≤ ‖f‖ := by
  rw [cut, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).2.ne (eLpNorm_indicator_le _)

def cutCLM : Ambient →L[ℂ] Ambient :=
  LinearMap.mkContinuous
    { toFun := cut, map_add' := cut_add, map_smul' := cut_smul }
    1 (by intro f; simpa using norm_cut_le f)

@[simp] theorem cutCLM_apply (f : Ambient) : cutCLM f = cut f := rfl

theorem cut_idempotent (f : Ambient) : cut (cut f) = cut f := by
  apply Lp.ext
  filter_upwards [cut_ae (cut f), cut_ae f] with t h h₁
  rw [h]
  by_cases ht : t ∈ Ici 0 <;> simp_all

/-- Closed half-line support condition in the original physical L² norm. -/
def supported : Submodule ℂ Ambient :=
  (cutCLM - ContinuousLinearMap.id ℂ Ambient).ker

abbrev Hilbert := supported

instance : CompleteSpace Hilbert := by unfold Hilbert supported; infer_instance

theorem mem_supported_iff (f : Ambient) : f ∈ supported ↔ cut f = f := by
  simp [supported, sub_eq_zero]

theorem cut_mem_supported (f : Ambient) : cut f ∈ supported :=
  (mem_supported_iff _).2 (cut_idempotent f)

def projection : Ambient →L[ℂ] Hilbert := cutCLM.codRestrict supported cut_mem_supported

@[simp] theorem projection_coe (f : Ambient) : (projection f : Ambient) = cut f := rfl

@[simp] theorem projection_self (f : Hilbert) : projection f = f := by
  apply Subtype.ext
  exact (mem_supported_iff f).1 f.property

theorem supported_ae (f : Hilbert) :
    ((f : Ambient) : ℝ → ℂ) =ᵐ[volume] (Ici 0).indicator (f : Ambient) := by
  have h := cut_ae (f : Ambient)
  rwa [(mem_supported_iff f).1 f.property] at h

/-- Half-line backward shift, as an actual bounded operator on L² classes. -/
def killedShift (y : ℝ≥0) : Hilbert →L[ℂ] Hilbert :=
  projection.comp ((FiniteWindow.translate y).comp supported.subtypeL)

theorem norm_killedShift_apply_le (y : ℝ≥0) (f : Hilbert) :
    ‖killedShift y f‖ ≤ ‖f‖ := by
  change ‖cut (FiniteWindow.translate y f)‖ ≤ ‖(f : Ambient)‖
  exact (norm_cut_le _).trans_eq (FiniteWindow.norm_translate y f)

/-- Exact representative action; the output is zero at negative coordinates. -/
theorem killedShift_ae (y : ℝ≥0) (f : Hilbert) :
    (((killedShift y f : Hilbert) : Ambient) : ℝ → ℂ) =ᵐ[volume]
      fun t => if 0 ≤ t then (f : Ambient) ((y : ℝ) + t) else 0 := by
  filter_upwards [cut_ae (FiniteWindow.translate y f), FiniteWindow.translate_ae y f]
    with t hc ht
  change (cut (FiniteWindow.translate y f) : ℝ → ℂ) t = _
  rw [hc]
  by_cases h : 0 ≤ t <;> simp [h, ht]

@[simp] theorem killedShift_zero : killedShift 0 = ContinuousLinearMap.id ℂ Hilbert := by
  apply ContinuousLinearMap.ext
  intro f
  change projection (FiniteWindow.translate 0 (f : Ambient)) = f
  rw [FiniteWindow.translate_eq_vadd]
  change projection ((0 : ℝᵈᵃᵃ) +ᵥ (f : Ambient)) = f
  simp

theorem killedShift_add (a b : ℝ≥0) :
    (killedShift a).comp (killedShift b) = killedShift (a + b) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply Lp.ext
  have hb := (measurePreserving_add_left volume (a : ℝ)).quasiMeasurePreserving.ae
    (killedShift_ae b f)
  filter_upwards [killedShift_ae a (killedShift b f), killedShift_ae (a + b) f, hb]
    with t h₁ h₂ h₃
  change (((killedShift a (killedShift b f)) : Ambient) : ℝ → ℂ) t =
    (((killedShift (a + b) f) : Ambient) : ℝ → ℂ) t
  rw [h₁, h₂]
  by_cases ht : 0 ≤ t
  · have hat : 0 ≤ (a : ℝ) + t := add_nonneg a.2 ht
    simp only [ht, hat, ↓reduceIte, h₃, NNReal.coe_add]
    congr 1
    ring
  · simp only [ht, ↓reduceIte]

theorem norm_killedShift_le (y : ℝ≥0) : ‖killedShift y‖ ≤ 1 :=
  (killedShift y).opNorm_le_bound zero_le_one (by
    intro f; simpa using norm_killedShift_apply_le y f)

theorem continuous_killedShift_apply (f : Hilbert) :
    Continuous (fun y : ℝ≥0 => killedShift y f) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have h : Continuous (fun y : ℝ≥0 => DomAddAct.mk (y : ℝ) +ᵥ (f : Ambient)) :=
    (DomAddAct.continuous_mk.comp continuous_subtype_val).vadd continuous_const
  exact projection.continuous.comp h

/-- Real notation for integration; only nonnegative times have semigroup meaning. -/
def shift (y : ℝ) : Hilbert →L[ℂ] Hilbert := killedShift y.toNNReal

@[simp] theorem shift_zero : shift 0 = ContinuousLinearMap.id ℂ Hilbert := by simp [shift]

theorem shift_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (shift a).comp (shift b) = shift (a + b) := by
  rw [shift, shift, shift, Real.toNNReal_add ha hb, killedShift_add]

theorem norm_shift_apply_le (y : ℝ) (f : Hilbert) : ‖shift y f‖ ≤ ‖f‖ :=
  norm_killedShift_apply_le _ f

theorem norm_shift_le (y : ℝ) : ‖shift y‖ ≤ 1 := norm_killedShift_le _

theorem continuous_shift_apply (f : Hilbert) : Continuous (fun y : ℝ => shift y f) :=
  (continuous_killedShift_apply f).comp continuous_real_toNNReal

end Riemann.Analysis.HalfLine
