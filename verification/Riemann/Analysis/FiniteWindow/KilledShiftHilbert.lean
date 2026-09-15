import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # Killed backward translation on the supported interval Hilbert space

The carrier is the closed subspace of `L²(ℝ, ℂ)` supported almost everywhere in
`[0,L)`. Its physical inner product is the inherited Lebesgue integral. Zero
extension is intrinsic to this realization. Translation is followed by the
interval indicator; nonnegative shifts therefore have the terminal boundary
condition at `L`, rather than periodic boundary conditions.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace Riemann.Analysis.FiniteWindow

abbrev Ambient : Type := Lp ℂ 2 (volume : Measure ℝ)

/-- Multiplication by the indicator of `[0,L)`, on actual `L²` classes. -/
def cut (L : ℝ) (f : Ambient) : Ambient :=
  ((Lp.memLp f).indicator measurableSet_Ico).toLp ((Ico 0 L).indicator f)

theorem cut_ae (L : ℝ) (f : Ambient) :
    (cut L f : ℝ → ℂ) =ᵐ[volume] (Ico 0 L).indicator f :=
  MemLp.coeFn_toLp _

theorem cut_add (L : ℝ) (f g : Ambient) : cut L (f + g) = cut L f + cut L g := by
  apply Lp.ext
  filter_upwards [cut_ae L (f + g), cut_ae L f, cut_ae L g,
    Lp.coeFn_add f g, Lp.coeFn_add (cut L f) (cut L g)] with t h h₁ h₂ h₃ h₄
  rw [h, h₄]
  simp only [Pi.add_apply]
  rw [h₁, h₂]
  by_cases ht : t ∈ Ico 0 L
  · simpa only [indicator_of_mem ht, Pi.add_apply] using h₃
  · simp only [indicator_of_notMem ht, add_zero]

theorem cut_smul (L : ℝ) (c : ℂ) (f : Ambient) : cut L (c • f) = c • cut L f := by
  apply Lp.ext
  filter_upwards [cut_ae L (c • f), cut_ae L f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (cut L f)] with t h h₁ h₂ h₃
  rw [h, h₃]
  simp only [Pi.smul_apply]
  rw [h₁]
  by_cases ht : t ∈ Ico 0 L <;> simp [ht, h₂]

theorem norm_cut_le (L : ℝ) (f : Ambient) : ‖cut L f‖ ≤ ‖f‖ := by
  rw [cut, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).2.ne (eLpNorm_indicator_le _)

/-- The contractive interval projection. -/
def cutCLM (L : ℝ) : Ambient →L[ℂ] Ambient :=
  LinearMap.mkContinuous
    { toFun := cut L, map_add' := cut_add L, map_smul' := cut_smul L }
    1 (by intro f; simpa using norm_cut_le L f)

@[simp] theorem cutCLM_apply (L : ℝ) (f : Ambient) : cutCLM L f = cut L f := rfl

theorem cut_idempotent (L : ℝ) (f : Ambient) : cut L (cut L f) = cut L f := by
  apply Lp.ext
  filter_upwards [cut_ae L (cut L f), cut_ae L f] with t h h₁
  rw [h]
  by_cases ht : t ∈ Ico 0 L <;> simp_all

/-- The closed submodule of functions with zero extension outside the window. -/
def supported (L : ℝ) : Submodule ℂ Ambient :=
  (cutCLM L - ContinuousLinearMap.id ℂ Ambient).ker

abbrev Hilbert (L : ℝ) := supported L

instance (L : ℝ) : CompleteSpace (Hilbert L) := by
  unfold Hilbert supported
  infer_instance

theorem mem_supported_iff (L : ℝ) (f : Ambient) :
    f ∈ supported L ↔ cut L f = f := by
  simp [supported, sub_eq_zero]

theorem cut_mem_supported (L : ℝ) (f : Ambient) : cut L f ∈ supported L :=
  (mem_supported_iff L _).2 (cut_idempotent L f)

/-- Restriction followed by zero extension, as a map to the supported carrier. -/
def projection (L : ℝ) : Ambient →L[ℂ] Hilbert L :=
  (cutCLM L).codRestrict (supported L) (cut_mem_supported L)

@[simp] theorem projection_coe (L : ℝ) (f : Ambient) :
    (projection L f : Ambient) = cut L f := rfl

@[simp] theorem projection_self (L : ℝ) (f : Hilbert L) : projection L f = f := by
  apply Subtype.ext
  exact (mem_supported_iff L f).1 f.property

/-- Ambient translation `f(t) ↦ f(y+t)`. -/
def translate (y : ℝ) : Ambient →L[ℂ] Ambient :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun t : ℝ => y + t)
    (measurePreserving_add_left volume y)).toContinuousLinearMap

theorem translate_eq_vadd (y : ℝ) (f : Ambient) :
    translate y f = DomAddAct.mk y +ᵥ f := rfl

theorem translate_ae (y : ℝ) (f : Ambient) :
    (translate y f : ℝ → ℂ) =ᵐ[volume] fun t => f (y + t) :=
  Lp.coeFn_compMeasurePreserving _ _

@[simp] theorem norm_translate (y : ℝ) (f : Ambient) : ‖translate y f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

/-- Killed backward translation on the genuine interval Hilbert carrier. -/
def killedShift (L : ℝ) (y : ℝ≥0) : Hilbert L →L[ℂ] Hilbert L :=
  (projection L).comp ((translate y).comp (supported L).subtypeL)

theorem norm_killedShift_apply_le (L : ℝ) (y : ℝ≥0) (f : Hilbert L) :
    ‖killedShift L y f‖ ≤ ‖f‖ := by
  change ‖cut L (translate y f)‖ ≤ ‖(f : Ambient)‖
  exact (norm_cut_le L _).trans_eq (norm_translate y f)

theorem supported_ae (L : ℝ) (f : Hilbert L) :
    ((f : Ambient) : ℝ → ℂ) =ᵐ[volume] (Ico 0 L).indicator (f : Ambient) := by
  have h := cut_ae L (f : Ambient)
  rwa [(mem_supported_iff L f).1 f.property] at h

/-- Exact killed action, including the terminal cutoff, for representatives. -/
theorem killedShift_ae (L : ℝ) (y : ℝ≥0) (f : Hilbert L) :
    (((killedShift L y f : Hilbert L) : Ambient) : ℝ → ℂ) =ᵐ[volume]
      fun t => if t ∈ Ico 0 L ∧ (y : ℝ) + t < L then (f : Ambient) (y + t) else 0 := by
  have hs := (measurePreserving_add_left volume (y : ℝ)).quasiMeasurePreserving.ae
    (supported_ae L f)
  filter_upwards [cut_ae L (translate y f), translate_ae y f, hs] with t hc ht hf
  change (cut L (translate y f) : ℝ → ℂ) t = _
  rw [hc]
  by_cases h₁ : t ∈ Ico 0 L
  · rw [indicator_of_mem h₁, ht]
    by_cases h₂ : (y : ℝ) + t < L
    · simp only [h₁, h₂, and_self, ↓reduceIte]
    · have hn : (y : ℝ) + t ∉ Ico 0 L := fun h => h₂ h.2
      simpa only [h₁, h₂, and_false, ↓reduceIte, indicator_of_notMem hn] using hf
  · simp only [indicator_of_notMem h₁, h₁, false_and, ↓reduceIte]

@[simp] theorem killedShift_zero (L : ℝ) : killedShift L 0 = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro f
  change projection L (translate 0 (f : Ambient)) = f
  rw [translate_eq_vadd]
  change projection L ((0 : ℝᵈᵃᵃ) +ᵥ (f : Ambient)) = f
  simp

theorem killedShift_add (L : ℝ) (a b : ℝ≥0) :
    (killedShift L a).comp (killedShift L b) = killedShift L (a + b) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply Lp.ext
  have hb := (measurePreserving_add_left volume (a : ℝ)).quasiMeasurePreserving.ae
    (killedShift_ae L b f)
  filter_upwards [killedShift_ae L a (killedShift L b f),
    killedShift_ae L (a + b) f, hb] with t h₁ h₂ h₃
  change (((killedShift L a (killedShift L b f)) : Ambient) : ℝ → ℂ) t =
    (((killedShift L (a + b) f) : Ambient) : ℝ → ℂ) t
  rw [h₁, h₂]
  by_cases ht : t ∈ Ico 0 L
  · by_cases ha : (a : ℝ) + t < L
    · have hat : (a : ℝ) + t ∈ Ico 0 L := ⟨add_nonneg a.2 ht.1, ha⟩
      simp only [ht, ha, and_self, ↓reduceIte, h₃, hat, true_and, NNReal.coe_add]
      congr 2 <;> ring
    · have hab : ¬((a + b : ℝ≥0) : ℝ) + t < L := by
        simp only [NNReal.coe_add]
        have hb0 : (0 : ℝ) ≤ b := b.2
        exact not_lt_of_ge (le_trans (le_of_not_gt ha) (by linarith))
      simp only [ht, ha, hab, and_false, ↓reduceIte]
  · simp only [ht, false_and, ↓reduceIte]

theorem killedShift_eq_zero (L : ℝ) (y : ℝ≥0) (hy : L ≤ (y : ℝ)) :
    killedShift L y = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [killedShift_ae L y f, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t h h₀
  change (((killedShift L y f) : Ambient) : ℝ → ℂ) t = (0 : Ambient) t
  rw [h, h₀]
  by_cases ht : t ∈ Ico 0 L
  · have hn : ¬ (y : ℝ) + t < L := by have := ht.1; linarith
    simp [ht, hn]
  · simp [ht]

theorem norm_killedShift_le (L : ℝ) (y : ℝ≥0) : ‖killedShift L y‖ ≤ 1 :=
  (killedShift L y).opNorm_le_bound zero_le_one (by
    intro f; simpa using norm_killedShift_apply_le L y f)

/-- Strong continuity is inherited from the standard translation action on `Lp`. -/
theorem continuous_killedShift_apply (L : ℝ) (f : Hilbert L) :
    Continuous (fun y : ℝ≥0 => killedShift L y f) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have h : Continuous (fun y : ℝ≥0 => DomAddAct.mk (y : ℝ) +ᵥ (f : Ambient)) :=
    (DomAddAct.continuous_mk.comp continuous_subtype_val).vadd continuous_const
  exact (projection L).continuous.comp h

/-- Real-parameter notation: negative parameters are clamped to zero. All
semigroup identities below retain their nonnegative-parameter hypotheses. -/
def shift (L y : ℝ) : Hilbert L →L[ℂ] Hilbert L := killedShift L y.toNNReal

@[simp] theorem shift_zero (L : ℝ) : shift L 0 = ContinuousLinearMap.id ℂ _ := by
  simp [shift]

theorem shift_add (L : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (shift L a).comp (shift L b) = shift L (a + b) := by
  rw [shift, shift, shift, Real.toNNReal_add ha hb, killedShift_add]

theorem shift_eq_zero (L : ℝ) {y : ℝ} (hy : L ≤ y) : shift L y = 0 :=
  killedShift_eq_zero L _ (hy.trans (Real.le_coe_toNNReal _))

theorem norm_shift_apply_le (L y : ℝ) (f : Hilbert L) : ‖shift L y f‖ ≤ ‖f‖ :=
  norm_killedShift_apply_le L _ f

theorem norm_shift_le (L y : ℝ) : ‖shift L y‖ ≤ 1 := norm_killedShift_le L _

theorem continuous_shift_apply (L : ℝ) (f : Hilbert L) :
    Continuous (fun y : ℝ => shift L y f) :=
  (continuous_killedShift_apply L f).comp continuous_real_toNNReal

end Riemann.Analysis.FiniteWindow
