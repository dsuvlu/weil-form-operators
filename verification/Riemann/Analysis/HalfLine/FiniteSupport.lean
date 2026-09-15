import Riemann.Analysis.HalfLine.Hilbert
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Physical finite-window embeddings and compact-support domain -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace Riemann.Analysis.HalfLine

/-- Every old finite-window vector is literally a half-line vector. -/
theorem finite_supported (L : ℝ) (f : FiniteWindow.Hilbert L) :
    (f : Ambient) ∈ supported := by
  rw [mem_supported_iff]
  apply Lp.ext
  filter_upwards [cut_ae (f : Ambient), FiniteWindow.supported_ae L f] with t hc hf
  rw [hc]
  by_cases ht : 0 ≤ t
  · simp [ht]
  · have hn : t ∉ Ico 0 L := fun h => ht h.1
    simp only [mem_Ici, ht, not_false_eq_true, indicator_of_notMem] at *
    rw [indicator_of_notMem hn] at hf
    exact hf.symm

/-- Zero extension is an isometry for the unchanged physical L² norm. -/
def finiteInclusion (L : ℝ) : FiniteWindow.Hilbert L →ₗᵢ[ℂ] Hilbert where
  toLinearMap :=
    { toFun f := ⟨f, finite_supported L f⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  norm_map' _ := rfl

@[simp] theorem finiteInclusion_coe (L : ℝ) (f : FiniteWindow.Hilbert L) :
    (finiteInclusion L f : Ambient) = f := rfl

/-- Actual interval restriction, with codomain the frozen finite-window carrier. -/
def finiteProjection (L : ℝ) : Hilbert →L[ℂ] FiniteWindow.Hilbert L :=
  (FiniteWindow.projection L).comp supported.subtypeL

@[simp] theorem finiteProjection_inclusion (L : ℝ) (f : FiniteWindow.Hilbert L) :
    finiteProjection L (finiteInclusion L f) = f := FiniteWindow.projection_self L f

/-- Physical support truncation, not a periodic Fourier projection. -/
def supportProjection (L : ℝ) : Hilbert →L[ℂ] Hilbert :=
  (finiteInclusion L).toContinuousLinearMap.comp (finiteProjection L)

@[simp] theorem supportProjection_coe (L : ℝ) (f : Hilbert) :
    (supportProjection L f : Ambient) = FiniteWindow.cut L f := rfl

@[simp] theorem supportProjection_idempotent (L : ℝ) (f : Hilbert) :
    supportProjection L (supportProjection L f) = supportProjection L f := by
  change finiteInclusion L (finiteProjection L (finiteInclusion L (finiteProjection L f))) = _
  rw [finiteProjection_inclusion]
  rfl

theorem norm_supportProjection_apply_le (L : ℝ) (f : Hilbert) :
    ‖supportProjection L f‖ ≤ ‖f‖ := FiniteWindow.norm_cut_le L f

theorem norm_supportProjection_le (L : ℝ) : ‖supportProjection L‖ ≤ 1 :=
  (supportProjection L).opNorm_le_bound zero_le_one
    (fun f => by simpa using norm_supportProjection_apply_le L f)

/-- Exact shift restriction on the physical finite interval. -/
theorem killedShift_finiteInclusion (L : ℝ) (y : ℝ≥0) (f : FiniteWindow.Hilbert L) :
    killedShift y (finiteInclusion L f) = finiteInclusion L (FiniteWindow.killedShift L y f) := by
  apply Subtype.ext
  apply Lp.ext
  have hs := (measurePreserving_add_left volume (y : ℝ)).quasiMeasurePreserving.ae
    (FiniteWindow.supported_ae L f)
  filter_upwards [killedShift_ae y (finiteInclusion L f), FiniteWindow.killedShift_ae L y f, hs]
    with t hh hf hs
  change ((killedShift y (finiteInclusion L f) : Ambient) : ℝ → ℂ) t =
    ((FiniteWindow.killedShift L y f : Ambient) : ℝ → ℂ) t
  rw [hh, hf]
  by_cases ht : 0 ≤ t
  · by_cases hy : (y : ℝ) + t < L
    · have htm : t ∈ Ico 0 L := ⟨ht, lt_of_le_of_lt (le_add_of_nonneg_left y.2) hy⟩
      simp [ht, hy, htm]
    · have hnm : (y : ℝ) + t ∉ Ico 0 L := fun h => hy h.2
      have hzero : (f : Ambient) ((y : ℝ) + t) = 0 := by simpa [hnm] using hs
      simp [ht, hy, hzero]
  · have htm : t ∉ Ico 0 L := fun h => ht h.1
    simp [ht, htm]

theorem shift_finiteInclusion (L y : ℝ) (f : FiniteWindow.Hilbert L) :
    shift y (finiteInclusion L f) = finiteInclusion L (FiniteWindow.shift L y f) :=
  killedShift_finiteInclusion L y.toNNReal f

theorem shift_finiteInclusion_eq_zero (L : ℝ) {y : ℝ} (hy : L ≤ y)
    (f : FiniteWindow.Hilbert L) : shift y (finiteInclusion L f) = 0 := by
  rw [shift_finiteInclusion, FiniteWindow.shift_eq_zero L hy]
  simp

/-- Exact finite support expressed without choosing a preferred cutoff. -/
def HasFiniteSupport (f : Hilbert) : Prop :=
  ∃ L : ℝ, 0 < L ∧ (f : Ambient) ∈ FiniteWindow.supported L

theorem finite_support_mono {L M : ℝ} (hLM : L ≤ M) (f : Ambient)
    (hf : f ∈ FiniteWindow.supported L) : f ∈ FiniteWindow.supported M := by
  rw [FiniteWindow.mem_supported_iff]
  apply Lp.ext
  filter_upwards [FiniteWindow.cut_ae M f, FiniteWindow.supported_ae L ⟨f, hf⟩] with t hm hl
  rw [hm]
  by_cases ht : t ∈ Ico 0 M
  · simp [ht]
  · have hn : t ∉ Ico 0 L := fun h => ht ⟨h.1, h.2.trans_le hLM⟩
    simpa [ht, hn] using hl.symm

/-- The algebraic domain is the union of the actual positive finite windows. -/
def compactSupport : Submodule ℂ Hilbert where
  carrier := HasFiniteSupport
  zero_mem' := ⟨1, zero_lt_one, (FiniteWindow.supported 1).zero_mem⟩
  add_mem' := by
    rintro f g ⟨L, hL, hf⟩ ⟨M, hM, hg⟩
    exact ⟨max L M, hL.trans_le (le_max_left _ _),
      (FiniteWindow.supported (max L M)).add_mem
        (finite_support_mono (le_max_left _ _) f hf)
        (finite_support_mono (le_max_right _ _) g hg)⟩
  smul_mem' := by
    rintro a f ⟨L, hL, hf⟩
    exact ⟨L, hL, (FiniteWindow.supported L).smul_mem a hf⟩

def finiteCoreInclusion (L : ℝ) (hL : 0 < L) : FiniteWindow.Hilbert L →ₗ[ℂ] compactSupport :=
  (finiteInclusion L).toLinearMap.codRestrict compactSupport
    (fun f => ⟨L, hL, f.property⟩)

@[simp] theorem finiteCoreInclusion_coe (L : ℝ) (hL : 0 < L) (f : FiniteWindow.Hilbert L) :
    (finiteCoreInclusion L hL f : Hilbert) = finiteInclusion L f := rfl

theorem compactSupport_representation (f : compactSupport) :
    ∃ (L : ℝ) (hL : 0 < L) (g : FiniteWindow.Hilbert L),
      f = finiteCoreInclusion L hL g := by
  obtain ⟨L, hL, hf⟩ := f.property
  exact ⟨L, hL, ⟨f, hf⟩, rfl⟩

/-- Physical L² norm as an integral of the squared pointwise modulus. -/
theorem ambient_norm_sq (f : Ambient) : ‖f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f (𝕜 := ℂ))]
  simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]

theorem supportProjection_sub_norm_sq (L : ℝ) (f : Hilbert) :
    ‖supportProjection L f - f‖ ^ 2 =
      ∫ t, (Ici L).indicator (fun t => ‖(f : Ambient) t‖ ^ 2) t := by
  change ‖(supportProjection L f : Ambient) - (f : Ambient)‖ ^ 2 = _
  rw [ambient_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (supportProjection L f : Ambient) (f : Ambient),
    FiniteWindow.cut_ae L (f : Ambient), supported_ae f] with t hs hc hf
  rw [hs]
  change ‖FiniteWindow.cut L (f : Ambient) t - (f : Ambient) t‖ ^ 2 = _
  rw [hc]
  by_cases ht : 0 ≤ t
  · by_cases hL : t < L
    · simp [mem_Ico, ht, hL, not_le.mpr hL]
    · simp [mem_Ico, ht, hL, le_of_not_gt hL]
  · have hf0 : (f : Ambient) t = 0 := by simpa [ht] using hf
    by_cases hm : t ∈ Ici L <;> simp [mem_Ico, ht, hf0, hm]

/-- Increasing physical support cutoffs converge strongly to the identity. -/
theorem supportProjection_tendsto (f : Hilbert) :
    Tendsto (fun n : ℕ => supportProjection (n : ℝ) f) atTop (𝓝 f) := by
  have hi : Integrable (fun t => ‖(f : Ambient) t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (f : Ambient))).mp
      (Lp.memLp (f : Ambient))
  have ht := tendsto_integral_of_dominated_convergence
    (fun t => ‖(f : Ambient) t‖ ^ 2)
    (F := fun n : ℕ => (Ici (n : ℝ)).indicator (fun t => ‖(f : Ambient) t‖ ^ 2))
    (fun n : ℕ => hi.aestronglyMeasurable.indicator measurableSet_Ici) hi
    (fun n : ℕ => ae_of_all _ (fun t => by
      by_cases h : t ∈ Ici (n : ℝ) <;> simp [h]))
    (f := fun _ : ℝ => (0 : ℝ)) (ae_of_all _ (fun t => by
      apply tendsto_const_nhds.congr'
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop t)] with n hn
      simp [not_le.mpr hn]))
  have hn : Tendsto (fun n : ℕ => ‖supportProjection (n : ℝ) f - f‖) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n : ℕ => ‖supportProjection (n : ℝ) f - f‖ ^ 2)
        atTop (𝓝 0) := by
      simpa only [supportProjection_sub_norm_sq, integral_zero] using ht
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    change Tendsto (fun n : ℕ => Real.sqrt (‖supportProjection (n : ℝ) f - f‖ ^ 2))
      atTop (𝓝 (Real.sqrt 0)) at ht
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- The raw arithmetic domain is dense in the actual half-line Hilbert space. -/
theorem compactSupport_dense : Dense (compactSupport : Set Hilbert) := by
  intro f
  apply mem_closure_of_tendsto (supportProjection_tendsto f)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact ⟨n, by exact_mod_cast hn, (finiteProjection (n : ℝ) f).property⟩

end Riemann.Analysis.HalfLine
