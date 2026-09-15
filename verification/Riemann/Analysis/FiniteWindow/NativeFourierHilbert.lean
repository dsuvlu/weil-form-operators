import Riemann.Analysis.FiniteWindow.GeneratorDomain
import Riemann.CCM.FourierSection

/-! # Literal Hilbert realization of the frozen native Fourier section

The polynomial and its frequencies are the existing native definitions. The
constant Fourier mode and the admitted arithmetic ground are not identified by assumption.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace Riemann.Analysis.FiniteWindow

lemma memLp_cut_continuous (L : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    MemLp ((Ico 0 L).indicator f) 2 volume := by
  apply (memLp_indicator_iff_restrict measurableSet_Ico).2
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound (hf.aestronglyMeasurable) C
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  exact hC t (Icc_subset_uIcc ⟨ht.1, ht.2.le⟩)

/-- Supported L² class of a continuous function on the finite interval. -/
def ofContinuous (L : ℝ) (f : ℝ → ℂ) (hf : Continuous f) : Hilbert L :=
  projection L ((memLp_cut_continuous L hf).toLp ((Ico 0 L).indicator f))

lemma ofContinuous_ae (L : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    ((ofContinuous L f hf : Ambient) : ℝ → ℂ) =ᵐ[volume] (Ico 0 L).indicator f := by
  filter_upwards [cut_ae L ((memLp_cut_continuous L hf).toLp ((Ico 0 L).indicator f)),
    (memLp_cut_continuous L hf).coeFn_toLp] with t ht hg
  change (cut L ((memLp_cut_continuous L hf).toLp ((Ico 0 L).indicator f))) t = _
  rw [ht]
  by_cases hm : t ∈ Ico 0 L <;> simp [hm, hg]

open Riemann.CCM.Native

lemma continuous_nativeFourier {N : ℕ} (L : ℝ) (x : Section N) :
    Continuous (fourierFunction L x) := by unfold fourierFunction; fun_prop

lemma contDiff_nativeFourier {N : ℕ} (L : ℝ) (x : Section N) :
    ContDiff ℝ ⊤ (fourierFunction L x) := by
  have hreal : ContDiff ℝ ⊤ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  unfold fourierFunction
  fun_prop

/-- The existing native polynomial, realized in the actual interval Hilbert space. -/
def fourierHilbert {N : ℕ} (L : ℝ) (x : Section N) : Hilbert L :=
  ofContinuous L (fourierFunction L x) (continuous_nativeFourier L x)

lemma fourierHilbert_ae {N : ℕ} (L : ℝ) (x : Section N) :
    ((fourierHilbert L x : Ambient) : ℝ → ℂ) =ᵐ[volume]
      (Ico 0 L).indicator (fourierFunction L x) :=
  ofContinuous_ae _ _ _

/-- Linear native Fourier synthesis into the supported interval Hilbert space. -/
def fourierInclusionLinearMap (N : ℕ) (L : ℝ) : Section N →ₗ[ℂ] Hilbert L where
  toFun := fourierHilbert L
  map_add' x y := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [fourierHilbert_ae L (x+y), fourierHilbert_ae L x,
      fourierHilbert_ae L y,
      Lp.coeFn_add (fourierHilbert L x : Ambient) (fourierHilbert L y : Ambient)]
      with t hxy hx hy ha
    have he : ((fourierHilbert L x + fourierHilbert L y : Hilbert L) : Ambient) =
      (fourierHilbert L x : Ambient) + (fourierHilbert L y : Ambient) := rfl
    rw [he, hxy, ha, Pi.add_apply, hx, hy]
    by_cases ht : t ∈ Ico 0 L
    · simp [ht, fourierFunction, add_mul, Finset.sum_add_distrib]
    · simp [ht]
  map_smul' c x := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [fourierHilbert_ae L (c • x), fourierHilbert_ae L x,
      Lp.coeFn_smul c (fourierHilbert L x : Ambient)] with t hcx hx hc
    have he : ((c • fourierHilbert L x : Hilbert L) : Ambient) =
      c • (fourierHilbert L x : Ambient) := rfl
    rw [RingHom.id_apply, he, hcx, hc, Pi.smul_apply, hx]
    by_cases ht : t ∈ Ico 0 L
    · simp [ht, fourierFunction, smul_eq_mul, mul_assoc, Finset.mul_sum]
    · simp [ht]

/-- The finite-dimensional coefficient map is continuous in the physical norm. -/
def fourierInclusion (N : ℕ) (L : ℝ) : Section N →L[ℂ] Hilbert L :=
  (fourierInclusionLinearMap N L).toContinuousLinearMap

@[simp] theorem fourierInclusion_apply {N : ℕ} (L : ℝ) (x : Section N) :
    fourierInclusion N L x = fourierHilbert L x := rfl

/-- Differentiation of the actual polynomial is `i` times the native physical derivative. -/
theorem hasDerivAt_nativeFourier {N : ℕ} (L : ℝ) (x : Section N) (t : ℝ) :
    HasDerivAt (fourierFunction L x)
      (fourierFunction L (Complex.I • derivative L x) t) t := by
  have hd (i : Index N) : HasDerivAt
      (fun t : ℝ => x i * ((Real.sqrt L)⁻¹ : ℂ) *
        Complex.exp (Complex.I * ((frequency L i : ℂ) * (t : ℂ))))
      ((x i * ((Real.sqrt L)⁻¹ : ℂ)) *
        (Complex.exp (Complex.I * ((frequency L i : ℂ) * (t : ℂ))) *
          (Complex.I * (frequency L i : ℂ)))) t := by
    simpa using ((((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul
      (frequency L i : ℂ)).const_mul Complex.I).cexp.const_mul
        (x i * ((Real.sqrt L)⁻¹ : ℂ)))
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ => hd i)
  convert h using 1
  all_goals try rfl
  · funext u
    simp only [fourierFunction, Finset.sum_apply]
  · simp only [fourierFunction, PiLp.smul_apply, smul_eq_mul, derivative_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Endpoint-zero native Fourier vectors belong to the actual generator domain. -/
theorem nativeFourier_hasGenerator {N : ℕ} {L : ℝ} (hL : 0 < L) (x : Section N)
    (hx : endpoint N L x = 0) :
    HasGenerator L (fourierHilbert L x)
      (fourierHilbert L (Complex.I • derivative L x)) := by
  apply (hasGenerator_iff_hasACDerivative hL.le _ _).2
  refine ⟨fourierFunction L x,
    ((contDiff_nativeFourier L x).of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval,
    ?_, fourierHilbert_ae L x, ?_⟩
  · rw [fourierFunction_end hL]
    exact hx
  · have hEnd : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ L := by simp [ae_iff]
    filter_upwards [fourierHilbert_ae L (Complex.I • derivative L x),
      hEnd] with t ht hEnd hmem
    have hm : t ∈ Ico 0 L := by
      rw [uIcc_of_le hL.le] at hmem
      exact ⟨hmem.1, lt_of_le_of_ne hmem.2 hEnd⟩
    rw [ht, indicator_of_mem hm]
    exact hasDerivAt_nativeFourier L x t

end Riemann.Analysis.FiniteWindow
