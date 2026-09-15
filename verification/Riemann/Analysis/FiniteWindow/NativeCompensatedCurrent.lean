import Riemann.Analysis.FiniteWindow.NativeIntegralCoefficients

/-! # Native coordinates of compensated strong currents

The singular weight always multiplies `S_y-I` before integration. All operator
matrix entries below arise from the actual Fourier inclusion and killed shift.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace NNReal
namespace Riemann.Analysis.FiniteWindow
open Riemann.CCM.Native

/-- Pointwise native Hermitian coefficients, with the scalar subtraction retained. -/
def compensatedCoefficients (N : ℕ) (L y w d : ℝ) : Coefficients N where
  diagonal i := 2 * (w * ((1 - y / L) * Real.cos (frequency L i * y) - 1) + d)
  beta i := -w * Real.sin (frequency L i * y) / Real.pi
  diagonal_even i := by simp
  beta_odd i := by simp [mul_neg, neg_div]

/-- The actual compressed difference operator at one shift. -/
def compensatedShift (N : ℕ) (L y w d : ℝ) : Section N →L[ℂ] Section N :=
  (w : ℂ) • (nativeCompression N L (shift L y) - 1) + (d : ℂ) • 1

theorem compensatedShift_hermitian {N : ℕ} {L y : ℝ} (hL : 0 < L)
    (hy : y ∈ Icc 0 L) (w d : ℝ) :
    compensatedShift N L y w d + (compensatedShift N L y w d).adjoint =
      weilOperator (compensatedCoefficients N L y w d) := by
  have he := hermitianShift_entry (N := N) hL y.toNNReal
    (by simpa only [Real.coe_toNNReal _ hy.1] using hy.2)
  apply nativeOperator_ext_single
  intro i j
  have he' := he i j
  simp only [Real.coe_toNNReal _ hy.1] at he'
  change fourierShiftCompression N L y.toNNReal (EuclideanSpace.single j (1 : ℂ)) i +
    (fourierShiftCompression N L y.toNNReal).adjoint (EuclideanSpace.single j (1 : ℂ)) i = _ at he'
  simp only [compensatedShift, shift, nativeCompression_killedShift, map_add, map_sub,
    map_smulₛₗ, Complex.conj_ofReal, ContinuousLinearMap.adjoint_one]
  simp only [weilOperator_apply]
  change (w : ℂ) * (_ - _) + (d : ℂ) * _ +
    ((w : ℂ) * (_ - _) + (d : ℂ) * _) = _
  rw [show (w : ℂ) * (_ - _) + (d : ℂ) * _ +
      ((w : ℂ) * (_ - _) + (d : ℂ) * _) =
      (w : ℂ) * (fourierShiftCompression N L y.toNNReal (EuclideanSpace.single j (1 : ℂ)) i +
        (fourierShiftCompression N L y.toNNReal).adjoint (EuclideanSpace.single j (1 : ℂ)) i) +
        (2 * (d - w) : ℂ) * (EuclideanSpace.single j (1 : ℂ)) i by
          change (w : ℂ) * (fourierShiftCompression N L y.toNNReal (EuclideanSpace.single j 1) i - (EuclideanSpace.single j 1) i) + (d : ℂ) * (EuclideanSpace.single j 1) i +
            ((w : ℂ) * ((fourierShiftCompression N L y.toNNReal).adjoint (EuclideanSpace.single j 1) i - (EuclideanSpace.single j 1) i) + (d : ℂ) * (EuclideanSpace.single j 1) i) = _
          ring]
  rw [he']
  by_cases hij : i = j
  · subst j
    simp [weilMatrix, hermitianShiftCoefficients, compensatedCoefficients]
    ring
  · simp [weilMatrix, hij, hermitianShiftCoefficients, compensatedCoefficients]
    ring

/-- The physical Fourier inclusion is an isometry, expressed as its Gram identity. -/
theorem fourierInclusion_adjoint_comp {N : ℕ} {L : ℝ} (hL : 0 < L) :
    (fourierInclusion N L).adjoint.comp (fourierInclusion N L) = 1 := by
  apply (fourierInclusion N L).inner_map_map_iff_adjoint_comp_self.mp
  intro x z
  exact fourierHilbert_inner hL x z

/-- A compensated orbit remains a strong Hilbert-space vector integrand. -/
def compensatedOrbit {N : ℕ} (L : ℝ) (w d : ℝ → ℝ) (x : Section N) (y : ℝ) : Hilbert L :=
  (w y : ℂ) • (shift L y (fourierHilbert L x) - fourierHilbert L x) +
    (d y : ℂ) • fourierHilbert L x

theorem compensatedOrbit_compression {N : ℕ} {L : ℝ} (hL : 0 < L)
    (w d : ℝ → ℝ) (x : Section N) (y : ℝ) :
    (fourierInclusion N L).adjoint (compensatedOrbit L w d x y) =
      compensatedShift N L y (w y) (d y) x := by
  have hi := congrArg (fun T : Section N →L[ℂ] Section N => T x)
    (fourierInclusion_adjoint_comp (N := N) hL)
  simp only [ContinuousLinearMap.comp_apply, fourierInclusion_apply] at hi
  simp only [compensatedOrbit, map_add, map_smul, map_sub, hi]
  rfl

/-- Every compressed entry is integrable by a bounded coordinate observation. -/
theorem compensatedShift_entry_integrable {N : ℕ} {L : ℝ} (hL : 0 < L)
    (w d : ℝ → ℝ)
    (hf : ∀ x : Section N, IntegrableOn (compensatedOrbit L w d x) (Ioo 0 L))
    (i j : Index N) :
    IntegrableOn (fun y => compensatedShift N L y (w y) (d y)
      (EuclideanSpace.single j (1 : ℂ)) i) (Ioo 0 L) := by
  have hh := ((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Index N => ℂ) i).comp
    (fourierInclusion N L).adjoint).integrable_comp (hf (EuclideanSpace.single j 1))
  unfold IntegrableOn
  convert hh using 1 <;> try rfl
  funext y
  simp only [ContinuousLinearMap.comp_apply, compensatedOrbit_compression hL]
  rfl

/-- Coefficient integrability follows from the actual compensated strong orbits. -/
theorem compensatedCoefficients_integrable {N : ℕ} {L : ℝ} (hL : 0 < L)
    (w d : ℝ → ℝ)
    (hf : ∀ x : Section N, IntegrableOn (compensatedOrbit L w d x) (Ioo 0 L)) :
    (∀ i, IntegrableOn (fun y => (compensatedCoefficients N L y (w y) (d y)).diagonal i) (Ioo 0 L)) ∧
    (∀ i, IntegrableOn (fun y => (compensatedCoefficients N L y (w y) (d y)).beta i) (Ioo 0 L)) := by
  apply integrable_coefficients_of_entries (volume.restrict (Ioo 0 L))
    (fun y => compensatedCoefficients N L y (w y) (d y))
  · intro y
    simp [compensatedCoefficients, frequency]
  · intro i j
    have hi := compensatedShift_entry_integrable hL w d hf i j
    have hj := Complex.conjCLE.toContinuousLinearMap.integrable_comp
      (compensatedShift_entry_integrable hL w d hf j i)
    apply (hi.add hj).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have he := congrArg (fun T : Section N →L[ℂ] Section N => T (EuclideanSpace.single j 1) i)
      (compensatedShift_hermitian (N := N) hL ⟨hy.1.le, hy.2.le⟩ (w y) (d y))
    change _ + (compensatedShift N L y (w y) (d y)).adjoint (EuclideanSpace.single j 1) i = _ at he
    rw [adjoint_single_entry] at he
    simpa [weilOperator_apply] using he

/-- Integration is strong and per vector; continuity follows only after finite compression. -/
def compensatedIntegral {N : ℕ} (L : ℝ) (w d : ℝ → ℝ)
    (hf : ∀ x : Section N, IntegrableOn (compensatedOrbit L w d x) (Ioo 0 L)) :
    Section N →L[ℂ] Section N :=
  LinearMap.toContinuousLinearMap
    { toFun x := (fourierInclusion N L).adjoint (∫ y in Ioo 0 L, compensatedOrbit L w d x y)
      map_add' x z := by
        have he : compensatedOrbit L w d (x + z) =
            fun y => compensatedOrbit L w d x y + compensatedOrbit L w d z y := by
          funext y
          simp only [compensatedOrbit, ← fourierInclusion_apply, map_add]
          module
        rw [he, integral_add (hf x) (hf z), map_add]
      map_smul' a x := by
        have he : compensatedOrbit L w d (a • x) =
            fun y => a • compensatedOrbit L w d x y := by
          funext y
          simp only [compensatedOrbit, ← fourierInclusion_apply, map_smul]
          module
        rw [he, integral_smul, map_smul]
        rfl }

/-- Each finite entry is the scalar integral of its actual compressed shift entry. -/
theorem compensatedIntegral_entry {N : ℕ} {L : ℝ} (hL : 0 < L)
    (w d : ℝ → ℝ)
    (hf : ∀ x : Section N, IntegrableOn (compensatedOrbit L w d x) (Ioo 0 L))
    (i j : Index N) :
    compensatedIntegral L w d hf (EuclideanSpace.single j (1 : ℂ)) i =
      ∫ y in Ioo 0 L, compensatedShift N L y (w y) (d y) (EuclideanSpace.single j (1 : ℂ)) i := by
  have hh := ((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Index N => ℂ) i).comp
    (fourierInclusion N L).adjoint).integral_comp_comm (hf (EuclideanSpace.single j 1))
  change _ = (fourierInclusion N L).adjoint
    (∫ y in Ioo 0 L, compensatedOrbit L w d (EuclideanSpace.single j 1) y) i at hh
  rw [show compensatedIntegral L w d hf (EuclideanSpace.single j 1) i =
    (fourierInclusion N L).adjoint
      (∫ y in Ioo 0 L, compensatedOrbit L w d (EuclideanSpace.single j 1) y) i from rfl, ← hh]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [ContinuousLinearMap.comp_apply, compensatedOrbit_compression hL]
    rfl

/-- Actual Hermitian current compression equals the integrated native coefficients. -/
theorem compensatedIntegral_weilOperator {N : ℕ} {L : ℝ} (hL : 0 < L)
    (w d : ℝ → ℝ)
    (hf : ∀ x : Section N, IntegrableOn (compensatedOrbit L w d x) (Ioo 0 L)) :
    compensatedIntegral L w d hf + (compensatedIntegral L w d hf).adjoint =
      weilOperator (integralCoefficients (volume.restrict (Ioo 0 L))
        (fun y => compensatedCoefficients N L y (w y) (d y))) := by
  have hc := compensatedCoefficients_integrable hL w d hf
  apply nativeOperator_ext_single
  intro i j
  change compensatedIntegral L w d hf (EuclideanSpace.single j 1) i +
    (compensatedIntegral L w d hf).adjoint (EuclideanSpace.single j 1) i = _
  rw [adjoint_single_entry, compensatedIntegral_entry hL, compensatedIntegral_entry hL]
  change _ + (starRingEnd ℂ) _ = _
  have hj := Complex.conjCLE.toContinuousLinearMap.integrable_comp
    (compensatedShift_entry_integrable hL w d hf j i)
  change Integrable (fun y => (starRingEnd ℂ) (compensatedShift N L y (w y) (d y)
    (EuclideanSpace.single i 1) j)) (volume.restrict (Ioo 0 L)) at hj
  rw [← integral_conj, ← integral_add (compensatedShift_entry_integrable hL w d hf i j) hj]
  have hr : weilOperator (integralCoefficients (volume.restrict (Ioo 0 L))
      (fun y => compensatedCoefficients N L y (w y) (d y))) (EuclideanSpace.single j 1) i =
      ∫ y in Ioo 0 L, weilMatrix (compensatedCoefficients N L y (w y) (d y)) i j := by
    simp only [weilOperator_apply]
    simp only [PiLp.single_apply]
    simpa [weilOperator_apply] using
      (weilMatrix_integralCoefficients (volume.restrict (Ioo 0 L))
        (fun y => compensatedCoefficients N L y (w y) (d y)) hc.2 i j)
  rw [hr]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have he := congrArg (fun T : Section N →L[ℂ] Section N => T (EuclideanSpace.single j 1) i)
    (compensatedShift_hermitian (N := N) hL ⟨hy.1.le, hy.2.le⟩ (w y) (d y))
  change _ + (compensatedShift N L y (w y) (d y)).adjoint (EuclideanSpace.single j 1) i = _ at he
  rw [adjoint_single_entry] at he
  simpa [weilOperator_apply] using he

end Riemann.Analysis.FiniteWindow
