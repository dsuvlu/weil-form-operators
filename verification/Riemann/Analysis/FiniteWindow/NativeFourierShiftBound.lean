import Riemann.Analysis.FiniteWindow.NativeShiftEntries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # The terminal-strip estimate for actual native Fourier vectors

These vectors need not satisfy the absorbing endpoint condition. The square-root
term records the terminal strip and is proved in the physical L² norm.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace NNReal
namespace Riemann.Analysis.FiniteWindow
open Riemann.CCM.Native

theorem norm_fourier_single {N : ℕ} {L : ℝ} (hL : 0 < L) (i : Index N) :
    ‖fourierHilbert L (EuclideanSpace.single i (1 : ℂ))‖ = 1 := by
  change ‖fourierIsometry N hL (EuclideanSpace.single i (1 : ℂ))‖ = 1
  rw [LinearIsometry.norm_map]
  simp

theorem norm_nativeMode {N : ℕ} {L : ℝ} (_hL : 0 < L) (i : Index N) (t : ℝ) :
    ‖((Real.sqrt L)⁻¹ : ℂ) * Complex.exp (Complex.I * (frequency L i * t))‖ =
      (Real.sqrt L)⁻¹ := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg L)]
  simp [Complex.norm_exp, Complex.mul_re]

/-- A killed unit Fourier mode loses exactly the terminal strip's physical mass. -/
theorem norm_killed_fourier_single_sq {N : ℕ} {L : ℝ} (hL : 0 < L)
    (y : ℝ≥0) (hy : (y : ℝ) ≤ L) (i : Index N) :
    ‖killedShift L y (fourierHilbert L (EuclideanSpace.single i (1 : ℂ)))‖ ^ 2 =
      (L - (y : ℝ)) / L := by
  let u := fourierHilbert L (EuclideanSpace.single i (1 : ℂ))
  have hu := fourierHilbert_ae L (EuclideanSpace.single i (1 : ℂ))
  have hu' := (measurePreserving_add_left volume (y : ℝ)).quasiMeasurePreserving.ae hu
  have hi : ⟪killedShift L y u, killedShift L y u⟫_ℂ =
      (((L - (y : ℝ)) * (Real.sqrt L)⁻¹ ^ 2 : ℝ) : ℂ) := by
    change ⟪(killedShift L y u : Ambient), (killedShift L y u : Ambient)⟫_ℂ = _
    rw [L2.inner_def]
    calc
      _ = ∫ t, (Ico 0 (L - (y : ℝ))).indicator
          (fun _ => (((Real.sqrt L)⁻¹ ^ 2 : ℝ) : ℂ)) t := by
        apply integral_congr_ae
        filter_upwards [killedShift_ae L y u, hu'] with t hs ht
        rw [hs]
        by_cases hm : t ∈ Ico 0 (L - (y : ℝ))
        · have htL : t ∈ Ico 0 L := ⟨hm.1, lt_of_lt_of_le hm.2 (sub_le_self L y.2)⟩
          have hyt : (y : ℝ) + t < L := by linarith [hm.2]
          have hytL : (y : ℝ) + t ∈ Ico 0 L := ⟨add_nonneg y.2 hm.1, hyt⟩
          simp only [htL, hyt, and_self, ↓reduceIte, indicator_of_mem hm]
          change ⟪(fourierHilbert L (EuclideanSpace.single i (1 : ℂ)) : Ambient) (y+t),
            (fourierHilbert L (EuclideanSpace.single i (1 : ℂ)) : Ambient) (y+t)⟫_ℂ = _
          rw [ht, indicator_of_mem hytL, fourierFunction_single, inner_self_eq_norm_sq_to_K,
            norm_nativeMode hL]
          simp
        · have hn : ¬(t ∈ Ico 0 L ∧ (y : ℝ) + t < L) := by
            intro h
            exact hm ⟨h.1.1, by linarith [h.2]⟩
          simp only [hn, ↓reduceIte, inner_zero_left, indicator_of_notMem hm]
      _ = _ := by
        rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (sub_nonneg.mpr hy)]
        simp [Complex.real_smul]
  have hr := congrArg Complex.re hi
  change RCLike.re ⟪killedShift L y u, killedShift L y u⟫_ℂ = _ at hr
  rw [inner_self_eq_norm_sq] at hr
  simp only [Complex.ofReal_re] at hr
  have hs : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hL.le
  change ‖killedShift L y u‖ ^ 2 = _
  rw [hr, inv_pow, hs, div_eq_mul_inv]

/-- The phase change and the lost terminal strip give the exact native mode bound. -/
theorem norm_killed_fourier_single_sub_le {N : ℕ} {L : ℝ} (hL : 0 < L)
    (y : ℝ≥0) (hy : (y : ℝ) ≤ L) (i : Index N) :
    ‖killedShift L y (fourierHilbert L (EuclideanSpace.single i (1 : ℂ))) -
      fourierHilbert L (EuclideanSpace.single i (1 : ℂ))‖ ≤
      |frequency L i| * (y : ℝ) + Real.sqrt ((y : ℝ) / L) := by
  let u := fourierHilbert L (EuclideanSpace.single i (1 : ℂ))
  let c : ℂ := Complex.exp (Complex.I * (frequency L i * (y : ℝ)))
  let r : ℝ := (L - (y : ℝ)) / L
  have hr0 : 0 ≤ r := div_nonneg (sub_nonneg.mpr hy) hL.le
  have hr1 : r ≤ 1 := (div_le_one hL).mpr (sub_le_self L y.2)
  have hstrip : 1 - r = (y : ℝ) / L := by dsimp [r]; field_simp; ring
  have hu : ‖u‖ = 1 := norm_fourier_single hL i
  have hw : ‖killedShift L y u‖ ^ 2 = r := norm_killed_fourier_single_sq hL y hy i
  have hc : ‖c‖ = 1 := by simp [c, Complex.norm_exp, Complex.mul_re]
  have hip : ⟪u, killedShift L y u⟫_ℂ = (r : ℂ) * c := by
    have he := fourierShiftCompression_entry_explicit hL y hy i i
    rw [fourierShiftCompression_entry] at he
    change ⟪u, killedShift L y u⟫_ℂ = _ at he
    rw [he]
    simp only [↓reduceIte]
    dsimp [r, c]
    push_cast
    ring
  have hd : ‖killedShift L y u - u‖ ^ 2 = r * ‖c - 1‖ ^ 2 + (1 - r) := by
    have he := norm_sub_sq (𝕜 := ℂ) c 1
    simp only [hc, one_pow, norm_one, RCLike.inner_apply, one_mul] at he
    have he' : ‖c - 1‖ ^ 2 = 1 - 2 * c.re + 1 := by
      simpa only [RCLike.re_to_complex, Complex.conj_re] using he
    rw [norm_sub_sq (𝕜 := ℂ), hw, hu, one_pow, inner_re_symm, hip]
    change r - 2 * ((r : ℂ) * c).re + 1 = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [he']
    ring
  have hp : ‖c - 1‖ ≤ |frequency L i| * (y : ℝ) := by
    have he := Real.norm_exp_I_mul_ofReal_sub_one_le (x := frequency L i * (y : ℝ))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ y from y.2)] at he
    simpa only [c, Complex.ofReal_mul] using he
  have hsq : ‖killedShift L y u - u‖ ^ 2 ≤
      (|frequency L i| * (y : ℝ)) ^ 2 + (y : ℝ) / L := by
    rw [hd, hstrip]
    have h₁ : r * ‖c - 1‖ ^ 2 ≤ ‖c - 1‖ ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) hr1
    have h₂ : ‖c - 1‖ ^ 2 ≤ (|frequency L i| * (y : ℝ)) ^ 2 :=
      sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) y.2) |>.2 hp
    linarith
  have hs : Real.sqrt ((y : ℝ) / L) ^ 2 = (y : ℝ) / L :=
    Real.sq_sqrt (div_nonneg (show (0 : ℝ) ≤ y from y.2) hL.le)
  have hs0 := Real.sqrt_nonneg ((y : ℝ) / L)
  have hp0 : 0 ≤ |frequency L i| * (y : ℝ) := mul_nonneg (abs_nonneg _) y.2
  change ‖killedShift L y u - u‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg hp0 hs0)).mp
  have hadd (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by
    nlinarith [mul_nonneg ha hb]
  exact hsq.trans (by nlinarith only [hs, hadd _ _ hp0 hs0])

theorem fourierHilbert_eq_sum_single {N : ℕ} (L : ℝ) (x : Section N) :
    fourierHilbert L x = ∑ i, x i • fourierHilbert L (EuclideanSpace.single i (1 : ℂ)) := by
  have hx : x = ∑ i, x i • EuclideanSpace.single i (1 : ℂ) := by
    ext j
    simp [Pi.single_apply]
  have he := congrArg (fourierInclusion N L) hx
  simpa only [map_sum, map_smul, fourierInclusion_apply] using he

/-- The finite polynomial estimate is proved from its actual signed Fourier expansion. -/
theorem norm_killed_fourier_sub_le {N : ℕ} {L : ℝ} (hL : 0 < L)
    (y : ℝ≥0) (hy : (y : ℝ) ≤ L) (x : Section N) :
    ‖killedShift L y (fourierHilbert L x) - fourierHilbert L x‖ ≤
      ∑ i, ‖x i‖ * (|frequency L i| * (y : ℝ) + Real.sqrt ((y : ℝ) / L)) := by
  rw [fourierHilbert_eq_sum_single L x, map_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖killedShift L y (x i • fourierHilbert L (EuclideanSpace.single i (1 : ℂ))) -
        x i • fourierHilbert L (EuclideanSpace.single i (1 : ℂ))‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, ← smul_sub, norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_killed_fourier_single_sub_le hL y hy i) (norm_nonneg _)

/-- An explicit finite native constant for the square-root translation modulus. -/
def fourierShiftConstant {N : ℕ} (L : ℝ) (x : Section N) : ℝ :=
  ∑ i, ‖x i‖ * (|frequency L i| * Real.sqrt L + (Real.sqrt L)⁻¹)

theorem fourierShiftConstant_nonneg {N : ℕ} (L : ℝ) (x : Section N) :
    0 ≤ fourierShiftConstant L x := by
  apply Finset.sum_nonneg
  intro i _
  positivity

/-- Full native Fourier vectors satisfy the required square-root modulus,
including those outside the absorbing generator domain. -/
theorem norm_killed_fourier_sub_le_sqrt {N : ℕ} {L : ℝ} (hL : 0 < L)
    (y : ℝ≥0) (hy : (y : ℝ) ≤ L) (x : Section N) :
    ‖killedShift L y (fourierHilbert L x) - fourierHilbert L x‖ ≤
      fourierShiftConstant L x * Real.sqrt (y : ℝ) := by
  have hy0 : (0 : ℝ) ≤ y := y.2
  have hys : Real.sqrt (y : ℝ) ≤ Real.sqrt L := Real.sqrt_le_sqrt hy
  have hyy : (y : ℝ) ≤ Real.sqrt L * Real.sqrt (y : ℝ) := by
    calc
      _ = Real.sqrt (y : ℝ) * Real.sqrt (y : ℝ) := (Real.mul_self_sqrt hy0).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hys (Real.sqrt_nonneg _)
  apply (norm_killed_fourier_sub_le hL y hy x).trans
  unfold fourierShiftConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hphase := mul_le_mul_of_nonneg_left hyy (abs_nonneg (frequency L i))
  have hs : Real.sqrt ((y : ℝ) / L) = (Real.sqrt L)⁻¹ * Real.sqrt (y : ℝ) := by
    rw [Real.sqrt_div hy0, div_eq_mul_inv, mul_comm]
  calc
    _ ≤ ‖x i‖ * (|frequency L i| * (Real.sqrt L * Real.sqrt (y : ℝ)) +
        (Real.sqrt L)⁻¹ * Real.sqrt (y : ℝ)) := by
      rw [hs]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [add_comm] using add_le_add_right hphase ((Real.sqrt L)⁻¹ * Real.sqrt (y : ℝ))
    _ = _ := by ring

/-- Real-parameter version used in the literal current's strong integrals. -/
theorem norm_shift_fourier_sub_le_sqrt {N : ℕ} {L : ℝ} (hL : 0 < L)
    {y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) (x : Section N) :
    ‖shift L y (fourierHilbert L x) - fourierHilbert L x‖ ≤
      fourierShiftConstant L x * Real.sqrt y := by
  simpa only [shift, Real.coe_toNNReal y hy0] using
    norm_killed_fourier_sub_le_sqrt hL y.toNNReal (by simpa only [Real.coe_toNNReal y hy0]) x

end Riemann.Analysis.FiniteWindow
