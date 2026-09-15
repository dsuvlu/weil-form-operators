import Riemann.CCM.LatticeTail
import Mathlib.Analysis.Complex.RealDeriv
import Riemann.CCM.InverseEnergyTrace

/-! Actual logarithmic slopes of the existing finite boundary characteristic. -/
noncomputable section
open scoped BigOperators Topology
open Riemann.Basic
namespace Riemann.CCM.Native
variable {N : ℕ}

/-- The existing characteristic normalized at the prescribed imaginary anchor. -/
def anchoredBoundaryCharacteristic (L : ℝ) (v : Section N) (a : ℝ) (z : ℂ) : ℂ :=
  boundaryCharacteristic L v z / boundaryCharacteristic L v (Complex.I * (a : ℂ))

/-- The slope uses the actual complex derivative, not a supplied decomposition. -/
def boundarySoftMean (L : ℝ) (v : Section N) (a : ℝ) : ℂ :=
  (Complex.I * (a : ℂ) / 2) *
    deriv (anchoredBoundaryCharacteristic L v a) (Complex.I * (a : ℂ))

lemma boundarySoftMean_eq_logDeriv (L : ℝ) (v : Section N) (a : ℝ) :
    boundarySoftMean L v a = (Complex.I * (a : ℂ) / 2) *
      logDeriv (boundaryCharacteristic L v) (Complex.I * (a : ℂ)) := by
  unfold boundarySoftMean anchoredBoundaryCharacteristic
  rw [deriv_div_const, logDeriv_apply]

lemma native_anchoredBoundaryCharacteristic_anchor (C : Coefficients N) (L : ℝ)
    (hL : 0 < L) (A : GroundAdmission C) {a : ℝ} (ha : 0 < a) :
    anchoredBoundaryCharacteristic L (fullData C L hL A).groundVector a (Complex.I * (a : ℂ)) = 1 := by
  apply div_self
  apply native_boundaryCharacteristic_nonreal C L hL A
  simpa using ha.ne'

lemma boundarySoftMean_quarter (L : ℝ) (v : Section N) :
    boundarySoftMean L v (1/4) = (Complex.I / 8) *
      deriv (anchoredBoundaryCharacteristic L v (1/4)) (Complex.I / 4) := by
  unfold boundarySoftMean
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [show Complex.I * (1 / 4) / 2 = Complex.I / 8 by ring,
    show Complex.I * (1 / 4) = Complex.I / 4 by ring]

/-- Differentiating w sinc(w)=sin(w) retains the removable entire definition. -/
lemma complexSinc_derivative_identity (w : ℂ) :
    complexSinc w + w * deriv complexSinc w = Complex.cos w := by
  have h := congrArg (fun f : ℂ → ℂ => deriv f w) (funext mul_complexSinc)
  have hd := ((hasDerivAt_id w).mul (differentiable_complexSinc w).hasDerivAt).deriv
  simpa only [one_mul, id_eq, Complex.deriv_sin] using hd.symm.trans h


lemma complexSinc_logDeriv {w : ℂ} (hw : w ≠ 0) (hs : complexSinc w ≠ 0) :
    w * logDeriv complexSinc w = w * Complex.cot w - 1 := by
  have hd := complexSinc_derivative_identity w
  have hsin : Complex.sin w ≠ 0 := by rw [← mul_complexSinc]; exact mul_ne_zero hw hs
  rw [logDeriv_apply, Complex.cot]
  rw [← mul_complexSinc]
  field_simp
  linear_combination hd

/-- The actual sine factor has exactly the full positive free-lattice slope. -/
lemma sinc_slope_eq_latticeTail {L a : ℝ} (hL : 0 < L) (ha : 0 < a) :
    (Complex.I * (a : ℂ) / 2) *
      logDeriv (fun z : ℂ => complexSinc ((L : ℂ)*z/2)) (Complex.I * (a : ℂ)) =
        (latticeTail L 0 (a^2) : ℂ) := by
  let w : ℂ := (L : ℂ) * (Complex.I * (a : ℂ)) / 2
  have hwim : w.im ≠ 0 := by
    dsimp [w]
    simp only [Complex.div_ofNat_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, zero_add, add_zero]
    positivity
  have hw : w ≠ 0 := fun h => hwim (by simp [h])
  have hs := complexSinc_ne_zero_of_im_ne_zero hwim
  have hc := logDeriv_comp (g := fun z : ℂ => (L : ℂ)*z/2) (x := Complex.I * (a : ℂ))
    (differentiable_complexSinc w)
    (show DifferentiableAt ℂ (fun z : ℂ => (L : ℂ)*z/2) (Complex.I * (a : ℂ)) by fun_prop)
  change logDeriv (fun z : ℂ => complexSinc ((L : ℂ)*z/2)) (Complex.I * (a : ℂ)) = _ at hc
  rw [hc]
  have hlin : deriv (fun z : ℂ => (L : ℂ)*z/2) (Complex.I * (a : ℂ)) = (L : ℂ)/2 := by
    convert! (((hasDerivAt_id (Complex.I * (a : ℂ))).const_mul (L : ℂ)).div_const 2).deriv using 1; simp
  rw [hlin]
  rw [latticeTail_zero_eq_cot hL ha]
  have hd := complexSinc_logDeriv hw hs
  change (Complex.I * (a : ℂ) / 2) * (logDeriv complexSinc w * ((L : ℂ)/2)) =
    (w * Complex.cot w - 1) / 2
  rw [← hd]
  dsimp [w]
  ring

/-- Restricting an actual complex derivative to the imaginary axis fixes its phase. -/
lemma logDeriv_imaginary_axis {f : ℂ → ℂ} {a : ℝ}
    (hf : DifferentiableAt ℂ f (Complex.I * (a : ℂ))) :
    logDeriv (fun t : ℝ => f (Complex.I * (t : ℂ))) a =
      Complex.I * logDeriv f (Complex.I * (a : ℂ)) := by
  have hd := (hf.hasDerivAt.comp (a : ℂ)
    ((hasDerivAt_id (a : ℂ)).const_mul Complex.I)).comp_ofReal
  simp only [mul_one, Function.comp_apply] at hd
  rw [logDeriv_apply, hd.deriv, logDeriv_apply]
  ring

/-- The finite determinant-ratio identity determines the actual anchored slope.
The premise is an identity for the existing characteristic on the positive
imaginary axis; native applications must prove it from their admitted ground. -/
lemma boundarySoftMean_of_axis_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Riemann.CCM.InverseEnergyData ι) {L a : ℝ} (hL : 0 < L) (ha : 0 < a)
    (v : Section N) (hv : Differentiable ℂ (boundaryCharacteristic L v))
    (hfactor : ∀ t : ℝ, 0 < t →
      boundaryCharacteristic L v (Complex.I * (t : ℂ)) =
        complexSinc ((L : ℂ) * (Complex.I * (t : ℂ)) / 2) *
          (M.determinantRatio (t^2) : ℂ)) :
    boundarySoftMean L v a =
      ((M.highMean (a^2) - M.freeMean (a^2) + latticeTail L 0 (a^2) : ℝ) : ℂ) := by
  let S : ℂ → ℂ := fun z => complexSinc ((L : ℂ)*z/2)
  let F : ℝ → ℂ := fun t => boundaryCharacteristic L v (Complex.I * (t : ℂ))
  let T : ℝ → ℂ := fun t => (M.determinantRatio (t^2) : ℂ)
  have hs2 : 0 < a^2 := sq_pos_of_pos ha
  have hS : Differentiable ℂ S := differentiable_complexSinc.comp (by fun_prop)
  have hSn : S (Complex.I * (a : ℂ)) ≠ 0 := by
    apply complexSinc_ne_zero_of_im_ne_zero
    simp only [Complex.div_ofNat_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, zero_add, add_zero]
    positivity
  have hTd : HasDerivAt T ((deriv M.determinantRatio (a^2) * (2*a) : ℝ) : ℂ) a := by
    have hp : HasDerivAt (fun t : ℝ => t^2) (2*a) a := by
      convert! (hasDerivAt_id a).pow 2 using 1; simp
    exact ((M.hasDerivAt_determinantRatio hs2).differentiableAt.hasDerivAt.comp
      (h := fun t : ℝ => t^2) a hp).ofReal_comp
  have hTn : T a ≠ 0 := Complex.ofReal_ne_zero.mpr (M.determinantRatio_pos hs2).ne'
  have hSd : DifferentiableAt ℝ (fun t : ℝ => S (Complex.I * (t : ℂ))) a := by
    exact ((hS (Complex.I * (a : ℂ))).hasDerivAt.comp (a : ℂ)
      ((hasDerivAt_id (a : ℂ)).const_mul Complex.I)).comp_ofReal.differentiableAt
  have he : F =ᶠ[𝓝 a] (fun t : ℝ => S (Complex.I * (t : ℂ)) * T t) := by
    filter_upwards [eventually_gt_nhds ha] with t ht
    exact hfactor t ht
  have hl : logDeriv F a =
      Complex.I * logDeriv S (Complex.I * (a : ℂ)) +
        ((deriv M.determinantRatio (a^2) * (2*a) / M.determinantRatio (a^2) : ℝ) : ℂ) := by
    rw [logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
    rw [← logDeriv_apply, logDeriv_mul a hSn hTn hSd hTd.differentiableAt,
      logDeriv_imaginary_axis (hS _), logDeriv_apply T a, hTd.deriv]
    simp only [T, Complex.ofReal_div]
  have haxis := logDeriv_imaginary_axis (hv (Complex.I * (a : ℂ)))
  change logDeriv F a = _ at haxis
  have hsine := sinc_slope_eq_latticeTail hL ha
  change (Complex.I * (a : ℂ) / 2) * logDeriv S (Complex.I * (a : ℂ)) = _ at hsine
  rw [boundarySoftMean_eq_logDeriv]
  calc
    _ = (a : ℂ)/2 * logDeriv F a := by rw [haxis]; ring
    _ = _ := by
      rw [hl, M.highMean_eq hs2]
      push_cast
      linear_combination hsine

end Riemann.CCM.Native
