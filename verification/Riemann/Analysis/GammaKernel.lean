import Riemann.Basic.L1ParameterDerivative
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Scalar Gamma-ratio kernel at the critical parameter

The real parameter is σ, the reference parameter is 5/2, and
α(σ)=(5/2−σ)/2. The kernel is defined independently of the current.
Source: PASS28AW, GAMMA-RATIO-COMPLETION, C1–C8.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Riemann.Analysis.GammaCompletion

def alpha (σ : ℝ) : ℝ := (5 / 2 - σ) / 2

def prefactor (σ : ℝ) : ℝ := 2 * Real.pi ^ alpha σ / Real.Gamma (alpha σ)

def base (σ y : ℝ) : ℝ :=
  Real.exp (-σ * y) * (1 - Real.exp (-2 * y)) ^ (alpha σ - 1)

def kernel (σ y : ℝ) : ℝ := prefactor σ * base σ y

def baseDerivative (σ y : ℝ) : ℝ :=
  base σ y * (-y - Real.log (1 - Real.exp (-2 * y)) / 2)

def criticalDerivative (y : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (-y / 2) *
    (-y - (Real.eulerMascheroniConstant + Real.log Real.pi) / 2 -
      Real.log (1 - Real.exp (-2 * y)) / 2)

@[simp] theorem alpha_half : alpha (1 / 2) = 1 := by norm_num [alpha]

@[simp] theorem prefactor_half : prefactor (1 / 2) = 2 * Real.pi := by
  rw [prefactor, alpha_half]
  simp

@[simp] theorem base_half (y : ℝ) : base (1 / 2) y = Real.exp (-y / 2) := by
  rw [base, alpha_half]
  simp only [sub_self, Real.rpow_zero, mul_one]
  congr 1
  ring

@[simp] theorem kernel_half (y : ℝ) : kernel (1 / 2) y =
    2 * Real.pi * Real.exp (-y / 2) := by rw [kernel, prefactor_half, base_half]

theorem hasDerivAt_alpha (σ : ℝ) : HasDerivAt alpha (-(1 / 2)) σ := by
  convert! ((hasDerivAt_const σ (5 / 2)).sub (hasDerivAt_id σ)).div_const 2 using 1
  norm_num [alpha]

theorem hasDerivAt_prefactor_half : HasDerivAt prefactor
    (-Real.pi * (Real.eulerMascheroniConstant + Real.log Real.pi)) (1 / 2) := by
  have hGamma : HasDerivAt (fun σ => Real.Gamma (alpha σ))
      (Real.eulerMascheroniConstant / 2) (1 / 2) := by
    have hg : HasDerivAt Real.Gamma (-Real.eulerMascheroniConstant) (alpha (1 / 2)) :=
      alpha_half.symm ▸ Real.hasDerivAt_Gamma_one
    convert! hg.comp (1 / 2) (hasDerivAt_alpha (1 / 2)) using 1
    ring
  have hpi := (hasDerivAt_alpha (1 / 2)).const_rpow Real.pi_pos
  convert! (hpi.const_mul 2).div hGamma (by rw [alpha_half, Real.Gamma_one]; norm_num) using 1
  rw [alpha_half, Real.rpow_one, Real.Gamma_one]
  ring

theorem base_arg_pos {y : ℝ} (hy : 0 < y) : 0 < 1 - Real.exp (-2 * y) := by
  have : Real.exp (-2 * y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

theorem base_arg_le_one (y : ℝ) : 1 - Real.exp (-2 * y) ≤ 1 := by
  linarith [Real.exp_pos (-2 * y)]

theorem hasDerivAt_base (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun σ => base σ y) (baseDerivative σ y) σ := by
  have he := (((hasDerivAt_id σ).neg).mul_const y).exp
  have hp := ((hasDerivAt_alpha σ).sub_const 1).const_rpow (base_arg_pos hy)
  convert! he.mul hp using 1
  simp only [baseDerivative, base, Pi.neg_apply, id_eq]
  ring

theorem hasDerivAt_kernel_half {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun σ => kernel σ y) (criticalDerivative y) (1 / 2) := by
  convert! hasDerivAt_prefactor_half.mul (hasDerivAt_base (1 / 2) hy) using 1
  rw [prefactor_half, baseDerivative, base_half]
  simp only [criticalDerivative]
  ring

/-- Comparison with the endpoint distance, uniform on the finite window. -/
theorem base_arg_lower {L y : ℝ} (hy : 0 ≤ y) (hyL : y ≤ L) :
    (2 * Real.exp (-2 * L)) * y ≤ 1 - Real.exp (-2 * y) := by
  have ht := Real.add_one_le_exp (2 * y)
  have hp := Real.exp_pos (-2 * y)
  have heq : Real.exp (2 * y) * Real.exp (-2 * y) = 1 := by
    rw [← Real.exp_add, show 2 * y + -2 * y = 0 by ring, Real.exp_zero]
  have hh := mul_le_mul_of_nonneg_right ht hp.le
  have he : Real.exp (-2 * L) ≤ Real.exp (-2 * y) := by
    apply Real.exp_le_exp.mpr
    linarith
  nlinarith [mul_le_mul_of_nonneg_right he hy]

theorem base_nonneg (σ : ℝ) {y : ℝ} (hy : 0 < y) : 0 ≤ base σ y := by
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (base_arg_pos hy).le _)

theorem base_le_quarter {σ y : ℝ} (hσ : σ ∈ Icc 0 1) (hy : 0 < y) :
    base σ y ≤ (1 - Real.exp (-2 * y)) ^ (-(1 / 4 : ℝ)) := by
  have he : Real.exp (-σ * y) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hσ.1])
  have hp := Real.rpow_le_rpow_of_exponent_ge (base_arg_pos hy) (base_arg_le_one y)
    (show -(1 / 4 : ℝ) ≤ alpha σ - 1 by dsimp [alpha]; linarith [hσ.2])
  exact (mul_le_mul_of_nonneg_right he (Real.rpow_nonneg (base_arg_pos hy).le _)).trans
    (by simpa using hp)

theorem abs_log_le_quarter {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    |Real.log q| ≤ 4 * q ^ (-(1 / 4 : ℝ)) := by
  have hh := (Real.abs_log_mul_self_rpow_lt q (1 / 4) hq hq1 (by norm_num)).le
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hq _)] at hh
  have hp : q ^ (1 / 4 : ℝ) * q ^ (-(1 / 4 : ℝ)) = 1 := by
    rw [← Real.rpow_add hq]
    norm_num
  have hm := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hq.le (-(1 / 4 : ℝ)))
  rw [mul_assoc, hp, mul_one] at hm
  norm_num at hm ⊢
  exact hm

def majorant (L y : ℝ) : ℝ :=
  (L + 2) * (2 * Real.exp (-2 * L)) ^ (-(1 / 2 : ℝ)) * y ^ (-(1 / 2 : ℝ))

theorem norm_baseDerivative_le {L σ y : ℝ} (hL : 0 < L)
    (hσ : σ ∈ Icc 0 1) (hy : y ∈ Ioo 0 L) :
    ‖baseDerivative σ y‖ ≤ majorant L y := by
  let q := 1 - Real.exp (-2 * y)
  let r := q ^ (-(1 / 4 : ℝ))
  have hq : 0 < q := base_arg_pos hy.1
  have hq1 : q ≤ 1 := base_arg_le_one y
  have hr : 0 ≤ r := Real.rpow_nonneg hq.le _
  have hr1 : 1 ≤ r := by
    simpa [r] using Real.rpow_le_rpow_of_exponent_ge hq hq1
      (show -(1 / 4 : ℝ) ≤ 0 by norm_num)
  have hb : base σ y ≤ r := base_le_quarter hσ hy.1
  have hlog : |Real.log q| ≤ 4 * r := abs_log_le_quarter hq hq1
  have hbr : ‖baseDerivative σ y‖ ≤ (L + 2) * (r * r) := by
    have hterm : |-y - Real.log q / 2| ≤ y + |Real.log q| / 2 := by
      calc
        _ ≤ |-y| + |Real.log q / 2| := abs_sub _ _
        _ = y + |Real.log q| / 2 := by rw [abs_neg, abs_of_pos hy.1, abs_div]; norm_num
    rw [baseDerivative, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (base_nonneg σ hy.1)]
    change base σ y * |-y - Real.log q / 2| ≤ _
    calc
      _ ≤ r * (y + |Real.log q| / 2) :=
        mul_le_mul hb hterm (abs_nonneg _) hr
      _ ≤ r * (L + 2 * r) := by gcongr <;> linarith [hy.2]
      _ ≤ (L + 2) * (r * r) := by
        nlinarith [mul_nonneg hL.le (mul_nonneg hr (sub_nonneg.mpr hr1))]
  have hrsq : r * r = q ^ (-(1 / 2 : ℝ)) := by
    dsimp [r]
    rw [← Real.rpow_add hq]
    norm_num
  have hc : 0 < 2 * Real.exp (-2 * L) := by positivity
  have hlower : (2 * Real.exp (-2 * L)) * y ≤ q := base_arg_lower hy.1.le hy.2.le
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hc hy.1) hlower
    (show -(1 / 2 : ℝ) ≤ 0 by norm_num)
  rw [Real.mul_rpow hc.le hy.1.le] at hp
  rw [hrsq] at hbr
  exact hbr.trans (by dsimp [majorant]; nlinarith [mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ L + 2)])

theorem majorant_nonneg {L y : ℝ} (hL : 0 < L) (hy : 0 ≤ y) : 0 ≤ majorant L y := by
  dsimp [majorant]
  positivity

theorem majorant_integrable {L : ℝ} (hL : 0 < L) :
    IntegrableOn (majorant L) (Ioo 0 L) := by
  have hp : IntegrableOn (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) (Ioo 0 L) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hL).mpr (by norm_num)
  exact hp.const_mul _

theorem norm_base_le_majorant {L σ y : ℝ} (hL : 0 < L)
    (hσ : σ ∈ Icc 0 1) (hy : y ∈ Ioo 0 L) : ‖base σ y‖ ≤ majorant L y := by
  have hq := base_arg_pos hy.1
  have hp := Real.rpow_le_rpow_of_exponent_ge hq (base_arg_le_one y)
    (show -(1 / 2 : ℝ) ≤ -(1 / 4 : ℝ) by norm_num)
  have hc : 0 < 2 * Real.exp (-2 * L) := by positivity
  have hr := Real.rpow_le_rpow_of_nonpos (mul_pos hc hy.1)
    (base_arg_lower hy.1.le hy.2.le) (show -(1 / 2 : ℝ) ≤ 0 by norm_num)
  rw [Real.mul_rpow hc.le hy.1.le] at hr
  rw [Real.norm_eq_abs, abs_of_nonneg (base_nonneg σ hy.1)]
  refine (base_le_quarter hσ hy.1).trans (hp.trans (hr.trans ?_))
  dsimp [majorant]
  have hprod := mul_nonneg (Real.rpow_nonneg hc.le (-(1 / 2 : ℝ)))
    (Real.rpow_nonneg hy.1.le (-(1 / 2 : ℝ)))
  nlinarith

theorem continuousOn_base (σ L : ℝ) : ContinuousOn (base σ) (Ioo 0 L) := by
  apply ContinuousOn.mul
  · fun_prop
  · exact (show ContinuousOn (fun y : ℝ => 1 - Real.exp (-2 * y)) (Ioo 0 L) by
      fun_prop).rpow_const (fun y hy => Or.inl (base_arg_pos hy.1).ne')

theorem continuousOn_baseDerivative (σ L : ℝ) :
    ContinuousOn (baseDerivative σ) (Ioo 0 L) := by
  apply (continuousOn_base σ L).mul
  apply ContinuousOn.sub
  · fun_prop
  · apply ContinuousOn.div_const
    exact (show ContinuousOn (fun y : ℝ => 1 - Real.exp (-2 * y)) (Ioo 0 L) by
      fun_prop).log (fun y hy => (base_arg_pos hy.1).ne')

theorem base_integrable {L σ : ℝ} (hL : 0 < L) (hσ : σ ∈ Icc 0 1) :
    IntegrableOn (base σ) (Ioo 0 L) := by
  apply (majorant_integrable hL).mono'
    ((continuousOn_base σ L).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact norm_base_le_majorant hL hσ hy

theorem baseDerivative_integrable {L σ : ℝ} (hL : 0 < L) (hσ : σ ∈ Icc 0 1) :
    IntegrableOn (baseDerivative σ) (Ioo 0 L) := by
  apply (majorant_integrable hL).mono'
    ((continuousOn_baseDerivative σ L).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact norm_baseDerivative_le hL hσ hy

/-- The L¹ class of the scalar base kernel. Outside its integrability domain
this total definition returns zero; all representation theorems below prove
integrability and eliminate that branch. -/
def baseL1 (L σ : ℝ) : ℝ →₁[volume.restrict (Ioo 0 L)] ℝ := by
  classical
  exact if h : IntegrableOn (base σ) (Ioo 0 L) volume then h.toL1 (base σ) else 0

def baseDerivativeL1 (L σ : ℝ) : ℝ →₁[volume.restrict (Ioo 0 L)] ℝ := by
  classical
  exact if h : IntegrableOn (baseDerivative σ) (Ioo 0 L) volume then h.toL1 (baseDerivative σ) else 0

theorem coe_baseL1 {L σ : ℝ} (hL : 0 < L) (hσ : σ ∈ Icc 0 1) :
    (baseL1 L σ : ℝ → ℝ) =ᵐ[volume.restrict (Ioo 0 L)] base σ := by
  rw [baseL1, dif_pos (base_integrable hL hσ)]
  exact Integrable.coeFn_toL1 _

theorem coe_baseDerivativeL1 {L σ : ℝ} (hL : 0 < L) (hσ : σ ∈ Icc 0 1) :
    (baseDerivativeL1 L σ : ℝ → ℝ) =ᵐ[volume.restrict (Ioo 0 L)] baseDerivative σ := by
  rw [baseDerivativeL1, dif_pos (baseDerivative_integrable hL hσ)]
  exact Integrable.coeFn_toL1 _

/-- The derivative is in the L¹ norm, not merely after scalar integration. -/
theorem hasDerivAt_baseL1 {L σ : ℝ} (hL : 0 < L) (hσ : σ ∈ Ioo 0 1) :
    HasDerivAt (baseL1 L) (baseDerivativeL1 L σ) σ := by
  apply Riemann.Basic.hasDerivAt_L1_of_dominated_deriv
    (baseL1 L) (baseDerivativeL1 L σ) base baseDerivative σ (Icc 0 1) (majorant L)
    (Icc_mem_nhds hσ.1 hσ.2) (convex_Icc 0 1)
  · exact fun x hx => coe_baseL1 hL hx
  · exact coe_baseDerivativeL1 hL ⟨hσ.1.le, hσ.2.le⟩
  · exact majorant_integrable hL
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact majorant_nonneg hL hy.1.le
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact fun x hx => norm_baseDerivative_le hL hx hy
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact fun x _ => hasDerivAt_base x hy.1

/-- L¹ class of the full independent Gamma kernel. -/
def kernelL1 (L σ : ℝ) : ℝ →₁[volume.restrict (Ioo 0 L)] ℝ :=
  prefactor σ • baseL1 L σ

/-- The actual critical L¹ derivative of the Gamma kernel. -/
def criticalDerivativeL1 (L : ℝ) : ℝ →₁[volume.restrict (Ioo 0 L)] ℝ :=
  (-Real.pi * (Real.eulerMascheroniConstant + Real.log Real.pi)) • baseL1 L (1 / 2) +
    (2 * Real.pi) • baseDerivativeL1 L (1 / 2)

theorem hasDerivAt_kernelL1_half {L : ℝ} (hL : 0 < L) :
    HasDerivAt (kernelL1 L) (criticalDerivativeL1 L) (1 / 2) := by
  have hh := hasDerivAt_prefactor_half.smul
    (hasDerivAt_baseL1 hL (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num))
  convert! hh using 1
  dsimp [criticalDerivativeL1]
  rw [prefactor_half, add_comm]

theorem coe_kernelL1 {L σ : ℝ} (hL : 0 < L) (hσ : σ ∈ Icc 0 1) :
    (kernelL1 L σ : ℝ → ℝ) =ᵐ[volume.restrict (Ioo 0 L)] kernel σ := by
  filter_upwards [Lp.coeFn_smul (prefactor σ) (baseL1 L σ), coe_baseL1 hL hσ] with y hs hb
  change (prefactor σ • baseL1 L σ : ℝ →₁[volume.restrict (Ioo 0 L)] ℝ) y = _
  rw [hs, Pi.smul_apply, hb]
  rfl

theorem coe_criticalDerivativeL1 {L : ℝ} (hL : 0 < L) :
    (criticalDerivativeL1 L : ℝ → ℝ) =ᵐ[volume.restrict (Ioo 0 L)] criticalDerivative := by
  have hh : (1 / 2 : ℝ) ∈ Icc 0 1 := by norm_num
  filter_upwards [Lp.coeFn_add
      ((-Real.pi * (Real.eulerMascheroniConstant + Real.log Real.pi)) • baseL1 L (1 / 2))
      ((2 * Real.pi) • baseDerivativeL1 L (1 / 2)),
    Lp.coeFn_smul (-Real.pi * (Real.eulerMascheroniConstant + Real.log Real.pi)) (baseL1 L (1 / 2)),
    Lp.coeFn_smul (2 * Real.pi) (baseDerivativeL1 L (1 / 2)),
    coe_baseL1 hL hh, coe_baseDerivativeL1 hL hh] with y ha hb hc hd he
  change (_ + _ : ℝ →₁[volume.restrict (Ioo 0 L)] ℝ) y = _
  rw [ha, Pi.add_apply, hb, hc, Pi.smul_apply, Pi.smul_apply, hd, he,
    baseDerivative, base_half]
  dsimp [criticalDerivative, smul_eq_mul]
  ring

theorem differentiableAt_prefactor {σ : ℝ} (hσ : σ < 5 / 2) :
    DifferentiableAt ℝ prefactor σ := by
  have hα : 0 < alpha σ := by dsimp [alpha]; linarith
  have hGamma := (Real.differentiableAt_Gamma (s := alpha σ)
    (fun m => ne_of_gt (lt_of_le_of_lt (neg_nonpos.mpr m.cast_nonneg) hα))).comp σ
      (hasDerivAt_alpha σ).differentiableAt
  exact (((hasDerivAt_alpha σ).const_rpow Real.pi_pos).differentiableAt.const_mul 2).div
    hGamma (Real.Gamma_pos_of_pos hα).ne'

theorem differentiableAt_kernelL1 {L σ : ℝ} (hL : 0 < L) (hσ : σ ∈ Ioo 0 1) :
    DifferentiableAt ℝ (kernelL1 L) σ := by
  exact (differentiableAt_prefactor (by linarith [hσ.2])).smul
    (hasDerivAt_baseL1 hL hσ).differentiableAt

end Riemann.Analysis.GammaCompletion
