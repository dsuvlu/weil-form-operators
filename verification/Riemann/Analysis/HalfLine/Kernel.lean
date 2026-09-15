import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.BigOperators.Intervals

/-! # The scalar critical arithmetic kernel

The arithmetic integer and square sums are evaluated before estimating the
result. The signed fractional-part factor is retained. All half-line integral
bounds are upper bounds, not claims of equality for the absolute kernel mass.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Riemann.Analysis.HalfLine

/-- Number of positive integers not exceeding exp(y). -/
def arithmeticCount (y : ℝ) : ℕ := ⌊Real.exp y⌋₊

/-- The signed completed critical kernel, with its natural zero extension. -/
def criticalKernel (y : ℝ) : ℝ :=
  Real.pi * Real.exp (-5*y/2) * (arithmeticCount y : ℝ) *
    ((arithmeticCount y : ℝ)+1) * (1-2*(Real.exp y-(arithmeticCount y : ℝ)))

lemma arithmeticCount_le (y : ℝ) : (arithmeticCount y : ℝ) ≤ Real.exp y :=
  Nat.floor_le (Real.exp_pos y).le

lemma exp_lt_arithmeticCount_add_one (y : ℝ) :
    Real.exp y < (arithmeticCount y : ℝ)+1 := Nat.lt_floor_add_one _

lemma criticalKernel_of_neg {y : ℝ} (hy : y < 0) : criticalKernel y = 0 := by
  have hm : arithmeticCount y = 0 := Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr hy)
  simp [criticalKernel, hm]

lemma criticalKernel_measurable : Measurable criticalKernel := by
  unfold criticalKernel arithmeticCount
  fun_prop

lemma sum_positive_integers (m : ℕ) :
    (∑ n ∈ Finset.range (m+1), (n : ℝ)) = (m:ℝ)*((m:ℝ)+1)/2 := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [Finset.sum_range_succ, hm]
    push_cast
    ring

lemma sum_positive_squares (m : ℕ) :
    (∑ n ∈ Finset.range (m+1), (n : ℝ)^2) =
      (m:ℝ)*((m:ℝ)+1)*(2*(m:ℝ)+1)/6 := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [Finset.sum_range_succ, hm]
    push_cast
    ring

/-- The actual integer and square sums yield the fractional-part kernel. -/
theorem criticalKernel_arithmetic_sums (y : ℝ) :
    2*Real.pi * (3*Real.exp (-5*y/2) *
      (∑ n ∈ Finset.range (arithmeticCount y+1), (n:ℝ)^2) -
      2*Real.exp (-3*y/2) *
      (∑ n ∈ Finset.range (arithmeticCount y+1), (n:ℝ))) = criticalKernel y := by
  rw [sum_positive_squares, sum_positive_integers]
  have he : Real.exp (-3*y/2) = Real.exp (-5*y/2) * Real.exp y := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  unfold criticalKernel
  ring

/-- The cancellation is estimated only after combining the two arithmetic sums. -/
theorem abs_criticalKernel_le (y : ℝ) :
    |criticalKernel y| ≤ Real.pi * (Real.exp (-y/2)+Real.exp (-3*y/2)) := by
  have hm := arithmeticCount_le y
  have hm0 : 0 ≤ (arithmeticCount y : ℝ) := Nat.cast_nonneg _
  have ht := exp_lt_arithmeticCount_add_one y
  have hs : |1-2*(Real.exp y-(arithmeticCount y:ℝ))| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hp : 0 ≤ Real.pi * Real.exp (-5*y/2) :=
    mul_nonneg Real.pi_pos.le (Real.exp_pos _).le
  have he1 : Real.exp (-5*y/2) * Real.exp y * Real.exp y = Real.exp (-y/2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp (-5*y/2) * Real.exp y = Real.exp (-3*y/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    |criticalKernel y| = Real.pi * Real.exp (-5*y/2) * (arithmeticCount y:ℝ) *
      ((arithmeticCount y:ℝ)+1) * |1-2*(Real.exp y-(arithmeticCount y:ℝ))| := by
        simp only [criticalKernel, abs_mul, abs_of_nonneg hp,
          abs_of_nonneg hm0, abs_of_nonneg (by linarith : 0 ≤ (arithmeticCount y:ℝ)+1)]
    _ ≤ Real.pi * Real.exp (-5*y/2) * Real.exp y * (Real.exp y+1) := by
      calc
        _ ≤ Real.pi * Real.exp (-5*y/2) * (arithmeticCount y:ℝ) *
          ((arithmeticCount y:ℝ)+1) := by
            exact mul_le_of_le_one_right (by positivity) hs
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hm hp) (by linarith)
          (by positivity) (by positivity)
    _ = _ := by
      calc
        _ = Real.pi * (Real.exp (-5*y/2)*Real.exp y*Real.exp y +
          Real.exp (-5*y/2)*Real.exp y) := by ring
        _ = _ := by rw [he1, he2]

lemma criticalKernel_eq_fract (y : ℝ) :
    criticalKernel y = Real.pi * Real.exp (-5*y/2) * (arithmeticCount y : ℝ) *
      ((arithmeticCount y : ℝ)+1) * (1-2*Int.fract (Real.exp y)) := by
  simp only [criticalKernel, Int.fract, arithmeticCount,
    ← Int.natCast_floor_eq_floor (Real.exp_pos y).le, Int.cast_natCast]

lemma integrable_kernel_majorant :
    IntegrableOn (fun y : ℝ => Real.pi * (Real.exp (-y/2)+Real.exp (-3*y/2))) (Ioi 0) := by
  have h1 := integrableOn_exp_mul_Ioi (a := -(1/2:ℝ)) (by norm_num) 0
  have h3 := integrableOn_exp_mul_Ioi (a := -(3/2:ℝ)) (by norm_num) 0
  have he : (fun y : ℝ => Real.pi * (Real.exp (-y/2)+Real.exp (-3*y/2))) =
      (fun y : ℝ => Real.pi * (Real.exp (-(1/2:ℝ)*y)+Real.exp (-(3/2:ℝ)*y))) := by
    ext y
    congr 1; congr 1 <;> congr 1 <;> ring
  rw [he]
  exact (h1.add h3).const_mul Real.pi

lemma integral_kernel_majorant :
    (∫ y : ℝ in Ioi 0, Real.pi * (Real.exp (-y/2)+Real.exp (-3*y/2))) =
      8*Real.pi/3 := by
  have h1 := integrableOn_exp_mul_Ioi (a := -(1/2:ℝ)) (by norm_num) 0
  have h3 := integrableOn_exp_mul_Ioi (a := -(3/2:ℝ)) (by norm_num) 0
  have hf : (fun y : ℝ => Real.exp (-y/2)+Real.exp (-3*y/2)) =
      (fun y : ℝ => Real.exp (-(1/2:ℝ)*y)+Real.exp (-(3/2:ℝ)*y)) := by
    ext y
    congr 1 <;> congr 1 <;> ring
  rw [integral_const_mul, hf, integral_add h1 h3,
    integral_exp_mul_Ioi (by norm_num : -(1/2:ℝ)<0),
    integral_exp_mul_Ioi (by norm_num : -(3/2:ℝ)<0)]
  norm_num
  ring

lemma criticalKernel_integrableOn : IntegrableOn criticalKernel (Ioi 0) := by
  apply integrable_kernel_majorant.mono' criticalKernel_measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    simpa only [Real.norm_eq_abs] using abs_criticalKernel_le y

/-- Absolute kernel mass has the stated upper bound; it is not asserted sharp. -/
theorem integral_abs_criticalKernel_le :
    (∫ y : ℝ in Ioi 0, |criticalKernel y|) ≤ 8*Real.pi/3 := by
  rw [← integral_kernel_majorant]
  exact integral_mono_ae criticalKernel_integrableOn.abs integrable_kernel_majorant
    (Filter.Eventually.of_forall abs_criticalKernel_le)

lemma criticalKernel_support : Function.support criticalKernel ⊆ Ici 0 := by
  intro y hy
  by_contra h
  exact hy (criticalKernel_of_neg (lt_of_not_ge h))

lemma criticalKernel_integrable : Integrable criticalKernel := by
  apply (integrableOn_iff_integrable_of_support_subset criticalKernel_support).mp
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact criticalKernel_integrableOn

lemma integral_abs_criticalKernel_global_le :
    (∫ y : ℝ, |criticalKernel y|) ≤ 8*Real.pi/3 := by
  have he : (∫ y : ℝ in Ici 0, |criticalKernel y|) = ∫ y : ℝ, |criticalKernel y| := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [criticalKernel_of_neg (lt_of_not_ge hy), abs_zero]
  rw [← he, integral_Ici_eq_integral_Ioi]
  exact integral_abs_criticalKernel_le

/-- The genuine complex scalar L¹ kernel consumed by strong shift integration. -/
def criticalKernelL1 : Lp ℂ 1 (volume : Measure ℝ) :=
  (memLp_one_iff_integrable.mpr criticalKernel_integrable.ofReal).toLp
    (fun y => (criticalKernel y : ℂ))

lemma criticalKernelL1_ae :
    criticalKernelL1 =ᵐ[volume] (fun y => (criticalKernel y : ℂ)) :=
  MemLp.coeFn_toLp _

theorem norm_criticalKernelL1_le : ‖criticalKernelL1‖ ≤ 8*Real.pi/3 := by
  rw [L1.norm_eq_integral_norm]
  have he : (∫ y : ℝ, ‖criticalKernelL1 y‖) = ∫ y : ℝ, |criticalKernel y| := by
    apply integral_congr_ae
    filter_upwards [criticalKernelL1_ae] with y hy
    rw [hy, Complex.norm_real, Real.norm_eq_abs]
  rw [he]
  exact integral_abs_criticalKernel_global_le

end Riemann.Analysis.HalfLine
