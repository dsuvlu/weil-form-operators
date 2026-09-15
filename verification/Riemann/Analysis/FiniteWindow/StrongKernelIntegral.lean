import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Strong integration of scalar kernels against contractions

Only the orbit of each vector is assumed strongly measurable. No measurability
of the operator-valued map is required. The scalar L¹ norm controls the operator
norm, which will transport L¹ parameter derivatives to completed frames.
-/

noncomputable section

namespace Riemann.Analysis

open MeasureTheory

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A family of contractions with strongly measurable vector orbits. -/
structure StrongContractionFamily (μ : Measure Ω) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] where
  operator : Ω → E →L[ℂ] E
  measurable_orbit : ∀ u, AEStronglyMeasurable (fun y => operator y u) μ
  norm_le : ∀ y, ‖operator y‖ ≤ 1

namespace StrongContractionFamily

variable (S : StrongContractionFamily μ E)

lemma norm_apply_le (y : Ω) (u : E) : ‖S.operator y u‖ ≤ ‖u‖ :=
  (S.operator y).le_opNorm u |>.trans (by
    simpa using mul_le_mul_of_nonneg_right (S.norm_le y) (norm_nonneg u))

lemma integrable_kernel_orbit (k : Lp ℂ 1 μ) (u : E) :
    Integrable (fun y => k y • S.operator y u) μ := by
  apply ((L1.integrable_coeFn k).norm.mul_const ‖u‖).mono'
    ((Lp.aestronglyMeasurable k).smul (S.measurable_orbit u))
  exact Filter.Eventually.of_forall fun y => by
    change ‖k y • S.operator y u‖ ≤ ‖k y‖ * ‖u‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (S.norm_apply_le y u) (norm_nonneg _)

lemma norm_integral_kernel_orbit_le (k : Lp ℂ 1 μ) (u : E) :
    ‖∫ y, k y • S.operator y u ∂μ‖ ≤ ‖k‖ * ‖u‖ := by
  calc
    _ ≤ ∫ y, ‖k y‖ * ‖u‖ ∂μ :=
      norm_integral_le_of_norm_le ((L1.integrable_coeFn k).norm.mul_const ‖u‖)
        (Filter.Eventually.of_forall fun y => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (S.norm_apply_le y u) (norm_nonneg _))
    _ = _ := by rw [integral_mul_const, ← L1.norm_eq_integral_norm]

/-- Integration is linear in the vector on which the family acts. -/
def kernelLinearMap (k : Lp ℂ 1 μ) : E →ₗ[ℂ] E where
  toFun u := ∫ y, k y • S.operator y u ∂μ
  map_add' u v := by
    simp only [map_add, smul_add]
    exact integral_add (S.integrable_kernel_orbit k u) (S.integrable_kernel_orbit k v)
  map_smul' c u := by
    simp only [map_smul, RingHom.id_apply, smul_comm (k _) c]
    exact integral_smul c _

/-- The bounded operator defined by strong vector integration. -/
def kernelOperator (k : Lp ℂ 1 μ) : E →L[ℂ] E :=
  (S.kernelLinearMap k).mkContinuous ‖k‖ (S.norm_integral_kernel_orbit_le k)

@[simp] theorem kernelOperator_apply (k : Lp ℂ 1 μ) (u : E) :
    S.kernelOperator k u = ∫ y, k y • S.operator y u ∂μ := rfl

lemma norm_kernelOperator_le (k : Lp ℂ 1 μ) : ‖S.kernelOperator k‖ ≤ ‖k‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg k) (S.norm_integral_kernel_orbit_le k)

/-- Integration is linear in the scalar L¹ kernel. -/
def integrationLinearMap : Lp ℂ 1 μ →ₗ[ℂ] (E →L[ℂ] E) where
  toFun := S.kernelOperator
  map_add' k l := by
    ext u
    simp only [kernelOperator_apply, add_apply]
    calc
      _ = ∫ y, (k y + l y) • S.operator y u ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add k l] with y hy using congrArg (· • S.operator y u) hy
      _ = _ := by
        simp only [add_smul]
        exact integral_add (S.integrable_kernel_orbit k u) (S.integrable_kernel_orbit l u)
  map_smul' c k := by
    ext u
    simp only [kernelOperator_apply, smul_apply, RingHom.id_apply]
    calc
      _ = ∫ y, (c * k y) • S.operator y u ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c k] with y hy using congrArg (· • S.operator y u) hy
      _ = _ := by
        simp only [mul_smul]
        exact integral_smul c _

/-- Scalar L¹ kernels act continuously in operator norm, although the family
itself need not be a Bochner-measurable operator-valued function. -/
def integration : Lp ℂ 1 μ →L[ℂ] (E →L[ℂ] E) :=
  S.integrationLinearMap.mkContinuous 1 fun k => by
    simpa only [one_mul, integrationLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
      using S.norm_kernelOperator_le k

@[simp] theorem integration_apply (k : Lp ℂ 1 μ) :
    S.integration k = S.kernelOperator k := rfl

lemma norm_integration_le : ‖S.integration‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one fun k => by
    simpa only [one_mul, integrationLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
      using S.norm_kernelOperator_le k

/-- Real L¹ differentiability gives real operator-norm differentiability. -/
theorem hasDerivAt_integration {k : ℝ → Lp ℂ 1 μ} {k' : Lp ℂ 1 μ} {a : ℝ}
    (hk : HasDerivAt k k' a) :
    HasDerivAt (fun s => S.integration (k s)) (S.integration k') a := by
  exact (S.integration.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt a hk

/-- A bounded operator commuting with every member also commutes with each
strong kernel integral. No interchange of two operator-valued integrals occurs. -/
theorem kernelOperator_commute (T : E →L[ℂ] E)
    (hT : ∀ y u, T (S.operator y u) = S.operator y (T u)) (k : Lp ℂ 1 μ) :
    T.comp (S.kernelOperator k) = (S.kernelOperator k).comp T := by
  ext u
  change T (∫ y, k y • S.operator y u ∂μ) = ∫ y, k y • S.operator y (T u) ∂μ
  rw [← T.integral_comp_comm (S.integrable_kernel_orbit k u)]
  congr 1
  funext y
  simp only [map_smul, hT]

end StrongContractionFamily
end Riemann.Analysis
