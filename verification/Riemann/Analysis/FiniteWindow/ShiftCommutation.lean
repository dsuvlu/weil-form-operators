import Riemann.Analysis.FiniteWindow.PrimeHilbert
import Riemann.Analysis.FiniteWindow.GammaCurrent
import Riemann.Analysis.FiniteWindow.PolarOperator

/-! # Commutation obtained from the actual shift representation

Every passage through the singular current includes a proof of domain
preservation. Bounded-kernel factors commute by strong vector integration.
-/
noncomputable section
open MeasureTheory Set
namespace Riemann.Analysis.FiniteWindow

theorem shift_commute (L y z : ℝ) : Commute (shift L y) (shift L z) := by
  change killedShift L y.toNNReal * killedShift L z.toNNReal =
    killedShift L z.toNNReal * killedShift L y.toNNReal
  change (killedShift L y.toNNReal).comp (killedShift L z.toNNReal) =
    (killedShift L z.toNNReal).comp (killedShift L y.toNNReal)
  rw [killedShift_add, killedShift_add, add_comm]

theorem volterra_commute_shift (L : ℝ) (hL : 0 ≤ L) (b : ℂ) (y : ℝ) :
    Commute (volterra L b) (shift L y) := by
  by_cases hy : 0 ≤ y
  · exact (shift_volterra_commute L hL b hy).symm
  · have hz : shift L y = 1 := by
      simp only [shift, Real.toNNReal_of_nonpos (le_of_not_ge hy), killedShift_zero]
      rfl
    rw [hz]
    exact Commute.one_right _

theorem primeAlgebra_commute {L : ℝ} (T : Hilbert L →L[ℂ] Hilbert L)
    (hT : ∀ y : ℝ, Commute T (shift L y)) (a : primeAlgebra L) : Commute T (a : Hilbert L →L[ℂ] Hilbert L) := by
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute a.property
  rintro _ ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst n
    rw [map_zero]
    exact Commute.zero_right _
  · have he : primeShift L n = shift L (Arithmetic.natLog n : ℝ) := by
      simp only [primeShift, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg hn, shift,
        Real.toNNReal_coe]
    rw [he]
    exact hT _

theorem primeOperator_commute_shift (L σ y : ℝ) :
    Commute (primeOperator L σ) (shift L y) :=
  (primeAlgebra_commute (shift L y) (shift_commute L y)
    (Arithmetic.eulerSynthesis (primeCutoff L) (primeWeight L σ))).symm

theorem primeOperator_commute_volterra (L : ℝ) (hL : 0 ≤ L) (σ : ℝ) (b : ℂ) :
    Commute (primeOperator L σ) (volterra L b) :=
  (primeAlgebra_commute (volterra L b) (volterra_commute_shift L hL b)
    (Arithmetic.eulerSynthesis (primeCutoff L) (primeWeight L σ))).symm

theorem primeCurrent_commute_volterra (L : ℝ) (hL : 0 ≤ L) (σ : ℝ) (b : ℂ) :
    Commute (primeCurrent L σ) (volterra L b) :=
  (primeAlgebra_commute (volterra L b) (volterra_commute_shift L hL b)
    (Arithmetic.synthesis (primeCutoff L) (primeWeight L σ) ArithmeticFunction.vonMangoldt)).symm

theorem primeCurrent_commute_shift (L σ y : ℝ) :
    Commute (primeCurrent L σ) (shift L y) :=
  (primeAlgebra_commute (shift L y) (shift_commute L y)
    (Arithmetic.synthesis (primeCutoff L) (primeWeight L σ) ArithmeticFunction.vonMangoldt)).symm

theorem primeOperator_commute_current (L σ : ℝ) :
    Commute (primeOperator L σ) (primeCurrent L σ) := by
  exact congrArg (fun a : primeAlgebra L => (a : Hilbert L →L[ℂ] Hilbert L))
    (mul_comm (Arithmetic.eulerSynthesis (primeCutoff L) (primeWeight L σ))
      (Arithmetic.synthesis (primeCutoff L) (primeWeight L σ) ArithmeticFunction.vonMangoldt))

/-- The prime derivative written without any totalized inverse notation. -/
theorem primeDerivative_eq (L σ : ℝ) :
    primeDerivative L σ = -(primeOperator L σ * primeCurrent L σ) := by
  apply ContinuousLinearMap.ext
  intro u
  have hh := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T u)
    (prime_negative_logarithmic_derivative L σ)
  simp only [mul_apply_eq_comp, neg_apply] at hh
  have hp := congrArg (primeOperator L σ) hh
  rw [map_neg] at hp
  have hi := congrArg (fun T : Hilbert L →L[ℂ] Hilbert L => T (primeDerivative L σ u))
    (primeOperator_mul_inverse L σ)
  simp only [mul_apply_eq_comp, one_apply_eq_self] at hi
  rw [hi] at hp
  change primeDerivative L σ u = -(primeOperator L σ (primeCurrent L σ u))
  exact neg_eq_iff_eq_neg.mp hp

theorem kernelOperator_commute_of_shift {L : ℝ} (T : Hilbert L →L[ℂ] Hilbert L)
    (hT : ∀ y, Commute T (shift L y))
    (k : Lp ℂ 1 (volume.restrict (Ioo 0 L))) :
    Commute T ((shiftFamily L).kernelOperator k) := by
  apply (shiftFamily L).kernelOperator_commute T
  intro y u
  exact congrArg (fun A : Hilbert L →L[ℂ] Hilbert L => A u) (hT y).eq

theorem gammaOperator_commute_shift (L σ y : ℝ) :
    Commute (gammaOperator L σ) (shift L y) :=
  (kernelOperator_commute_of_shift (shift L y) (shift_commute L y) _).symm

theorem gammaDerivative_commute_shift (L y : ℝ) :
    Commute (gammaDerivative L) (shift L y) :=
  (kernelOperator_commute_of_shift (shift L y) (shift_commute L y) _).symm

theorem gammaOperator_commute_volterra (L : ℝ) (hL : 0 ≤ L) (σ : ℝ) (b : ℂ) :
    Commute (gammaOperator L σ) (volterra L b) :=
  (kernelOperator_commute_of_shift (volterra L b) (volterra_commute_shift L hL b) _).symm

theorem gammaDerivative_commute_volterra (L : ℝ) (hL : 0 ≤ L) (b : ℂ) :
    Commute (gammaDerivative L) (volterra L b) :=
  (kernelOperator_commute_of_shift (volterra L b) (volterra_commute_shift L hL b) _).symm

theorem gammaDerivative_commute_primeOperator (L σ : ℝ) :
    Commute (gammaDerivative L) (primeOperator L σ) :=
  primeAlgebra_commute (gammaDerivative L) (gammaDerivative_commute_shift L)
    (Arithmetic.eulerSynthesis (primeCutoff L) (primeWeight L σ))

theorem polarOperator_commute_shift (L : ℝ) (hL : 0 ≤ L) (σ y : ℝ) :
    Commute (polarOperator L σ) (shift L y) := by
  have hb (b : ℂ) : Commute (resolventFactor L b ((σ : ℂ) - 5/2)) (shift L y) := by
    apply ContinuousLinearMap.ext
    intro f
    have hc := congrArg (fun A : Hilbert L →L[ℂ] Hilbert L => A f)
      (volterra_commute_shift L hL b y).eq
    change volterra L b (shift L y f) = shift L y (volterra L b f) at hc
    change shift L y f + ((σ : ℂ) - 5/2) • volterra L b (shift L y f) =
      shift L y (f + ((σ : ℂ) - 5/2) • volterra L b f)
    rw [map_add, map_smul, hc]
  exact (hb (5/2)).mul_left (hb (3/2))

theorem gammaIntegrand_commute {L : ℝ} (T : Hilbert L →L[ℂ] Hilbert L)
    (hT : ∀ y, Commute T (shift L y)) (f : Hilbert L) (y : ℝ) :
    gammaIntegrand L (T f) y = T (gammaIntegrand L f y) := by
  have hc := congrArg (fun A : Hilbert L →L[ℂ] Hilbert L => A f) (hT y).eq
  change T (shift L y f) = shift L y (T f) at hc
  simp only [gammaIntegrand, map_add, map_smul, map_sub, hc]

/-- A bounded shift-commuting map preserves the singular-current domain. -/
theorem map_mem_gammaCurrentDomain {L : ℝ} (T : Hilbert L →L[ℂ] Hilbert L)
    (hT : ∀ y, Commute T (shift L y)) (f : gammaCurrentDomain L) :
    T (f : Hilbert L) ∈ gammaCurrentDomain L := by
  change IntegrableOn (gammaIntegrand L (T f)) (Ioo 0 L) volume
  have hi := T.integrable_comp f.property
  exact hi.congr (Filter.Eventually.of_forall fun y => (gammaIntegrand_commute T hT f y).symm)

/-- Current commutation, with its output domain inclusion supplied by the
preceding theorem rather than hidden in operator notation. -/
theorem gammaCurrent_commute {L : ℝ} (T : Hilbert L →L[ℂ] Hilbert L)
    (hT : ∀ y, Commute T (shift L y)) (f : gammaCurrentDomain L) :
    gammaCurrent L ⟨T f, map_mem_gammaCurrentDomain T hT f⟩ = T (gammaCurrent L f) := by
  change (gammaConstant L : ℂ) • T (f : Hilbert L) +
    (∫ y in Ioo 0 L, gammaIntegrand L (T f) y) =
      T ((gammaConstant L : ℂ) • (f : Hilbert L) + ∫ y in Ioo 0 L, gammaIntegrand L f y)
  rw [map_add, map_smul, ← T.integral_comp_comm f.property]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => gammaIntegrand_commute T hT f y

end Riemann.Analysis.FiniteWindow
