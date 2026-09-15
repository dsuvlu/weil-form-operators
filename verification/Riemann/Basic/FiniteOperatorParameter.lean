import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Elementary norm derivatives of finite operator families

The abstract Hilbert carrier keeps scalar-restriction instances uniform when
these lemmas are instantiated on a supported L² subspace.
-/

noncomputable section
namespace Riemann.Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A finite linear combination of fixed bounded operators has the actual
operator-norm derivative obtained by differentiating its scalar coefficients. -/
theorem hasDerivAt_operator_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℂ) (f' : ι → ℂ) (T : ι → E →L[ℂ] E) (σ : ℝ)
    (hf : ∀ i ∈ s, HasDerivAt (f i) (f' i) σ) :
    HasDerivAt (fun t => ∑ i ∈ s, f i t • T i) (∑ i ∈ s, f' i • T i) σ := by
  apply HasDerivAt.fun_sum
  intro i hi
  exact (hf i hi).smul_const (T i)

/-- Product rule in the actual bounded-operator norm. -/
theorem hasDerivAt_operator_mul {F G : ℝ → E →L[ℂ] E}
    {F' G' : E →L[ℂ] E} {σ : ℝ}
    (hF : HasDerivAt F F' σ) (hG : HasDerivAt G G' σ) :
    HasDerivAt (fun s => F s * G s) (F' * G σ + F σ * G') σ := by
  exact hF.mul hG

/-- An affine scalar perturbation of the identity. -/
theorem hasDerivAt_operator_affine (T : E →L[ℂ] E) (c : ℂ) (σ : ℝ) :
    HasDerivAt (fun s : ℝ => 1 + ((s : ℂ) - c) • T) T σ := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := σ)).sub_const c).smul_const T
  convert! (hasDerivAt_const σ (1 : E →L[ℂ] E)).add h using 1
  simp only [zero_add, Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]

end Riemann.Basic
