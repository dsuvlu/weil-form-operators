import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Differentiation of finite real matrix pencils

The inverse is the ordinary nonsingular inverse, with invertibility required
at the differentiation point. All derivatives are actual real derivatives.
-/
noncomputable section
open Matrix
open scoped Matrix.Norms.Operator
namespace Riemann.Basic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : AddCommGroup (Matrix ι ι ℝ) :=
  (Matrix.linftyOpNormedAddCommGroup : NormedAddCommGroup (Matrix ι ι ℝ)).toAddCommGroup
local instance : Module ℝ (Matrix ι ι ℝ) :=
  (Matrix.linftyOpNormedSpace : NormedSpace ℝ (Matrix ι ι ℝ)).toModule
local instance : TopologicalSpace (Matrix ι ι ℝ) :=
  (Matrix.linftyOpNormedAddCommGroup : NormedAddCommGroup (Matrix ι ι ℝ)).toUniformSpace.toTopologicalSpace

/-- Actual derivative of an affine matrix pencil. -/
theorem hasDerivAt_matrixPencil (A B : Matrix ι ι ℝ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => A + t • B) B s := by
  convert! (hasDerivAt_const s A).add ((hasDerivAt_id s).smul_const B) using 1
  simp only [zero_add, one_smul]

/-- The inverse-pencil derivative retains the order of the two inverse factors. -/
theorem hasDerivAt_inverseMatrixPencil (A B : Matrix ι ι ℝ) (s : ℝ)
    (h : IsUnit (A + s • B)) :
    HasDerivAt (fun t : ℝ => (A + t • B)⁻¹)
      (-((A + s • B)⁻¹ * B * (A + s • B)⁻¹)) s := by
  obtain ⟨u, hu⟩ := h
  have hinv := (hasFDerivAt_ringInverse (𝕜 := ℝ) u)
  rw [hu] at hinv
  have hd := hinv.comp_hasDerivAt s (hasDerivAt_matrixPencil A B s)
  have hui : (↑u⁻¹ : Matrix ι ι ℝ) = (A + s • B)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  simpa only [Matrix.nonsing_inv_eq_ringInverse, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, hui, Function.comp_def] using hd

/-- The real bilinear boundary contraction, continuous in its matrix argument. -/
def matrixContraction (x y : ι → ℝ) : Matrix ι ι ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => x ⬝ᵥ (M *ᵥ y)
      map_add' := by intros; simp [add_mulVec, dotProduct_add]
      map_smul' := by intros; simp [smul_mulVec, dotProduct_smul] }

@[simp] theorem matrixContraction_apply (x y : ι → ℝ) (M : Matrix ι ι ℝ) :
    matrixContraction x y M = x ⬝ᵥ (M *ᵥ y) := rfl

/-- Scalar contraction of the actual inverse-pencil derivative. -/
theorem hasDerivAt_inverseContraction (A B : Matrix ι ι ℝ) (s : ℝ)
    (h : IsUnit (A + s • B)) (x y : ι → ℝ) :
    HasDerivAt (fun t : ℝ => x ⬝ᵥ ((A + t • B)⁻¹ *ᵥ y))
      (-(x ⬝ᵥ (((A + s • B)⁻¹ * B * (A + s • B)⁻¹) *ᵥ y))) s := by
  have hd := (matrixContraction x y).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_inverseMatrixPencil A B s h)
  simpa [Function.comp_def, neg_mulVec, dotProduct_neg] using hd

/-- Differentiating two inverse factors with a fixed matrix between them. -/
theorem hasDerivAt_doubleInverseContraction (A B C : Matrix ι ι ℝ) (s : ℝ)
    (h : IsUnit (A + s • B)) (x y : ι → ℝ) :
    HasDerivAt (fun t : ℝ => x ⬝ᵥ (((A + t • B)⁻¹ * C * (A + t • B)⁻¹) *ᵥ y))
      (x ⬝ᵥ ((-((A + s • B)⁻¹ * B * (A + s • B)⁻¹) * C * (A + s • B)⁻¹ +
        (A + s • B)⁻¹ * C * (-((A + s • B)⁻¹ * B * (A + s • B)⁻¹))) *ᵥ y)) s := by
  have hd := hasDerivAt_inverseMatrixPencil A B s h
  have hp := (hd.mul_const C).mul hd
  have hc := (matrixContraction x y).hasFDerivAt.comp_hasDerivAt s hp
  convert! hc using 1

/-- Continuity of a scalar contraction containing three inverse factors. -/
theorem continuousAt_tripleInverseContraction (A B C D : Matrix ι ι ℝ) (s : ℝ)
    (h : IsUnit (A + s • B)) (x y : ι → ℝ) :
    ContinuousAt (fun t : ℝ => x ⬝ᵥ
      (((A + t • B)⁻¹ * C * (A + t • B)⁻¹ * D * (A + t • B)⁻¹) *ᵥ y)) s := by
  have hr := (hasDerivAt_inverseMatrixPencil A B s h).continuousAt
  have hp := (((hr.mul_const C).mul hr).mul_const D).mul hr
  exact (matrixContraction x y).continuous.continuousAt.comp hp

end Riemann.Basic
