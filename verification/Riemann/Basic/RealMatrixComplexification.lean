import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant

/-! Scalar extension of finite real matrices to the physical complex coefficient
space. The real vectors embed into, but do not exhaust, the complex space. -/
noncomputable section
open scoped InnerProductSpace BigOperators
open Matrix
namespace Riemann.Basic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scalar extension preserves a genuine nonsingular inverse. -/
theorem complexification_inverse (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    (A.map Complex.ofReal)⁻¹ = A⁻¹.map Complex.ofReal := by
  apply Matrix.inv_eq_left_inv
  change Complex.ofRealHom.mapMatrix A⁻¹ * Complex.ofRealHom.mapMatrix A = 1
  rw [← map_mul, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), map_one]

/-- The trace of the physical Euclidean operator is its coordinate trace. -/
theorem trace_toEuclideanLin {𝕜 : Type*} [RCLike 𝕜] (A : Matrix ι ι 𝕜) :
    LinearMap.trace 𝕜 _ A.toEuclideanLin = A.trace :=
  Matrix.trace_toLin_eq A (EuclideanSpace.basisFun ι 𝕜).toBasis

/-- The determinant likewise uses the same scalar field and finite coordinates. -/
theorem det_toEuclideanLin {𝕜 : Type*} [RCLike 𝕜] (A : Matrix ι ι 𝕜) :
    LinearMap.det A.toEuclideanLin = A.det :=
  LinearMap.det_toLin (EuclideanSpace.basisFun ι 𝕜).toBasis A

/-- Complexification preserves physical energy on the represented real form. -/
theorem complexification_energy (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    ⟪WithLp.toLp 2 (fun i => (x i : ℂ)),
      (A.map Complex.ofReal).toEuclideanLin (WithLp.toLp 2 (fun i => (x i : ℂ)))⟫_ℂ =
      (x ⬝ᵥ (A *ᵥ x) : ℝ) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
    dotProduct, Matrix.mulVec, mul_comm]

end Riemann.Basic
