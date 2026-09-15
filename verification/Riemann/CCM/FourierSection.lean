import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Riemann.Basic.RankOne
import Mathlib.Tactic

/-! Native full Fourier coordinates. The coefficient metric is Euclidean L²,
not the supremum norm on a function array. No ground vector is selected here. -/

noncomputable section
open scoped InnerProductSpace BigOperators

namespace Riemann.CCM.Native

abbrev Index (N : ℕ) := Fin (2 * N + 1)
abbrev Section (N : ℕ) := EuclideanSpace ℂ (Index N)

def mode {N : ℕ} (i : Index N) : ℤ := (i.val : ℤ) - N
def zeroIndex (N : ℕ) : Index N := ⟨N, by omega⟩

@[simp] theorem mode_zero (N : ℕ) : mode (zeroIndex N) = 0 := by simp [mode, zeroIndex]

theorem mode_injective (N : ℕ) : Function.Injective (@mode N) := by
  intro i j h
  apply Fin.ext
  simp only [mode] at h
  omega

@[simp] theorem mode_eq_zero {N : ℕ} (i : Index N) :
    mode i = 0 ↔ i = zeroIndex N := by
  constructor
  · intro h; apply mode_injective N; simpa using h
  · rintro rfl; exact mode_zero N

/-- The centered indices cover exactly the full signed interval. -/
theorem mode_range (N : ℕ) (k : ℤ) :
    (∃ i : Index N, mode i = k) ↔ -(N : ℤ) ≤ k ∧ k ≤ N := by
  constructor
  · rintro ⟨i, rfl⟩
    have hi := i.isLt
    simp only [mode]
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨⟨(k + N).toNat, by omega⟩, ?_⟩
    simp only [mode]
    omega

@[simp] theorem mode_rev {N : ℕ} (i : Index N) : mode i.rev = -mode i := by
  simp only [mode, Fin.rev, Fin.val_mk]
  have hi := i.isLt
  omega

def frequency {N : ℕ} (L : ℝ) (i : Index N) : ℝ := (2 * Real.pi / L) * mode i

@[simp] theorem frequency_rev {N : ℕ} (L : ℝ) (i : Index N) :
    frequency L i.rev = -frequency L i := by simp [frequency]

theorem frequency_zero_iff {N : ℕ} {L : ℝ} (hL : 0 < L) (i : Index N) :
    frequency L i = 0 ↔ i = zeroIndex N := by
  have hs : 2 * Real.pi / L ≠ 0 := ne_of_gt (div_pos (by positivity) hL)
  simp [frequency, hs]

theorem frequency_injective {N : ℕ} {L : ℝ} (hL : 0 < L) :
    Function.Injective (@frequency N L) := by
  intro i j h
  have hs : 2 * Real.pi / L ≠ 0 := ne_of_gt (div_pos (by positivity) hL)
  have hm : (mode i : ℝ) = mode j := mul_left_cancel₀ hs h
  apply mode_injective N
  exact_mod_cast hm

/-- An orthonormal coefficient matrix as a continuous physical operator. -/
def ofMatrix {N : ℕ} (A : Matrix (Index N) (Index N) ℂ) : Section N →L[ℂ] Section N :=
  A.toEuclideanLin.toContinuousLinearMap

@[simp] theorem ofMatrix_apply {N : ℕ} (A : Matrix (Index N) (Index N) ℂ)
    (x : Section N) (i : Index N) : ofMatrix A x i = ∑ j, A i j * x j := rfl

theorem ofMatrix_selfadjoint {N : ℕ} (A : Matrix (Index N) (Index N) ℂ)
    (hA : A.IsHermitian) : (ofMatrix A).adjoint = ofMatrix A := by
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).isSelfAdjoint

/-- The periodic physical derivative has eigenvalue 2πn/L on mode n. -/
def derivative {N : ℕ} (L : ℝ) : Section N →L[ℂ] Section N :=
  ofMatrix (Matrix.diagonal fun i => (frequency L i : ℂ))

@[simp] theorem derivative_apply {N : ℕ} (L : ℝ) (x : Section N) (i : Index N) :
    derivative L x i = (frequency L i : ℂ) * x i := by
  simp [derivative, ofMatrix_apply, Matrix.diagonal_apply]

theorem derivative_selfadjoint {N : ℕ} (L : ℝ) :
    (@derivative N L).adjoint = derivative L := by
  apply ofMatrix_selfadjoint
  ext i j
  by_cases h : i = j
  · subst j; simp [Matrix.conjTranspose_apply]
  · simp [Matrix.conjTranspose_apply, h, Ne.symm h]

/-- Native reflection swaps modes n and −n. -/
def reflection (N : ℕ) : Section N →L[ℂ] Section N :=
  ofMatrix (fun i j => if j = i.rev then 1 else 0)

@[simp] theorem reflection_apply {N : ℕ} (x : Section N) (i : Index N) :
    reflection N x i = x i.rev := by simp [reflection]

@[simp] theorem reflection_involutive {N : ℕ} (x : Section N) :
    reflection N (reflection N x) = x := by ext i; simp

theorem reflection_selfadjoint (N : ℕ) : (reflection N).adjoint = reflection N := by
  apply ofMatrix_selfadjoint
  ext i j
  have h : i = j.rev ↔ j = i.rev := by
    constructor <;> intro h <;> rw [h] <;> simp
  simp [Matrix.conjTranspose_apply, h]

theorem reflection_derivative {N : ℕ} (L : ℝ) (x : Section N) :
    reflection N (derivative L x) = -derivative L (reflection N x) := by
  ext i
  simp

/-- The unit free constant mode, defined separately from the endpoint vector. -/
def constant (N : ℕ) : Section N := EuclideanSpace.single (zeroIndex N) 1

@[simp] theorem constant_apply {N : ℕ} (i : Index N) :
    constant N i = if i = zeroIndex N then 1 else 0 := by
  simp [constant]

theorem derivative_kernel {N : ℕ} {L : ℝ} (hL : 0 < L) (x : Section N) :
    derivative L x = 0 ↔ ∃ a : ℂ, x = a • constant N := by
  constructor
  · intro hx
    refine ⟨x (zeroIndex N), ?_⟩
    ext i
    by_cases hi : i = zeroIndex N
    · simp [hi]
    · have hfreq : (frequency L i : ℂ) ≠ 0 := by
        exact_mod_cast (mt ((frequency_zero_iff hL i).mp) hi)
      have h := congrArg (fun v : Section N => v i) hx
      have hxi : x i = 0 := (mul_eq_zero.mp (by simpa using h)).resolve_left hfreq
      simp [hi, hxi]
  · rintro ⟨a, rfl⟩
    ext i
    by_cases hi : i = zeroIndex N <;> simp [hi, frequency]

/-- Endpoint evaluation is represented by the constant coefficient vector L^(-1/2). -/
def endpointVector (N : ℕ) (L : ℝ) : Section N :=
  WithLp.toLp 2 (fun _ => ((Real.sqrt L)⁻¹ : ℂ))

@[simp] theorem endpointVector_apply (N : ℕ) (L : ℝ) (i : Index N) :
    endpointVector N L i = ((Real.sqrt L)⁻¹ : ℂ) := rfl

@[simp] theorem endpointVector_even (N : ℕ) (L : ℝ) :
    reflection N (endpointVector N L) = endpointVector N L := by ext i; simp

theorem endpoint_pairing {N : ℕ} (L : ℝ) (x : Section N) :
    ⟪endpointVector N L, x⟫_ℂ = ((Real.sqrt L)⁻¹ : ℂ) * ∑ i, x i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, Finset.sum_mul, mul_comm]

/-- The bounded endpoint row in native finite coordinates. -/
def endpoint (N : ℕ) (L : ℝ) : Section N →L[ℂ] ℂ :=
  Riemann.Basic.boundaryRow (endpointVector N L)

@[simp] theorem endpoint_apply {N : ℕ} (L : ℝ) (x : Section N) :
    endpoint N L x = ⟪endpointVector N L, x⟫_ℂ := rfl

theorem endpoint_adjoint_one (N : ℕ) (L : ℝ) :
    (endpoint N L).adjoint 1 = endpointVector N L :=
  Riemann.Basic.boundaryRow_adjoint_one _

theorem constant_bright {N : ℕ} {L : ℝ} (hL : 0 < L) :
    ⟪endpointVector N L, constant N⟫_ℂ ≠ 0 := by
  rw [endpoint_pairing]
  simp [constant_apply, ne_of_gt (Real.sqrt_pos.mpr hL)]

theorem endpointVector_norm_sq (N : ℕ) {L : ℝ} (hL : 0 < L) :
    ‖endpointVector N L‖ ^ 2 = (2 * N + 1 : ℕ) / L := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [endpointVector_apply, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg L), Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [inv_pow, Real.sq_sqrt hL.le]
  simp [div_eq_mul_inv]

/-- The actual finite Fourier polynomial represented by a coefficient vector.
This interpretation introduces no choice of arithmetic ground. -/
def fourierFunction {N : ℕ} (L : ℝ) (x : Section N) (t : ℝ) : ℂ :=
  ∑ i, x i * ((Real.sqrt L)⁻¹ : ℂ) * Complex.exp (Complex.I * (frequency L i * t))

theorem fourierFunction_zero {N : ℕ} (L : ℝ) (x : Section N) :
    fourierFunction L x 0 = ⟪endpointVector N L, x⟫_ℂ := by
  simp [fourierFunction, endpoint_pairing, Finset.sum_mul, mul_comm]

/-- The physical free frequencies have exactly the native periodic phase. -/
theorem frequency_period {N : ℕ} {L : ℝ} (hL : 0 < L) (i : Index N) :
    Complex.exp (Complex.I * (frequency L i * L)) = 1 := by
  have hp : frequency L i * L = (mode i : ℝ) * (2 * Real.pi) := by
    unfold frequency
    field_simp
  rw [← Complex.ofReal_mul, hp]
  push_cast
  rw [show Complex.I * ((mode i : ℂ) * (2 * (Real.pi : ℂ))) =
    (mode i : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I (mode i)

/-- The two endpoint evaluations agree on every native finite Fourier polynomial. -/
theorem fourierFunction_end {N : ℕ} {L : ℝ} (hL : 0 < L) (x : Section N) :
    fourierFunction L x L = ⟪endpointVector N L, x⟫_ℂ := by
  simp only [fourierFunction, frequency_period hL, mul_one]
  simp [endpoint_pairing, Finset.sum_mul, mul_comm]

end Riemann.CCM.Native
