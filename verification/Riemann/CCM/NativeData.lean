import Riemann.CCM.WeilMatrix
import Riemann.CCM.GroundComplement

/-! Native admission supplies only the true full simple-even ground hypotheses.
All finite Fourier geometry and the divided-difference displacement are derived
in the preceding modules and are inserted into the preserved first-pass API. -/

noncomputable section
open scoped InnerProductSpace

namespace Riemann.CCM.Native

variable {N : ℕ}

/-- Spectral admission for the actual full matrix. Leastness quantifies over the
entire Euclidean Fourier section, not its even block or a trial subspace. -/
structure GroundAdmission (C : Coefficients N) where
  ground : Section N
  e₀ : ℝ
  nonzero : ground ≠ 0
  even : reflection N ground = ground
  eigen : weilOperator C ground = (e₀ : ℂ) • ground
  least : ∀ x : Section N, e₀ * ‖x‖ ^ 2 ≤ (⟪x, weilOperator C x⟫_ℂ).re
  simple : ∀ x : Section N, weilOperator C x = (e₀ : ℂ) • x ↔
    ∃ a : ℂ, x = a • ground

/-- The first-pass CCM hypotheses are now instantiated on the native coordinates;
no reflection, self-adjointness, endpoint or displacement assertion is supplied
by the spectral admission. -/
def fullData (C : Coefficients N) (L : ℝ) (hL : 0 < L) (A : GroundAdmission C) :
    FullSimpleEvenData (Section N) where
  finite_dimensional := inferInstance
  H := weilOperator C
  D := derivative L
  reflection := reflection N
  eta := endpointVector N L
  b := displacementVector C L
  ground := A.ground
  constant := constant N
  e₀ := A.e₀
  H_selfadjoint := weilOperator_selfadjoint C
  D_selfadjoint := derivative_selfadjoint L
  reflection_selfadjoint := reflection_selfadjoint N
  reflection_involutive := reflection_involutive
  reflection_H := reflection_weilOperator C
  reflection_D := reflection_derivative L
  eta_even := endpointVector_even N L
  b_odd := displacementVector_odd C L
  ground_even := A.even
  ground_ne_zero := A.nonzero
  ground_eigen := A.eigen
  least := A.least
  simple := A.simple
  constant_kernel := derivative_kernel hL
  constant_bright := constant_bright hL
  displacement := native_displacement C hL

/-- The actual full ground is boundary-bright, now with all structural data
verified from native coordinates. -/
theorem native_ground_bright (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) : ⟪endpointVector N L, A.ground⟫_ℂ ≠ 0 :=
  (fullData C L hL A).ground_bright

theorem native_groundWeight_pos (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) : 0 < (fullData C L hL A).groundWeight :=
  (fullData C L hL A).groundWeight_pos

theorem native_metric_intertwining (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) :
    (fullData C L hL A).shifted.comp (fullData C L hL A).corrected =
      (fullData C L hL A).corrected.adjoint.comp (fullData C L hL A).shifted :=
  (fullData C L hL A).metric_intertwining

theorem native_corrected_eigenvalue_real (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) {x : Section N} {z : ℂ} (hx : x ≠ 0)
    (hz : (fullData C L hL A).corrected x = z • x) : z.im = 0 :=
  (fullData C L hL A).corrected_eigenvalue_real_via_complement hx hz

end Riemann.CCM.Native
