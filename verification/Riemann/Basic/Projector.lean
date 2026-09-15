import Riemann.Basic.RankOne
import Mathlib.Tactic

/-!
# Boundary normalization of an orthogonal projector

The hypotheses are ordinary idempotence and the actual Hilbert-space adjoint
identity. Brightness is supplied by a fixed vector with nonzero boundary
observation, not assumed of the projector-normalized answer.
-/

noncomputable section

namespace Riemann.Basic

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The real boundary weight; the complex pairing dictionary is proved below. -/
def boundaryWeight (P : E →L[ℂ] E) (η : E) : ℝ := ‖P η‖ ^ 2

/-- Projector-based normalization, independent of an eigenvector phase. -/
def projectorNormalized (P : E →L[ℂ] E) (η : E) : E :=
  ((boundaryWeight P η : ℂ)⁻¹) • P η

theorem inner_projector_eq_weight (P : E →L[ℂ] E)
    (hP : P.comp P = P) (hPstar : P.adjoint = P) (η : E) :
    inner ℂ η (P η) = (boundaryWeight P η : ℂ) := by
  have hPP : P (P η) = P η := congrArg (fun A : E →L[ℂ] E => A η) hP
  calc
    inner ℂ η (P η) = inner ℂ η (P (P η)) := by rw [hPP]
    _ = inner ℂ (P.adjoint η) (P η) := (P.adjoint_inner_left (P η) η).symm
    _ = inner ℂ (P η) (P η) := by rw [hPstar]
    _ = (boundaryWeight P η : ℂ) := by
      simp [boundaryWeight, inner_self_eq_norm_sq_to_K]

/-- The literal row-projector-adjoint scalar equals the real boundary weight. -/
theorem boundaryRow_projector_adjoint (P : E →L[ℂ] E)
    (hP : P.comp P = P) (hPstar : P.adjoint = P) (η : E) :
    boundaryRow η (P ((boundaryRow η).adjoint 1)) = (boundaryWeight P η : ℂ) := by
  rw [boundaryRow_adjoint_one, boundaryRow_apply]
  exact inner_projector_eq_weight P hP hPstar η

theorem projector_boundary_ne_zero (P : E →L[ℂ] E) (hPstar : P.adjoint = P)
    (η u : E) (hPu : P u = u) (hu : inner ℂ η u ≠ 0) : P η ≠ 0 := by
  intro hzero
  apply hu
  calc
    inner ℂ η u = inner ℂ η (P u) := by rw [hPu]
    _ = inner ℂ (P.adjoint η) u := (P.adjoint_inner_left u η).symm
    _ = 0 := by rw [hPstar, hzero]; simp

omit [CompleteSpace E] in
theorem boundaryWeight_pos (P : E →L[ℂ] E) (η : E) (h : P η ≠ 0) :
    0 < boundaryWeight P η := by
  exact sq_pos_of_pos (norm_pos_iff.mpr h)

theorem projectorNormalized_boundary (P : E →L[ℂ] E)
    (hP : P.comp P = P) (hPstar : P.adjoint = P) (η : E) (hη : P η ≠ 0) :
    inner ℂ η (projectorNormalized P η) = 1 := by
  have hq : (boundaryWeight P η : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (boundaryWeight_pos P η hη))
  simp [projectorNormalized, inner_smul_right,
    inner_projector_eq_weight P hP hPstar η, hq]

omit [CompleteSpace E] in
theorem projectorNormalized_fixed (P : E →L[ℂ] E) (hP : P.comp P = P) (η : E) :
    P (projectorNormalized P η) = projectorNormalized P η := by
  have hPP : P (P η) = P η := congrArg (fun A : E →L[ℂ] E => A η) hP
  simp [projectorNormalized, hPP]

omit [CompleteSpace E] in
theorem projectorNormalized_norm_sq (P : E →L[ℂ] E) (η : E) (hη : P η ≠ 0) :
    ‖projectorNormalized P η‖ ^ 2 = (boundaryWeight P η)⁻¹ := by
  have hq := boundaryWeight_pos P η hη
  have hn : ‖P η‖ ^ 2 = boundaryWeight P η := rfl
  calc
    ‖projectorNormalized P η‖ ^ 2 =
        ((boundaryWeight P η)⁻¹) ^ 2 * ‖P η‖ ^ 2 := by
      simp [projectorNormalized, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hq, mul_pow]
    _ = (boundaryWeight P η)⁻¹ := by rw [hn]; field_simp

omit [CompleteSpace E] in
/-- Any nonzero boundary observation gives a unique normalized point on a line. -/
theorem normalized_line_unique (η u v : E) (hu : inner ℂ η u ≠ 0)
    (hv : v ∈ Submodule.span ℂ {u}) (hδv : inner ℂ η v = 1) :
    v = (inner ℂ η u)⁻¹ • u := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have ha : a * inner ℂ η u = 1 := by simpa only [inner_smul_right] using hδv
  have hae : a = (inner ℂ η u)⁻¹ := by
    apply (mul_right_cancel₀ hu)
    simpa [hu] using ha
  rw [hae]

theorem projectorNormalized_eq_normalized_ground (P : E →L[ℂ] E)
    (hP : P.comp P = P) (hPstar : P.adjoint = P) (η u : E)
    (hPu : P u = u) (hu : inner ℂ η u ≠ 0)
    (hrange : P.range = Submodule.span ℂ {u}) :
    projectorNormalized P η = (inner ℂ η u)⁻¹ • u := by
  have hη := projector_boundary_ne_zero P hPstar η u hPu hu
  apply normalized_line_unique η u
  · exact hu
  · rw [← hrange]
    exact ⟨projectorNormalized P η, projectorNormalized_fixed P hP η⟩
  · exact projectorNormalized_boundary P hP hPstar η hη

/-- The actual orthogonal projection onto a vector's line. -/
def lineProjector (u : E) : E →L[ℂ] E := (Submodule.span ℂ {u}).starProjection

omit [CompleteSpace E] in
@[simp] theorem lineProjector_comp (u : E) : (lineProjector u).comp (lineProjector u) = lineProjector u := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem (Submodule.span ℂ {u}) x)

@[simp] theorem lineProjector_adjoint (u : E) : (lineProjector u).adjoint = lineProjector u :=
  (isSelfAdjoint_starProjection (Submodule.span ℂ {u})).adjoint_eq

omit [CompleteSpace E] in
@[simp] theorem lineProjector_self (u : E) : lineProjector u u = u :=
  Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self u)

omit [CompleteSpace E] in
@[simp] theorem lineProjector_range (u : E) : (lineProjector u).range = Submodule.span ℂ {u} :=
  Submodule.range_starProjection (Submodule.span ℂ {u})

/-- Specialization to the constructed ground-line projector, with no projector laws assumed. -/
theorem lineProjectorNormalized_eq (η u : E) (hu : inner ℂ η u ≠ 0) :
    projectorNormalized (lineProjector u) η = (inner ℂ η u)⁻¹ • u :=
  projectorNormalized_eq_normalized_ground (lineProjector u) (lineProjector_comp u)
    (lineProjector_adjoint u) η u (lineProjector_self u) hu (lineProjector_range u)

end Riemann.Basic
