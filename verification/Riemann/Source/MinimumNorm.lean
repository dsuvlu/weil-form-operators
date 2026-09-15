import Riemann.Basic.Projector
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Minimum-norm sources for a surjective finite observation

The observation space F is finite-dimensional; the source space E may be any
complete complex Hilbert space. The Gram inverse is constructed from
surjectivity and finite dimensionality of F.
No right inverse, minimizing source, or energy identity is assumed. All
adjoints are mathlib Hilbert-space adjoints, with conjugate-first products.
-/

noncomputable section

namespace Riemann.Source

open InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ F] in
/-- The output Gram is injective when the observation is onto. -/
theorem gram_injective (T : E →L[ℂ] F) (hT : Function.Surjective T) :
    Function.Injective (T.comp T.adjoint) := by
  have hr : T.range = ⊤ := LinearMap.range_eq_top.mpr hT
  have hk : T.adjoint.ker = ⊥ := by
    rw [← T.orthogonal_range, hr]
    simp
  have hg : (T.comp T.adjoint).ker = ⊥ := by
    rw [T.ker_self_comp_adjoint, hk]
  exact LinearMap.ker_eq_bot.mp hg

/-- The actual output Gram operator bundled with its proved inverse. -/
def gramEquiv (T : E →L[ℂ] F) (hT : Function.Surjective T) : F ≃L[ℂ] F :=
  (LinearEquiv.ofBijective (T.comp T.adjoint).toLinearMap
    ⟨gram_injective T hT, LinearMap.injective_iff_surjective.mp (gram_injective T hT)⟩).toContinuousLinearEquiv

@[simp] theorem gramEquiv_apply (T : E →L[ℂ] F) (hT : Function.Surjective T) (y : F) :
    gramEquiv T hT y = T (T.adjoint y) := rfl

/-- The canonical minimum-norm right inverse `T* (T T*)⁻¹`. -/
def minimumNormMap (T : E →L[ℂ] F) (hT : Function.Surjective T) : F →L[ℂ] E :=
  T.adjoint.comp (gramEquiv T hT).symm.toContinuousLinearMap

theorem minimumNormMap_apply (T : E →L[ℂ] F) (hT : Function.Surjective T) (y : F) :
    minimumNormMap T hT y = T.adjoint ((gramEquiv T hT).symm y) := rfl

@[simp] theorem observation_minimumNorm (T : E →L[ℂ] F) (hT : Function.Surjective T) (y : F) :
    T (minimumNormMap T hT y) = y := by
  change gramEquiv T hT ((gramEquiv T hT).symm y) = y
  exact (gramEquiv T hT).apply_symm_apply y

/-- Minimum-norm sources are orthogonal to the observation kernel. -/
theorem minimumNorm_inner_kernel (T : E →L[ℂ] F) (hT : Function.Surjective T)
    (y : F) (z : E) (hz : T z = 0) :
    inner ℂ (minimumNormMap T hT y) z = 0 := by
  rw [minimumNormMap_apply, T.adjoint_inner_left, hz]
  simp

/-- The excess source norm is exactly the squared norm of its kernel component. -/
theorem source_norm_sq_decomposition (T : E →L[ℂ] F) (hT : Function.Surjective T)
    (y : F) (x : E) (hx : T x = y) :
    ‖x‖ ^ 2 = ‖minimumNormMap T hT y‖ ^ 2 + ‖x - minimumNormMap T hT y‖ ^ 2 := by
  have hk : T (x - minimumNormMap T hT y) = 0 := by simp [hx]
  have ho := minimumNorm_inner_kernel T hT y (x - minimumNormMap T hT y) hk
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (minimumNormMap T hT y) (x - minimumNormMap T hT y) ho
  simpa only [add_sub_cancel, pow_two] using hp

/-- The constructed source minimizes the ambient norm among all exact preimages. -/
theorem minimumNorm_le (T : E →L[ℂ] F) (hT : Function.Surjective T)
    (y : F) (x : E) (hx : T x = y) : ‖minimumNormMap T hT y‖ ≤ ‖x‖ := by
  have h := source_norm_sq_decomposition T hT y x hx
  have hn := sq_nonneg ‖x - minimumNormMap T hT y‖
  nlinarith [norm_nonneg x, norm_nonneg (minimumNormMap T hT y)]

/-- Equality in the minimum-norm inequality characterizes the chosen preimage. -/
theorem minimumNorm_unique (T : E →L[ℂ] F) (hT : Function.Surjective T)
    (y : F) (x : E) (hx : T x = y)
    (hn : ‖x‖ = ‖minimumNormMap T hT y‖) : x = minimumNormMap T hT y := by
  have h := source_norm_sq_decomposition T hT y x hx
  have hz : ‖x - minimumNormMap T hT y‖ = 0 := by rw [hn] at h; nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Output energy in the inverse Gram equals the minimum source energy. -/
theorem minimumNorm_energy (T : E →L[ℂ] F) (hT : Function.Surjective T) (y : F) :
    ‖minimumNormMap T hT y‖ ^ 2 =
      (inner ℂ y ((gramEquiv T hT).symm y)).re := by
  have h := T.adjoint_inner_right (minimumNormMap T hT y) ((gramEquiv T hT).symm y)
  rw [← minimumNormMap_apply, observation_minimumNorm] at h
  have hr := congrArg Complex.re h
  have hself : (inner ℂ (minimumNormMap T hT y) (minimumNormMap T hT y)).re =
      ‖minimumNormMap T hT y‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hself] at hr
  exact hr

/-- Exact error energy between two canonical sources. -/
theorem minimumNorm_error_energy (T : E →L[ℂ] F) (hT : Function.Surjective T) (y z : F) :
    ‖minimumNormMap T hT y - minimumNormMap T hT z‖ ^ 2 =
      (inner ℂ (y - z) ((gramEquiv T hT).symm (y - z))).re := by
  rw [← map_sub]
  exact minimumNorm_energy T hT (y - z)

/-- The inverse-Gram energy is the attained least squared norm of an exact source. -/
theorem minimumNorm_isLeast (T : E →L[ℂ] F) (hT : Function.Surjective T) (y : F) :
    IsLeast {r : ℝ | ∃ x : E, T x = y ∧ ‖x‖ ^ 2 = r}
      (inner ℂ y ((gramEquiv T hT).symm y)).re := by
  refine ⟨⟨minimumNormMap T hT y, observation_minimumNorm T hT y,
    minimumNorm_energy T hT y⟩, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  rw [← minimumNorm_energy T hT y]
  have hd := source_norm_sq_decomposition T hT y x hx
  nlinarith [sq_nonneg ‖x - minimumNormMap T hT y‖]

/-- Infimum formulation of the exact minimum-source energy. -/
theorem minimumNorm_sInf (T : E →L[ℂ] F) (hT : Function.Surjective T) (y : F) :
    sInf {r : ℝ | ∃ x : E, T x = y ∧ ‖x‖ ^ 2 = r} =
      (inner ℂ y ((gramEquiv T hT).symm y)).re :=
  (minimumNorm_isLeast T hT y).csInf_eq

end Riemann.Source
