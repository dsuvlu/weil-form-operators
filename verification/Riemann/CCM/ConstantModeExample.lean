import Riemann.CCM.Brightness

/-!
# A constant-ground consistency control

This one-dimensional abstract model verifies that full simple-even data are
inhabited and that the ground is allowed to coincide with the free constant
mode. It is not a claim about a literal arithmetic Fourier section.
-/

namespace Riemann.CCM

/-- Zero Hamiltonian and derivative on the complex line, with a bright endpoint. -/
noncomputable def constantModeExample : FullSimpleEvenData ℂ where
  finite_dimensional := inferInstance
  H := 0
  D := 0
  reflection := ContinuousLinearMap.id ℂ ℂ
  eta := 1
  b := 0
  ground := 1
  constant := 1
  e₀ := 0
  H_selfadjoint := by simp
  D_selfadjoint := by simp
  reflection_selfadjoint := by simp
  reflection_involutive := by intro x; rfl
  reflection_H := by intro x; simp
  reflection_D := by intro x; simp
  eta_even := by rfl
  b_odd := by simp
  ground_even := by rfl
  ground_ne_zero := by norm_num
  ground_eigen := by simp
  least := by intro x; simp
  simple := by
    intro x
    constructor
    · intro _
      exact ⟨x, by simp⟩
    · intro _
      simp
  constant_kernel := by
    intro x
    constructor
    · intro _
      exact ⟨x, by simp⟩
    · intro _
      simp
  constant_bright := by simp
  displacement := by intro x; simp

/-- An admitted abstract ground may be exactly the free constant mode. -/
theorem constantModeExample_ground_eq_constant :
    constantModeExample.ground = constantModeExample.constant := rfl

/-- The generic brightness theorem covers the zero-derivative case. -/
theorem constantModeExample_bright :
    inner ℂ constantModeExample.eta constantModeExample.ground ≠ 0 :=
  constantModeExample.ground_bright

/-- The zero-mode branch is actually exercised by this control. -/
theorem constantModeExample_derivative_ground :
    constantModeExample.D constantModeExample.ground = 0 := rfl

end Riemann.CCM
