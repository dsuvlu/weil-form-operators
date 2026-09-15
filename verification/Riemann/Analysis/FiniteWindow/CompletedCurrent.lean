import Riemann.Analysis.FiniteWindow.CompletedFrame
import Riemann.Analysis.FiniteWindow.GammaFourierDomain
import Riemann.Analysis.FiniteWindow.SourceGramDerivative

/-! # The explicit completed current as a domain-correct form

The singular Gamma term determines the common domain. Prime and polar terms
are bounded operators restricted to that domain. In particular the full
Fourier section and every literal completed output lie in it. The form uses
two pairings, not a globally defined unbounded adjoint.
-/
noncomputable section
open scoped InnerProductSpace ComplexConjugate
namespace Riemann.Analysis.FiniteWindow

def completedCurrent (L : ℝ) : gammaCurrentDomain L →ₗ[ℂ] Hilbert L :=
  (primeCurrent L (1 / 2)).toLinearMap.comp (gammaCurrentDomain L).subtype +
    gammaCurrent L -
    (volterra L (1 / 2)).toLinearMap.comp (gammaCurrentDomain L).subtype -
    (volterra L (-(1 / 2))).toLinearMap.comp (gammaCurrentDomain L).subtype

theorem completedCurrent_apply (L : ℝ) (u : gammaCurrentDomain L) :
    completedCurrent L u = primeCurrent L (1 / 2) u + gammaCurrent L u -
      volterra L (1 / 2) u - volterra L (-(1 / 2)) u := rfl

theorem completedFrame_mem_currentDomain {L : ℝ} (hL : 0 < L) (u : Hilbert L) :
    completedFrame L (1 / 2) u ∈ gammaCurrentDomain L := by
  apply generatorDomain_le_gammaCurrentDomain hL
  rw [← range_completedFrame hL]
  exact ⟨u, rfl⟩

def completedCurrentForm (L : ℝ) (u v : gammaCurrentDomain L) : ℂ :=
  currentForm (gammaCurrentDomain L) (completedCurrent L) u v

theorem completedCurrentForm_hermitian (L : ℝ) (u v : gammaCurrentDomain L) :
    completedCurrentForm L v u = conj (completedCurrentForm L u v) :=
  currentForm_hermitian _ _ u v

/-- Full Fourier synthesis into the current domain, without an endpoint-zero
or odd-parity assumption. -/
def nativeCurrentInclusion (N : ℕ) {L : ℝ} (hL : 0 < L) :
    Riemann.CCM.Native.Section N →ₗ[ℂ] gammaCurrentDomain L :=
  (fourierInclusionLinearMap N L).codRestrict (gammaCurrentDomain L)
    fun x => fourierHilbert_mem_gammaCurrentDomain hL x

@[simp] theorem nativeCurrentInclusion_coe (N : ℕ) {L : ℝ} (hL : 0 < L)
    (x : Riemann.CCM.Native.Section N) :
    (nativeCurrentInclusion N hL x : Hilbert L) = fourierHilbert L x := rfl

end Riemann.Analysis.FiniteWindow
