import Riemann.Analysis.FiniteWindow.CompletedCurrentIdentity
import Riemann.Analysis.FiniteWindow.SourceGramDerivative
import Riemann.Analysis.FiniteWindow.NativeFourierIsometry

/-! # Actual frozen literal-source Grams

Both sources are held fixed while the completion parameter varies. The
critical Gram is the physical Gram of their literal outputs. Identification
of its derivative with a Weil form is a separate current theorem.
-/
noncomputable section
open scoped InnerProductSpace
namespace Riemann.Analysis.FiniteWindow

def completedSourceGram (L : ℝ) (u v : Hilbert L) (σ : ℝ) : ℂ :=
  ⟪completedFrame L σ u, completedFrame L σ v⟫_ℂ

theorem hasDerivAt_completedSourceGram {L : ℝ} (hL : 0 < L) (u v : Hilbert L) :
    HasDerivAt (completedSourceGram L u v)
      (⟪completedFrame L (1 / 2) u, completedDerivative L v⟫_ℂ +
        ⟪completedDerivative L u, completedFrame L (1 / 2) v⟫_ℂ) (1 / 2) :=
  hasDerivAt_frozenSourceGram (hasDerivAt_completedFrame_half hL) u v

/-- A literal source Gram agrees at the anchor with the physical output Gram. -/
theorem completedSourceGram_half {L : ℝ} (hL : 0 < L) (w z : generatorDomain L) :
    completedSourceGram L (completedSource L hL w) (completedSource L hL z) (1 / 2) =
      ⟪(w : Hilbert L), (z : Hilbert L)⟫_ℂ := by
  simp only [completedSourceGram, completedFrame_completedSource]

def completedColumnGram {ι : Type*} (L : ℝ) (U : ι → Hilbert L) (σ : ℝ) :
    Matrix ι ι ℂ := fun i j => completedSourceGram L (U i) (U j) σ

/-- Actual matrix-valued real differentiation, with a fixed finite source map. -/
theorem hasDerivAt_completedColumnGram {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 < L) (U : ι → Hilbert L) :
    HasDerivAt (completedColumnGram L U)
      (fun i j => ⟪completedFrame L (1 / 2) (U i), completedDerivative L (U j)⟫_ℂ +
        ⟪completedDerivative L (U i), completedFrame L (1 / 2) (U j)⟫_ℂ) (1 / 2) :=
  hasDerivAt_frozenSourceColumnGram (hasDerivAt_completedFrame_half hL) U

/-- Endpoint-zero Fourier columns have their actual native physical Gram,
including the original normalization of the Fourier isometry. -/
theorem nativeCompletedSourceGram_half {N : ℕ} {L : ℝ} (hL : 0 < L)
    (x y : Riemann.CCM.Native.Section N)
    (hx : Riemann.CCM.Native.endpoint N L x = 0)
    (hy : Riemann.CCM.Native.endpoint N L y = 0) :
    completedSourceGram L (nativeCompletedSource hL x hx)
      (nativeCompletedSource hL y hy) (1 / 2) = ⟪x, y⟫_ℂ := by
  simp only [completedSourceGram, completedFrame_nativeCompletedSource]
  exact fourierHilbert_inner hL x y


/-- The polarized derivative is the literal negative Hermitian current on the
actual outputs. Sources themselves may lie outside the current domain. -/
theorem hasDerivAt_completedSourceGram_current {L : ℝ} (hL : 0 < L) (u v : Hilbert L) :
    HasDerivAt (completedSourceGram L u v)
      (completedCurrentForm L
        ⟨completedFrame L (1/2) u, completedFrame_mem_currentDomain hL u⟩
        ⟨completedFrame L (1/2) v, completedFrame_mem_currentDomain hL v⟩) (1/2) := by
  apply hasDerivAt_frozenSourceGram_current (hasDerivAt_completedFrame_half hL)
    (gammaCurrentDomain L) (completedCurrent L) (completedFrame_mem_currentDomain hL)
  intro f
  simpa only [neg_neg] using congrArg Neg.neg (completedCurrent_frame_eq_neg_derivative hL f).symm

/-- The finite source-column derivative uses the same actual current pairings. -/
theorem hasDerivAt_completedColumnGram_current {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 < L) (U : ι → Hilbert L) :
    HasDerivAt (completedColumnGram L U)
      (fun i j => completedCurrentForm L
        ⟨completedFrame L (1/2) (U i), completedFrame_mem_currentDomain hL (U i)⟩
        ⟨completedFrame L (1/2) (U j), completedFrame_mem_currentDomain hL (U j)⟩) (1/2) := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_completedSourceGram_current hL (U i) (U j)

/-- The derivative for the unique literal sources of two domain vectors. -/
theorem hasDerivAt_literalSourceGram {L : ℝ} (hL : 0 < L) (w z : generatorDomain L) :
    HasDerivAt (completedSourceGram L (completedSource L hL w) (completedSource L hL z))
      (completedCurrentForm L
        ⟨w, generatorDomain_le_gammaCurrentDomain hL w.property⟩
        ⟨z, generatorDomain_le_gammaCurrentDomain hL z.property⟩) (1/2) := by
  convert hasDerivAt_completedSourceGram_current hL
    (completedSource L hL w) (completedSource L hL z) using 1
  congr 1 <;> apply Subtype.ext <;> simp only [completedFrame_completedSource]

/-- Full native Fourier form scope; endpoint zero is required for literal
sources, though the current form itself admits the full Fourier section. -/
theorem hasDerivAt_nativeCompletedSourceGram_current {N : ℕ} {L : ℝ} (hL : 0 < L)
    (x y : Riemann.CCM.Native.Section N)
    (hx : Riemann.CCM.Native.endpoint N L x = 0)
    (hy : Riemann.CCM.Native.endpoint N L y = 0) :
    HasDerivAt (completedSourceGram L (nativeCompletedSource hL x hx)
      (nativeCompletedSource hL y hy))
      (completedCurrentForm L (nativeCurrentInclusion N hL x)
        (nativeCurrentInclusion N hL y)) (1/2) := by
  convert hasDerivAt_completedSourceGram_current hL
    (nativeCompletedSource hL x hx) (nativeCompletedSource hL y hy) using 1
  congr 1 <;> apply Subtype.ext <;> simp only [completedFrame_nativeCompletedSource,
    nativeCurrentInclusion_coe]

end Riemann.Analysis.FiniteWindow
