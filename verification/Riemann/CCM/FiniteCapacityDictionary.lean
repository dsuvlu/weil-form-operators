import Riemann.CCM.NativeLatticeMean
import Riemann.CCM.NativeHighLowChart
import Riemann.Capacity.FullDecomposition

/-! The finite dictionary uses the existing entire characteristic, the actual
native odd pencil, and the metric graph in its canonical Fourier chart. -/
noncomputable section
namespace Riemann.CCM.Native
open Riemann.Capacity
variable {N : ℕ}

/-- The formerly supplied lattice input is now the actual omitted sine tail. -/
theorem native_characteristic_capacity (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (hN : 0 < N) (J : ℕ) {a : ℝ} (ha : 0 < a) :
    boundarySoftMean L (fullData C L hL A).groundVector a =
      ((canonicalNativeGraphData C L hL A J).capacityWithLattice (a^2)
        (sq_pos_of_pos ha) (latticeTail L N (a^2)) : ℂ) := by
  rw [native_boundarySoftMean_eq_highMean_add_lattice C L hL A hN ha,
    GraphData.capacityWithLattice, canonicalNativeGraphData_fullMean_real C L hL A J hN]

/-- The actual characteristic slope is high + graph + coupling + free lattice. -/
theorem native_characteristic_capacity_decomposition (C : Coefficients N) (L : ℝ)
    (hL : 0 < L) (A : GroundAdmission C) (hN : 0 < N) (J : ℕ) {a : ℝ} (ha : 0 < a) :
    let P := canonicalNativeGraphData C L hL A J
    boundarySoftMean L (fullData C L hL A).groundVector a =
      ((nativeHighPencil C L hL A J).softMean (a^2) (sq_pos_of_pos ha) +
        P.graphPencil.softMean (a^2) (sq_pos_of_pos ha) +
        P.coupling (a^2) (sq_pos_of_pos ha) + latticeTail L N (a^2) : ℝ) := by
  dsimp only
  rw [native_characteristic_capacity C L hL A hN J ha,
    GraphData.capacityWithLattice_decomposition, canonicalNativeGraphData_highMean]

/-- Both bounds are pointwise at a fixed admitted carrier; no indexed-family
boundedness premise or conclusion is introduced. -/
theorem native_characteristic_capacity_bounds (C : Coefficients N) (L : ℝ)
    (hL : 0 < L) (A : GroundAdmission C) (hN : 0 < N) (J : ℕ) {a : ℝ} (ha : 0 < a) :
    let P := canonicalNativeGraphData C L hL A J
    let mu := (boundarySoftMean L (fullData C L hL A).groundVector a).re
    (nativeHighPencil C L hL A J).softMean (a^2) (sq_pos_of_pos ha) +
      P.graphPencil.softMean (a^2) (sq_pos_of_pos ha) ≤ mu ∧
    mu < (nativeHighPencil C L hL A J).softMean (a^2) (sq_pos_of_pos ha) +
      P.graphPencil.softMean (a^2) (sq_pos_of_pos ha) + 1 + latticeTail L N (a^2) := by
  dsimp only
  rw [native_characteristic_capacity C L hL A hN J ha, Complex.ofReal_re]
  have h := (canonicalNativeGraphData C L hL A J).capacityWithLattice_bounds
    (a^2) (sq_pos_of_pos ha) (latticeTail L N (a^2))
    (latticeTail_nonneg L N (sq_nonneg a))
  rwa [canonicalNativeGraphData_highMean] at h

/-- The exact same coupling in the characteristic dictionary belongs to [0,1). -/
theorem native_characteristic_coupling_bounds (C : Coefficients N) (L : ℝ)
    (hL : 0 < L) (A : GroundAdmission C) (J : ℕ) {a : ℝ} (ha : 0 < a) :
    let P := canonicalNativeGraphData C L hL A J
    0 ≤ P.coupling (a^2) (sq_pos_of_pos ha) ∧
      P.coupling (a^2) (sq_pos_of_pos ha) < 1 :=
  ⟨GraphData.coupling_nonneg _ _ _, GraphData.coupling_lt_one _ _ _⟩

/-- The finite mean is the actual positive odd-pencil trace in its physical carrier. -/
theorem native_boundarySoftMean_eq_softMean_add_lattice (C : Coefficients N)
    (L : ℝ) (hL : 0 < L) (A : GroundAdmission C) (hN : 0 < N)
    {a : ℝ} (ha : 0 < a) :
    boundarySoftMean L (fullData C L hL A).groundVector a =
      (((nativeHighPencil C L hL A 0).softMean (a^2) (sq_pos_of_pos ha) +
        latticeTail L N (a^2) : ℝ) : ℂ) := by
  rw [native_boundarySoftMean_eq_highMean_add_lattice C L hL A hN ha,
    nativeHigh_softMean_eq C L hL A 0 hN (a^2) (sq_pos_of_pos ha)]

/-- The imaginary part vanishes because the actual characteristic slope is a real positive-pencil expression. -/
theorem native_boundarySoftMean_im (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (hN : 0 < N) {a : ℝ} (ha : 0 < a) :
    (boundarySoftMean L (fullData C L hL A).groundVector a).im = 0 := by
  rw [native_boundarySoftMean_eq_highMean_add_lattice C L hL A hN ha]
  exact Complex.ofReal_im _


end Riemann.CCM.Native
