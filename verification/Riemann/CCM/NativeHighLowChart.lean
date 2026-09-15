import Riemann.CCM.NativeHighCoordinateEquiv
import Riemann.CCM.NativeGraph
import Riemann.CCM.NativeHighCoordinateDictionary

/-! Canonical physical low/high odd Fourier coordinates and their metric graph. -/
noncomputable section
open scoped InnerProductSpace BigOperators
namespace Riemann.CCM.Native
open Riemann.Basic.PositiveSchur Riemann.Capacity
variable {N J : ℕ}

abbrev LowIndex (N J : ℕ) := {j : Fin (N+1) // 0 < j.val ∧ j.val ≤ J}
abbrev LowCoordinates (N J : ℕ) := EuclideanSpace ℂ (LowIndex N J)

/-- Each positive mode occurs once, in its prescribed low or high component. -/
def lowHighIndexEquiv (N J : ℕ) : LowIndex N J ⊕ HighIndex N J ≃ HighIndex N 0 where
  toFun := Sum.elim (fun j => ⟨j.val, j.property.1⟩) (fun j => ⟨j.val, by omega⟩)
  invFun j := if h : j.val.val ≤ J then Sum.inl ⟨j.val, j.property, h⟩
    else Sum.inr ⟨j.val, by omega⟩
  left_inv j := by
    rcases j with j | j
    · simp [j.property.2]
    · simp [not_le.mpr j.property]
  right_inv j := by
    dsimp
    split_ifs <;> rfl

/-- The canonical orthogonal sum of the two coefficient blocks. -/
def lowHighMerge (N J : ℕ) : Space (LowCoordinates N J) (HighCoordinates N J) ≃ₗᵢ[ℂ]
    HighCoordinates N 0 :=
  (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℂ) 2 (fun _ : LowIndex N J ⊕ HighIndex N J => ℂ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (lowHighIndexEquiv N J))

lemma lowHighMerge_apply (x : Space (LowCoordinates N J) (HighCoordinates N J))
    (j : HighIndex N 0) : lowHighMerge N J x j =
      if h : j.val.val ≤ J then x.fst ⟨j.val, j.property, h⟩ else x.snd ⟨j.val, by omega⟩ := by
  by_cases h : j.val.val ≤ J <;> simp [lowHighMerge, lowHighIndexEquiv, Equiv.piCongrLeft', h]

/-- The complete physical odd section, with a prescribed Fourier low/high split. -/
def nativeLowHighEquiv (N J : ℕ) : Space (LowCoordinates N J) (HighCoordinates N J) ≃ₗᵢ[ℂ]
    oddHighSection N 0 := (lowHighMerge N J).trans (highCoordinateEquiv N 0)

def nativeLowHighColumns (N J : ℕ) : Space (LowCoordinates N J) (HighCoordinates N J) →L[ℂ]
    Section N := (oddHighInclusion N 0).comp (nativeLowHighEquiv N J).toContinuousLinearEquiv.toContinuousLinearMap

lemma nativeLowHighColumns_injective (N J : ℕ) : Function.Injective (nativeLowHighColumns N J) :=
  (oddHighInclusion_injective N 0).comp (nativeLowHighEquiv N J).injective

lemma nativeLowHighColumns_odd (x : Space (LowCoordinates N J) (HighCoordinates N J)) :
    reflection N (nativeLowHighColumns N J x) = -nativeLowHighColumns N J x :=
  (nativeLowHighEquiv N J x).property.1

lemma nativeLowHighColumns_range (N J : ℕ) :
    Set.range (nativeLowHighColumns N J) = (oddHighSection N 0 : Set (Section N)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (nativeLowHighEquiv N J y).property
  · intro hx
    obtain ⟨y, hy⟩ := (nativeLowHighEquiv N J).surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

lemma nativeLowHighColumns_isometry (N J : ℕ) : Isometry (nativeLowHighColumns N J) :=
  (Submodule.subtypeₗᵢ (oddHighSection N 0)).isometry.comp (nativeLowHighEquiv N J).isometry

/-- The low free square uses the same physical frequencies as the full Fourier section. -/
def lowFreeOperator (L : ℝ) (N J : ℕ) : LowCoordinates N J →L[ℂ] LowCoordinates N J :=
  (Matrix.diagonal (fun j : LowIndex N J =>
    ((highFrequency L (⟨j.val, j.property.1⟩ : HighIndex N 0) ^ 2 : ℝ) : ℂ))).toEuclideanLin.toContinuousLinearMap

lemma lowFreeOperator_apply (L : ℝ) (x : LowCoordinates N J) (j : LowIndex N J) :
    lowFreeOperator L N J x j =
      ((highFrequency L (⟨j.val, j.property.1⟩ : HighIndex N 0) ^ 2 : ℝ) : ℂ) * x j := by
  simp [lowFreeOperator, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Matrix.diagonal_apply]

lemma highFreeOperator_apply (L : ℝ) (x : HighCoordinates N J) (j : HighIndex N J) :
    highMatrixOperator ((highRealFree L N J).map Complex.ofReal) x j =
      ((highFrequency L j ^ 2 : ℝ) : ℂ) * x j := by
  simp [highMatrixOperator_apply, highRealFree, Matrix.diagonal_apply]

lemma lowHighMerge_free (L : ℝ) (x : Space (LowCoordinates N J) (HighCoordinates N J)) :
    highMatrixOperator ((highRealFree L N 0).map Complex.ofReal) (lowHighMerge N J x) =
    lowHighMerge N J (block (lowFreeOperator L N J) 0
      (highMatrixOperator ((highRealFree L N J).map Complex.ofReal)) x) := by
  ext j
  rw [highFreeOperator_apply, lowHighMerge_apply, lowHighMerge_apply]
  by_cases h : j.val.val ≤ J
  · simp [h, lowFreeOperator_apply]
  · simp [h, highRealFree, Matrix.diagonal_apply, highFrequency, highPositiveIndex]

lemma nativeLowHighColumns_free (L : ℝ)
    (x : Space (LowCoordinates N J) (HighCoordinates N J)) :
    derivative L (derivative L (nativeLowHighColumns N J x)) =
      nativeLowHighColumns N J (block (lowFreeOperator L N J) 0
        (highMatrixOperator ((highRealFree L N J).map Complex.ofReal)) x) := by
  have h := congrArg Subtype.val (highCoordinateEquiv_free L (lowHighMerge N J x))
  rw [lowHighMerge_free] at h
  exact h

/-- The BI metric graph in its canonical paired Fourier coordinates.  All
positivity and rank-one displacement fields follow from the full admission. -/
def canonicalNativeGraphData (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) : GraphData (LowCoordinates N J) (HighCoordinates N J) :=
  (fullData C L hL A).oddGraphData (nativeLowHighColumns N J)
    (nativeLowHighColumns_injective N J) (nativeLowHighColumns_odd)
    (lowFreeOperator L N J) (highMatrixOperator ((highRealFree L N J).map Complex.ofReal))
    (nativeLowHighColumns_free L)

/-- The canonical full graph pencil is the full odd pencil in physical unitary coordinates. -/
lemma canonicalNativeGraphData_fullPencil (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) :
    (canonicalNativeGraphData C L hL A J).fullPencil =
      (nativeHighPencil C L hL A 0).congruence (nativeLowHighEquiv N J).toContinuousLinearEquiv := by
  apply PositivePencil.ext
  · simp only [canonicalNativeGraphData, GraphData.fullPencil, FullSimpleEvenData.oddGraphData, PositivePencil.congruence, nativeHighPencil]
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    rw [columnEnergy_inner, Riemann.Basic.galerkinGram_inner, nativeHighEnergy, columnEnergy_inner]
    rfl
  · have hm := (fullData C L hL A).oddGraphData_metric (nativeLowHighColumns N J)
      (nativeLowHighColumns_injective N J) nativeLowHighColumns_odd
      (lowFreeOperator L N J) (highMatrixOperator ((highRealFree L N J).map Complex.ofReal))
      (nativeLowHighColumns_free L)
    change (canonicalNativeGraphData C L hL A J).fullMetric = _
    rw [show (canonicalNativeGraphData C L hL A J).fullMetric =
      columnEnergy (E := Section N) (F := Space (LowCoordinates N J) (HighCoordinates N J)) (fullData C L hL A).shifted (nativeLowHighColumns N J) from hm]
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    rw [columnEnergy_inner]
    simp only [PositivePencil.congruence, nativeHighPencil]
    rw [Riemann.Basic.galerkinGram_inner, nativeHighMass, columnEnergy_inner]
    rfl

lemma canonicalNativeGraphData_fullMean (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (s : ℝ) (hs : 0 < s) :
    (canonicalNativeGraphData C L hL A J).fullPencil.softMean s hs =
      (nativeHighPencil C L hL A 0).softMean s hs := by
  rw [canonicalNativeGraphData_fullPencil, PositivePencil.softMean_congruence]

lemma canonicalNativeGraphData_fullMean_real (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (hN : 0 < N) (s : ℝ) (hs : 0 < s) :
    (canonicalNativeGraphData C L hL A J).fullPencil.softMean s hs =
      (nativeInverseEnergyData C L hL A 0 hN).highMean s := by
  rw [canonicalNativeGraphData_fullMean, nativeHigh_softMean_eq C L hL A 0 hN s hs]

lemma lowHighMerge_inl (x : Space (LowCoordinates N J) (HighCoordinates N J))
    (j : LowIndex N J) : lowHighMerge N J x (lowHighIndexEquiv N J (Sum.inl j)) = x.fst j := by
  simp [lowHighIndexEquiv, lowHighMerge_apply, j.property.2]

lemma lowHighMerge_inr (x : Space (LowCoordinates N J) (HighCoordinates N J))
    (j : HighIndex N J) : lowHighMerge N J x (lowHighIndexEquiv N J (Sum.inr j)) = x.snd j := by
  simp [lowHighIndexEquiv, lowHighMerge_apply, not_le.mpr j.property]

lemma nativeLowHighColumns_sum (x : Space (LowCoordinates N J) (HighCoordinates N J)) :
    nativeLowHighColumns N J x =
      (∑ j : LowIndex N J, x.fst j • oddHighVector (⟨j.val, j.property.1⟩ : HighIndex N 0)) +
      ∑ j : HighIndex N J, x.snd j • oddHighVector j := by
  change (highCoordinateEquiv N 0 (lowHighMerge N J x) : Section N) = _
  rw [highCoordinateEquiv_apply, ← (lowHighIndexEquiv N J).sum_comp]
  rw [Fintype.sum_sum_type]
  simp only [lowHighMerge_inl, lowHighMerge_inr]
  rfl

lemma nativeLowHighColumns_high (x : HighCoordinates N J) :
    nativeLowHighColumns N J (highIncl (U := LowCoordinates N J) x) =
      (highCoordinateEquiv N J x : Section N) := by
  rw [nativeLowHighColumns_sum, highCoordinateEquiv_apply]
  simp [highIncl_apply]

/-- The principal high block is exactly the native high pencil in paired coordinates. -/
lemma canonicalNativeGraphData_highPencil (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) :
    (canonicalNativeGraphData C L hL A J).highPencil =
      (nativeHighPencil C L hL A J).congruence (highCoordinateEquiv N J).toContinuousLinearEquiv := by
  apply PositivePencil.ext
  · simp only [canonicalNativeGraphData, GraphData.highPencil,
      GraphData.highOperator, FullSimpleEvenData.oddGraphData, PositivePencil.congruence, nativeHighPencil]
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    rw [Riemann.Basic.galerkinGram_inner, columnEnergy_inner,
      Riemann.Basic.galerkinGram_inner, nativeHighEnergy, columnEnergy_inner]
    change ⟪derivative L (nativeLowHighColumns N J (highIncl y)),
      (fullData C L hL A).shifted (derivative L (nativeLowHighColumns N J (highIncl x)))⟫_ℂ = _
    rw [nativeLowHighColumns_high, nativeLowHighColumns_high]
    rfl
  · change (canonicalNativeGraphData C L hL A J).metric.C = _
    rw [← GraphData.high_metric]
    have hm := (fullData C L hL A).oddGraphData_metric (nativeLowHighColumns N J)
      (nativeLowHighColumns_injective N J) nativeLowHighColumns_odd
      (lowFreeOperator L N J) (highMatrixOperator ((highRealFree L N J).map Complex.ofReal))
      (nativeLowHighColumns_free L)
    rw [show (canonicalNativeGraphData C L hL A J).fullMetric =
      columnEnergy (E := Section N) (F := Space (LowCoordinates N J) (HighCoordinates N J)) (fullData C L hL A).shifted (nativeLowHighColumns N J) from hm]
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    simp only [PositivePencil.congruence, nativeHighPencil]
    rw [Riemann.Basic.galerkinGram_inner, columnEnergy_inner, nativeLowHighColumns_high,
      nativeLowHighColumns_high, Riemann.Basic.galerkinGram_inner, nativeHighMass, columnEnergy_inner]
    rfl

lemma canonicalNativeGraphData_highMean (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (s : ℝ) (hs : 0 < s) :
    (canonicalNativeGraphData C L hL A J).highPencil.softMean s hs =
      (nativeHighPencil C L hL A J).softMean s hs := by
  rw [canonicalNativeGraphData_highPencil, PositivePencil.softMean_congruence]

lemma canonicalNativeGraphData_highMean_real (C : Coefficients N) (L : ℝ) (hL : 0 < L)
    (A : GroundAdmission C) (J : ℕ) (hJN : J < N) (s : ℝ) (hs : 0 < s) :
    (canonicalNativeGraphData C L hL A J).highPencil.softMean s hs =
      (nativeInverseEnergyData C L hL A J hJN).highMean s := by
  rw [canonicalNativeGraphData_highMean, nativeHigh_softMean_eq C L hL A J hJN s hs]

end Riemann.CCM.Native
