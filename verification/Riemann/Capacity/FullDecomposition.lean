import Riemann.Capacity.SoftMeanGeometry
import Riemann.Capacity.HighGraph

/-! Exact finite full/high/graph means and their rank-one coupling. -/
noncomputable section
namespace Riemann.Capacity
open scoped InnerProductSpace
open Riemann.Basic Riemann.Basic.PositiveSchur InnerProductSpace
variable {U W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- Nonnegative quadratic differences give nonnegative trace against any
positive mass, by its finite rank-one decomposition. -/
theorem trace_mass_nonneg (D B : U →L[ℂ] U) (hB : B.IsPositive)
    (hD : ∀ x, 0 ≤ (inner ℂ x (D x)).re) :
    0 ≤ (LinearMap.trace ℂ U (D.comp B).toLinearMap).re := by
  obtain ⟨n,u,rfl⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hB
  simp only [ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.toLinearMap_sum,
    map_sum, comp_rankOne, trace_rankOne, Complex.re_sum]
  exact Finset.sum_nonneg (fun i _ => hD (u i))

/-- Exact Galerkin energy yields a lower bound for each occupied source. -/
theorem galerkin_inverse_energy_le (H : U →L[ℂ] U)
    (hH : ∀ x, x ≠ 0 → 0 < (inner ℂ x (H x)).re) (hs : H.adjoint = H)
    (Z : W →L[ℂ] U) (hZ : Function.Injective Z) (c : U) :
    (inner ℂ (Z.adjoint c)
      (positiveInverse (galerkinGram H Z) (galerkinGram_positive H Z hH hZ)
        (Z.adjoint c))).re ≤ (inner ℂ c (positiveInverse H hH c)).re := by
  have he := positiveGalerkin_energy H Z hH hZ hs c
  have hn : 0 ≤ (inner ℂ (galerkinResidual H Z hH hZ c)
      (positiveInverse H hH (galerkinResidual H Z hH hZ c))).re := by
    by_cases hz : galerkinResidual H Z hH hZ c = 0
    · simp [hz]
    · exact (positiveInverse_positive H hH
        ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hs)) _ hz).le
  change inner ℂ c (positiveInverse H hH c) = inner ℂ (Z.adjoint c)
      (positiveInverse (galerkinGram H Z) (galerkinGram_positive H Z hH hZ)
        (Z.adjoint c)) + inner ℂ (galerkinResidual H Z hH hZ c)
      (positiveInverse H hH (galerkinResidual H Z hH hZ c)) at he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re] at hr
  linarith

/-- Physical retained inclusion, before graph lifting. -/
def lowIncl : U →L[ℂ] Space U W :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ U W).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℂ U).prod (0 : U →L[ℂ] W))

omit [FiniteDimensional ℂ U] [FiniteDimensional ℂ W] in
@[simp] theorem lowIncl_apply (u : U) : lowIncl (W:=W) u = WithLp.toLp 2 (u,0) := rfl

omit [FiniteDimensional ℂ U] [FiniteDimensional ℂ W] in
theorem lowIncl_injective : Function.Injective (lowIncl (U:=U) (W:=W)) := by
  intro x y h
  exact congrArg (fun z : Space U W => z.fst) h

theorem lowIncl_adjoint (z : Space U W) : (lowIncl (U:=U) (W:=W)).adjoint z = z.fst := by
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [lowIncl_apply]

theorem block_low_gram (M : Data U W) :
    galerkinGram (block M.A M.B M.C) (lowIncl (W:=W)) = M.A := by
  ext u
  rw [galerkinGram]
  change lowIncl.adjoint (block M.A M.B M.C (lowIncl u)) = M.A u
  rw [lowIncl_adjoint]
  simp

theorem block_high_gram (M : Data U W) :
    galerkinGram (block M.A M.B M.C) (highIncl (U:=U)) = M.C := by
  ext w
  rw [galerkinGram]
  change highIncl.adjoint (block M.A M.B M.C (highIncl w)) = M.C w
  rw [highIncl_adjoint]
  simp

/-- Full inverse energy dominates the retained principal inverse energy. -/
theorem block_inverse_energy_low (M : Data U W) (u : U) :
    (inner ℂ u (positiveInverse M.A M.A_positive u)).re ≤
      (inner ℂ (lowIncl u) (positiveInverse (block M.A M.B M.C) M.positive (lowIncl u))).re := by
  have h := galerkin_inverse_energy_le (block M.A M.B M.C) M.positive M.block_adjoint
    (lowIncl (W:=W)) lowIncl_injective (lowIncl u)
  simpa [block_low_gram, lowIncl_adjoint, lowIncl_apply] using h

/-- Full inverse energy dominates the complementary principal inverse energy. -/
theorem block_inverse_energy_high (M : Data U W) (w : W) :
    (inner ℂ w (positiveInverse M.C M.C_positive w)).re ≤
      (inner ℂ (highIncl w) (positiveInverse (block M.A M.B M.C) M.positive (highIncl w))).re := by
  have h := galerkin_inverse_energy_le (block M.A M.B M.C) M.positive M.block_adjoint
    (highIncl (U:=U)) highIncl_injective (highIncl w)
  simpa [block_high_gram, highIncl_adjoint, highIncl_apply] using h

/-- Pairing the inverse with block-diagonal positive mass cannot reduce the
sum of the two principal inverse traces. -/
theorem block_inverseMassTrace_lower (M : Data U W) (R : U →L[ℂ] U) (T : W →L[ℂ] W)
    (hR : R.IsPositive) (hT : T.IsPositive) :
    (inverseMassTrace M.A M.A_positive R).re + (inverseMassTrace M.C M.C_positive T).re ≤
      (inverseMassTrace (block M.A M.B M.C) M.positive (block R 0 T)).re := by
  let Z : Space U W →L[ℂ] Space U W := positiveInverse (block M.A M.B M.C) M.positive
  have hlo : 0 ≤ (LinearMap.trace ℂ U
      ((galerkinGram Z (lowIncl (W:=W)) - positiveInverse M.A M.A_positive).comp R).toLinearMap).re := by
    apply trace_mass_nonneg _ R hR
    intro u
    simp only [sub_apply, inner_sub_right, Complex.sub_re, galerkinGram_inner]
    exact sub_nonneg.mpr (block_inverse_energy_low M u)
  have hhi : 0 ≤ (LinearMap.trace ℂ W
      ((galerkinGram Z (highIncl (U:=U)) - positiveInverse M.C M.C_positive).comp T).toLinearMap).re := by
    apply trace_mass_nonneg _ T hT
    intro w
    simp only [sub_apply, inner_sub_right, Complex.sub_re, galerkinGram_inner]
    exact sub_nonneg.mpr (block_inverse_energy_high M w)
  have hd : block R 0 T = lowIncl.comp (R.comp lowIncl.adjoint) +
      highIncl.comp (T.comp highIncl.adjoint) := by
    ext z
    simp only [add_apply, ContinuousLinearMap.comp_apply]
    rw [lowIncl_adjoint, highIncl_adjoint, diagonal_apply]
    apply (WithLp.equiv 2 (U × W)).injective
    apply Prod.ext <;> simp
  have ht : inverseMassTrace (block M.A M.B M.C) M.positive (block R 0 T) =
      LinearMap.trace ℂ U ((galerkinGram Z lowIncl).comp R).toLinearMap +
      LinearMap.trace ℂ W ((galerkinGram Z highIncl).comp T).toLinearMap := by
    unfold inverseMassTrace
    rw [hd, ContinuousLinearMap.comp_add, ContinuousLinearMap.toLinearMap_add, map_add]
    congr 1
    · change LinearMap.trace ℂ (Space U W)
        ((Z.comp lowIncl).toLinearMap.comp (R.comp lowIncl.adjoint).toLinearMap) = _
      rw [LinearMap.trace_comp_comm']
      have hc : (R.comp lowIncl.adjoint).comp (Z.comp lowIncl) =
          R.comp (galerkinGram Z lowIncl) := rfl
      change LinearMap.trace ℂ U ((R.comp lowIncl.adjoint).comp (Z.comp lowIncl)).toLinearMap = _
      rw [hc]
      exact (LinearMap.trace_comp_comm' R.toLinearMap (galerkinGram Z lowIncl).toLinearMap).symm
    · change LinearMap.trace ℂ (Space U W)
        ((Z.comp highIncl).toLinearMap.comp (T.comp highIncl.adjoint).toLinearMap) = _
      rw [LinearMap.trace_comp_comm']
      change LinearMap.trace ℂ W (T.toLinearMap.comp (galerkinGram Z highIncl).toLinearMap) = _
      exact (LinearMap.trace_comp_comm' T.toLinearMap (galerkinGram Z highIncl).toLinearMap).symm
  rw [ht, Complex.add_re]
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.toLinearMap_sub,
    map_sub, Complex.sub_re] at hlo hhi
  unfold inverseMassTrace
  linarith

namespace GraphData
variable (P : GraphData U W)

/-- The original pair, with its actual full metric. -/
def fullPencil : PositivePencil (Space U W) where
  energy := P.K
  mass := P.fullMetric
  energy_symmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp P.selfK
  mass_symmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp P.metric.block_adjoint
  energy_nonneg x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (P.positiveK x hx).le
  mass_positive := P.metric.positive

/-- The deterministic low graph carries its pulled-back physical metric. -/
def graphPencil : PositivePencil U where
  energy := P.graphOperator
  mass := P.graphMetric
  energy_symmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp P.graphOperator_adjoint
  mass_symmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp P.metric.short_adjoint
  energy_nonneg x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (P.graphOperator_positive x hx).le
  mass_positive := P.metric.short_positive

/-- The physical principal high pencil. -/
def highPencil : PositivePencil W where
  energy := P.highOperator
  mass := P.metric.C
  energy_symmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp P.highOperator_adjoint
  mass_symmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp P.metric.selfC
  energy_nonneg x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (P.highOperator_positive x hx).le
  mass_positive := P.metric.C_positive

def liftedPencil : PositivePencil (Space U W) := P.fullPencil.congruence P.graphChange
def decoupledPencil : PositivePencil (Space U W) := P.graphPencil.orthogonalSum P.highPencil

 theorem lifted_energy : P.liftedPencil.energy =
    block P.graphOperator (rankOne ℂ P.betaGraph P.zeta.snd) P.highOperator :=
  P.transformed_energy

 theorem lifted_mass : P.liftedPencil.mass = block P.graphMetric 0 P.metric.C :=
  P.transformed_metric

 theorem lifted_positive (z : Space U W) (hz : z ≠ 0) :
    0 < (inner ℂ z (P.liftedPencil.energy z)).re :=
  galerkinGram_positive P.K P.graphChange.toContinuousLinearMap P.positiveK
    P.graphChange.injective z hz

 theorem lifted_pencil (s : ℝ) : P.liftedPencil.pencil s =
    block (P.graphPencil.pencil s) (rankOne ℂ P.betaGraph P.zeta.snd)
      (P.highPencil.pencil s) := by
  unfold PositivePencil.pencil
  rw [P.lifted_energy, P.lifted_mass]
  ext z
  apply (WithLp.equiv 2 (U × W)).injective
  apply Prod.ext <;> simp [block, graphPencil, highPencil] <;> abel

/-- At every positive parameter the transformed full pencil is an actual
positive Schur problem. -/
def pencilBlocks (s : ℝ) (hs : 0 < s) : Data U W where
  A := P.graphPencil.pencil s
  B := rankOne ℂ P.betaGraph P.zeta.snd
  C := P.highPencil.pencil s
  selfA := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (P.graphPencil.pencil_symmetric s))
  selfC := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (P.highPencil.pencil_symmetric s))
  positive := by
    rw [← P.lifted_pencil]
    exact P.liftedPencil.pencil_positive s hs

/-- The complete finite mean separates into high, graph, and coupling terms. -/
def coupling (s : ℝ) (hs : 0 < s) : ℝ :=
  P.fullPencil.softMean s hs - P.graphPencil.softMean s hs - P.highPencil.softMean s hs

 theorem mean_decomposition (s : ℝ) (hs : 0 < s) :
    P.fullPencil.softMean s hs = P.highPencil.softMean s hs +
      P.graphPencil.softMean s hs + P.coupling s hs := by
  unfold coupling
  ring

 theorem coupling_eq_lifted_difference (s : ℝ) (hs : 0 < s) :
    P.coupling s hs = P.liftedPencil.softMean s hs - P.decoupledPencil.softMean s hs := by
  unfold coupling liftedPencil decoupledPencil
  rw [PositivePencil.softMean_congruence, PositivePencil.softMean_orthogonalSum]
  ring

theorem graphMetric_isPositive : P.graphMetric.IsPositive := by
  refine ⟨P.graphPencil.mass_symmetric, ?_⟩
  intro x
  change 0 ≤ (inner ℂ (P.graphMetric x) x).re
  rw [← Complex.conj_re, inner_conj_symm]
  by_cases hx : x = 0
  · simp [hx]
  · exact (P.metric.short_positive x hx).le

theorem highMetric_isPositive : P.metric.C.IsPositive := by
  refine ⟨P.highPencil.mass_symmetric, ?_⟩
  intro x
  change 0 ≤ (inner ℂ (P.metric.C x) x).re
  rw [← Complex.conj_re, inner_conj_symm]
  by_cases hx : x = 0
  · simp [hx]
  · exact (P.metric.C_positive x hx).le

theorem coupling_trace_lower (s : ℝ) (hs : 0 < s) :
    (inverseMassTrace (P.graphPencil.pencil s) (P.graphPencil.pencil_positive s hs) P.graphMetric).re +
      (inverseMassTrace (P.highPencil.pencil s) (P.highPencil.pencil_positive s hs) P.metric.C).re ≤
    (inverseMassTrace (P.liftedPencil.pencil s) (P.liftedPencil.pencil_positive s hs)
      P.liftedPencil.mass).re := by
  have h := block_inverseMassTrace_lower (P.pencilBlocks s hs) P.graphMetric P.metric.C
    P.graphMetric_isPositive P.highMetric_isPositive
  simpa only [P.lifted_pencil, P.lifted_mass, pencilBlocks] using h

 theorem coupling_nonneg (s : ℝ) (hs : 0 < s) : 0 ≤ P.coupling s hs := by
  have h := P.coupling_trace_lower s hs
  rw [P.coupling_eq_lifted_difference]
  unfold decoupledPencil
  rw [PositivePencil.softMean_orthogonalSum]
  change 0 ≤ s * (inverseMassTrace (P.liftedPencil.pencil s) _ P.liftedPencil.mass).re -
    (s * (inverseMassTrace (P.graphPencil.pencil s) _ P.graphMetric).re +
      s * (inverseMassTrace (P.highPencil.pencil s) _ P.metric.C).re)
  nlinarith

/-- The coupled and decoupled forms agree on the actual coupling-normal
hyperplane; it is not a low spectral projection. -/
theorem common_coupling_hyperplane :
    physicalCompression (vectorHyperplane (lowIncl (W:=W) P.betaGraph)) P.liftedPencil.energy =
      physicalCompression (vectorHyperplane (lowIncl (W:=W) P.betaGraph)) P.decoupledPencil.energy := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [physicalCompression_inner, physicalCompression_inner, P.lifted_energy]
  have hx : inner ℂ P.betaGraph (x : Space U W).fst = 0 := by
    have h := x.property
    change inner ℂ (lowIncl P.betaGraph) (x : Space U W) = 0 at h
    simpa using h
  have hy : inner ℂ P.betaGraph (y : Space U W).fst = 0 := by
    have h := y.property
    change inner ℂ (lowIncl P.betaGraph) (y : Space U W) = 0 at h
    simpa using h
  have hx' := inner_eq_zero_symm.mpr hx
  change inner ℂ (x : Space U W)
      (block P.graphOperator (rankOne ℂ P.betaGraph P.zeta.snd) P.highOperator y) =
    inner ℂ (x : Space U W) (block P.graphOperator 0 P.highOperator y)
  simp [block, rankOne_apply, adjoint_rankOne, inner_add_right, inner_smul_right, hx', hy]

 theorem common_coupling_mass : P.liftedPencil.mass = P.decoupledPencil.mass :=
  P.lifted_mass

/-- A vanished coupling vector makes the exact correction zero. -/
theorem coupling_eq_zero (hbeta : P.betaGraph = 0) (s : ℝ) (hs : 0 < s) :
    P.coupling s hs = 0 := by
  have he : P.liftedPencil = P.decoupledPencil := by
    apply PositivePencil.ext _ P.common_coupling_mass
    rw [P.lifted_energy, hbeta]
    change block P.graphOperator (rankOne ℂ (0:U) P.zeta.snd) P.highOperator =
      block P.graphOperator 0 P.highOperator
    simp
  rw [P.coupling_eq_lifted_difference, he, sub_self]

/-- Strict finite energy positivity gives the sharp upper coupling bound. -/
theorem coupling_lt_one (s : ℝ) (hs : 0 < s) : P.coupling s hs < 1 := by
  by_cases hb : P.betaGraph = 0
  · rw [P.coupling_eq_zero hb]
    norm_num
  · let eta : Space U W := lowIncl P.betaGraph
    have he : eta ≠ 0 := by
      intro h
      exact hb (congrArg (fun x : Space U W => x.fst) h)
    have hc : P.liftedPencil.compress (vectorHyperplane eta) =
        P.decoupledPencil.compress (vectorHyperplane eta) := by
      apply PositivePencil.ext P.common_coupling_hyperplane
      change physicalCompression _ P.liftedPencil.mass = physicalCompression _ P.decoupledPencil.mass
      rw [P.common_coupling_mass]
    have hfull := P.liftedPencil.softMean_hyperplane_lt_one P.lifted_positive s hs eta he
    have hdiag := (P.decoupledPencil.softMean_hyperplane_bounds s hs eta he).1
    rw [hc] at hfull
    rw [P.coupling_eq_lifted_difference]
    linarith

/-- The full/high/graph decomposition has a coupling in [0,1), on every
fixed admitted positive pair and every positive parameter. -/
theorem full_high_graph_bounds (s : ℝ) (hs : 0 < s) :
    P.highPencil.softMean s hs + P.graphPencil.softMean s hs ≤ P.fullPencil.softMean s hs ∧
    P.fullPencil.softMean s hs < P.highPencil.softMean s hs + P.graphPencil.softMean s hs + 1 := by
  have hlo := P.coupling_nonneg s hs
  have hhi := P.coupling_lt_one s hs
  rw [P.mean_decomposition s hs]
  constructor <;> linarith

/-- A supplied additive lattice contribution at a single parameter. This
definition does not identify an infinite sine tail or a logarithmic derivative. -/
def capacityWithLattice (s : ℝ) (hs : 0 < s) (ell : ℝ) : ℝ :=
  P.fullPencil.softMean s hs + ell

theorem capacityWithLattice_decomposition (s : ℝ) (hs : 0 < s) (ell : ℝ) :
    P.capacityWithLattice s hs ell = P.highPencil.softMean s hs +
      P.graphPencil.softMean s hs + P.coupling s hs + ell := by
  rw [capacityWithLattice, P.mean_decomposition]

/-- The lattice contribution is an explicit nonnegative input. -/
theorem capacityWithLattice_bounds (s : ℝ) (hs : 0 < s) (ell : ℝ) (hell : 0 ≤ ell) :
    P.highPencil.softMean s hs + P.graphPencil.softMean s hs ≤
      P.capacityWithLattice s hs ell ∧
    P.capacityWithLattice s hs ell <
      P.highPencil.softMean s hs + P.graphPencil.softMean s hs + 1 + ell := by
  have h := P.full_high_graph_bounds s hs
  dsimp only [capacityWithLattice]
  constructor <;> linarith [h.1, h.2]

end GraphData

end Riemann.Capacity
