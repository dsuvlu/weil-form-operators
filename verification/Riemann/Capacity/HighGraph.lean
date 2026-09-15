import Riemann.Basic.PositiveSchurTransitivity
import Riemann.Basic.RankOne

/-!
# The graph of a positive metric and its structured pencil

The retained graph uses the full metric B, not the unmodified low inclusion.
This is the exact fixed-carrier algebra of BI G1–G2 and BJ HB1.
-/
noncomputable section
namespace Riemann.Capacity
open scoped InnerProductSpace
open Riemann.Basic Riemann.Basic.PositiveSchur InnerProductSpace

variable {U W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- Physical complementary inclusion, with no graph modification. -/
def highIncl : W →L[ℂ] Space U W :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ U W).symm.toContinuousLinearMap.comp
    ((0 : W →L[ℂ] U).prod (ContinuousLinearMap.id ℂ W))

omit [FiniteDimensional ℂ U] [FiniteDimensional ℂ W] in
@[simp] theorem highIncl_apply (w : W) : highIncl (U:=U) w = WithLp.toLp 2 (0,w) := rfl

omit [FiniteDimensional ℂ U] [FiniteDimensional ℂ W] in
theorem highIncl_injective : Function.Injective (highIncl (U:=U) (W:=W)) := by
  intro x y h
  exact congrArg (fun z : Space U W => z.snd) h

theorem highIncl_adjoint (z : Space U W) : (highIncl (U:=U) (W:=W)).adjoint z = z.snd := by
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [highIncl_apply]

/-- An admitted positive structured pair on one fixed carrier. The diagonal
free operator is supplied in the physical orthogonal split. -/
structure GraphData (U W : Type*) [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [FiniteDimensional ℂ U] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] where
  metric : Data U W
  K : Space U W →L[ℂ] Space U W
  selfK : K.adjoint = K
  positiveK : ∀ z, z ≠ 0 → 0 < (inner ℂ z (K z)).re
  A₁ : U →L[ℂ] U
  A₂ : W →L[ℂ] W
  beta : Space U W
  zeta : Space U W
  displacement : K = (block metric.A metric.B metric.C).comp (block A₁ 0 A₂) +
    rankOne ℂ beta zeta

namespace GraphData
variable (P : GraphData U W)

abbrev fullMetric := block P.metric.A P.metric.B P.metric.C
abbrev graphMetric := P.metric.short
abbrev graphLift := P.metric.liftMap

def graphOperator : U →L[ℂ] U := galerkinGram P.K P.graphLift
def highOperator : W →L[ℂ] W := galerkinGram P.K highIncl
def betaGraph : U := P.graphLift.adjoint P.beta
def zetaGraph : U := P.graphLift.adjoint P.zeta

 theorem graphOperator_adjoint : P.graphOperator.adjoint = P.graphOperator :=
  galerkinGram_selfAdjoint P.K P.graphLift P.selfK

 theorem highOperator_adjoint : P.highOperator.adjoint = P.highOperator :=
  galerkinGram_selfAdjoint P.K highIncl P.selfK

 theorem graphOperator_positive (u : U) (hu : u ≠ 0) :
    0 < (inner ℂ u (P.graphOperator u)).re :=
  galerkinGram_positive P.K P.graphLift P.positiveK P.metric.liftMap_injective u hu

 theorem highOperator_positive (w : W) (hw : w ≠ 0) :
    0 < (inner ℂ w (P.highOperator w)).re :=
  galerkinGram_positive P.K highIncl P.positiveK highIncl_injective w hw

 theorem metric_graph_high (u : U) (w : W) :
    inner ℂ (P.graphLift u) (P.fullMetric (highIncl w)) = 0 := by
  unfold fullMetric
  rw [← P.metric.block_adjoint, ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (block P.metric.A P.metric.B P.metric.C (P.metric.lift u))
    (WithLp.toLp 2 (0,w)) = 0
  rw [P.metric.block_lift]
  simp

 theorem graph_metric : galerkinGram P.fullMetric P.graphLift = P.graphMetric :=
  P.metric.graph_gram

 theorem high_metric : galerkinGram P.fullMetric (highIncl (U:=U)) = P.metric.C := by
  ext w
  apply ext_inner_left ℂ
  intro v
  rw [galerkinGram_inner]
  simp [fullMetric, highIncl_apply]

/-- The cross block after the metric graph lift is genuinely rank one. -/
theorem graph_high_cross (u : U) (w : W) :
    inner ℂ (P.graphLift u) (P.K (highIncl w)) =
      inner ℂ u P.betaGraph * inner ℂ P.zeta.snd w := by
  rw [P.displacement]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    inner_add_right, rankOne_apply]
  have hfree : block P.A₁ 0 P.A₂ (highIncl w) = highIncl (P.A₂ w) := by simp
  rw [hfree, P.metric_graph_high, zero_add, inner_smul_right]
  rw [← P.graphLift.adjoint_inner_right]
  change inner ℂ P.zeta (WithLp.toLp 2 (0,w)) * inner ℂ u P.betaGraph = _
  simp [mul_comm]

/-- Native high principal restriction: the diagonal free block prevents a
spurious low cross term in K22=B22 A2+beta2 zeta2*. -/
theorem high_displacement : P.highOperator = P.metric.C.comp P.A₂ +
    rankOne ℂ P.beta.snd P.zeta.snd := by
  ext w
  apply ext_inner_left ℂ
  intro v
  unfold highOperator
  rw [galerkinGram_inner, P.displacement]
  simp [highIncl_apply, rankOne_apply, inner_add_right, inner_smul_right]

/-- The metric graph kills every complementary column in the B pairing. -/
theorem metric_graph_pairing (u : U) (z : Space U W) :
    inner ℂ (P.graphLift u) (P.fullMetric z) = inner ℂ u (P.graphMetric z.fst) := by
  unfold fullMetric
  rw [← P.metric.block_adjoint, ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (block P.metric.A P.metric.B P.metric.C (P.metric.lift u)) z = _
  rw [P.metric.block_lift]
  change inner ℂ (P.metric.short u) z.fst + inner ℂ (0:W) z.snd = _
  rw [inner_zero_left, add_zero, ← P.metric.short_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

/-- The low graph retains the original rank-one pencil identity. -/
theorem graph_displacement : P.graphOperator = P.graphMetric.comp P.A₁ +
    rankOne ℂ P.betaGraph P.zetaGraph := by
  ext u
  apply ext_inner_left ℂ
  intro v
  unfold graphOperator
  rw [galerkinGram_inner, P.displacement]
  simp only [add_apply, ContinuousLinearMap.comp_apply, inner_add_right, rankOne_apply,
    inner_smul_right]
  rw [P.metric_graph_pairing]
  have hf : (block P.A₁ 0 P.A₂ (P.graphLift u)).fst = P.A₁ u := by
    change P.A₁ u + (0 : W →L[ℂ] U) (-P.metric.inverseC (P.metric.B.adjoint u)) = P.A₁ u
    simp
  rw [hf]
  change inner ℂ v (P.graphMetric (P.A₁ u)) +
    inner ℂ P.zeta (P.graphLift u) * inner ℂ (P.graphLift v) P.beta = _
  rw [← P.graphLift.adjoint_inner_left, ← P.graphLift.adjoint_inner_right]
  simp only [betaGraph, zetaGraph]

/-- The invertible triangular graph change, not a physical isometry. -/
def graphChange : Space U W ≃L[ℂ] Space U W :=
  ContinuousLinearEquiv.equivOfInverse
    (row P.graphLift highIncl)
    ((ContinuousLinearMap.id ℂ (Space U W)) +
      highIncl.comp (P.metric.inverseC.comp (P.metric.B.adjoint.comp (WithLp.fstL 2 ℂ U W))))
    (by
      intro z
      apply (WithLp.equiv 2 (U × W)).injective
      apply Prod.ext
      · change (z.fst + 0) + 0 = z.fst
        simp
      · change -P.metric.inverseC (P.metric.B.adjoint z.fst) + z.snd +
          P.metric.inverseC (P.metric.B.adjoint (z.fst + 0)) = z.snd
        simp only [add_zero]
        abel)
    (by
      intro z
      apply (WithLp.equiv 2 (U × W)).injective
      apply Prod.ext
      · change (z.fst + 0) + 0 = z.fst
        simp
      · change -P.metric.inverseC (P.metric.B.adjoint (z.fst + 0)) +
          (z.snd + P.metric.inverseC (P.metric.B.adjoint z.fst)) = z.snd
        simp only [add_zero]
        abel)

@[simp] theorem graphChange_apply (u : U) (w : W) :
    P.graphChange (WithLp.toLp 2 (u,w)) = P.graphLift u + highIncl w := rfl

/-- Both metric blocks are retained by the actual triangular congruence. -/
theorem transformed_metric :
    galerkinGram P.fullMetric P.graphChange.toContinuousLinearMap =
      block P.graphMetric 0 P.metric.C := by
  ext z
  apply ext_inner_left ℂ
  intro y
  rw [galerkinGram_inner]
  change inner ℂ (P.graphLift y.fst + highIncl y.snd)
    (P.fullMetric (P.graphLift z.fst + highIncl z.snd)) = _
  rw [map_add, inner_add_left, inner_add_right, inner_add_right,
    P.metric_graph_high]
  have hc : inner ℂ (highIncl y.snd) (P.fullMetric (P.graphLift z.fst)) = 0 := by
    change inner ℂ (WithLp.toLp 2 ((0:U),y.snd))
      (block P.metric.A P.metric.B P.metric.C (P.metric.lift z.fst)) = 0
    rw [P.metric.block_lift]
    simp
  rw [hc, zero_add, add_zero]
  change inner ℂ (P.metric.lift y.fst)
    (block P.metric.A P.metric.B P.metric.C (P.metric.lift z.fst)) +
      inner ℂ (WithLp.toLp 2 ((0:U),y.snd))
        (block P.metric.A P.metric.B P.metric.C (WithLp.toLp 2 (0,z.snd))) = _
  rw [P.metric.short_inner]
  simp [block, graphMetric]

/-- The full transformed energy retains its rank-one high/graph coupling. -/
theorem transformed_energy :
    galerkinGram P.K P.graphChange.toContinuousLinearMap =
      block P.graphOperator (rankOne ℂ P.betaGraph P.zeta.snd) P.highOperator := by
  ext z
  apply ext_inner_left ℂ
  intro y
  rw [galerkinGram_inner]
  change inner ℂ (P.graphLift y.fst + highIncl y.snd)
    (P.K (P.graphLift z.fst + highIncl z.snd)) = _
  rw [map_add, inner_add_left, inner_add_right, inner_add_right,
    P.graph_high_cross]
  have hc : inner ℂ (highIncl y.snd) (P.K (P.graphLift z.fst)) =
      inner ℂ y.snd P.zeta.snd * inner ℂ P.betaGraph z.fst := by
    rw [← P.selfK, ContinuousLinearMap.adjoint_inner_right]
    rw [← inner_conj_symm, P.graph_high_cross]
    simp only [map_mul, inner_conj_symm]
    ring
  rw [hc]
  rw [← galerkinGram_inner, ← galerkinGram_inner]
  change inner ℂ y.fst (P.graphOperator z.fst) +
      inner ℂ y.fst P.betaGraph * inner ℂ P.zeta.snd z.snd +
      (inner ℂ y.snd P.zeta.snd * inner ℂ P.betaGraph z.fst +
        inner ℂ y.snd (P.highOperator z.snd)) = _
  change _ = inner ℂ y.fst (P.graphOperator z.fst +
      (rankOne ℂ P.betaGraph P.zeta.snd) z.snd) +
    inner ℂ y.snd ((rankOne ℂ P.betaGraph P.zeta.snd).adjoint z.fst +
      P.highOperator z.snd)
  simp only [inner_add_right, rankOne_apply, inner_smul_right, adjoint_rankOne]
  ring

end GraphData
end Riemann.Capacity
