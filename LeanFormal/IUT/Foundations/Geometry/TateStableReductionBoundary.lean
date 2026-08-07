import LeanFormal.IUT.Foundations.Geometry.TateCurveLocalReduction
import Iut.Foundations.SourceTateStableGraph

namespace LeanFormal.IUT

open Polynomial

noncomputable section

namespace TateCurvePadic

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

abbrev StableResidueField : Type := IsLocalRing.ResidueField ℤ_[l.value]

structure CanonicalStableReductionBoundary where
  localReduction : CanonicalLocalReductionPacket l
  graph : Iut.SourceTateStableGraphCertificate
  reducedCurve : WeierstrassCurve (StableResidueField l)
  reducedCurve_eq_nodal : reducedCurve = nodalCurve l
  tangentPolynomial : (StableResidueField l)[X]
  tangentPolynomial_eq :
    tangentPolynomial = X * (X + C 1)
  tangentPolynomial_splits : Polynomial.Splits tangentPolynomial
  tangentPolynomial_monic : tangentPolynomial.Monic
  tangentPolynomial_degree : tangentPolynomial.natDegree = 2
  branch_zero : StableResidueField l
  branch_neg_one : StableResidueField l
  branch_zero_eq : branch_zero = 0
  branch_neg_one_eq : branch_neg_one = -1
  branch_distinct : branch_zero ≠ branch_neg_one
  normalizedPoint : StableResidueField l →
    StableResidueField l × StableResidueField l
  normalizedPoint_onCurve : ∀ t,
    NodalNormalization.OnCurve (normalizedPoint t).1
      (normalizedPoint t).2
  normalizedPoint_node_iff : ∀ t,
    normalizedPoint t = (0, 0) ↔ t = branch_zero ∨ t = branch_neg_one
  normalizedPoint_injective_off_node : ∀ {s t},
    s ≠ branch_zero ∧ s ≠ branch_neg_one →
      normalizedPoint s = normalizedPoint t → s = t

def canonicalStableReductionBoundary : CanonicalStableReductionBoundary l where
  localReduction := canonicalLocalReductionPacket l
  graph := Iut.sourceTateStableGraphCertificate
  reducedCurve := nodalCurve l
  reducedCurve_eq_nodal := rfl
  tangentPolynomial := nodalTangentPolynomial l
  tangentPolynomial_eq := nodalTangentPolynomial_eq_X_mul_X_add_C_one l
  tangentPolynomial_splits := nodalTangentPolynomial_splits l
  tangentPolynomial_monic := nodalTangentPolynomial_monic l
  tangentPolynomial_degree := nodalTangentPolynomial_natDegree l
  branch_zero := 0
  branch_neg_one := -1
  branch_zero_eq := rfl
  branch_neg_one_eq := rfl
  branch_distinct := nodalTangent_roots_distinct l
  normalizedPoint := reducedNodalPoint l
  normalizedPoint_onCurve := reducedNodalPoint_satisfies l
  normalizedPoint_node_iff := reducedNodalPoint_eq_node_iff l
  normalizedPoint_injective_off_node := by
    intro s t hs hst
    exact reducedNodalPoint_injective_off_node l hs hst

theorem canonicalStableReductionBoundary_local_curve :
    (canonicalStableReductionBoundary l).localReduction.curve =
      canonicalCurve l := by
  rfl

theorem canonicalStableReductionBoundary_integral :
    WeierstrassCurve.IsIntegral ℤ_[l.value]
      (canonicalStableReductionBoundary l).localReduction.curve :=
  (canonicalStableReductionBoundary l).localReduction.integral

theorem canonicalStableReductionBoundary_minimal :
    WeierstrassCurve.IsMinimal ℤ_[l.value]
      (canonicalStableReductionBoundary l).localReduction.curve :=
  (canonicalStableReductionBoundary l).localReduction.minimal

theorem canonicalStableReductionBoundary_elliptic :
    (canonicalStableReductionBoundary l).localReduction.curve.IsElliptic :=
  (canonicalStableReductionBoundary l).localReduction.elliptic

theorem canonicalStableReductionBoundary_delta_nonzero :
    (canonicalStableReductionBoundary l).localReduction.curve.Δ ≠ 0 :=
  (canonicalStableReductionBoundary l).localReduction.delta_nonzero

theorem canonicalStableReductionBoundary_delta_valuation_lt_one :
    (IsDiscreteValuationRing.maximalIdeal ℤ_[l.value]).valuation
        ℚ_[l.value] (canonicalStableReductionBoundary l).localReduction.curve.Δ < 1 :=
  (canonicalStableReductionBoundary l).localReduction.delta_valuation_lt_one

theorem canonicalStableReductionBoundary_c4_valuation_eq_one :
    (IsDiscreteValuationRing.maximalIdeal ℤ_[l.value]).valuation
        ℚ_[l.value] (canonicalStableReductionBoundary l).localReduction.curve.c₄ = 1 :=
  (canonicalStableReductionBoundary l).localReduction.c4_valuation_eq_one

theorem canonicalStableReductionBoundary_multiplicative :
    (canonicalStableReductionBoundary l).localReduction.curve.HasMultiplicativeReduction
      ℤ_[l.value] :=
  (canonicalStableReductionBoundary l).localReduction.multiplicative

theorem canonicalStableReductionBoundary_splitMultiplicative :
    (canonicalStableReductionBoundary l).localReduction.curve.HasSplitMultiplicativeReduction
      ℤ_[l.value] :=
  (canonicalStableReductionBoundary l).localReduction.splitMultiplicative

theorem canonicalStableReductionBoundary_reducedCurve :
    (canonicalStableReductionBoundary l).reducedCurve = nodalCurve l :=
  (canonicalStableReductionBoundary l).reducedCurve_eq_nodal

theorem canonicalStableReductionBoundary_tangentPolynomial :
    (canonicalStableReductionBoundary l).tangentPolynomial =
      X * (X + C 1) :=
  (canonicalStableReductionBoundary l).tangentPolynomial_eq

theorem canonicalStableReductionBoundary_tangent_splits :
    Polynomial.Splits (canonicalStableReductionBoundary l).tangentPolynomial :=
  (canonicalStableReductionBoundary l).tangentPolynomial_splits

theorem canonicalStableReductionBoundary_tangent_monic :
    (canonicalStableReductionBoundary l).tangentPolynomial.Monic :=
  (canonicalStableReductionBoundary l).tangentPolynomial_monic

theorem canonicalStableReductionBoundary_tangent_degree :
    (canonicalStableReductionBoundary l).tangentPolynomial.natDegree = 2 :=
  (canonicalStableReductionBoundary l).tangentPolynomial_degree

theorem canonicalStableReductionBoundary_branch_zero :
    (canonicalStableReductionBoundary l).branch_zero = 0 :=
  (canonicalStableReductionBoundary l).branch_zero_eq

theorem canonicalStableReductionBoundary_branch_neg_one :
    (canonicalStableReductionBoundary l).branch_neg_one = -1 :=
  (canonicalStableReductionBoundary l).branch_neg_one_eq

theorem canonicalStableReductionBoundary_branches_distinct :
    (canonicalStableReductionBoundary l).branch_zero ≠
      (canonicalStableReductionBoundary l).branch_neg_one :=
  (canonicalStableReductionBoundary l).branch_distinct

theorem canonicalStableReductionBoundary_normalizedPoint_onCurve (t : StableResidueField l) :
    NodalNormalization.OnCurve
      ((canonicalStableReductionBoundary l).normalizedPoint t).1
      ((canonicalStableReductionBoundary l).normalizedPoint t).2 :=
  (canonicalStableReductionBoundary l).normalizedPoint_onCurve t

theorem canonicalStableReductionBoundary_normalizedPoint_node_iff
    (t : StableResidueField l) :
    (canonicalStableReductionBoundary l).normalizedPoint t = (0, 0) ↔
      t = (canonicalStableReductionBoundary l).branch_zero ∨
        t = (canonicalStableReductionBoundary l).branch_neg_one := by
  exact (canonicalStableReductionBoundary l).normalizedPoint_node_iff t

theorem canonicalStableReductionBoundary_normalizedPoint_injective_off_node
    {s t : StableResidueField l}
    (hs : s ≠ (canonicalStableReductionBoundary l).branch_zero ∧
      s ≠ (canonicalStableReductionBoundary l).branch_neg_one)
    (hpoint : (canonicalStableReductionBoundary l).normalizedPoint s =
      (canonicalStableReductionBoundary l).normalizedPoint t) :
    s = t := by
  exact (canonicalStableReductionBoundary l).normalizedPoint_injective_off_node hs hpoint

theorem canonicalStableReductionBoundary_graph_connected
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] :
    Iut.sourceTateStableDualGraph.{0}.IsConnected :=
  (canonicalStableReductionBoundary l).graph.dual_connected

theorem canonicalStableReductionBoundary_graph_finite
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] :
    Iut.sourceTateStableDualGraph.{0}.IsFinite :=
  (canonicalStableReductionBoundary l).graph.dual_finite

theorem canonicalStableReductionBoundary_compact_connected
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] :
    Iut.sourceTateStableCompactSemiGraph.{0}.IsConnected :=
  (canonicalStableReductionBoundary l).graph.compact_connected

theorem canonicalStableReductionBoundary_node_closed
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] :
    Iut.sourceTateStableCompactSemiGraph.{0}.IsClosed
      Iut.SourceTateStableCompactEdge.node :=
  (canonicalStableReductionBoundary l).graph.node_closed

theorem canonicalStableReductionBoundary_marked_open
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] :
    Iut.sourceTateStableCompactSemiGraph.{0}.IsOpen
      Iut.SourceTateStableCompactEdge.marked :=
  (canonicalStableReductionBoundary l).graph.marked_open

theorem canonicalStableReductionBoundary_inclusion :
    (canonicalStableReductionBoundary l).graph.inclusion.vertexMap
      Iut.SourceTateStableComponent.component =
        Iut.SourceTateStableComponent.component :=
  rfl

structure CanonicalStableReductionOutput where
  localCurve : WeierstrassCurve ℚ_[l.value]
  integralModel : WeierstrassCurve ℤ_[l.value]
  residueCurve : WeierstrassCurve (StableResidueField l)
  graph : Iut.SourceSemiGraph
  tangentPolynomial : (StableResidueField l)[X]
  normalization : StableResidueField l →
    StableResidueField l × StableResidueField l
  localCurve_eq : localCurve = canonicalCurve l
  integralModel_eq : integralModel = integralCurve l
  residueCurve_eq : residueCurve = nodalCurve l
  graph_eq : graph = Iut.sourceTateStableDualGraph
  tangentPolynomial_eq : tangentPolynomial = nodalTangentPolynomial l
  normalization_eq : normalization = reducedNodalPoint l

def canonicalStableReductionOutput : CanonicalStableReductionOutput l where
  localCurve := canonicalCurve l
  integralModel := integralCurve l
  residueCurve := nodalCurve l
  graph := Iut.sourceTateStableDualGraph
  tangentPolynomial := nodalTangentPolynomial l
  normalization := reducedNodalPoint l
  localCurve_eq := rfl
  integralModel_eq := rfl
  residueCurve_eq := rfl
  graph_eq := rfl
  tangentPolynomial_eq := rfl
  normalization_eq := rfl

theorem canonicalStableReductionOutput_localCurve :
    (canonicalStableReductionOutput l).localCurve = canonicalCurve l := rfl

theorem canonicalStableReductionOutput_integralModel :
    (canonicalStableReductionOutput l).integralModel = integralCurve l := rfl

theorem canonicalStableReductionOutput_residueCurve :
    (canonicalStableReductionOutput l).residueCurve = nodalCurve l := rfl

theorem canonicalStableReductionOutput_graph :
    (canonicalStableReductionOutput l).graph = Iut.sourceTateStableDualGraph := rfl

theorem canonicalStableReductionOutput_tangentPolynomial :
    (canonicalStableReductionOutput l).tangentPolynomial =
      nodalTangentPolynomial l := rfl

theorem canonicalStableReductionOutput_normalization :
    (canonicalStableReductionOutput l).normalization = reducedNodalPoint l := rfl

theorem canonicalStableReductionOutput_graph_connected :
    (canonicalStableReductionOutput l).graph.IsConnected := by
  rw [canonicalStableReductionOutput_graph]
  exact Iut.SourceTateStableDualGraph.isConnected

theorem canonicalStableReductionOutput_graph_finite :
    (canonicalStableReductionOutput l).graph.IsFinite := by
  rw [canonicalStableReductionOutput_graph]
  exact Iut.SourceTateStableDualGraph.isFinite

theorem canonicalStableReductionOutput_tangent_splits :
    Polynomial.Splits (canonicalStableReductionOutput l).tangentPolynomial := by
  rw [canonicalStableReductionOutput_tangentPolynomial]
  exact nodalTangentPolynomial_splits l

theorem canonicalStableReductionOutput_normalization_onCurve
    (t : StableResidueField l) :
    NodalNormalization.OnCurve
      ((canonicalStableReductionOutput l).normalization t).1
      ((canonicalStableReductionOutput l).normalization t).2 := by
  rw [canonicalStableReductionOutput_normalization]
  exact reducedNodalPoint_satisfies l t

theorem canonicalStableReductionOutput_normalization_node_iff
    (t : StableResidueField l) :
    (canonicalStableReductionOutput l).normalization t = (0, 0) ↔
      t = 0 ∨ t = -1 := by
  rw [canonicalStableReductionOutput_normalization]
  exact reducedNodalPoint_eq_node_iff l t

theorem canonicalStableReductionOutput_normalization_injective_off_node
    {s t : StableResidueField l}
    (hs : s ≠ 0 ∧ s ≠ -1)
    (hpoint : (canonicalStableReductionOutput l).normalization s =
      (canonicalStableReductionOutput l).normalization t) :
    s = t := by
  change reducedNodalPoint l s = reducedNodalPoint l t at hpoint
  exact reducedNodalPoint_injective_off_node l hs hpoint

end TateCurvePadic

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def tateStableReductionBoundary : Obligation :=
  { id := "Foundations.Geometry.tate-stable-reduction-boundary"
    source := "IUT I, Example 3.2(i); IUT I-II selected bad-place boundary"
    status := VerificationStatus.proved
    note :=
      "The canonical q=p local reduction packet is combined with the " ++
        "source semi-graph of one component and one nodal loop, including " ++
        "the compact marked open edge. The arithmetic-to-number-field curve " ++
        "identification and tame anabelioid realization remain separate " ++
        "interfaces."
    dependsOn :=
      [ "Foundations.Geometry.tate-curve-local-reduction",
        "IUT-I.source-tate-stable-graph" ] }

end LeanFormal.IUT.Audit
