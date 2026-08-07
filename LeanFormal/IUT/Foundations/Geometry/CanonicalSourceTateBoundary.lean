import LeanFormal.IUT.Foundations.Geometry.TateStableReductionBoundary
import Iut.Foundations.SourceTateStableBoundary

namespace LeanFormal.IUT

open Polynomial

noncomputable section

namespace TateCurvePadic

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

def canonicalSourceTateStableBoundary :
    Iut.SourceTateStableBoundary
      ℤ_[l.value] ℚ_[l.value] (ResidueField l) where
  genericCurve := canonicalCurve l
  integralModel := integralCurve l
  genericCurve_eq_integralModel := by
    simpa [WeierstrassCurve.baseChange, integralCurveMap] using
      (integralCurveMap_eq_canonical l).symm
  minimal := canonicalCurve_isMinimal l
  reductionMap := IsLocalRing.residue ℤ_[l.value]
  residueCurve := nodalCurve l
  residueCurve_eq_map := by
    change nodalCurve l = reducedIntegralCurve l
    exact (reducedIntegralCurve_eq_nodalCurve l).symm
  tangentPolynomial := nodalTangentPolynomial l
  tangentPolynomial_splits := nodalTangentPolynomial_splits l
  tangentPolynomial_degree := nodalTangentPolynomial_natDegree l
  component := Iut.SourceTateStableComponent
  node := Iut.SourceTateStableNode
  dualGraph := Iut.sourceTateStableDualGraph
  dualGraph_connected := Iut.SourceTateStableDualGraph.isConnected
  dualGraph_finite := Iut.SourceTateStableDualGraph.isFinite
  compactGraph := Iut.sourceTateStableCompactSemiGraph
  compactGraph_connected := Iut.SourceTateStableCompactSemiGraph.isConnected
  nodeEdge := Iut.SourceTateStableCompactEdge.node
  nodeEdge_closed := Iut.SourceTateStableCompactSemiGraph.node_isClosed
  markedEdge := Iut.SourceTateStableCompactEdge.marked
  markedEdge_open := Iut.SourceTateStableCompactSemiGraph.marked_isOpen

theorem canonicalSourceTateStableBoundary_genericCurve :
    (canonicalSourceTateStableBoundary l).genericCurve = canonicalCurve l :=
  rfl

theorem canonicalSourceTateStableBoundary_integralModel :
    (canonicalSourceTateStableBoundary l).integralModel = integralCurve l :=
  rfl

theorem canonicalSourceTateStableBoundary_genericCurve_eq_integralModel :
    (canonicalSourceTateStableBoundary l).genericCurve =
      (canonicalSourceTateStableBoundary l).integralModel.baseChange ℚ_[l.value] :=
  (canonicalSourceTateStableBoundary l).genericCurve_eq_integralModel

theorem canonicalSourceTateStableBoundary_minimal :
    (canonicalSourceTateStableBoundary l).genericCurve.IsMinimal ℤ_[l.value] :=
  (canonicalSourceTateStableBoundary l).minimal

theorem canonicalSourceTateStableBoundary_residueMap :
    (canonicalSourceTateStableBoundary l).reductionMap =
      IsLocalRing.residue ℤ_[l.value] :=
  rfl

theorem canonicalSourceTateStableBoundary_residueCurve :
    (canonicalSourceTateStableBoundary l).residueCurve = nodalCurve l :=
  rfl

theorem canonicalSourceTateStableBoundary_residueCurve_eq_map :
    (canonicalSourceTateStableBoundary l).residueCurve =
      (canonicalSourceTateStableBoundary l).integralModel.map
        (canonicalSourceTateStableBoundary l).reductionMap :=
  (canonicalSourceTateStableBoundary l).residueCurve_eq_map

theorem canonicalSourceTateStableBoundary_tangentPolynomial :
    (canonicalSourceTateStableBoundary l).tangentPolynomial =
      nodalTangentPolynomial l :=
  rfl

theorem canonicalSourceTateStableBoundary_tangent_splits :
    Polynomial.Splits (canonicalSourceTateStableBoundary l).tangentPolynomial :=
  (canonicalSourceTateStableBoundary l).tangentPolynomial_splits

theorem canonicalSourceTateStableBoundary_tangent_degree :
    (canonicalSourceTateStableBoundary l).tangentPolynomial.natDegree = 2 :=
  (canonicalSourceTateStableBoundary l).tangentPolynomial_degree

theorem canonicalSourceTateStableBoundary_graph_connected :
    (canonicalSourceTateStableBoundary l).dualGraph.IsConnected :=
  (canonicalSourceTateStableBoundary l).dualGraph_connected

theorem canonicalSourceTateStableBoundary_graph_finite :
    (canonicalSourceTateStableBoundary l).dualGraph.IsFinite :=
  (canonicalSourceTateStableBoundary l).dualGraph_finite

theorem canonicalSourceTateStableBoundary_compact_connected :
    (canonicalSourceTateStableBoundary l).compactGraph.IsConnected :=
  (canonicalSourceTateStableBoundary l).compactGraph_connected

theorem canonicalSourceTateStableBoundary_node_closed :
    (canonicalSourceTateStableBoundary l).compactGraph.IsClosed
      Iut.SourceTateStableCompactEdge.node :=
  (canonicalSourceTateStableBoundary l).nodeEdge_closed

theorem canonicalSourceTateStableBoundary_marked_open :
    (canonicalSourceTateStableBoundary l).compactGraph.IsOpen
      Iut.SourceTateStableCompactEdge.marked :=
  (canonicalSourceTateStableBoundary l).markedEdge_open

set_option linter.defProp false in
def canonicalSourceTateStableBoundaryComparison :
    Iut.SourceTateStableBoundary.Comparison
      (canonicalSourceTateStableBoundary l)
      (canonicalSourceTateStableBoundary l) :=
  Iut.SourceTateStableBoundary.Comparison.refl _

structure CanonicalSourceTateStableOutput where
  localCurve : WeierstrassCurve ℚ_[l.value]
  integralModel : WeierstrassCurve ℤ_[l.value]
  residueCurve : WeierstrassCurve (ResidueField l)
  dualGraph : Iut.SourceSemiGraph
  compactGraph : Iut.SourceSemiGraph
  tangentPolynomial : (ResidueField l)[X]
  localCurve_eq : localCurve = canonicalCurve l
  integralModel_eq : integralModel = integralCurve l
  residueCurve_eq : residueCurve = nodalCurve l
  dualGraph_eq : dualGraph = Iut.sourceTateStableDualGraph
  compactGraph_eq : compactGraph = Iut.sourceTateStableCompactSemiGraph
  tangentPolynomial_eq : tangentPolynomial = nodalTangentPolynomial l

def canonicalSourceTateStableOutput : CanonicalSourceTateStableOutput l where
  localCurve := (canonicalSourceTateStableBoundary l).genericCurve
  integralModel := (canonicalSourceTateStableBoundary l).integralModel
  residueCurve := (canonicalSourceTateStableBoundary l).residueCurve
  dualGraph := (canonicalSourceTateStableBoundary l).dualGraph
  compactGraph := (canonicalSourceTateStableBoundary l).compactGraph
  tangentPolynomial := (canonicalSourceTateStableBoundary l).tangentPolynomial
  localCurve_eq := rfl
  integralModel_eq := rfl
  residueCurve_eq := rfl
  dualGraph_eq := rfl
  compactGraph_eq := rfl
  tangentPolynomial_eq := rfl

theorem canonicalSourceTateStableOutput_localCurve :
    (canonicalSourceTateStableOutput l).localCurve = canonicalCurve l := rfl

theorem canonicalSourceTateStableOutput_integralModel :
    (canonicalSourceTateStableOutput l).integralModel = integralCurve l := rfl

theorem canonicalSourceTateStableOutput_residueCurve :
    (canonicalSourceTateStableOutput l).residueCurve = nodalCurve l := rfl

theorem canonicalSourceTateStableOutput_dualGraph :
    (canonicalSourceTateStableOutput l).dualGraph =
      Iut.sourceTateStableDualGraph := rfl

theorem canonicalSourceTateStableOutput_compactGraph :
    (canonicalSourceTateStableOutput l).compactGraph =
      Iut.sourceTateStableCompactSemiGraph := rfl

theorem canonicalSourceTateStableOutput_tangentPolynomial :
    (canonicalSourceTateStableOutput l).tangentPolynomial =
      nodalTangentPolynomial l := rfl

theorem canonicalSourceTateStableOutput_graph_connected :
    (canonicalSourceTateStableOutput l).dualGraph.IsConnected := by
  rw [canonicalSourceTateStableOutput_dualGraph]
  exact Iut.SourceTateStableDualGraph.isConnected

theorem canonicalSourceTateStableOutput_graph_finite :
    (canonicalSourceTateStableOutput l).dualGraph.IsFinite := by
  rw [canonicalSourceTateStableOutput_dualGraph]
  exact Iut.SourceTateStableDualGraph.isFinite

theorem canonicalSourceTateStableOutput_compact_connected :
    (canonicalSourceTateStableOutput l).compactGraph.IsConnected := by
  rw [canonicalSourceTateStableOutput_compactGraph]
  exact Iut.SourceTateStableCompactSemiGraph.isConnected

theorem canonicalSourceTateStableOutput_tangent_splits :
    Polynomial.Splits (canonicalSourceTateStableOutput l).tangentPolynomial := by
  rw [canonicalSourceTateStableOutput_tangentPolynomial]
  exact nodalTangentPolynomial_splits l

end TateCurvePadic

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def canonicalSourceTateStableBoundary : Obligation :=
  { id := "Foundations.Geometry.canonical-source-tate-stable-boundary"
    source := "IUT I, Example 3.2(i); source-facing local stable boundary"
    status := VerificationStatus.proved
    note :=
      "The canonical p-adic q-series equation is assembled into the generic " ++
        "source-facing stable-boundary interface with a concrete node graph. " ++
        "This remains a local Q_p realization; it does not claim an arbitrary " ++
        "number-field input curve has been identified with it."
    dependsOn :=
      [ "Foundations.Geometry.tate-stable-reduction-boundary",
        "IUT-I.source-tate-stable-boundary" ] }

end LeanFormal.IUT.Audit
