import Iut.Foundations.SourceSemiGraph
import Iut.Foundations.SourceTateStableGraph
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

namespace Iut

universe u v w

/-!
The source-facing local stable boundary used by the later theta-data layers.
It records the arithmetic carrier and the two graph presentations separately:
the dual graph is closed, while the compact graph may contain the marked open
edge.  No number-field identification or analytic uniformization is hidden in
this interface.
-/
structure SourceTateStableBoundary
    (R : Type u) (K : Type v) (k : Type w)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field k] where
  genericCurve : WeierstrassCurve K
  integralModel : WeierstrassCurve R
  genericCurve_eq_integralModel :
    genericCurve = integralModel.baseChange K
  minimal : genericCurve.IsMinimal R
  reductionMap : R →+* k
  residueCurve : WeierstrassCurve k
  residueCurve_eq_map : residueCurve = integralModel.map reductionMap
  tangentPolynomial : Polynomial k
  tangentPolynomial_splits : Polynomial.Splits tangentPolynomial
  tangentPolynomial_degree : tangentPolynomial.natDegree = 2
  component : Type u
  [componentFintype : Fintype component]
  node : Type u
  [nodeFintype : Fintype node]
  dualGraph : SourceSemiGraph.{u}
  dualGraph_connected : dualGraph.IsConnected
  dualGraph_finite : dualGraph.IsFinite
  compactGraph : SourceSemiGraph.{u}
  compactGraph_connected : compactGraph.IsConnected
  nodeEdge : compactGraph.Edge
  nodeEdge_closed : compactGraph.IsClosed nodeEdge
  markedEdge : compactGraph.Edge
  markedEdge_open : compactGraph.IsOpen markedEdge

attribute [instance] SourceTateStableBoundary.componentFintype
attribute [instance] SourceTateStableBoundary.nodeFintype

namespace SourceTateStableBoundary

variable {R : Type u} {K : Type v} {k : Type w}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Field k]

structure Comparison
    (first second : SourceTateStableBoundary R K k) where
  genericCurve_eq : first.genericCurve = second.genericCurve
  integralModel_eq : first.integralModel = second.integralModel
  residueCurve_eq : first.residueCurve = second.residueCurve
  tangentPolynomial_eq : first.tangentPolynomial = second.tangentPolynomial
  dualGraph_eq : first.dualGraph = second.dualGraph
  compactGraph_eq : first.compactGraph = second.compactGraph

namespace Comparison

variable {first second third : SourceTateStableBoundary R K k}

theorem refl (boundary : SourceTateStableBoundary R K k) :
    Comparison boundary boundary where
  genericCurve_eq := rfl
  integralModel_eq := rfl
  residueCurve_eq := rfl
  tangentPolynomial_eq := rfl
  dualGraph_eq := rfl
  compactGraph_eq := rfl

theorem symm (comparison : Comparison first second) : Comparison second first where
  genericCurve_eq := comparison.genericCurve_eq.symm
  integralModel_eq := comparison.integralModel_eq.symm
  residueCurve_eq := comparison.residueCurve_eq.symm
  tangentPolynomial_eq := comparison.tangentPolynomial_eq.symm
  dualGraph_eq := comparison.dualGraph_eq.symm
  compactGraph_eq := comparison.compactGraph_eq.symm

theorem trans (firstSecond : Comparison first second)
    (secondThird : Comparison second third) : Comparison first third where
  genericCurve_eq := firstSecond.genericCurve_eq.trans secondThird.genericCurve_eq
  integralModel_eq := firstSecond.integralModel_eq.trans secondThird.integralModel_eq
  residueCurve_eq := firstSecond.residueCurve_eq.trans secondThird.residueCurve_eq
  tangentPolynomial_eq :=
    firstSecond.tangentPolynomial_eq.trans secondThird.tangentPolynomial_eq
  dualGraph_eq := firstSecond.dualGraph_eq.trans secondThird.dualGraph_eq
  compactGraph_eq := firstSecond.compactGraph_eq.trans secondThird.compactGraph_eq

end Comparison
end SourceTateStableBoundary
end Iut
