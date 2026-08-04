/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedGeometricDomination
import Iut.Foundations.SourceTemperedSubcoverClassification

/-!
# Classifying connected tempered covers

Every connected tempered geometric cover is split by a pointed Galois level.
The finite-level universal cover at that level maps geometrically to the
target, and evaluation recovers the target as the associated quotient of the
transitive deck action on maps from the universal cover.

This is the connected-object essential-surjectivity step in *Semi-graphs of
Anabelioids*, Proposition 3.6(ii).  The target remains a literal object of
`B^cov(G)` throughout; no geometric cover is defined through an action.
-/

namespace Iut

universe u

open CategoryTheory
open scoped SourceCountableTypeCatDiscrete

namespace SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

open SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

/-- A connected tempered geometric cover is an associated quotient of a
finite-level geometric universal cover by the recovered transitive deck
action.  The Galois level is obtained from temperedness, while the root point
needed for geometric domination is transported from the intrinsic
connectedness witness along the connected base semigraph. -/
noncomputable def connectedTemperedClassification
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (target : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root target)
    (connected : IsGeometricallyConnected target) :
    Σ level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
        diagram root,
      Σ action : SourceConnectedTemperoid (DeckGroup diagram root level),
        (((associatedTemperedFunctor diagram root level).obj action.obj).obj ≅
          target) := by
  let connectedBasePoint : GeometricPoint target := Classical.choose connected
  let baseConnected : IsPointConnected target connectedBasePoint :=
    Classical.choose_spec connected
  let splitting :=
    SourceSemiGraphOfAnabelioids.CovObject.exists_galoisLevel_splitting_of_isPointConnected
      diagram root tempered connectedBasePoint baseConnected
  let level := Classical.choose splitting
  let split := Classical.choose_spec splitting
  let initial : (target.vertexObject root).obj.V.obj :=
    connectedVertexCarrierEquiv diagram target connectedBasePoint.1 root
      connectedBasePoint.2
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  let sourceBasePoint : GeometricPoint source :=
    ⟨root, rootVertexPoint diagram root level⟩
  let map : source ⟶ target :=
    GeometricDomination.hom diagram root level target split initial
  have targetConnected : IsPointConnected target
      (geometricPointMap map sourceBasePoint) :=
    baseConnected.rebase (geometricPointMap map sourceBasePoint)
  exact ⟨level,
    finiteLevelSubcoverAction diagram root level target map targetConnected,
    finiteLevelSubcoverComparison diagram root level target map
      targetConnected⟩

end SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

end Iut
