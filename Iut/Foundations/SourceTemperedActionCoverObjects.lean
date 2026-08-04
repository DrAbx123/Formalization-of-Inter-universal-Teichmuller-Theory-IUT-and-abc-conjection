/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperoidOrbitDecomposition
import Iut.Foundations.SourceTemperedCoverCoproduct
import Iut.Foundations.SourceTemperedDeckProjectionSurjectivity

/-!
# Geometric covers attached to tempered inverse-limit actions

This file performs the object-level passage in *Semi-graphs of Anabelioids*,
Proposition 3.6(ii).  An action of the tempered deck group is transported to
the literal inverse-limit presentation and decomposed into countably many
orbits.  Each orbit descends to its own finite Galois level, is transported
across the universe lift of that level's deck group, and is sent through the
existing finite-level associated-quotient functor.  The countable coproduct
of those connected covers is a geometric tempered cover.

No common finite level is selected for the complete action.
-/

namespace Iut

universe u v w

open CategoryTheory
open scoped SourceCountableTypeCatDiscrete

/-! ## Transport of connected actions along a topological group isomorphism -/

/-- Transporting a transitive action through a topological group isomorphism
preserves transitivity. -/
theorem sourceTemperoidResEquivInverse_pretransitive
    {G : Type v} {H : Type w}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (equivalence : G ≃ₜ* H)
    (object : SourceTemperoidAction.{u, v} G)
    (transitive : MulAction.IsPretransitive G object.obj.V.obj) :
    MulAction.IsPretransitive H
      ((ContAction.resEquiv SourceCountableTypeCat equivalence).inverse.obj
        object).obj.V.obj := by
  constructor
  intro first second
  change object.obj.V.obj at first second
  obtain ⟨element, maps⟩ := transitive.exists_smul_eq first second
  refine ⟨equivalence element, ?_⟩
  change equivalence.symm (equivalence element) • first = second
  simpa only [equivalence.symm_apply_apply] using maps

/-- Transport a connected temperoid object through a topological group
isomorphism. -/
noncomputable def sourceConnectedTemperoidResEquivInverse
    {G : Type v} {H : Type w}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (equivalence : G ≃ₜ* H)
    (object : SourceConnectedTemperoid.{u, v} G) :
    SourceConnectedTemperoid.{u, w} H :=
  ⟨(ContAction.resEquiv SourceCountableTypeCat equivalence).inverse.obj
      object.obj,
    ⟨object.property.1,
      sourceTemperoidResEquivInverse_pretransitive equivalence object.obj
        object.property.2⟩⟩

namespace SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

open SourceSemiGraphOfAnabelioids.GluedObject
open SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]

/-- Remove the universe lift from a literal finite-level deck group.  Both
sides carry their canonical discrete topologies. -/
noncomputable def deckULiftContinuousMulEquiv
    (level : GaloisLevel diagram root) :
    (literalTemperedPresentation diagram root).DiscreteLevel level ≃ₜ*
      DeckGroup diagram root level where
  toMulEquiv := MulEquiv.ulift
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- The action-category equivalence induced by the canonical isomorphism
from the literal deck-group inverse limit to `TemperedDeckGroup`. -/
noncomputable def literalLimitActionEquivalence :
    SourceTemperoidAction.{u, u + 1} (TemperedDeckGroup diagram root) ≌
      SourceTemperoidAction.{u, u + 1}
        (literalTemperedPresentation diagram root).Limit :=
  ContAction.resEquiv SourceCountableTypeCat
    (rawDeckLimitContinuousMulEquiv diagram root)

/-- View an action of the declared tempered deck group as an action of the
definitionally literal inverse limit. -/
noncomputable def literalLimitAction
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)) :
    SourceTemperoidAction.{u, u + 1}
      (literalTemperedPresentation diagram root).Limit :=
  (literalLimitActionEquivalence diagram root).functor.obj object

/-- The independently selected finite-level factorization of one orbit. -/
noncomputable def literalOrbitLevelFactorization
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    (literalTemperedPresentation diagram root).ConnectedActionLevelFactorization
      (sourceConnectedTemperoidOrbit
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root object) orbit) :=
  (literalTemperedPresentation diagram root).orbitLevelFactorization
    (literalTemperedPresentation_projection_surjective diagram root)
    (literalLimitAction diagram root object) orbit

/-- The connected action of the original, unlifted deck group selected for
one inverse-limit orbit. -/
noncomputable def finiteDeckOrbitAction
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    SourceConnectedTemperoid.{u, u}
      (DeckGroup diagram root
        (literalOrbitLevelFactorization diagram root object orbit).level) := by
  let factor := literalOrbitLevelFactorization diagram root object orbit
  let liftedConnected : SourceConnectedTemperoid.{u, u + 1}
      ((literalTemperedPresentation diagram root).DiscreteLevel factor.level) :=
    ⟨factor.levelAction, factor.levelConnected⟩
  exact sourceConnectedTemperoidResEquivInverse
    (deckULiftContinuousMulEquiv diagram root factor.level) liftedConnected

/-- The connected finite-level geometric quotient attached to one orbit. -/
noncomputable def finiteDeckOrbitCover
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    SourceSemiGraphOfAnabelioids.CovObject.TemperedCover diagram root :=
  let factor := literalOrbitLevelFactorization diagram root object orbit
  (associatedTemperedFunctor diagram root factor.level).obj
    (finiteDeckOrbitAction diagram root object orbit).obj

/-- Every orbit cover is intrinsically geometrically connected. -/
theorem finiteDeckOrbitCover_isGeometricallyConnected
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    IsGeometricallyConnected
      (finiteDeckOrbitCover diagram root object orbit).obj := by
  let factor := literalOrbitLevelFactorization diagram root object orbit
  let action := finiteDeckOrbitAction diagram root object orbit
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root factor.level.object factor.level.rootVertex
  let deckAction := deckCovActionHom diagram root factor.level
  let basePoint := rootVertexPoint diagram root factor.level
  let point : action.obj.obj.V.obj := Classical.choice action.property.1
  refine ⟨⟨root, SourceTemperoidAssociatedQuotient.mk
    (source.vertexObject root)
    (vertexDeckAction source deckAction root)
    (basePoint, point)⟩, ?_⟩
  change IsPointConnected
    (SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.covObject
      source deckAction action.obj.obj.V.obj) _
  exact covObject_isPointConnected_of_pretransitive
    source deckAction root basePoint
    (covObject_isPointConnected diagram root factor.level) point
    action.property.2

/-- The countable coproduct of the componentwise finite-level quotients. -/
noncomputable def actionCoverCovObject
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)) : diagram.CovObject :=
  SourceSemiGraphOfAnabelioids.CovObject.Coproduct.covObject
    (fun orbit : SourceTemperoidOrbit
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root object) ↦
      (finiteDeckOrbitCover diagram root object orbit).obj)

/-- The geometric cover assembled from all action orbits satisfies corrected
componentwise temperedness. -/
theorem actionCoverCovObject_isTempered
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)) :
    SourceSemiGraphOfAnabelioids.CovObject.IsTempered diagram root
      (actionCoverCovObject diagram root object) := by
  apply SourceSemiGraphOfAnabelioids.CovObject.Coproduct.covObject_isTempered
  · intro orbit
    exact (finiteDeckOrbitCover diagram root object orbit).property
  · intro orbit
    exact finiteDeckOrbitCover_isGeometricallyConnected
      diagram root object orbit

/-- Object assignment from tempered deck-group actions to literal geometric
tempered covers. -/
noncomputable def actionCoverObject
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)) :
    SourceSemiGraphOfAnabelioids.CovObject.TemperedCover diagram root :=
  ⟨actionCoverCovObject diagram root object,
    actionCoverCovObject_isTempered diagram root object⟩

end SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

end Iut
