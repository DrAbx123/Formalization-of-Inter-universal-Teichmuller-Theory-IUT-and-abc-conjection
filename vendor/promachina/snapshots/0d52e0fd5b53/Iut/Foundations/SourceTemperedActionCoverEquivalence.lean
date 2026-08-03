/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedActionCoverFunctor

/-!
# Equivalence between tempered actions and geometric tempered covers

This file completes *Semi-graphs of Anabelioids*, Proposition 3.6(ii).  It
recovers an inverse-limit action morphism from a geometric morphism by
restricting every connected source orbit to the unique target orbit it
reaches, comparing their independently chosen finite presentations at a
common refinement, and using full faithfulness of the finite-level
associated-quotient functor.
-/

namespace Iut

universe u

open CategoryTheory
open scoped SourceCountableTypeCatDiscrete

namespace SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

open SourceSemiGraphOfAnabelioids.GluedObject
open SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]

/-! ## Root normalization -/

/-- The literal inverse-limit action carrier is canonically the root fiber
of its geometric action cover. -/
noncomputable def actionCoverRootEquiv
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)) :
    (literalLimitAction diagram root object).obj.V.obj ≃
      ((actionCoverObject diagram root object).obj.vertexObject root).obj.V.obj := by
  let literal := literalLimitAction diagram root object
  let decomposed :=
    SourceTemperoidOrbitDecompositionCarrier
      (literalTemperedPresentation diagram root).Limit literal
  let componentEquiv : decomposed ≃
      ((actionCoverObject diagram root object).obj.vertexObject root).obj.V.obj :=
    { toFun := fun point ↦
        ⟨point.1,
          rootAssociatedCarrierEquiv diagram root
            (literalOrbitLevelFactorization diagram root object point.1).level
            (finiteDeckOrbitAction diagram root object point.1).obj
            ((literalOrbitLevelFactorization diagram root object point.1
              ).comparison.inv.hom.hom point.2)⟩
      invFun := fun point ↦
        ⟨point.1,
          (literalOrbitLevelFactorization diagram root object point.1
            ).comparison.hom.hom
            ((rootAssociatedCarrierEquiv diagram root
              (literalOrbitLevelFactorization diagram root object point.1).level
              (finiteDeckOrbitAction diagram root object point.1).obj).symm
                point.2)⟩
      left_inv := by
        rintro ⟨orbit, point⟩
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          change (literalOrbitLevelFactorization diagram root object orbit
              ).comparison.hom.hom
                ((rootAssociatedCarrierEquiv diagram root
                  (literalOrbitLevelFactorization diagram root object orbit).level
                  (finiteDeckOrbitAction diagram root object orbit).obj).symm
                    (rootAssociatedCarrierEquiv diagram root
                      (literalOrbitLevelFactorization diagram root object orbit).level
                      (finiteDeckOrbitAction diagram root object orbit).obj
                      ((literalOrbitLevelFactorization diagram root object orbit
                        ).comparison.inv.hom.hom point))) = point
          rw [(rootAssociatedCarrierEquiv diagram root
            (literalOrbitLevelFactorization diagram root object orbit).level
            (finiteDeckOrbitAction diagram root object orbit).obj).symm_apply_apply]
          exact congrArg
            (fun morphism : sourceTemperoidOrbitAction
                (literalTemperedPresentation diagram root).Limit
                (literalLimitAction diagram root object) orbit ⟶
                sourceTemperoidOrbitAction
                  (literalTemperedPresentation diagram root).Limit
                  (literalLimitAction diagram root object) orbit ↦
              morphism.hom.hom point)
            (literalOrbitLevelFactorization diagram root object orbit
              ).comparison.inv_hom_id
      right_inv := by
        rintro ⟨orbit, point⟩
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          change rootAssociatedCarrierEquiv diagram root
              (literalOrbitLevelFactorization diagram root object orbit).level
              (finiteDeckOrbitAction diagram root object orbit).obj
              ((literalOrbitLevelFactorization diagram root object orbit
                ).comparison.inv.hom.hom
                ((literalOrbitLevelFactorization diagram root object orbit
                  ).comparison.hom.hom
                  ((rootAssociatedCarrierEquiv diagram root
                    (literalOrbitLevelFactorization diagram root object orbit).level
                    (finiteDeckOrbitAction diagram root object orbit).obj).symm
                      point))) = point
          have cancellation := congrArg
            (fun morphism : literalOrbitLevelAction diagram root object orbit ⟶
                literalOrbitLevelAction diagram root object orbit ↦
              morphism.hom.hom
                ((rootAssociatedCarrierEquiv diagram root
                  (literalOrbitLevelFactorization diagram root object orbit).level
                  (finiteDeckOrbitAction diagram root object orbit).obj).symm
                    point))
            (literalOrbitLevelFactorization diagram root object orbit
              ).comparison.hom_inv_id
          change (literalOrbitLevelFactorization diagram root object orbit
              ).comparison.inv.hom.hom
                ((literalOrbitLevelFactorization diagram root object orbit
                  ).comparison.hom.hom
                  ((rootAssociatedCarrierEquiv diagram root
                    (literalOrbitLevelFactorization diagram root object orbit).level
                    (finiteDeckOrbitAction diagram root object orbit).obj).symm
                      point)) =
              (rootAssociatedCarrierEquiv diagram root
                (literalOrbitLevelFactorization diagram root object orbit).level
                (finiteDeckOrbitAction diagram root object orbit).obj).symm
                  point at cancellation
          rw [cancellation]
          exact (rootAssociatedCarrierEquiv diagram root
            (literalOrbitLevelFactorization diagram root object orbit).level
            (finiteDeckOrbitAction diagram root object orbit).obj).apply_symm_apply
              point }
  exact
    (sourceTemperoidOrbitDecompositionCarrierEquiv
      (literalTemperedPresentation diagram root).Limit literal).symm.trans
        componentEquiv

/-- Root normalization is natural for every morphism of tempered actions. -/
theorem actionCoverRootEquiv_naturality
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : source ⟶ target)
    (point : (literalLimitAction diagram root source).obj.V.obj) :
    actionCoverRootEquiv diagram root target
        ((literalLimitActionMap diagram root arrow).hom.hom point) =
      ((actionCoverMap diagram root arrow).hom.app root).hom.hom
        (actionCoverRootEquiv diagram root source point) := by
  let orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source) := Quotient.mk'' point
  let orbitPoint : SourceTemperoidOrbitFiber
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source) orbit := ⟨point, rfl⟩
  let sourceFactor := literalOrbitLevelFactorization
    diagram root source orbit
  let targetOrbit := literalTargetOrbit diagram root arrow orbit
  let targetFactor := literalOrbitLevelFactorization
    diagram root target targetOrbit
  let levelPoint := sourceFactor.comparison.inv.hom.hom orbitPoint
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change rootAssociatedCarrierEquiv diagram root targetFactor.level
        (finiteDeckOrbitAction diagram root target targetOrbit).obj
        (targetFactor.comparison.inv.hom.hom
          ((literalOrbitMap diagram root arrow orbit).hom.hom orbitPoint)) =
      ((finiteDeckOrbitCoverMap diagram root arrow orbit).hom.app root).hom.hom
        (rootAssociatedCarrierEquiv diagram root sourceFactor.level
          (finiteDeckOrbitAction diagram root source orbit).obj levelPoint)
    rw [finiteDeckOrbitCoverMap_root]
    apply congrArg
      (rootAssociatedCarrierEquiv diagram root targetFactor.level
        (finiteDeckOrbitAction diagram root target targetOrbit).obj)
    change targetFactor.comparison.inv.hom.hom
        ((literalOrbitMap diagram root arrow orbit).hom.hom orbitPoint) =
      (chosenLevelOrbitMap diagram root arrow orbit).hom.hom levelPoint
    change targetFactor.comparison.inv.hom.hom
        ((literalOrbitMap diagram root arrow orbit).hom.hom orbitPoint) =
      targetFactor.comparison.inv.hom.hom
        ((literalOrbitMap diagram root arrow orbit).hom.hom
          (sourceFactor.comparison.hom.hom levelPoint))
    apply congrArg targetFactor.comparison.inv.hom.hom
    apply congrArg (literalOrbitMap diagram root arrow orbit).hom.hom
    change orbitPoint = sourceFactor.comparison.hom.hom
      (sourceFactor.comparison.inv.hom.hom orbitPoint)
    symm
    exact congrArg
      (fun morphism : sourceTemperoidOrbitAction
          (literalTemperedPresentation diagram root).Limit
          (literalLimitAction diagram root source) orbit ⟶
          sourceTemperoidOrbitAction
            (literalTemperedPresentation diagram root).Limit
            (literalLimitAction diagram root source) orbit ↦
        morphism.hom.hom orbitPoint)
      sourceFactor.comparison.inv_hom_id

/-- A selected finite-level point, returned to its literal orbit through the
factorization comparison, normalizes to the corresponding root point in that
orbit cover. -/
theorem actionCoverRootEquiv_comparison_hom
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object))
    (point : (finiteDeckOrbitAction
      diagram root object orbit).obj.obj.V.obj) :
    actionCoverRootEquiv diagram root object
        (((literalOrbitLevelFactorization diagram root object orbit
          ).comparison.hom.hom point).1) =
      ⟨orbit, rootAssociatedCarrierEquiv diagram root
        (literalOrbitLevelFactorization diagram root object orbit).level
        (finiteDeckOrbitAction diagram root object orbit).obj point⟩ := by
  apply (actionCoverRootEquiv diagram root object).symm.injective
  rw [(actionCoverRootEquiv diagram root object).symm_apply_apply]
  change ((literalOrbitLevelFactorization diagram root object orbit
      ).comparison.hom.hom point).1 =
    ((literalOrbitLevelFactorization diagram root object orbit
      ).comparison.hom.hom
        ((rootAssociatedCarrierEquiv diagram root
          (literalOrbitLevelFactorization diagram root object orbit).level
          (finiteDeckOrbitAction diagram root object orbit).obj).symm
          (rootAssociatedCarrierEquiv diagram root
            (literalOrbitLevelFactorization diagram root object orbit).level
            (finiteDeckOrbitAction diagram root object orbit).obj point))).1
  rw [(rootAssociatedCarrierEquiv diagram root
    (literalOrbitLevelFactorization diagram root object orbit).level
    (finiteDeckOrbitAction diagram root object orbit).obj).symm_apply_apply]

/-- A geometric action-cover map determines its action morphism already on
the normalized root fiber. -/
noncomputable instance actionCoverFunctorFaithful :
    (actionCoverFunctor diagram root).Faithful := by
  constructor
  intro source target first second equality
  apply (literalLimitActionEquivalence diagram root).functor.map_injective
  apply CategoryTheory.ObjectProperty.hom_ext Action.IsContinuous
  apply Action.Hom.ext
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro point
  apply (actionCoverRootEquiv diagram root target).injective
  change actionCoverRootEquiv diagram root target
      ((literalLimitActionMap diagram root first).hom.hom point) =
    actionCoverRootEquiv diagram root target
      ((literalLimitActionMap diagram root second).hom.hom point)
  rw [actionCoverRootEquiv_naturality, actionCoverRootEquiv_naturality]
  have underlyingEquality :
      (actionCoverMap diagram root first).hom =
        (actionCoverMap diagram root second).hom :=
    congrArg (fun arrow ↦ arrow.hom) equality
  exact congrArg
    (fun arrow : (actionCoverObject diagram root source).obj ⟶
        (actionCoverObject diagram root target).obj ↦
      (arrow.app root).hom.hom
        (actionCoverRootEquiv diagram root source point))
    underlyingEquality

/-! ## Recovering an action morphism -/

/-- A normalized root point used to identify the target component of a
geometric morphism. -/
noncomputable def recoveryOrbitPoint
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    (finiteDeckOrbitAction diagram root object orbit).obj.obj.V.obj :=
  Classical.choice (finiteDeckOrbitAction
    diagram root object orbit).property.1

/-- The corresponding point of the connected geometric orbit cover. -/
noncomputable def recoveryOrbitBasePoint
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    GeometricPoint (finiteDeckOrbitCover diagram root object orbit).obj :=
  ⟨root, rootAssociatedCarrierEquiv diagram root
    (literalOrbitLevelFactorization diagram root object orbit).level
    (finiteDeckOrbitAction diagram root object orbit).obj
    (recoveryOrbitPoint diagram root object orbit)⟩

/-- Restrict a geometric action-cover morphism to one source orbit, retaining
the full target coproduct. -/
noncomputable def recoveryOrbitToCoproductMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    (finiteDeckOrbitCover diagram root source orbit).obj ⟶
      (actionCoverObject diagram root target).obj :=
  CategoryTheory.CategoryStruct.comp
    (SourceSemiGraphOfAnabelioids.CovObject.Coproduct.inclusion
      (fun targetOrbit ↦
        (finiteDeckOrbitCover diagram root source targetOrbit).obj) orbit)
    arrow.hom

/-- The unique target orbit reached by one connected source orbit under a
geometric morphism. -/
noncomputable def recoveredTargetOrbit
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root target) :=
  SourceSemiGraphOfAnabelioids.CovObject.Coproduct.connectedMapTargetIndex
    (finiteDeckOrbitCover diagram root source orbit).obj
    (fun targetOrbit ↦
      (finiteDeckOrbitCover diagram root target targetOrbit).obj)
    (recoveryOrbitToCoproductMap diagram root arrow orbit)
    (recoveryOrbitBasePoint diagram root source orbit)

/-- The geometric component map obtained by restricting to that unique
target orbit. -/
noncomputable def recoveredOrbitCoverMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    (finiteDeckOrbitCover diagram root source orbit).obj ⟶
      (finiteDeckOrbitCover diagram root target
        (recoveredTargetOrbit diagram root arrow orbit)).obj :=
  SourceSemiGraphOfAnabelioids.CovObject.Coproduct.connectedMapToMember
    (finiteDeckOrbitCover diagram root source orbit).obj
    (fun targetOrbit ↦
      (finiteDeckOrbitCover diagram root target targetOrbit).obj)
    (recoveryOrbitToCoproductMap diagram root arrow orbit)
    (recoveryOrbitBasePoint diagram root source orbit)
    (finiteDeckOrbitCover_root_isPointConnected diagram root source orbit
      (recoveryOrbitPoint diagram root source orbit))

/-- Re-including the recovered target component gives the original map from
the selected source orbit to the target coproduct. -/
theorem recoveredOrbitCoverMap_comp_inclusion
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    CategoryTheory.CategoryStruct.comp
        (recoveredOrbitCoverMap diagram root arrow orbit)
        (SourceSemiGraphOfAnabelioids.CovObject.Coproduct.inclusion
          (fun targetOrbit ↦
            (finiteDeckOrbitCover diagram root target targetOrbit).obj)
          (recoveredTargetOrbit diagram root arrow orbit)) =
      recoveryOrbitToCoproductMap diagram root arrow orbit :=
  SourceSemiGraphOfAnabelioids.CovObject.Coproduct.connectedMapToMember_comp_inclusion
    _ _ _ _ _

/-- A common refinement of the independently selected source and recovered
target orbit levels. -/
noncomputable def recoveryCommonLevel
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    GaloisLevel diagram root :=
  CategoryTheory.IsCofiltered.min
    (literalOrbitLevelFactorization diagram root source orbit).level
    (literalOrbitLevelFactorization diagram root target
      (recoveredTargetOrbit diagram root arrow orbit)).level

/-- The recovery common level refines the selected source level. -/
noncomputable def recoveryCommonToSource
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    recoveryCommonLevel diagram root arrow orbit ⟶
      (literalOrbitLevelFactorization diagram root source orbit).level :=
  CategoryTheory.IsCofiltered.minToLeft _ _

/-- The recovery common level refines the selected target level. -/
noncomputable def recoveryCommonToTarget
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    recoveryCommonLevel diagram root arrow orbit ⟶
      (literalOrbitLevelFactorization diagram root target
        (recoveredTargetOrbit diagram root arrow orbit)).level :=
  CategoryTheory.IsCofiltered.minToRight _ _

/-- Move the recovered geometric component map to the common refinement. -/
noncomputable def recoveryCommonCoverMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    (associatedTemperedFunctor diagram root
        (recoveryCommonLevel diagram root arrow orbit)).obj
      (restrictDeckAction diagram root
        (recoveryCommonToSource diagram root arrow orbit)
        (finiteDeckOrbitAction diagram root source orbit).obj) ⟶
    (associatedTemperedFunctor diagram root
        (recoveryCommonLevel diagram root arrow orbit)).obj
      (restrictDeckAction diagram root
        (recoveryCommonToTarget diagram root arrow orbit)
        (finiteDeckOrbitAction diagram root target
          (recoveredTargetOrbit diagram root arrow orbit)).obj) :=
  CategoryTheory.CategoryStruct.comp
    (associatedTemperedRefinementIso diagram root
      (recoveryCommonToSource diagram root arrow orbit)
      (finiteDeckOrbitAction diagram root source orbit).obj).hom
    (CategoryTheory.CategoryStruct.comp
      (CategoryTheory.ObjectProperty.homMk
        (recoveredOrbitCoverMap diagram root arrow orbit))
      (associatedTemperedRefinementIso diagram root
        (recoveryCommonToTarget diagram root arrow orbit)
        (finiteDeckOrbitAction diagram root target
          (recoveredTargetOrbit diagram root arrow orbit)).obj).inv)

/-- Fullness at the common finite level recovers the unique deck-equivariant
map underlying the geometric component map. -/
noncomputable def recoveredCommonDeckMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    restrictDeckAction diagram root
        (recoveryCommonToSource diagram root arrow orbit)
        (finiteDeckOrbitAction diagram root source orbit).obj ⟶
      restrictDeckAction diagram root
        (recoveryCommonToTarget diagram root arrow orbit)
        (finiteDeckOrbitAction diagram root target
          (recoveredTargetOrbit diagram root arrow orbit)).obj :=
  recoverAuxiliaryMap diagram root
    (recoveryCommonLevel diagram root arrow orbit)
    (recoveryCommonCoverMap diagram root arrow orbit)

/-- Reapplying the common-level associated-quotient functor to the recovered
deck map returns the transported geometric component map. -/
theorem recoveredCommonDeckMap_maps_to_coverMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    (associatedTemperedFunctor diagram root
      (recoveryCommonLevel diagram root arrow orbit)).map
        (recoveredCommonDeckMap diagram root arrow orbit) =
      recoveryCommonCoverMap diagram root arrow orbit :=
  associatedTemperedFunctor_map_recoverAuxiliaryMap _ _ _ _

/-- On normalized root fibers, the recovered geometric component map is
exactly the selected-level map obtained from common-level fullness. -/
theorem recoveredOrbitCoverMap_root
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source))
    (point : (finiteDeckOrbitAction
      diagram root source orbit).obj.obj.V.obj) :
    ((recoveredOrbitCoverMap diagram root arrow orbit).app root).hom.hom
        (rootAssociatedCarrierEquiv diagram root
          (literalOrbitLevelFactorization diagram root source orbit).level
          (finiteDeckOrbitAction diagram root source orbit).obj point) =
      rootAssociatedCarrierEquiv diagram root
        (literalOrbitLevelFactorization diagram root target
          (recoveredTargetOrbit diagram root arrow orbit)).level
        (finiteDeckOrbitAction diagram root target
          (recoveredTargetOrbit diagram root arrow orbit)).obj
        ((recoveredCommonDeckMap diagram root arrow orbit).hom.hom point) := by
  let sourceIso := associatedTemperedRefinementIso diagram root
    (recoveryCommonToSource diagram root arrow orbit)
    (finiteDeckOrbitAction diagram root source orbit).obj
  let targetIso := associatedTemperedRefinementIso diagram root
    (recoveryCommonToTarget diagram root arrow orbit)
    (finiteDeckOrbitAction diagram root target
      (recoveredTargetOrbit diagram root arrow orbit)).obj
  let commonMap := recoveredCommonDeckMap diagram root arrow orbit
  let sourceCommonPoint := rootAssociatedCarrierEquiv diagram root
    (recoveryCommonLevel diagram root arrow orbit)
    (restrictDeckAction diagram root
      (recoveryCommonToSource diagram root arrow orbit)
      (finiteDeckOrbitAction diagram root source orbit).obj) point
  have evaluated := congrArg
    (fun map : (associatedTemperedFunctor diagram root
        (recoveryCommonLevel diagram root arrow orbit)).obj
          (restrictDeckAction diagram root
            (recoveryCommonToSource diagram root arrow orbit)
            (finiteDeckOrbitAction diagram root source orbit).obj) ⟶
        (associatedTemperedFunctor diagram root
          (recoveryCommonLevel diagram root arrow orbit)).obj
          (restrictDeckAction diagram root
            (recoveryCommonToTarget diagram root arrow orbit)
            (finiteDeckOrbitAction diagram root target
              (recoveredTargetOrbit diagram root arrow orbit)).obj) ↦
      (map.hom.app root).hom.hom sourceCommonPoint)
    (recoveredCommonDeckMap_maps_to_coverMap diagram root arrow orbit)
  change rootAssociatedCarrierEquiv diagram root
      (recoveryCommonLevel diagram root arrow orbit)
      (restrictDeckAction diagram root
        (recoveryCommonToTarget diagram root arrow orbit)
        (finiteDeckOrbitAction diagram root target
          (recoveredTargetOrbit diagram root arrow orbit)).obj)
      (commonMap.hom.hom point) =
    (targetIso.inv.hom.app root).hom.hom
      (((recoveredOrbitCoverMap diagram root arrow orbit).app root).hom.hom
        ((sourceIso.hom.hom.app root).hom.hom sourceCommonPoint)) at evaluated
  dsimp only [sourceIso] at evaluated
  rw [associatedTemperedRefinementIso_hom] at evaluated
  rw [associatedTemperedRefinementHom_root_mk] at evaluated
  let expected := rootAssociatedCarrierEquiv diagram root
    (literalOrbitLevelFactorization diagram root target
      (recoveredTargetOrbit diagram root arrow orbit)).level
    (finiteDeckOrbitAction diagram root target
      (recoveredTargetOrbit diagram root arrow orbit)).obj
    (commonMap.hom.hom point)
  have expectedMaps : (targetIso.inv.hom.app root).hom.hom expected =
      rootAssociatedCarrierEquiv diagram root
        (recoveryCommonLevel diagram root arrow orbit)
        (restrictDeckAction diagram root
          (recoveryCommonToTarget diagram root arrow orbit)
          (finiteDeckOrbitAction diagram root target
            (recoveredTargetOrbit diagram root arrow orbit)).obj)
        (commonMap.hom.hom point) :=
    associatedTemperedRefinementIso_inv_root_mk diagram root
      (recoveryCommonToTarget diagram root arrow orbit)
      (finiteDeckOrbitAction diagram root target
        (recoveredTargetOrbit diagram root arrow orbit)).obj
      (commonMap.hom.hom point)
  let actual := ((recoveredOrbitCoverMap diagram root arrow orbit).app root).hom.hom
      (rootAssociatedCarrierEquiv diagram root
        (literalOrbitLevelFactorization diagram root source orbit).level
        (finiteDeckOrbitAction diagram root source orbit).obj point)
  have afterInverse : (targetIso.inv.hom.app root).hom.hom actual =
      (targetIso.inv.hom.app root).hom.hom expected :=
    evaluated.symm.trans expectedMaps.symm
  have cancellation := congrArg
    (fun value ↦ (targetIso.hom.hom.app root).hom.hom value) afterInverse
  change (((CategoryTheory.CategoryStruct.comp targetIso.inv targetIso.hom).hom
      ).app root).hom.hom actual =
    (((CategoryTheory.CategoryStruct.comp targetIso.inv targetIso.hom).hom
      ).app root).hom.hom expected at cancellation
  rw [targetIso.inv_hom_id] at cancellation
  exact cancellation

/-- The recovered common-level map is equivariant for the inverse-limit
group when both selected level actions are pulled back along their coordinate
projections. -/
noncomputable def recoveredChosenLevelMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    literalOrbitLevelAction diagram root source orbit ⟶
      literalOrbitLevelAction diagram root target
        (recoveredTargetOrbit diagram root arrow orbit) := by
  let presentation := literalTemperedPresentation diagram root
  let sourceFactor := literalOrbitLevelFactorization
    diagram root source orbit
  let targetOrbit := recoveredTargetOrbit diagram root arrow orbit
  let targetFactor := literalOrbitLevelFactorization
    diagram root target targetOrbit
  let common := recoveryCommonLevel diagram root arrow orbit
  let toSource := recoveryCommonToSource diagram root arrow orbit
  let toTarget := recoveryCommonToTarget diagram root arrow orbit
  let commonMap := recoveredCommonDeckMap diagram root arrow orbit
  apply CategoryTheory.ObjectProperty.homMk
  refine
    { hom := SourceCountableTypeCat.homMk commonMap.hom.hom
      comm := ?_ }
  intro limitElement
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro point
  let commonElement : DeckGroup diagram root common :=
    (presentation.projection common limitElement).down
  have atCommon : presentation.projection common limitElement =
      ULift.up commonElement := by
    exact (ULift.up_down _).symm
  have atSource : presentation.projection sourceFactor.level limitElement =
      ULift.up (deckTransition diagram root toSource commonElement) := by
    calc
      presentation.projection sourceFactor.level limitElement =
          presentation.transition toSource
            (presentation.projection common limitElement) :=
        (presentation.projection_transition toSource limitElement).symm
      _ = presentation.transition toSource (ULift.up commonElement) :=
        congrArg (presentation.transition toSource) atCommon
      _ = ULift.up (deckTransition diagram root toSource commonElement) := rfl
  have atTarget : presentation.projection targetFactor.level limitElement =
      ULift.up (deckTransition diagram root toTarget commonElement) := by
    calc
      presentation.projection targetFactor.level limitElement =
          presentation.transition toTarget
            (presentation.projection common limitElement) :=
        (presentation.projection_transition toTarget limitElement).symm
      _ = presentation.transition toTarget (ULift.up commonElement) :=
        congrArg (presentation.transition toTarget) atCommon
      _ = ULift.up (deckTransition diagram root toTarget commonElement) := rfl
  have equivariant := CategoryTheory.ConcreteCategory.congr_hom
    (commonMap.hom.comm commonElement) point
  change commonMap.hom.hom
      (CategoryTheory.ConcreteCategory.hom
        (sourceFactor.levelAction.obj.ρ
          (presentation.projection sourceFactor.level limitElement)) point) =
    CategoryTheory.ConcreteCategory.hom
      (targetFactor.levelAction.obj.ρ
        (presentation.projection targetFactor.level limitElement))
      (commonMap.hom.hom point)
  rw [atSource, atTarget]
  exact equivariant

/-- The root formula may be expressed directly with the recovered
inverse-limit-equivariant selected-level map. -/
theorem recoveredOrbitCoverMap_root_chosen
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source))
    (point : (finiteDeckOrbitAction
      diagram root source orbit).obj.obj.V.obj) :
    ((recoveredOrbitCoverMap diagram root arrow orbit).app root).hom.hom
        (rootAssociatedCarrierEquiv diagram root
          (literalOrbitLevelFactorization diagram root source orbit).level
          (finiteDeckOrbitAction diagram root source orbit).obj point) =
      rootAssociatedCarrierEquiv diagram root
        (literalOrbitLevelFactorization diagram root target
          (recoveredTargetOrbit diagram root arrow orbit)).level
        (finiteDeckOrbitAction diagram root target
          (recoveredTargetOrbit diagram root arrow orbit)).obj
        ((recoveredChosenLevelMap diagram root arrow orbit).hom.hom point) :=
  recoveredOrbitCoverMap_root diagram root arrow orbit point

/-- Compose the recovered selected-level map with the two factorization
comparisons to obtain a map of literal inverse-limit orbit actions. -/
noncomputable def recoveredLiteralOrbitMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root source) orbit ⟶
      sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root target)
        (recoveredTargetOrbit diagram root arrow orbit) :=
  CategoryTheory.CategoryStruct.comp
    (literalOrbitLevelFactorization diagram root source orbit).comparison.inv
    (CategoryTheory.CategoryStruct.comp
      (recoveredChosenLevelMap diagram root arrow orbit)
      (literalOrbitLevelFactorization diagram root target
        (recoveredTargetOrbit diagram root arrow orbit)).comparison.hom)

/-- Assemble the recovered orbit maps on the explicit orbit decomposition
of the source literal inverse-limit action. -/
noncomputable def recoveredLiteralDecompositionMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target) :
    sourceTemperoidOrbitDecompositionAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root source) ⟶
      literalLimitAction diagram root target :=
  sourceTemperoidOrbitDecompositionMap
    (literalTemperedPresentation diagram root).Limit
    (literalLimitAction diagram root source)
    (literalLimitAction diagram root target)
    (recoveredTargetOrbit diagram root arrow)
    (recoveredLiteralOrbitMap diagram root arrow)

/-- The literal inverse-limit action morphism recovered from a geometric
action-cover morphism. -/
noncomputable def recoveredLiteralActionMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target) :
    literalLimitAction diagram root source ⟶
      literalLimitAction diagram root target :=
  CategoryTheory.CategoryStruct.comp
    (sourceTemperoidOrbitDecompositionIso
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)).inv
    (recoveredLiteralDecompositionMap diagram root arrow)

/-- Transport the recovered literal map back to the declared tempered deck
group. -/
noncomputable def recoveredActionMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target) : source ⟶ target :=
  (literalLimitActionEquivalence diagram root).functor.preimage
    (recoveredLiteralActionMap diagram root arrow)

/-- Re-transporting a recovered action map to the literal inverse-limit
presentation returns the assembled literal map. -/
theorem literalLimitActionMap_recoveredActionMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target) :
    literalLimitActionMap diagram root
        (recoveredActionMap diagram root arrow) =
      recoveredLiteralActionMap diagram root arrow :=
  (literalLimitActionEquivalence diagram root).functor.map_preimage _

/-- On a literal carrier point, the assembled recovery map applies the map
recovered on that point's orbit. -/
theorem recoveredLiteralActionMap_apply
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (point : (literalLimitAction diagram root source).obj.V.obj) :
    (recoveredLiteralActionMap diagram root arrow).hom.hom point =
      ((recoveredLiteralOrbitMap diagram root arrow
        (Quotient.mk'' point)).hom.hom
        (⟨point, rfl⟩ : SourceTemperoidOrbitFiber
          (literalTemperedPresentation diagram root).Limit
          (literalLimitAction diagram root source) (Quotient.mk'' point))).1 :=
  rfl

/-- The action map recovered from a geometric morphism sends every source
orbit to the target orbit selected geometrically. -/
theorem literalTargetOrbit_recoveredActionMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    literalTargetOrbit diagram root
        (recoveredActionMap diagram root arrow) orbit =
      recoveredTargetOrbit diagram root arrow orbit := by
  induction orbit using Quotient.inductionOn' with
  | _ point =>
      change Quotient.mk''
          ((literalLimitActionMap diagram root
            (recoveredActionMap diagram root arrow)).hom.hom point) =
        recoveredTargetOrbit diagram root arrow (Quotient.mk'' point)
      rw [literalLimitActionMap_recoveredActionMap]
      rw [recoveredLiteralActionMap_apply]
      exact ((recoveredLiteralOrbitMap diagram root arrow
        (Quotient.mk'' point)).hom.hom
          (⟨point, rfl⟩ : SourceTemperoidOrbitFiber
            (literalTemperedPresentation diagram root).Limit
            (literalLimitAction diagram root source)
          (Quotient.mk'' point))).2

/-! ## Root-fiber detection of geometric maps -/

/-- A morphism out of an action cover is determined by its complete root
fiber: every coproduct summand is connected and has a normalized root point. -/
theorem actionCover_hom_ext_root
    (source : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    {target : diagram.CovObject}
    {first second : (actionCoverObject diagram root source).obj ⟶ target}
    (atRoot : ∀ point :
      ((actionCoverObject diagram root source).obj.vertexObject root).obj.V.obj,
      (first.app root).hom.hom point = (second.app root).hom.hom point) :
    first = second := by
  apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
  intro vertex
  apply CategoryTheory.ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply CategoryTheory.ConcreteCategory.hom_ext
  rintro ⟨orbit, point⟩
  let family := fun sourceOrbit ↦
    (finiteDeckOrbitCover diagram root source sourceOrbit).obj
  let inclusion :=
    SourceSemiGraphOfAnabelioids.CovObject.Coproduct.inclusion family orbit
  let firstComponent := CategoryTheory.CategoryStruct.comp inclusion first
  let secondComponent := CategoryTheory.CategoryStruct.comp inclusion second
  have componentEquality : firstComponent = secondComponent := by
    apply finiteDeckOrbitCover_hom_ext diagram root source orbit
    intro levelPoint
    exact atRoot ⟨orbit,
      rootAssociatedCarrierEquiv diagram root
        (literalOrbitLevelFactorization diagram root source orbit).level
        (finiteDeckOrbitAction diagram root source orbit).obj levelPoint⟩
  exact congrArg
    (fun arrow : (finiteDeckOrbitCover diagram root source orbit).obj ⟶
        target ↦ (arrow.app vertex).hom.hom point)
    componentEquality

/-- Root normalization of the recovered literal action map is exactly the
given geometric morphism on the normalized root fiber. -/
theorem actionCoverRootEquiv_recoveredLiteralActionMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target)
    (point : (literalLimitAction diagram root source).obj.V.obj) :
    actionCoverRootEquiv diagram root target
        ((recoveredLiteralActionMap diagram root arrow).hom.hom point) =
      (arrow.hom.app root).hom.hom
        (actionCoverRootEquiv diagram root source point) := by
  let orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source) := Quotient.mk'' point
  let orbitPoint : SourceTemperoidOrbitFiber
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source) orbit := ⟨point, rfl⟩
  let sourceFactor := literalOrbitLevelFactorization
    diagram root source orbit
  let targetOrbit := recoveredTargetOrbit diagram root arrow orbit
  let targetFactor := literalOrbitLevelFactorization
    diagram root target targetOrbit
  let sourcePoint := sourceFactor.comparison.inv.hom.hom orbitPoint
  let targetPoint :=
    (recoveredChosenLevelMap diagram root arrow orbit).hom.hom sourcePoint
  have sourceCancellation :
      sourceFactor.comparison.hom.hom sourcePoint = orbitPoint := by
    exact congrArg
      (fun morphism : sourceTemperoidOrbitAction
          (literalTemperedPresentation diagram root).Limit
          (literalLimitAction diagram root source) orbit ⟶
          sourceTemperoidOrbitAction
            (literalTemperedPresentation diagram root).Limit
            (literalLimitAction diagram root source) orbit ↦
        morphism.hom.hom orbitPoint)
      sourceFactor.comparison.inv_hom_id
  have sourceValue :
      (sourceFactor.comparison.hom.hom sourcePoint).1 = point :=
    congrArg Subtype.val sourceCancellation
  have sourceRoot : actionCoverRootEquiv diagram root source point =
      ⟨orbit, rootAssociatedCarrierEquiv diagram root sourceFactor.level
        (finiteDeckOrbitAction diagram root source orbit).obj sourcePoint⟩ := by
    rw [← sourceValue]
    exact actionCoverRootEquiv_comparison_hom
      diagram root source orbit sourcePoint
  have recoveredValue :
      (recoveredLiteralActionMap diagram root arrow).hom.hom point =
        (targetFactor.comparison.hom.hom targetPoint).1 := by
    rw [recoveredLiteralActionMap_apply]
    change ((targetFactor.comparison.hom.hom
      ((recoveredChosenLevelMap diagram root arrow orbit).hom.hom
        (sourceFactor.comparison.inv.hom.hom orbitPoint))).1) = _
    rfl
  have componentEquality :=
    recoveredOrbitCoverMap_comp_inclusion diagram root arrow orbit
  have componentAtRoot := congrArg
    (fun map : (finiteDeckOrbitCover diagram root source orbit).obj ⟶
        (actionCoverObject diagram root target).obj ↦
      (map.app root).hom.hom
        (rootAssociatedCarrierEquiv diagram root sourceFactor.level
          (finiteDeckOrbitAction diagram root source orbit).obj sourcePoint))
    componentEquality
  change (⟨targetOrbit,
      ((recoveredOrbitCoverMap diagram root arrow orbit).app root).hom.hom
        (rootAssociatedCarrierEquiv diagram root sourceFactor.level
          (finiteDeckOrbitAction diagram root source orbit).obj sourcePoint)⟩ :
      ((actionCoverObject diagram root target).obj.vertexObject root).obj.V.obj) =
    (arrow.hom.app root).hom.hom
      ⟨orbit, rootAssociatedCarrierEquiv diagram root sourceFactor.level
        (finiteDeckOrbitAction diagram root source orbit).obj sourcePoint⟩
      at componentAtRoot
  rw [recoveredOrbitCoverMap_root_chosen] at componentAtRoot
  rw [recoveredValue]
  rw [actionCoverRootEquiv_comparison_hom]
  rw [sourceRoot]
  simpa only [targetPoint, targetFactor, sourceFactor, targetOrbit] using
    componentAtRoot

/-- Applying the geometric action-cover functor to the recovered action map
returns the original geometric morphism. -/
theorem actionCoverMap_recoveredActionMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target) :
    actionCoverMap diagram root (recoveredActionMap diagram root arrow) =
      arrow := by
  apply CategoryTheory.ObjectProperty.hom_ext
  apply actionCover_hom_ext_root diagram root source
  intro rootPoint
  let point := (actionCoverRootEquiv diagram root source).symm rootPoint
  rw [← (actionCoverRootEquiv diagram root source).apply_symm_apply rootPoint]
  rw [← actionCoverRootEquiv_naturality]
  rw [literalLimitActionMap_recoveredActionMap]
  exact actionCoverRootEquiv_recoveredLiteralActionMap
    diagram root arrow point

/-- Every geometric morphism between action covers is induced by a unique
morphism of tempered deck-group actions. -/
noncomputable instance actionCoverFunctorFull :
    (actionCoverFunctor diagram root).Full where
  map_surjective arrow :=
    ⟨recoveredActionMap diagram root arrow,
      actionCoverMap_recoveredActionMap diagram root arrow⟩

end SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

end Iut
