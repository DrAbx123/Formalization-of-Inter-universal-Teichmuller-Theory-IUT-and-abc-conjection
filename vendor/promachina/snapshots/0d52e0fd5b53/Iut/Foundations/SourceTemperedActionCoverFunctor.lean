/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedActionCoverObjects
import Iut.Foundations.SourceTemperedUniversalCoverRefinement

/-!
# Functorial geometric covers attached to tempered actions

This file upgrades the object assignment of
`SourceTemperedActionCoverObjects` to morphisms.  A morphism of inverse-limit
actions sends each connected source orbit into one connected target orbit.
The independently chosen finite levels of those two orbits are brought to a
common finer Galois level.  Coordinate surjectivity then descends the orbit
map to that common finite deck group, and refinement invariance turns the
resulting finite-level associated-quotient map into a map between the
original component covers.
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

/-- Transport a morphism of declared tempered deck-group actions to the
literal inverse-limit presentation. -/
noncomputable def literalLimitActionMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : source ⟶ target) :
    literalLimitAction diagram root source ⟶
      literalLimitAction diagram root target :=
  (literalLimitActionEquivalence diagram root).functor.map arrow

@[simp]
theorem literalLimitActionMap_id
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)) :
    literalLimitActionMap diagram root
        (CategoryTheory.CategoryStruct.id object) =
      CategoryTheory.CategoryStruct.id
        (literalLimitAction diagram root object) :=
  (literalLimitActionEquivalence diagram root).functor.map_id object

@[simp]
theorem literalLimitActionMap_comp
    {first second third : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (firstMap : first ⟶ second) (secondMap : second ⟶ third) :
    literalLimitActionMap diagram root
        (CategoryTheory.CategoryStruct.comp firstMap secondMap) =
      CategoryTheory.CategoryStruct.comp
        (literalLimitActionMap diagram root firstMap)
        (literalLimitActionMap diagram root secondMap) :=
  (literalLimitActionEquivalence diagram root).functor.map_comp
    firstMap secondMap

/-- The target orbit containing the image of a source orbit. -/
noncomputable def literalTargetOrbit
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : source ⟶ target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root target) :=
  sourceTemperoidOrbitMap (literalLimitActionMap diagram root arrow) orbit

@[simp]
theorem literalTargetOrbit_id
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    literalTargetOrbit diagram root
        (CategoryTheory.CategoryStruct.id object) orbit = orbit := by
  rw [literalTargetOrbit, literalLimitActionMap_id]
  exact sourceTemperoidOrbitMap_id _ orbit

theorem literalTargetOrbit_comp
    {first second third : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (firstMap : first ⟶ second) (secondMap : second ⟶ third)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root first)) :
    literalTargetOrbit diagram root
        (CategoryTheory.CategoryStruct.comp firstMap secondMap) orbit =
      literalTargetOrbit diagram root secondMap
        (literalTargetOrbit diagram root firstMap orbit) := by
  rw [literalTargetOrbit, literalLimitActionMap_comp]
  exact sourceTemperoidOrbitMap_comp
    (literalLimitActionMap diagram root firstMap)
    (literalLimitActionMap diagram root secondMap) orbit

/-- The map between connected literal inverse-limit orbit actions. -/
noncomputable def literalOrbitMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : source ⟶ target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root source) orbit ⟶
      sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root target)
        (literalTargetOrbit diagram root arrow orbit) :=
  sourceTemperoidOrbitFiberMap
    (literalLimitActionMap diagram root arrow) orbit

/-- The chosen common refinement of the independently selected finite levels
of a source orbit and its target orbit. -/
noncomputable def commonOrbitLevel
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : source ⟶ target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    GaloisLevel diagram root :=
  CategoryTheory.IsCofiltered.min
    (literalOrbitLevelFactorization diagram root source orbit).level
    (literalOrbitLevelFactorization diagram root target
      (literalTargetOrbit diagram root arrow orbit)).level

/-- The common orbit level refines the source orbit's selected level. -/
noncomputable def commonOrbitToSource
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : source ⟶ target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    commonOrbitLevel diagram root arrow orbit ⟶
      (literalOrbitLevelFactorization diagram root source orbit).level :=
  CategoryTheory.IsCofiltered.minToLeft _ _

/-- The common orbit level refines the target orbit's selected level. -/
noncomputable def commonOrbitToTarget
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : source ⟶ target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    commonOrbitLevel diagram root arrow orbit ⟶
      (literalOrbitLevelFactorization diagram root target
        (literalTargetOrbit diagram root arrow orbit)).level :=
  CategoryTheory.IsCofiltered.minToRight _ _

/-- The finite-level action selected for one literal inverse-limit orbit,
viewed again as an action of the inverse-limit group. -/
noncomputable def literalOrbitLevelAction
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    SourceTemperoidAction
      (literalTemperedPresentation diagram root).Limit :=
  (ContAction.res SourceCountableTypeCat
      ((literalTemperedPresentation diagram root).continuousProjection
        (literalOrbitLevelFactorization diagram root object orbit).level)).obj
    (literalOrbitLevelFactorization diagram root object orbit).levelAction

/-- Compare two independently selected finite-level orbit presentations
through an explicitly supplied map of their literal inverse-limit orbits. -/
noncomputable def chosenLevelOrbitMapBetween
    (source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (sourceOrbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source))
    (targetOrbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root target))
    (orbitMap : sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root source) sourceOrbit ⟶
      sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root target) targetOrbit) :
    literalOrbitLevelAction diagram root source sourceOrbit ⟶
      literalOrbitLevelAction diagram root target targetOrbit :=
  CategoryTheory.CategoryStruct.comp
    (literalOrbitLevelFactorization
      diagram root source sourceOrbit).comparison.hom
    (CategoryTheory.CategoryStruct.comp orbitMap
      (literalOrbitLevelFactorization
        diagram root target targetOrbit).comparison.inv)

/-- Compare the two chosen finite-level carriers through their literal
inverse-limit orbit actions. -/
noncomputable def chosenLevelOrbitMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : source ⟶ target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    (ContAction.res SourceCountableTypeCat
      ((literalTemperedPresentation diagram root).continuousProjection
        (literalOrbitLevelFactorization
          diagram root source orbit).level)).obj
        (literalOrbitLevelFactorization
          diagram root source orbit).levelAction ⟶
      (ContAction.res SourceCountableTypeCat
        ((literalTemperedPresentation diagram root).continuousProjection
      (literalOrbitLevelFactorization diagram root target
          (literalTargetOrbit diagram root arrow orbit)).level)).obj
        (literalOrbitLevelFactorization diagram root target
          (literalTargetOrbit diagram root arrow orbit)).levelAction := by
  exact chosenLevelOrbitMapBetween diagram root source target orbit
    (literalTargetOrbit diagram root arrow orbit)
    (literalOrbitMap diagram root arrow orbit)

/-- Transporting an orbit fiber along equality of orbit indices preserves
its underlying point. -/
theorem sourceTemperoidOrbitAction_eqToHom_val
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    {first second : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)}
    (equality : first = second)
    (point : (sourceTemperoidOrbitAction
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object) first).obj.V.obj) :
    ((((CategoryTheory.eqToHom (congrArg
      (sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root object)) equality)).hom.hom) point).1) =
      point.1 := by
  cases equality
  rfl

/-- The literal orbit map of an identity arrow, followed by transport along
the canonical equality of orbit indices. -/
noncomputable def literalOrbitMapIdNormalized
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root object) orbit ⟶
      sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root object) orbit :=
  CategoryTheory.CategoryStruct.comp
    (literalOrbitMap diagram root
      (CategoryTheory.CategoryStruct.id object) orbit)
    (CategoryTheory.eqToHom (congrArg
      (sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root object))
      (literalTargetOrbit_id diagram root object orbit)))

@[simp]
theorem literalOrbitMapIdNormalized_eq_id
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    literalOrbitMapIdNormalized diagram root object orbit =
      CategoryTheory.CategoryStruct.id _ := by
  apply CategoryTheory.ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro point
  apply Subtype.ext
  change (((CategoryTheory.eqToHom (congrArg
      (sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root object))
      (literalTargetOrbit_id diagram root object orbit))).hom.hom)
        ((literalOrbitMap diagram root
          (CategoryTheory.CategoryStruct.id object) orbit).hom.hom point)).1 = point.1
  · rw [sourceTemperoidOrbitAction_eqToHom_val]
    · change (literalLimitActionMap diagram root
        (CategoryTheory.CategoryStruct.id object)).hom.hom point.1 = point.1
      rw [literalLimitActionMap_id]
      rfl
    · exact literalTargetOrbit_id diagram root object orbit

/-- The direct literal orbit map of a composite, transported to the
iterated target orbit. -/
noncomputable def literalOrbitMapCompNormalized
    {first second third : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (firstMap : first ⟶ second) (secondMap : second ⟶ third)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root first)) :
    sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root first) orbit ⟶
      sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root third)
        (literalTargetOrbit diagram root secondMap
          (literalTargetOrbit diagram root firstMap orbit)) :=
  CategoryTheory.CategoryStruct.comp
    (literalOrbitMap diagram root
      (CategoryTheory.CategoryStruct.comp firstMap secondMap) orbit)
    (CategoryTheory.eqToHom (congrArg
      (sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root third))
      (literalTargetOrbit_comp diagram root firstMap secondMap orbit)))

/-- Restricted literal orbit maps respect composition after the canonical
identification of the direct and iterated target orbits. -/
theorem literalOrbitMapCompNormalized_eq_comp
    {first second third : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (firstMap : first ⟶ second) (secondMap : second ⟶ third)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root first)) :
    literalOrbitMapCompNormalized diagram root firstMap secondMap orbit =
      CategoryTheory.CategoryStruct.comp
        (literalOrbitMap diagram root firstMap orbit)
        (literalOrbitMap diagram root secondMap
          (literalTargetOrbit diagram root firstMap orbit)) := by
  apply CategoryTheory.ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro point
  apply Subtype.ext
  change (((CategoryTheory.eqToHom (congrArg
      (sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root third))
      (literalTargetOrbit_comp diagram root firstMap secondMap orbit))).hom.hom)
        ((literalOrbitMap diagram root
          (CategoryTheory.CategoryStruct.comp firstMap secondMap) orbit).hom.hom
          point)).1 = _
  · rw [sourceTemperoidOrbitAction_eqToHom_val]
    · change (literalLimitActionMap diagram root
          (CategoryTheory.CategoryStruct.comp firstMap secondMap)).hom.hom point.1 =
        (literalLimitActionMap diagram root secondMap).hom.hom
          ((literalLimitActionMap diagram root firstMap).hom.hom point.1)
      rw [literalLimitActionMap_comp]
      rfl
    · exact literalTargetOrbit_comp diagram root firstMap secondMap orbit

/-- Cancellation of independently selected orbit presentations is stable
under transport of the orbit index. -/
theorem chosenLevelOrbitMapBetween_normalized_eq_id
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (sourceOrbit targetOrbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object))
    (orbitMap : sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root object) sourceOrbit ⟶
      sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root object) targetOrbit)
    (equality : targetOrbit = sourceOrbit)
    (orbitMapLaw : CategoryTheory.CategoryStruct.comp orbitMap
        (CategoryTheory.eqToHom (congrArg
          (sourceTemperoidOrbitAction
            (literalTemperedPresentation diagram root).Limit
            (literalLimitAction diagram root object)) equality)) =
      CategoryTheory.CategoryStruct.id _) :
    CategoryTheory.CategoryStruct.comp
        (chosenLevelOrbitMapBetween diagram root object object
          sourceOrbit targetOrbit orbitMap)
        (CategoryTheory.eqToHom (congrArg
          (literalOrbitLevelAction diagram root object) equality)) =
      CategoryTheory.CategoryStruct.id _ := by
  subst targetOrbit
  simp only [CategoryTheory.eqToHom_refl,
    CategoryTheory.Category.comp_id] at orbitMapLaw
  unfold chosenLevelOrbitMapBetween
  rw [orbitMapLaw]
  change CategoryTheory.CategoryStruct.comp
      (literalOrbitLevelFactorization
        diagram root object sourceOrbit).comparison.hom
      (CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CategoryStruct.id _)
        (literalOrbitLevelFactorization
          diagram root object sourceOrbit).comparison.inv) =
    CategoryTheory.CategoryStruct.id _
  rw [CategoryTheory.Category.id_comp]
  exact (literalOrbitLevelFactorization
    diagram root object sourceOrbit).comparison.hom_inv_id

/-- The chosen-level identity map transported along the canonical equality
of its target orbit with the source orbit. -/
noncomputable def chosenLevelOrbitMapIdNormalized
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    literalOrbitLevelAction diagram root object orbit ⟶
      literalOrbitLevelAction diagram root object orbit :=
  CategoryTheory.CategoryStruct.comp
    (chosenLevelOrbitMap diagram root
      (CategoryTheory.CategoryStruct.id object) orbit)
    (CategoryTheory.eqToHom
      (congrArg (literalOrbitLevelAction diagram root object)
      (literalTargetOrbit_id diagram root object orbit)))

@[simp]
theorem chosenLevelOrbitMapIdNormalized_eq_id
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    chosenLevelOrbitMapIdNormalized diagram root object orbit =
      CategoryTheory.CategoryStruct.id _ := by
  exact chosenLevelOrbitMapBetween_normalized_eq_id diagram root object orbit
    (literalTargetOrbit diagram root
      (CategoryTheory.CategoryStruct.id object) orbit)
    (literalOrbitMap diagram root
      (CategoryTheory.CategoryStruct.id object) orbit)
    (literalTargetOrbit_id diagram root object orbit)
    (literalOrbitMapIdNormalized_eq_id diagram root object orbit)

/-- Comparison through independently selected finite-level presentations
preserves composition after target-orbit transport. -/
theorem chosenLevelOrbitMapBetween_normalized_eq_comp
    (first second third : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (sourceOrbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root first))
    (middleOrbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root second))
    (directTargetOrbit sequentialTargetOrbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root third))
    (directOrbitMap : sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root first) sourceOrbit ⟶
      sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root third) directTargetOrbit)
    (firstOrbitMap : sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root first) sourceOrbit ⟶
      sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root second) middleOrbit)
    (secondOrbitMap : sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root second) middleOrbit ⟶
      sourceTemperoidOrbitAction
        (literalTemperedPresentation diagram root).Limit
        (literalLimitAction diagram root third) sequentialTargetOrbit)
    (equality : directTargetOrbit = sequentialTargetOrbit)
    (orbitMapLaw : CategoryTheory.CategoryStruct.comp directOrbitMap
        (CategoryTheory.eqToHom (congrArg
          (sourceTemperoidOrbitAction
            (literalTemperedPresentation diagram root).Limit
            (literalLimitAction diagram root third)) equality)) =
      CategoryTheory.CategoryStruct.comp firstOrbitMap secondOrbitMap) :
    CategoryTheory.CategoryStruct.comp
        (chosenLevelOrbitMapBetween diagram root first third sourceOrbit
          directTargetOrbit directOrbitMap)
        (CategoryTheory.eqToHom (congrArg
          (literalOrbitLevelAction diagram root third) equality)) =
      CategoryTheory.CategoryStruct.comp
        (chosenLevelOrbitMapBetween diagram root first second sourceOrbit
          middleOrbit firstOrbitMap)
        (chosenLevelOrbitMapBetween diagram root second third middleOrbit
          sequentialTargetOrbit secondOrbitMap) := by
  subst directTargetOrbit
  rw [CategoryTheory.eqToHom_refl,
    CategoryTheory.Category.comp_id] at orbitMapLaw ⊢
  rw [orbitMapLaw]
  unfold chosenLevelOrbitMapBetween
  simp only [CategoryTheory.Category.assoc,
    CategoryTheory.Iso.cancel_iso_hom_left]
  calc
    CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CategoryStruct.comp firstOrbitMap secondOrbitMap)
        (literalOrbitLevelFactorization diagram root third
          sequentialTargetOrbit).comparison.inv =
      CategoryTheory.CategoryStruct.comp firstOrbitMap
        (CategoryTheory.CategoryStruct.comp secondOrbitMap
          (literalOrbitLevelFactorization diagram root third
            sequentialTargetOrbit).comparison.inv) :=
      CategoryTheory.Category.assoc _ _ _
    _ = CategoryTheory.CategoryStruct.comp firstOrbitMap
        (CategoryTheory.CategoryStruct.comp
          (literalOrbitLevelFactorization diagram root second
            middleOrbit).comparison.inv
          (CategoryTheory.CategoryStruct.comp
            (literalOrbitLevelFactorization diagram root second
              middleOrbit).comparison.hom
            (CategoryTheory.CategoryStruct.comp secondOrbitMap
              (literalOrbitLevelFactorization diagram root third
                sequentialTargetOrbit).comparison.inv))) := by
      apply congrArg (CategoryTheory.CategoryStruct.comp firstOrbitMap)
      exact ((literalOrbitLevelFactorization diagram root second
        middleOrbit).comparison.inv_hom_id_assoc _).symm

/-- The chosen-level map of a composite, transported to the iterated target
orbit presentation. -/
noncomputable def chosenLevelOrbitMapCompNormalized
    {first second third : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (firstMap : first ⟶ second) (secondMap : second ⟶ third)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root first)) :
    literalOrbitLevelAction diagram root first orbit ⟶
      literalOrbitLevelAction diagram root third
        (literalTargetOrbit diagram root secondMap
          (literalTargetOrbit diagram root firstMap orbit)) :=
  CategoryTheory.CategoryStruct.comp
    (chosenLevelOrbitMap diagram root
      (CategoryTheory.CategoryStruct.comp firstMap secondMap) orbit)
    (CategoryTheory.eqToHom (congrArg
      (literalOrbitLevelAction diagram root third)
      (literalTargetOrbit_comp diagram root firstMap secondMap orbit)))

/-- Chosen finite-level orbit maps respect composition after canonical
target-orbit transport. -/
theorem chosenLevelOrbitMapCompNormalized_eq_comp
    {first second third : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (firstMap : first ⟶ second) (secondMap : second ⟶ third)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root first)) :
    chosenLevelOrbitMapCompNormalized diagram root firstMap secondMap orbit =
      CategoryTheory.CategoryStruct.comp
        (chosenLevelOrbitMap diagram root firstMap orbit)
        (chosenLevelOrbitMap diagram root secondMap
          (literalTargetOrbit diagram root firstMap orbit)) := by
  exact chosenLevelOrbitMapBetween_normalized_eq_comp diagram root
    first second third orbit
    (literalTargetOrbit diagram root firstMap orbit)
    (literalTargetOrbit diagram root
      (CategoryTheory.CategoryStruct.comp firstMap secondMap) orbit)
    (literalTargetOrbit diagram root secondMap
      (literalTargetOrbit diagram root firstMap orbit))
    (literalOrbitMap diagram root
      (CategoryTheory.CategoryStruct.comp firstMap secondMap) orbit)
    (literalOrbitMap diagram root firstMap orbit)
    (literalOrbitMap diagram root secondMap
      (literalTargetOrbit diagram root firstMap orbit))
    (literalTargetOrbit_comp diagram root firstMap secondMap orbit)
    (literalOrbitMapCompNormalized_eq_comp
      diagram root firstMap secondMap orbit)

/-- The orbit map descended to the chosen common finite deck level, expressed
with the original unlifted deck groups used by the geometric associated
quotient functors. -/
noncomputable def commonDeckOrbitMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : source ⟶ target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    restrictDeckAction diagram root
        (commonOrbitToSource diagram root arrow orbit)
        (finiteDeckOrbitAction diagram root source orbit).obj ⟶
      restrictDeckAction diagram root
        (commonOrbitToTarget diagram root arrow orbit)
        (finiteDeckOrbitAction diagram root target
          (literalTargetOrbit diagram root arrow orbit)).obj := by
  let presentation := literalTemperedPresentation diagram root
  let sourceFactor := literalOrbitLevelFactorization
    diagram root source orbit
  let targetOrbit := literalTargetOrbit diagram root arrow orbit
  let targetFactor := literalOrbitLevelFactorization
    diagram root target targetOrbit
  let common := commonOrbitLevel diagram root arrow orbit
  let toSource := commonOrbitToSource diagram root arrow orbit
  let toTarget := commonOrbitToTarget diagram root arrow orbit
  let limitMap := chosenLevelOrbitMap diagram root arrow orbit
  apply CategoryTheory.ObjectProperty.homMk
  refine
    { hom := SourceCountableTypeCat.homMk limitMap.hom.hom
      comm := ?_ }
  intro transformation
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro point
  obtain ⟨limitElement, atCommon⟩ :=
    literalTemperedPresentation_projection_surjective
      diagram root common (ULift.up transformation)
  have atSource : presentation.projection sourceFactor.level limitElement =
      ULift.up (deckTransition diagram root toSource transformation) := by
    calc
      presentation.projection sourceFactor.level limitElement =
          presentation.transition toSource
            (presentation.projection common limitElement) :=
        (presentation.projection_transition toSource limitElement).symm
      _ = presentation.transition toSource (ULift.up transformation) :=
        congrArg (presentation.transition toSource) atCommon
      _ = ULift.up (deckTransition diagram root toSource transformation) := rfl
  have atTarget : presentation.projection targetFactor.level limitElement =
      ULift.up (deckTransition diagram root toTarget transformation) := by
    calc
      presentation.projection targetFactor.level limitElement =
          presentation.transition toTarget
            (presentation.projection common limitElement) :=
        (presentation.projection_transition toTarget limitElement).symm
      _ = presentation.transition toTarget (ULift.up transformation) :=
        congrArg (presentation.transition toTarget) atCommon
      _ = ULift.up (deckTransition diagram root toTarget transformation) := rfl
  have equivariant := CategoryTheory.ConcreteCategory.congr_hom
    (limitMap.hom.comm limitElement) point
  change limitMap.hom.hom
      (CategoryTheory.ConcreteCategory.hom
        (sourceFactor.levelAction.obj.ρ
          (presentation.projection sourceFactor.level limitElement)) point) =
    CategoryTheory.ConcreteCategory.hom
      (targetFactor.levelAction.obj.ρ
        (presentation.projection targetFactor.level limitElement))
      (limitMap.hom.hom point) at equivariant
  rw [atSource, atTarget] at equivariant
  change limitMap.hom.hom
      (CategoryTheory.ConcreteCategory.hom
        (sourceFactor.levelAction.obj.ρ
          (ULift.up (deckTransition diagram root toSource transformation)))
        point) =
    CategoryTheory.ConcreteCategory.hom
      (targetFactor.levelAction.obj.ρ
        (ULift.up (deckTransition diagram root toTarget transformation)))
      (limitMap.hom.hom point)
  exact equivariant

/-- The geometric map from one source orbit cover to the target orbit cover.
Both independently selected presentations are compared at their canonical
common refinement. -/
noncomputable def finiteDeckOrbitCoverMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : source ⟶ target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source)) :
    finiteDeckOrbitCover diagram root source orbit ⟶
      finiteDeckOrbitCover diagram root target
        (literalTargetOrbit diagram root arrow orbit) :=
  CategoryTheory.CategoryStruct.comp
    (associatedTemperedRefinementIso diagram root
      (commonOrbitToSource diagram root arrow orbit)
      (finiteDeckOrbitAction diagram root source orbit).obj).inv
    (CategoryTheory.CategoryStruct.comp
      ((associatedTemperedFunctor diagram root
        (commonOrbitLevel diagram root arrow orbit)).map
          (commonDeckOrbitMap diagram root arrow orbit))
      (associatedTemperedRefinementIso diagram root
        (commonOrbitToTarget diagram root arrow orbit)
        (finiteDeckOrbitAction diagram root target
          (literalTargetOrbit diagram root arrow orbit)).obj).hom)

/-- Every normalized root point of an orbit cover is a point of geometric
connectedness.  This is the pointed form used to compare independently
chosen finite-level presentations. -/
theorem finiteDeckOrbitCover_root_isPointConnected
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object))
    (point : (finiteDeckOrbitAction diagram root object orbit).obj.obj.V.obj) :
    IsPointConnected (finiteDeckOrbitCover diagram root object orbit).obj
      ⟨root, rootAssociatedCarrierEquiv diagram root
        (literalOrbitLevelFactorization diagram root object orbit).level
        (finiteDeckOrbitAction diagram root object orbit).obj point⟩ := by
  let factor := literalOrbitLevelFactorization diagram root object orbit
  let action := finiteDeckOrbitAction diagram root object orbit
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root factor.level.object factor.level.rootVertex
  let deckAction := deckCovActionHom diagram root factor.level
  rw [rootAssociatedCarrierEquiv_apply]
  change IsPointConnected
    (SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.covObject
      source deckAction action.obj.obj.V.obj) _
  exact covObject_isPointConnected_of_pretransitive
    source deckAction root (rootVertexPoint diagram root factor.level)
    (covObject_isPointConnected diagram root factor.level) point
    action.property.2

/-- A morphism out of one connected orbit cover is determined by its values
on normalized points over the distinguished root. -/
theorem finiteDeckOrbitCover_hom_ext
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object))
    {target : diagram.CovObject}
    {first second : (finiteDeckOrbitCover
      diagram root object orbit).obj ⟶ target}
    (atRoot : ∀ point : (finiteDeckOrbitAction
        diagram root object orbit).obj.obj.V.obj,
      (first.app root).hom.hom
          (rootAssociatedCarrierEquiv diagram root
            (literalOrbitLevelFactorization diagram root object orbit).level
            (finiteDeckOrbitAction diagram root object orbit).obj point) =
        (second.app root).hom.hom
          (rootAssociatedCarrierEquiv diagram root
            (literalOrbitLevelFactorization diagram root object orbit).level
            (finiteDeckOrbitAction diagram root object orbit).obj point)) :
    first = second := by
  let point : (finiteDeckOrbitAction
      diagram root object orbit).obj.obj.V.obj :=
    Classical.choice (finiteDeckOrbitAction
      diagram root object orbit).property.1
  exact hom_ext_of_isPointConnected
    (⟨root, rootAssociatedCarrierEquiv diagram root
      (literalOrbitLevelFactorization diagram root object orbit).level
      (finiteDeckOrbitAction diagram root object orbit).obj point⟩ :
      GeometricPoint (finiteDeckOrbitCover diagram root object orbit).obj)
    (finiteDeckOrbitCover_root_isPointConnected
      diagram root object orbit point) (atRoot point)

/-- On normalized root fibers, the geometric orbit-cover map is exactly its
chosen finite-level auxiliary map. -/
theorem finiteDeckOrbitCoverMap_root
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : source ⟶ target)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root source))
    (point : (finiteDeckOrbitAction diagram root source orbit).obj.obj.V.obj) :
    (((finiteDeckOrbitCoverMap diagram root arrow orbit).hom.app root).hom.hom)
        (rootAssociatedCarrierEquiv diagram root
          (literalOrbitLevelFactorization diagram root source orbit).level
          (finiteDeckOrbitAction diagram root source orbit).obj point) =
      rootAssociatedCarrierEquiv diagram root
        (literalOrbitLevelFactorization diagram root target
          (literalTargetOrbit diagram root arrow orbit)).level
        (finiteDeckOrbitAction diagram root target
          (literalTargetOrbit diagram root arrow orbit)).obj
        ((chosenLevelOrbitMap diagram root arrow orbit).hom.hom point) := by
  let sourceIso := associatedTemperedRefinementIso diagram root
    (commonOrbitToSource diagram root arrow orbit)
    (finiteDeckOrbitAction diagram root source orbit).obj
  let targetIso := associatedTemperedRefinementIso diagram root
    (commonOrbitToTarget diagram root arrow orbit)
    (finiteDeckOrbitAction diagram root target
      (literalTargetOrbit diagram root arrow orbit)).obj
  let middleMap := (associatedTemperedFunctor diagram root
    (commonOrbitLevel diagram root arrow orbit)).map
      (commonDeckOrbitMap diagram root arrow orbit)
  change ((targetIso.hom.hom.app root).hom.hom)
      (((middleMap.hom.app root).hom.hom)
        (((sourceIso.inv.hom.app root).hom.hom)
          (rootAssociatedCarrierEquiv diagram root
            (literalOrbitLevelFactorization diagram root source orbit).level
            (finiteDeckOrbitAction diagram root source orbit).obj point))) = _
  rw [associatedTemperedRefinementIso_inv_root_mk]
  rw [rootAssociatedCarrierEquiv_apply]
  change ((targetIso.hom.hom.app root).hom.hom)
      (rootAssociatedCarrierEquiv diagram root
        (commonOrbitLevel diagram root arrow orbit)
        (restrictDeckAction diagram root
          (commonOrbitToTarget diagram root arrow orbit)
          (finiteDeckOrbitAction diagram root target
            (literalTargetOrbit diagram root arrow orbit)).obj)
        ((chosenLevelOrbitMap diagram root arrow orbit).hom.hom point)) = _
  exact associatedTemperedRefinementHom_root_mk
    diagram root (commonOrbitToTarget diagram root arrow orbit)
    (finiteDeckOrbitAction diagram root target
      (literalTargetOrbit diagram root arrow orbit)).obj
    ((chosenLevelOrbitMap diagram root arrow orbit).hom.hom point)

/-- A pointed component map is the identity after orbit-index transport as
soon as its normalized finite-level carrier map is the identity. -/
theorem finiteDeckOrbitCoverHom_normalized_eq_id
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (sourceOrbit targetOrbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    let sourceLevel := literalOrbitLevelFactorization
      diagram root object sourceOrbit
    let targetLevel := literalOrbitLevelFactorization
      diagram root object targetOrbit
    ∀ (coverMap : finiteDeckOrbitCover diagram root object sourceOrbit ⟶
        finiteDeckOrbitCover diagram root object targetOrbit)
      (levelMap : literalOrbitLevelAction diagram root object sourceOrbit ⟶
        literalOrbitLevelAction diagram root object targetOrbit)
      (equality : targetOrbit = sourceOrbit),
      (∀ point : (finiteDeckOrbitAction
          diagram root object sourceOrbit).obj.obj.V.obj,
        ((coverMap.hom.app root).hom.hom)
            (rootAssociatedCarrierEquiv diagram root sourceLevel.level
              (finiteDeckOrbitAction diagram root object sourceOrbit).obj point) =
          rootAssociatedCarrierEquiv diagram root targetLevel.level
            (finiteDeckOrbitAction diagram root object targetOrbit).obj
            (levelMap.hom.hom point)) →
      CategoryTheory.CategoryStruct.comp levelMap
          (CategoryTheory.eqToHom (congrArg
            (literalOrbitLevelAction diagram root object) equality)) =
        CategoryTheory.CategoryStruct.id _ →
      CategoryTheory.CategoryStruct.comp coverMap.hom
          (CategoryTheory.eqToHom (congrArg
            (fun orbit ↦ (finiteDeckOrbitCover
              diagram root object orbit).obj) equality)) =
        CategoryTheory.CategoryStruct.id
          (finiteDeckOrbitCover diagram root object sourceOrbit).obj := by
  dsimp only
  intro coverMap levelMap equality atRoot levelMapLaw
  subst targetOrbit
  rw [CategoryTheory.eqToHom_refl] at levelMapLaw ⊢
  change CategoryTheory.CategoryStruct.comp levelMap
    (CategoryTheory.CategoryStruct.id _) =
      CategoryTheory.CategoryStruct.id _ at levelMapLaw
  rw [CategoryTheory.Category.comp_id] at levelMapLaw
  rw [CategoryTheory.Category.comp_id]
  apply finiteDeckOrbitCover_hom_ext diagram root object sourceOrbit
  intro point
  rw [atRoot]
  have atPoint := congrArg (fun map ↦ map.hom.hom point) levelMapLaw
  exact congrArg
    (rootAssociatedCarrierEquiv diagram root
      (literalOrbitLevelFactorization diagram root object sourceOrbit).level
      (finiteDeckOrbitAction diagram root object sourceOrbit).obj) atPoint

/-- The underlying geometric component map attached to an identity arrow,
transported along the canonical equality of target and source orbit indices. -/
noncomputable def finiteDeckOrbitCoverMapIdNormalizedHom
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    (finiteDeckOrbitCover diagram root object orbit).obj ⟶
      (finiteDeckOrbitCover diagram root object orbit).obj :=
  CategoryTheory.CategoryStruct.comp
    (finiteDeckOrbitCoverMap diagram root
      (CategoryTheory.CategoryStruct.id object) orbit).hom
    (CategoryTheory.eqToHom (congrArg
      (fun orbit ↦ (finiteDeckOrbitCover diagram root object orbit).obj)
      (literalTargetOrbit_id diagram root object orbit)))

theorem finiteDeckOrbitCoverMapIdNormalizedHom_eq_id
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root object)) :
    finiteDeckOrbitCoverMapIdNormalizedHom diagram root object orbit =
      CategoryTheory.CategoryStruct.id
        (finiteDeckOrbitCover diagram root object orbit).obj := by
  exact finiteDeckOrbitCoverHom_normalized_eq_id diagram root object orbit
    (literalTargetOrbit diagram root
      (CategoryTheory.CategoryStruct.id object) orbit)
    (finiteDeckOrbitCoverMap diagram root
      (CategoryTheory.CategoryStruct.id object) orbit)
    (chosenLevelOrbitMap diagram root
      (CategoryTheory.CategoryStruct.id object) orbit)
    (literalTargetOrbit_id diagram root object orbit)
    (finiteDeckOrbitCoverMap_root diagram root
      (CategoryTheory.CategoryStruct.id object) orbit)
    (chosenLevelOrbitMapIdNormalized_eq_id diagram root object orbit)

/-- Pointed component-cover maps preserve composition whenever their
normalized finite-level carrier maps do. -/
theorem finiteDeckOrbitCoverHom_normalized_eq_comp
    (first second third : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root))
    (sourceOrbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root first))
    (middleOrbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root second))
    (directTargetOrbit sequentialTargetOrbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root third))
    (directCoverMap : finiteDeckOrbitCover diagram root first sourceOrbit ⟶
      finiteDeckOrbitCover diagram root third directTargetOrbit)
    (firstCoverMap : finiteDeckOrbitCover diagram root first sourceOrbit ⟶
      finiteDeckOrbitCover diagram root second middleOrbit)
    (secondCoverMap : finiteDeckOrbitCover diagram root second middleOrbit ⟶
      finiteDeckOrbitCover diagram root third sequentialTargetOrbit)
    (directLevelMap : literalOrbitLevelAction diagram root first sourceOrbit ⟶
      literalOrbitLevelAction diagram root third directTargetOrbit)
    (firstLevelMap : literalOrbitLevelAction diagram root first sourceOrbit ⟶
      literalOrbitLevelAction diagram root second middleOrbit)
    (secondLevelMap : literalOrbitLevelAction diagram root second middleOrbit ⟶
      literalOrbitLevelAction diagram root third sequentialTargetOrbit)
    (equality : directTargetOrbit = sequentialTargetOrbit)
    (directAtRoot : ∀ point : (finiteDeckOrbitAction
        diagram root first sourceOrbit).obj.obj.V.obj,
      ((directCoverMap.hom.app root).hom.hom)
          (rootAssociatedCarrierEquiv diagram root
            (literalOrbitLevelFactorization diagram root first sourceOrbit).level
            (finiteDeckOrbitAction diagram root first sourceOrbit).obj point) =
        rootAssociatedCarrierEquiv diagram root
          (literalOrbitLevelFactorization diagram root third
            directTargetOrbit).level
          (finiteDeckOrbitAction diagram root third directTargetOrbit).obj
          (directLevelMap.hom.hom point))
    (firstAtRoot : ∀ point : (finiteDeckOrbitAction
        diagram root first sourceOrbit).obj.obj.V.obj,
      ((firstCoverMap.hom.app root).hom.hom)
          (rootAssociatedCarrierEquiv diagram root
            (literalOrbitLevelFactorization diagram root first sourceOrbit).level
            (finiteDeckOrbitAction diagram root first sourceOrbit).obj point) =
        rootAssociatedCarrierEquiv diagram root
          (literalOrbitLevelFactorization diagram root second middleOrbit).level
          (finiteDeckOrbitAction diagram root second middleOrbit).obj
          (firstLevelMap.hom.hom point))
    (secondAtRoot : ∀ point : (finiteDeckOrbitAction
        diagram root second middleOrbit).obj.obj.V.obj,
      ((secondCoverMap.hom.app root).hom.hom)
          (rootAssociatedCarrierEquiv diagram root
            (literalOrbitLevelFactorization diagram root second middleOrbit).level
            (finiteDeckOrbitAction diagram root second middleOrbit).obj point) =
        rootAssociatedCarrierEquiv diagram root
          (literalOrbitLevelFactorization diagram root third
            sequentialTargetOrbit).level
          (finiteDeckOrbitAction diagram root third
            sequentialTargetOrbit).obj
          (secondLevelMap.hom.hom point))
    (levelMapLaw : CategoryTheory.CategoryStruct.comp directLevelMap
        (CategoryTheory.eqToHom (congrArg
          (literalOrbitLevelAction diagram root third) equality)) =
      CategoryTheory.CategoryStruct.comp firstLevelMap secondLevelMap) :
    CategoryTheory.CategoryStruct.comp directCoverMap.hom
        (CategoryTheory.eqToHom (congrArg
          (fun orbit ↦ (finiteDeckOrbitCover diagram root third orbit).obj)
          equality)) =
      CategoryTheory.CategoryStruct.comp firstCoverMap.hom secondCoverMap.hom := by
  subst directTargetOrbit
  rw [CategoryTheory.eqToHom_refl] at levelMapLaw ⊢
  change CategoryTheory.CategoryStruct.comp directLevelMap
    (CategoryTheory.CategoryStruct.id _) = _ at levelMapLaw
  rw [CategoryTheory.Category.comp_id] at levelMapLaw
  change CategoryTheory.CategoryStruct.comp directCoverMap.hom
    (CategoryTheory.CategoryStruct.id _) = _
  rw [CategoryTheory.Category.comp_id]
  apply finiteDeckOrbitCover_hom_ext diagram root first sourceOrbit
  intro point
  change ((directCoverMap.hom.app root).hom.hom)
      (rootAssociatedCarrierEquiv diagram root
        (literalOrbitLevelFactorization diagram root first sourceOrbit).level
        (finiteDeckOrbitAction diagram root first sourceOrbit).obj point) =
    ((secondCoverMap.hom.app root).hom.hom)
      (((firstCoverMap.hom.app root).hom.hom)
        (rootAssociatedCarrierEquiv diagram root
          (literalOrbitLevelFactorization diagram root first sourceOrbit).level
          (finiteDeckOrbitAction diagram root first sourceOrbit).obj point))
  rw [directAtRoot, firstAtRoot, secondAtRoot]
  have atPoint := congrArg (fun map ↦ map.hom.hom point) levelMapLaw
  exact congrArg
    (rootAssociatedCarrierEquiv diagram root
      (literalOrbitLevelFactorization diagram root third
        sequentialTargetOrbit).level
      (finiteDeckOrbitAction diagram root third sequentialTargetOrbit).obj) atPoint

/-- The component-cover map of a composite, transported to the iterated
target orbit. -/
noncomputable def finiteDeckOrbitCoverMapCompNormalizedHom
    {first second third : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (firstMap : first ⟶ second) (secondMap : second ⟶ third)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root first)) :
    (finiteDeckOrbitCover diagram root first orbit).obj ⟶
      (finiteDeckOrbitCover diagram root third
        (literalTargetOrbit diagram root secondMap
          (literalTargetOrbit diagram root firstMap orbit))).obj :=
  CategoryTheory.CategoryStruct.comp
    (finiteDeckOrbitCoverMap diagram root
      (CategoryTheory.CategoryStruct.comp firstMap secondMap) orbit).hom
    (CategoryTheory.eqToHom (congrArg
      (fun targetOrbit ↦
        (finiteDeckOrbitCover diagram root third targetOrbit).obj)
      (literalTargetOrbit_comp diagram root firstMap secondMap orbit)))

/-- Component-cover maps respect composition after canonical target-orbit
transport. -/
theorem finiteDeckOrbitCoverMapCompNormalizedHom_eq_comp
    {first second third : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (firstMap : first ⟶ second) (secondMap : second ⟶ third)
    (orbit : SourceTemperoidOrbit
      (literalTemperedPresentation diagram root).Limit
      (literalLimitAction diagram root first)) :
    finiteDeckOrbitCoverMapCompNormalizedHom
        diagram root firstMap secondMap orbit =
      CategoryTheory.CategoryStruct.comp
        (finiteDeckOrbitCoverMap diagram root firstMap orbit).hom
        (finiteDeckOrbitCoverMap diagram root secondMap
          (literalTargetOrbit diagram root firstMap orbit)).hom := by
  exact finiteDeckOrbitCoverHom_normalized_eq_comp diagram root
    first second third orbit
    (literalTargetOrbit diagram root firstMap orbit)
    (literalTargetOrbit diagram root
      (CategoryTheory.CategoryStruct.comp firstMap secondMap) orbit)
    (literalTargetOrbit diagram root secondMap
      (literalTargetOrbit diagram root firstMap orbit))
    (finiteDeckOrbitCoverMap diagram root
      (CategoryTheory.CategoryStruct.comp firstMap secondMap) orbit)
    (finiteDeckOrbitCoverMap diagram root firstMap orbit)
    (finiteDeckOrbitCoverMap diagram root secondMap
      (literalTargetOrbit diagram root firstMap orbit))
    (chosenLevelOrbitMap diagram root
      (CategoryTheory.CategoryStruct.comp firstMap secondMap) orbit)
    (chosenLevelOrbitMap diagram root firstMap orbit)
    (chosenLevelOrbitMap diagram root secondMap
      (literalTargetOrbit diagram root firstMap orbit))
    (literalTargetOrbit_comp diagram root firstMap secondMap orbit)
    (finiteDeckOrbitCoverMap_root diagram root
      (CategoryTheory.CategoryStruct.comp firstMap secondMap) orbit)
    (finiteDeckOrbitCoverMap_root diagram root firstMap orbit)
    (finiteDeckOrbitCoverMap_root diagram root secondMap
      (literalTargetOrbit diagram root firstMap orbit))
    (chosenLevelOrbitMapCompNormalized_eq_comp
      diagram root firstMap secondMap orbit)

/-- Assemble the component maps into the geometric morphism attached to a
morphism of tempered deck-group actions. -/
noncomputable def actionCoverMap
    {source target : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (arrow : source ⟶ target) :
    actionCoverObject diagram root source ⟶
      actionCoverObject diagram root target := by
  apply CategoryTheory.ObjectProperty.homMk
  exact SourceSemiGraphOfAnabelioids.CovObject.Coproduct.map
    (literalTargetOrbit diagram root arrow)
    (fun orbit ↦ (finiteDeckOrbitCoverMap
      diagram root arrow orbit).hom)

omit [Finite diagram.base.Vertex] [Finite diagram.base.Edge] in
/-- A pointwise coproduct map fixes a summand after the target index and
component map are transported back to their source data. -/
theorem coproductPoint_eq_of_normalized
    {Index : Type u} [Countable Index]
    (family : Index → diagram.CovObject)
    (sourceIndex targetIndex : Index)
    (indexEquality : targetIndex = sourceIndex)
    (componentMap : family sourceIndex ⟶ family targetIndex)
    (componentLaw : CategoryTheory.CategoryStruct.comp componentMap
        (CategoryTheory.eqToHom (congrArg family indexEquality)) =
      CategoryTheory.CategoryStruct.id _)
    (vertex : diagram.base.Vertex)
    (point : ((family sourceIndex).vertexObject vertex).obj.V.obj) :
    (⟨targetIndex, (componentMap.app vertex).hom.hom point⟩ :
        SourceSemiGraphOfAnabelioids.CovObject.Coproduct.VertexCarrier
          family vertex) =
      ⟨sourceIndex, point⟩ := by
  subst targetIndex
  rw [CategoryTheory.eqToHom_refl,
    CategoryTheory.Category.comp_id] at componentLaw
  apply Sigma.ext
  · rfl
  · exact heq_of_eq <| congrArg
      (fun map ↦ (map.app vertex).hom.hom point) componentLaw

/-- The assembled geometric action-to-cover map respects identities. -/
theorem actionCoverMap_id_hom
    (object : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)) :
    (actionCoverMap diagram root
      (CategoryTheory.CategoryStruct.id object)).hom =
      CategoryTheory.CategoryStruct.id
        (actionCoverObject diagram root object).obj := by
  apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
  intro vertex
  apply CategoryTheory.ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply CategoryTheory.ConcreteCategory.hom_ext
  rintro ⟨orbit, point⟩
  exact coproductPoint_eq_of_normalized diagram
    (fun orbit ↦ (finiteDeckOrbitCover diagram root object orbit).obj)
    orbit
    (literalTargetOrbit diagram root
      (CategoryTheory.CategoryStruct.id object) orbit)
    (literalTargetOrbit_id diagram root object orbit)
    (finiteDeckOrbitCoverMap diagram root
      (CategoryTheory.CategoryStruct.id object) orbit).hom
    (finiteDeckOrbitCoverMapIdNormalizedHom_eq_id
      diagram root object orbit)
    vertex point

omit [Finite diagram.base.Vertex] [Finite diagram.base.Edge] in
/-- Pointwise composition of coproduct maps agrees after the direct target
index and component map are transported to the iterated target. -/
theorem coproductPoint_comp_eq_of_normalized
    {SourceIndex MiddleIndex TargetIndex : Type u}
    [Countable SourceIndex] [Countable MiddleIndex] [Countable TargetIndex]
    (sourceFamily : SourceIndex → diagram.CovObject)
    (middleFamily : MiddleIndex → diagram.CovObject)
    (targetFamily : TargetIndex → diagram.CovObject)
    (sourceIndex : SourceIndex) (middleIndex : MiddleIndex)
    (directTargetIndex sequentialTargetIndex : TargetIndex)
    (indexEquality : directTargetIndex = sequentialTargetIndex)
    (directMap : sourceFamily sourceIndex ⟶ targetFamily directTargetIndex)
    (firstMap : sourceFamily sourceIndex ⟶ middleFamily middleIndex)
    (secondMap : middleFamily middleIndex ⟶
      targetFamily sequentialTargetIndex)
    (componentLaw : CategoryTheory.CategoryStruct.comp directMap
        (CategoryTheory.eqToHom (congrArg targetFamily indexEquality)) =
      CategoryTheory.CategoryStruct.comp firstMap secondMap)
    (vertex : diagram.base.Vertex)
    (point : ((sourceFamily sourceIndex).vertexObject vertex).obj.V.obj) :
    (⟨directTargetIndex, (directMap.app vertex).hom.hom point⟩ :
        SourceSemiGraphOfAnabelioids.CovObject.Coproduct.VertexCarrier
          targetFamily vertex) =
      ⟨sequentialTargetIndex,
        (secondMap.app vertex).hom.hom
          ((firstMap.app vertex).hom.hom point)⟩ := by
  subst directTargetIndex
  rw [CategoryTheory.eqToHom_refl] at componentLaw
  change CategoryTheory.CategoryStruct.comp directMap
    (CategoryTheory.CategoryStruct.id _) = _ at componentLaw
  rw [CategoryTheory.Category.comp_id] at componentLaw
  apply Sigma.ext
  · rfl
  · exact heq_of_eq <| congrArg
      (fun map ↦ (map.app vertex).hom.hom point) componentLaw

/-- The assembled geometric action-to-cover map respects composition. -/
theorem actionCoverMap_comp_hom
    {first second third : SourceTemperoidAction.{u, u + 1}
      (TemperedDeckGroup diagram root)}
    (firstMap : first ⟶ second) (secondMap : second ⟶ third) :
    (actionCoverMap diagram root
      (CategoryTheory.CategoryStruct.comp firstMap secondMap)).hom =
      CategoryTheory.CategoryStruct.comp
        (actionCoverMap diagram root firstMap).hom
        (actionCoverMap diagram root secondMap).hom := by
  apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
  intro vertex
  apply CategoryTheory.ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply CategoryTheory.ConcreteCategory.hom_ext
  rintro ⟨orbit, point⟩
  exact coproductPoint_comp_eq_of_normalized diagram
    (fun orbit ↦ (finiteDeckOrbitCover diagram root first orbit).obj)
    (fun orbit ↦ (finiteDeckOrbitCover diagram root second orbit).obj)
    (fun orbit ↦ (finiteDeckOrbitCover diagram root third orbit).obj)
    orbit
    (literalTargetOrbit diagram root firstMap orbit)
    (literalTargetOrbit diagram root
      (CategoryTheory.CategoryStruct.comp firstMap secondMap) orbit)
    (literalTargetOrbit diagram root secondMap
      (literalTargetOrbit diagram root firstMap orbit))
    (literalTargetOrbit_comp diagram root firstMap secondMap orbit)
    (finiteDeckOrbitCoverMap diagram root
      (CategoryTheory.CategoryStruct.comp firstMap secondMap) orbit).hom
    (finiteDeckOrbitCoverMap diagram root firstMap orbit).hom
    (finiteDeckOrbitCoverMap diagram root secondMap
      (literalTargetOrbit diagram root firstMap orbit)).hom
    (finiteDeckOrbitCoverMapCompNormalizedHom_eq_comp
      diagram root firstMap secondMap orbit)
    vertex point

/-- Functor from countable continuous tempered deck-group actions to
componentwise geometric tempered covers. -/
noncomputable def actionCoverFunctor :
    CategoryTheory.Functor
      (SourceTemperoidAction.{u, u + 1} (TemperedDeckGroup diagram root))
      (SourceSemiGraphOfAnabelioids.CovObject.TemperedCover diagram root) where
  obj := actionCoverObject diagram root
  map := actionCoverMap diagram root
  map_id object := by
    apply CategoryTheory.ObjectProperty.hom_ext
    exact actionCoverMap_id_hom diagram root object
  map_comp firstMap secondMap := by
    apply CategoryTheory.ObjectProperty.hom_ext
    exact actionCoverMap_comp_hom diagram root firstMap secondMap

end SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

end Iut
