/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedGeometricComponents

/-!
# Countable coproducts of geometric tempered covers

Corrected temperedness is componentwise, so arbitrary objects must be
assembled from connected covers that may be presented at different finite
levels.  This file constructs the required countable coproduct directly in
the literal geometric covering category and proves that the intrinsic
components of a cover reconstruct the original object.
-/

namespace Iut

universe u

open CategoryTheory
open scoped SourceCountableTypeCatDiscrete

namespace SourceSemiGraphOfAnabelioids.CovObject.Coproduct

variable {diagram : SourceSemiGraphOfAnabelioids.{u}}
variable {Index : Type u} [Countable Index]

/-- The vertex carrier of a countable family of geometric covers. -/
abbrev VertexCarrier (family : Index → diagram.CovObject)
    (vertex : diagram.base.Vertex) :=
  Σ index : Index, ((family index).vertexObject vertex).obj.V.obj

namespace VertexCarrier

variable (family : Index → diagram.CovObject)
    (vertex : diagram.base.Vertex)

noncomputable instance : Countable (VertexCarrier family vertex) :=
  inferInstance

noncomputable instance : SMul (diagram.vertexAnabelioid vertex).group
    (VertexCarrier family vertex) where
  smul element point := ⟨point.1, element • point.2⟩

noncomputable instance : MulAction (diagram.vertexAnabelioid vertex).group
    (VertexCarrier family vertex) where
  one_smul point := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (one_smul _ point.2)
  mul_smul first second point := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (mul_smul first second point.2)

omit [Countable Index] in
@[simp] theorem smul_fst (element : (diagram.vertexAnabelioid vertex).group)
    (point : VertexCarrier family vertex) :
    (element • point).1 = point.1 :=
  rfl

omit [Countable Index] in
@[simp] theorem smul_snd (element : (diagram.vertexAnabelioid vertex).group)
    (point : VertexCarrier family vertex) :
    (element • point).2 = element • point.2 :=
  rfl

end VertexCarrier

/-- The continuous vertex action on a countable family of covers. -/
noncomputable def vertexAction (family : Index → diagram.CovObject)
    (vertex : diagram.base.Vertex) :
    SourceTemperoidAction (diagram.vertexAnabelioid vertex).group := by
  let Carrier := VertexCarrier family vertex
  let action : Action SourceCountableTypeCat.{u}
      (diagram.vertexAnabelioid vertex).group :=
    SourceCountableTypeCat.ofMulAction
      (diagram.vertexAnabelioid vertex).group
      (SourceCountableTypeCat.of Carrier)
  refine ⟨action, ?_⟩
  change ContinuousSMul (diagram.vertexAnabelioid vertex).group
    ((forget₂ (Action SourceCountableTypeCat.{u}
      (diagram.vertexAnabelioid vertex).group) TopCat).obj action)
  letI : DiscreteTopology
      ((forget₂ (Action SourceCountableTypeCat.{u}
        (diagram.vertexAnabelioid vertex).group) TopCat).obj action) := ⟨rfl⟩
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro point
  have openPoint : IsOpen
      (MulAction.stabilizer (diagram.vertexAnabelioid vertex).group
        point.2 : Set (diagram.vertexAnabelioid vertex).group) :=
    stabilizer_isOpen (diagram.vertexAnabelioid vertex).group point.2
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer
      (diagram.vertexAnabelioid vertex).group point.2)
    (H₂ := MulAction.stabilizer
      (diagram.vertexAnabelioid vertex).group point) _ openPoint
  intro element fixes
  rw [MulAction.mem_stabilizer_iff] at fixes ⊢
  apply Sigma.ext
  · rfl
  · exact heq_of_eq fixes

/-- Branch gluing acts inside each member of a countable family. -/
noncomputable def branchIso (family : Index → diagram.CovObject)
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    first.temperoidPullback.obj (vertexAction family first.vertex) ≅
      second.temperoidPullback.obj (vertexAction family second.vertex) := by
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ (comm := ?_)
  · exact
      { hom := SourceCountableTypeCat.homMk (fun point ↦
          ⟨point.1,
            ((family point.1).glue first second).hom.hom.hom point.2⟩)
        inv := SourceCountableTypeCat.homMk (fun point ↦
          ⟨point.1,
            ((family point.1).glue first second).inv.hom.hom point.2⟩)
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          intro point
          apply Sigma.ext
          · rfl
          · exact heq_of_eq <| by
              have cancellation := congrArg
                (fun morphism :
                    first.temperoidPullback.obj
                        ((family point.1).vertexObject first.vertex) ⟶
                      first.temperoidPullback.obj
                        ((family point.1).vertexObject first.vertex) ↦
                  ConcreteCategory.hom morphism.hom.hom point.2)
                ((family point.1).glue first second).hom_inv_id
              exact cancellation
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro point
          apply Sigma.ext
          · rfl
          · exact heq_of_eq <| by
              have cancellation := congrArg
                (fun morphism :
                    second.temperoidPullback.obj
                        ((family point.1).vertexObject second.vertex) ⟶
                      second.temperoidPullback.obj
                        ((family point.1).vertexObject second.vertex) ↦
                  ConcreteCategory.hom morphism.hom.hom point.2)
                ((family point.1).glue first second).inv_hom_id
              exact cancellation }
  · intro element
    apply ConcreteCategory.hom_ext
    intro point
    apply Sigma.ext
    · rfl
    · exact heq_of_eq <| ConcreteCategory.congr_hom
        (((family point.1).glue first second).hom.hom.comm element) point.2

/-- The literal countable coproduct of a family of geometric covers. -/
noncomputable def covObject (family : Index → diagram.CovObject) :
    diagram.CovObject where
  vertexObject := vertexAction family
  glue := branchIso family
  glue_refl := by
    intro edge branch
    apply Iso.ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    apply Sigma.ext
    · rfl
    · change HEq
        (ConcreteCategory.hom
          ((family point.1).glue branch branch).hom.hom.hom point.2)
        point.2
      exact heq_of_eq <| ConcreteCategory.congr_hom
        (congrArg Iso.hom ((family point.1).glue_refl branch)) point.2
  glue_trans := by
    intro edge first second third
    apply Iso.ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    apply Sigma.ext
    · rfl
    · change HEq
        (ConcreteCategory.hom
          ((family point.1).glue second third).hom.hom.hom
            (ConcreteCategory.hom
              ((family point.1).glue first second).hom.hom.hom point.2))
        (ConcreteCategory.hom
          ((family point.1).glue first third).hom.hom.hom point.2)
      exact heq_of_eq <| ConcreteCategory.congr_hom
        (congrArg Iso.hom
          ((family point.1).glue_trans first second third)) point.2

/-! ## Maps into a connected summand -/

open SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

/-- Include one member into the literal countable coproduct. -/
noncomputable def inclusion (family : Index → diagram.CovObject)
    (index : Index) : family index ⟶ covObject family where
  app vertex := ObjectProperty.homMk
    { hom := SourceCountableTypeCat.homMk (fun point ↦ ⟨index, point⟩)
      comm := fun _ ↦ by
        apply ConcreteCategory.hom_ext
        intro point
        rfl }
  naturality := by
    intro edge first second
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    rfl

@[simp]
theorem inclusion_apply (family : Index → diagram.CovObject)
    (index : Index) (vertex : diagram.base.Vertex)
    (point : ((family index).vertexObject vertex).obj.V.obj) :
    ((inclusion family index).app vertex).hom.hom point = ⟨index, point⟩ :=
  rfl

/-- The coproduct member containing the image of a chosen source point. -/
noncomputable def connectedMapTargetIndex
    (source : diagram.CovObject) (family : Index → diagram.CovObject)
    (map : source ⟶ covObject family) (basePoint : GeometricPoint source) :
    Index :=
  ((map.app basePoint.1).hom.hom basePoint.2).1

private theorem reachable_index
    (family : Index → diagram.CovObject)
    {first second : GeometricPoint (covObject family)}
    (path : GeometricallyReachable (covObject family) first second) :
    first.2.1 = second.2.1 := by
  induction path with
  | refl => rfl
  | tail path step inductionHypothesis =>
      exact inductionHypothesis.trans (by cases step <;> rfl)

/-- A map from a point-connected cover lands in one coproduct member. -/
theorem connectedMap_index_eq
    (source : diagram.CovObject) (family : Index → diagram.CovObject)
    (map : source ⟶ covObject family) (basePoint : GeometricPoint source)
    (connected : IsPointConnected source basePoint)
    (vertex : diagram.base.Vertex)
    (point : (source.vertexObject vertex).obj.V.obj) :
    ((map.app vertex).hom.hom point).1 =
      connectedMapTargetIndex source family map basePoint := by
  have mappedPath := reachable_map map (connected ⟨vertex, point⟩)
  have indexPreserved :
      ((map.app basePoint.1).hom.hom basePoint.2).1 =
        ((map.app vertex).hom.hom point).1 :=
    reachable_index family mappedPath
  exact indexPreserved.symm

/-- Cast the second coordinate of a dependent pair to a specified index. -/
private noncomputable def castSnd
    {Family : Index → Type u} (target : Index) (point : Σ index, Family index)
    (indexEquality : point.1 = target) : Family target :=
  cast (congrArg Family indexEquality) point.2

omit [Countable Index] in
private theorem castSnd_eq_of_sigma_eq
    {Family : Index → Type u} (target : Index)
    (first second : Σ index, Family index)
    (firstIndex : first.1 = target) (secondIndex : second.1 = target)
    (equality : first = second) :
    castSnd target first firstIndex = castSnd target second secondIndex := by
  subst second
  have proofEquality : firstIndex = secondIndex := Subsingleton.elim _ _
  subst secondIndex
  rfl

omit [Countable Index] in
private theorem castSnd_smul
    (family : Index → diagram.CovObject)
    (target : Index) (vertex : diagram.base.Vertex)
    (element : (diagram.vertexAnabelioid vertex).group)
    (point : VertexCarrier family vertex)
    (indexEquality : point.1 = target) :
    castSnd target (element • point) indexEquality =
      element • castSnd target point indexEquality := by
  rcases point with ⟨index, point⟩
  subst target
  rfl

private theorem castSnd_glue
    (family : Index → diagram.CovObject)
    (target : Index) {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge)
    (point : VertexCarrier family first.vertex)
    (indexEquality : point.1 = target) :
    castSnd target
        ((branchIso family first second).hom.hom.hom point) indexEquality =
      ((family target).glue first second).hom.hom.hom
        (castSnd target point indexEquality) := by
  rcases point with ⟨index, point⟩
  subst target
  rfl

/-- Restrict a map from a point-connected cover to the unique coproduct
member containing its image. -/
noncomputable def connectedMapToMember
    (source : diagram.CovObject) (family : Index → diagram.CovObject)
    (map : source ⟶ covObject family) (basePoint : GeometricPoint source)
    (connected : IsPointConnected source basePoint) :
    source ⟶ family (connectedMapTargetIndex source family map basePoint) where
  app vertex := ObjectProperty.homMk
    { hom := SourceCountableTypeCat.homMk (fun point ↦
        castSnd (connectedMapTargetIndex source family map basePoint)
          ((map.app vertex).hom.hom point)
          (connectedMap_index_eq source family map basePoint connected
            vertex point))
      comm := fun element ↦ by
        apply ConcreteCategory.hom_ext
        intro point
        let target := connectedMapTargetIndex source family map basePoint
        let first := (map.app vertex).hom.hom (element • point)
        let second := element • (map.app vertex).hom.hom point
        have equality : first = second :=
          ConcreteCategory.congr_hom ((map.app vertex).hom.comm element) point
        calc
          castSnd target first
              (connectedMap_index_eq source family map basePoint connected
                vertex (element • point)) =
            castSnd target second
              (connectedMap_index_eq source family map basePoint connected
                vertex point) :=
              castSnd_eq_of_sigma_eq target first second _ _ equality
          _ = element • castSnd target ((map.app vertex).hom.hom point)
              (connectedMap_index_eq source family map basePoint connected
                vertex point) :=
            castSnd_smul family target vertex element _ _ }
  naturality := by
    intro edge first second
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    let target := connectedMapTargetIndex source family map basePoint
    let firstPoint :=
      (map.app second.vertex).hom.hom
        ((source.glue first second).hom.hom.hom point)
    let secondPoint :=
      (branchIso family first second).hom.hom.hom
        ((map.app first.vertex).hom.hom point)
    have equality : firstPoint = secondPoint :=
      ConcreteCategory.congr_hom (map.naturality first second) point
    calc
      castSnd target firstPoint
          (connectedMap_index_eq source family map basePoint connected
            second.vertex ((source.glue first second).hom.hom.hom point)) =
        castSnd target secondPoint
          (connectedMap_index_eq source family map basePoint connected
            first.vertex point) :=
          castSnd_eq_of_sigma_eq target firstPoint secondPoint _ _ equality
      _ = ((family target).glue first second).hom.hom.hom
          (castSnd target ((map.app first.vertex).hom.hom point)
            (connectedMap_index_eq source family map basePoint connected
              first.vertex point)) :=
        castSnd_glue family target first second _ _

/-- Restriction to the selected member recovers the original coproduct map. -/
theorem connectedMapToMember_comp_inclusion
    (source : diagram.CovObject) (family : Index → diagram.CovObject)
    (map : source ⟶ covObject family) (basePoint : GeometricPoint source)
    (connected : IsPointConnected source basePoint) :
    CategoryTheory.CategoryStruct.comp
        (connectedMapToMember source family map basePoint connected)
        (inclusion family
          (connectedMapTargetIndex source family map basePoint)) = map := by
  apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
  intro vertex
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext
  intro point
  let output := (map.app vertex).hom.hom point
  let indexEquality :=
    connectedMap_index_eq source family map basePoint connected vertex point
  change (⟨connectedMapTargetIndex source family map basePoint,
      castSnd (connectedMapTargetIndex source family map basePoint)
        output indexEquality⟩ : VertexCarrier family vertex) = output
  apply Sigma.ext indexEquality.symm
  exact cast_heq
    (congrArg
      (fun index ↦ ((family index).vertexObject vertex).obj.V.obj)
      indexEquality) output.2

/-- A componentwise family of maps induces a map of countable coproducts.
The target family index may depend on the source index. -/
noncomputable def map
    {SourceIndex TargetIndex : Type u}
    [Countable SourceIndex] [Countable TargetIndex]
    {source : SourceIndex → diagram.CovObject}
    {target : TargetIndex → diagram.CovObject}
    (indexMap : SourceIndex → TargetIndex)
    (componentMap : ∀ index, source index ⟶ target (indexMap index)) :
    covObject source ⟶ covObject target where
  app vertex := ObjectProperty.homMk
    { hom := SourceCountableTypeCat.homMk (fun point ↦
        ⟨indexMap point.1,
          ConcreteCategory.hom
            ((componentMap point.1).app vertex).hom.hom point.2⟩)
      comm := fun element ↦ by
        apply ConcreteCategory.hom_ext
        intro point
        apply Sigma.ext
        · rfl
        · exact heq_of_eq <| ConcreteCategory.congr_hom
            ((componentMap point.1).app vertex |>.hom.comm element) point.2 }
  naturality := by
    intro edge first second
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    apply Sigma.ext
    · rfl
    · change HEq
        (ConcreteCategory.hom
          (second.temperoidPullback.map
            ((componentMap point.1).app second.vertex)).hom.hom
          (ConcreteCategory.hom
            ((source point.1).glue first second).hom.hom.hom point.2))
        (ConcreteCategory.hom
          ((target (indexMap point.1)).glue first second).hom.hom.hom
          (ConcreteCategory.hom
            (first.temperoidPullback.map
              ((componentMap point.1).app first.vertex)).hom.hom point.2))
      exact heq_of_eq <| ConcreteCategory.congr_hom
        ((componentMap point.1).naturality first second) point.2

/-- Componentwise constituent isomorphisms induce an isomorphism of the
coproduct vertex actions. -/
noncomputable def vertexIso
    {first second : Index → diagram.CovObject}
    (identification : ∀ index, first index ≅ second index)
    (vertex : diagram.base.Vertex) :
    vertexAction first vertex ≅ vertexAction second vertex := by
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ (comm := ?_)
  · exact
      { hom := SourceCountableTypeCat.homMk (fun point ↦
          ⟨point.1, ConcreteCategory.hom
            ((identification point.1).hom.app vertex).hom.hom point.2⟩)
        inv := SourceCountableTypeCat.homMk (fun point ↦
          ⟨point.1, ConcreteCategory.hom
            ((identification point.1).inv.app vertex).hom.hom point.2⟩)
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          intro point
          apply Sigma.ext
          · rfl
          · exact heq_of_eq <| by
              have cancellation := congrArg
                (fun morphism : first point.1 ⟶ first point.1 ↦
                  ConcreteCategory.hom (morphism.app vertex).hom.hom point.2)
                (identification point.1).hom_inv_id
              exact cancellation
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro point
          apply Sigma.ext
          · rfl
          · exact heq_of_eq <| by
              have cancellation := congrArg
                (fun morphism : second point.1 ⟶ second point.1 ↦
                  ConcreteCategory.hom (morphism.app vertex).hom.hom point.2)
                (identification point.1).inv_hom_id
              exact cancellation }
  · intro element
    apply ConcreteCategory.hom_ext
    intro point
    apply Sigma.ext
    · rfl
    · exact heq_of_eq <| ConcreteCategory.congr_hom
        (((identification point.1).hom.app vertex).hom.comm element) point.2

/-- Componentwise isomorphisms induce an isomorphism of countable
coproducts. -/
noncomputable def iso
    {first second : Index → diagram.CovObject}
    (identification : ∀ index, first index ≅ second index) :
    covObject first ≅ covObject second where
  hom :=
    { app := fun vertex ↦ (vertexIso identification vertex).hom
      naturality := by
        intro edge left right
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        apply ConcreteCategory.hom_ext
        intro point
        apply Sigma.ext
        · rfl
        · change HEq
            (ConcreteCategory.hom
              (right.temperoidPullback.map
                ((identification point.1).hom.app right.vertex)).hom.hom
              (ConcreteCategory.hom
                ((first point.1).glue left right).hom.hom.hom point.2))
            (ConcreteCategory.hom
              ((second point.1).glue left right).hom.hom.hom
              (ConcreteCategory.hom
                (left.temperoidPullback.map
                  ((identification point.1).hom.app left.vertex)).hom.hom
                point.2))
          exact heq_of_eq <| ConcreteCategory.congr_hom
            ((identification point.1).hom.naturality left right) point.2 }
  inv :=
    { app := fun vertex ↦ (vertexIso identification vertex).inv
      naturality := by
        intro edge left right
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        apply ConcreteCategory.hom_ext
        intro point
        apply Sigma.ext
        · rfl
        · change HEq
            (ConcreteCategory.hom
              (right.temperoidPullback.map
                ((identification point.1).inv.app right.vertex)).hom.hom
              (ConcreteCategory.hom
                ((second point.1).glue left right).hom.hom.hom point.2))
            (ConcreteCategory.hom
              ((first point.1).glue left right).hom.hom.hom
              (ConcreteCategory.hom
                (left.temperoidPullback.map
                  ((identification point.1).inv.app left.vertex)).hom.hom
                point.2))
          exact heq_of_eq <| ConcreteCategory.congr_hom
            ((identification point.1).inv.naturality left right) point.2 }
  hom_inv_id := by
    apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
    intro vertex
    exact (vertexIso identification vertex).hom_inv_id
  inv_hom_id := by
    apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
    intro vertex
    exact (vertexIso identification vertex).inv_hom_id

open SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

/-- The family index of a geometric point in a countable coproduct. -/
def geometricPointIndex (family : Index → diagram.CovObject)
    (point : GeometricPoint (covObject family)) : Index :=
  point.2.1

/-- Local action and branch gluing never change the coproduct-family index. -/
theorem geometricPointStep_index
    (family : Index → diagram.CovObject)
    {first second : GeometricPoint (covObject family)}
    (step : GeometricPointStep (covObject family) first second) :
    geometricPointIndex family first = geometricPointIndex family second := by
  cases step <;> rfl

/-- A finite geometric path in a coproduct stays in one family member. -/
theorem geometricallyReachable_index
    (family : Index → diagram.CovObject)
    {first second : GeometricPoint (covObject family)}
    (path : GeometricallyReachable (covObject family) first second) :
    geometricPointIndex family first = geometricPointIndex family second := by
  induction path with
  | refl => rfl
  | tail path step inductionHypothesis =>
      exact inductionHypothesis.trans (geometricPointStep_index family step)

/-- A countable coproduct of connected tempered covers is tempered.  The
splitter selected for a component depends only on its unchanged family index,
so no common finite level is required. -/
theorem covObject_isTempered
    (root : diagram.base.Vertex)
    (family : Index → diagram.CovObject)
    (tempered : ∀ index,
      SourceSemiGraphOfAnabelioids.CovObject.IsTempered
        diagram root (family index))
    (connected : ∀ index, IsGeometricallyConnected (family index)) :
    SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root (covObject family) := by
  rintro ⟨baseVertex, ⟨index, basePoint⟩⟩
  let memberBasePoint : GeometricPoint (family index) :=
    ⟨baseVertex, basePoint⟩
  have memberConnected : IsPointConnected (family index) memberBasePoint :=
    (Classical.choose_spec (connected index)).rebase memberBasePoint
  obtain ⟨splitter, split⟩ :=
    SourceSemiGraphOfAnabelioids.CovObject.IsTempered.exists_isSplitBy_of_isPointConnected
      diagram root (tempered index) memberBasePoint memberConnected
  refine ⟨splitter, ?_⟩
  constructor
  · intro vertex element fixes
    rintro ⟨targetIndex, targetPoint⟩ reachable
    have indexEquality : index = targetIndex :=
      geometricallyReachable_index family reachable
    subst targetIndex
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (split.1 vertex element fixes targetPoint)
  · intro edge
    dsimp only
    intro element fixes
    rintro ⟨targetIndex, targetPoint⟩ reachable
    have indexEquality : index = targetIndex :=
      geometricallyReachable_index family reachable
    subst targetIndex
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (split.2 edge element fixes targetPoint)

end SourceSemiGraphOfAnabelioids.CovObject.Coproduct

namespace SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

variable {diagram : SourceSemiGraphOfAnabelioids.{u}}

open SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

/-- At one vertex, the disjoint union of all intrinsic component fibers is
equivariantly identical to the original constituent carrier. -/
noncomputable def componentDecompositionVertexIso
    [Countable diagram.base.Vertex]
    (source : diagram.CovObject) (vertex : diagram.base.Vertex) :
    SourceSemiGraphOfAnabelioids.CovObject.Coproduct.vertexAction
        (fun component : GeometricComponent source ↦
          componentCovObject source component) vertex ≅
      source.vertexObject vertex := by
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ (comm := ?_)
  · exact
      { hom := SourceCountableTypeCat.homMk (fun point ↦ point.2.1)
        inv := SourceCountableTypeCat.homMk (fun point ↦
          ⟨geometricComponentOf source ⟨vertex, point⟩,
            ⟨point, rfl⟩⟩)
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          rintro ⟨component, ⟨point, belongs⟩⟩
          change (⟨geometricComponentOf source ⟨vertex, point⟩,
              ⟨point, rfl⟩⟩ :
                Σ component : GeometricComponent source,
                  ComponentVertexCarrier source component vertex) =
            ⟨component, ⟨point, belongs⟩⟩
          apply Sigma.ext belongs
          cases belongs
          rfl
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro point
          rfl }
  · intro element
    apply ConcreteCategory.hom_ext
    intro point
    rfl

/-- The countable coproduct of all intrinsic component subcovers reconstructs
the original geometric cover. -/
noncomputable def componentDecompositionIso
    [Countable diagram.base.Vertex]
    (source : diagram.CovObject) :
    SourceSemiGraphOfAnabelioids.CovObject.Coproduct.covObject
        (fun component : GeometricComponent source ↦
          componentCovObject source component) ≅ source where
  hom :=
    { app := fun vertex ↦ (componentDecompositionVertexIso source vertex).hom
      naturality := by
        intro edge first second
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        apply ConcreteCategory.hom_ext
        intro point
        rfl }
  inv :=
    { app := fun vertex ↦ (componentDecompositionVertexIso source vertex).inv
      naturality := by
        intro edge first second
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        apply ConcreteCategory.hom_ext
        intro point
        let mapped := ConcreteCategory.hom
          (source.glue first second).hom.hom.hom point
        have componentEquality :
            geometricComponentOf source
                ⟨second.vertex, mapped⟩ =
              geometricComponentOf source ⟨first.vertex, point⟩ :=
          (Quotient.sound
            (Relation.ReflTransGen.single
              (GeometricPointStep.glue first second point))).symm
        apply Sigma.ext componentEquality
        change HEq
          (⟨mapped, rfl⟩ : ComponentVertexCarrier source
            (geometricComponentOf source ⟨second.vertex, mapped⟩)
              second.vertex)
          (⟨mapped, _⟩ : ComponentVertexCarrier source
            (geometricComponentOf source ⟨first.vertex, point⟩)
              second.vertex)
        rw [Subtype.heq_iff_coe_heq rfl (by
          apply heq_of_eq
          funext value
          apply propext
          rw [componentEquality])] }
  hom_inv_id := by
    apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
    intro vertex
    exact (componentDecompositionVertexIso source vertex).hom_inv_id
  inv_hom_id := by
    apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
    intro vertex
    exact (componentDecompositionVertexIso source vertex).inv_hom_id

/-- The associated finite-level quotient selected for one intrinsic
component of a corrected tempered cover. -/
noncomputable def classifiedComponentCover
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source)
    (component : GeometricComponent source) : diagram.CovObject :=
  let classification :=
    componentwiseTemperedClassification diagram root source tempered component
  ((associatedTemperedFunctor diagram root classification.1).obj
    classification.2.1.obj).obj

/-- The componentwise connected classification compares its selected
finite-level quotient with the literal intrinsic component. -/
noncomputable def classifiedComponentComparison
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source)
    (component : GeometricComponent source) :
    classifiedComponentCover diagram root source tempered component ≅
      componentCovObject source component := by
  unfold classifiedComponentCover
  exact (componentwiseTemperedClassification
    diagram root source tempered component).2.2

/-- An arbitrary corrected tempered cover is the countable coproduct of
associated quotients of connected finite-level deck actions, with a separate
finite level allowed for every component. -/
noncomputable def componentwiseAssociatedQuotientClassification
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source) :
    SourceSemiGraphOfAnabelioids.CovObject.Coproduct.covObject
        (fun component : GeometricComponent source ↦
          classifiedComponentCover diagram root source tempered component) ≅
      source := by
  exact
    (SourceSemiGraphOfAnabelioids.CovObject.Coproduct.iso
      (fun component ↦ classifiedComponentComparison
        diagram root source tempered component)).trans
      (componentDecompositionIso source)

end SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

end Iut
