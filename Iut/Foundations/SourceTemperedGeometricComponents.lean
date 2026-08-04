/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedConnectedCoverClassification

/-!
# Intrinsic connected components of geometric tempered covers

The May 2020 correction to *Semi-graphs of Anabelioids*, Definition 3.5(ii),
allows every connected component of a tempered cover to choose its own finite
splitting cover.  This file constructs those components as literal objects of
the geometric covering category.  Their constituent carriers are the points
whose intrinsic geometric-reachability class is the selected component.
-/

namespace Iut

universe u

open CategoryTheory
open scoped SourceCountableTypeCatDiscrete

namespace SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

variable {diagram : SourceSemiGraphOfAnabelioids.{u}}

open SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

/-- Geometric reachability is the equivalence relation defining connected
components of a countable geometric cover. -/
def geometricComponentSetoid (source : diagram.CovObject) :
    Setoid (GeometricPoint source) where
  r := GeometricallyReachable source
  iseqv := ⟨
    fun _ ↦ Relation.ReflTransGen.refl,
    fun path ↦ reachable_symm path,
    fun first second ↦ first.trans second⟩

/-- Intrinsic connected components of a geometric cover. -/
abbrev GeometricComponent (source : diagram.CovObject) :=
  Quotient (geometricComponentSetoid source)

/-- The component represented by one geometric point. -/
def geometricComponentOf (source : diagram.CovObject)
    (point : GeometricPoint source) : GeometricComponent source :=
  Quotient.mk (geometricComponentSetoid source) point

noncomputable instance geometricComponentCountable
    [Countable diagram.base.Vertex] (source : diagram.CovObject) :
    Countable (GeometricComponent source) :=
  inferInstance

/-- The points of one vertex constituent lying in a selected geometric
component. -/
abbrev ComponentVertexCarrier (source : diagram.CovObject)
    (component : GeometricComponent source)
    (vertex : diagram.base.Vertex) :=
  { point : (source.vertexObject vertex).obj.V.obj //
      geometricComponentOf source ⟨vertex, point⟩ = component }

namespace ComponentVertexCarrier

variable (source : diagram.CovObject)
    (component : GeometricComponent source)
    (vertex : diagram.base.Vertex)

noncomputable instance : Countable
    (ComponentVertexCarrier source component vertex) :=
  Subtype.countable

noncomputable instance : SMul (diagram.vertexAnabelioid vertex).group
    (ComponentVertexCarrier source component vertex) where
  smul element point :=
    ⟨element • point.1, by
      have sameComponent :
          geometricComponentOf source ⟨vertex, point.1⟩ =
            geometricComponentOf source ⟨vertex, element • point.1⟩ :=
        Quotient.sound
          (Relation.ReflTransGen.single
            (GeometricPointStep.localAction vertex element point.1))
      exact sameComponent.symm.trans point.2⟩

noncomputable instance : MulAction (diagram.vertexAnabelioid vertex).group
    (ComponentVertexCarrier source component vertex) where
  one_smul point := by
    apply Subtype.ext
    exact one_smul _ point.1
  mul_smul first second point := by
    apply Subtype.ext
    exact mul_smul first second point.1

@[simp]
theorem smul_val (element : (diagram.vertexAnabelioid vertex).group)
    (point : ComponentVertexCarrier source component vertex) :
    (element • point).1 = element • point.1 :=
  rfl

end ComponentVertexCarrier

/-- The continuous constituent action carried by one geometric component. -/
noncomputable def componentVertexAction (source : diagram.CovObject)
    (component : GeometricComponent source)
    (vertex : diagram.base.Vertex) :
    SourceTemperoidAction (diagram.vertexAnabelioid vertex).group := by
  let Carrier := ComponentVertexCarrier source component vertex
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
  have openUnderlying : IsOpen
      (MulAction.stabilizer (diagram.vertexAnabelioid vertex).group
        point.1 : Set (diagram.vertexAnabelioid vertex).group) :=
    stabilizer_isOpen (diagram.vertexAnabelioid vertex).group point.1
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer
      (diagram.vertexAnabelioid vertex).group point.1)
    (H₂ := MulAction.stabilizer
      (diagram.vertexAnabelioid vertex).group point) _ openUnderlying
  intro element fixes
  rw [MulAction.mem_stabilizer_iff] at fixes ⊢
  apply Subtype.ext
  exact fixes

/-- Branch gluing restricts to the points in one geometric component. -/
noncomputable def componentGlue (source : diagram.CovObject)
    (component : GeometricComponent source)
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    first.temperoidPullback.obj
        (componentVertexAction source component first.vertex) ≅
      second.temperoidPullback.obj
        (componentVertexAction source component second.vertex) := by
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ (comm := ?_)
  · exact
      { hom := SourceCountableTypeCat.homMk (fun point ↦
          ⟨(source.glue first second).hom.hom.hom point.1, by
            have sameComponent :
                geometricComponentOf source ⟨first.vertex, point.1⟩ =
                  geometricComponentOf source
                    ⟨second.vertex,
                      (source.glue first second).hom.hom.hom point.1⟩ :=
              Quotient.sound
                (Relation.ReflTransGen.single
                  (GeometricPointStep.glue first second point.1))
            exact sameComponent.symm.trans point.2⟩)
        inv := SourceCountableTypeCat.homMk (fun point ↦
          ⟨(source.glue second first).hom.hom.hom point.1, by
            have sameComponent :
                geometricComponentOf source ⟨second.vertex, point.1⟩ =
                  geometricComponentOf source
                    ⟨first.vertex,
                      (source.glue second first).hom.hom.hom point.1⟩ :=
              Quotient.sound
                (Relation.ReflTransGen.single
                  (GeometricPointStep.glue second first point.1))
            exact sameComponent.symm.trans point.2⟩)
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          intro point
          apply Subtype.ext
          have coherence := congrArg Iso.hom
            (source.glue_trans first second first)
          rw [source.glue_refl] at coherence
          exact ConcreteCategory.congr_hom coherence point.1
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro point
          apply Subtype.ext
          have coherence := congrArg Iso.hom
            (source.glue_trans second first second)
          rw [source.glue_refl] at coherence
          exact ConcreteCategory.congr_hom coherence point.1 }
  · intro element
    apply ConcreteCategory.hom_ext
    intro point
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((source.glue first second).hom.hom.comm element) point.1

/-- One intrinsic connected component as a literal geometric cover. -/
noncomputable def componentCovObject (source : diagram.CovObject)
    (component : GeometricComponent source) : diagram.CovObject where
  vertexObject := componentVertexAction source component
  glue := componentGlue source component
  glue_refl := by
    intro edge branch
    apply Iso.ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      (congrArg Iso.hom (source.glue_refl branch)) point.1
  glue_trans := by
    intro edge first second third
    apply Iso.ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      (congrArg Iso.hom (source.glue_trans first second third)) point.1

/-- The selected component includes constituentwise into its source cover. -/
noncomputable def componentInclusion (source : diagram.CovObject)
    (component : GeometricComponent source) :
    componentCovObject source component ⟶ source where
  app vertex := ObjectProperty.homMk
    { hom := SourceCountableTypeCat.homMk Subtype.val
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
theorem componentInclusion_apply (source : diagram.CovObject)
    (component : GeometricComponent source)
    (vertex : diagram.base.Vertex)
    (point : ComponentVertexCarrier source component vertex) :
    ConcreteCategory.hom
        ((componentInclusion source component).app vertex).hom.hom point =
      point.1 :=
  rfl

/-- Regard a source point known to lie in `component` as a point of the
literal component subcover. -/
def componentPointOf (source : diagram.CovObject)
    (component : GeometricComponent source)
    (point : GeometricPoint source)
    (belongs : geometricComponentOf source point = component) :
    GeometricPoint (componentCovObject source component) :=
  ⟨point.1, ⟨point.2, belongs⟩⟩

/-- The canonical point selected by the quotient representative. -/
noncomputable def componentBasePoint (source : diagram.CovObject)
    (component : GeometricComponent source) :
    GeometricPoint (componentCovObject source component) :=
  componentPointOf source component component.out (Quotient.out_eq component)

/-- One source step between points of a selected component lifts to the
literal component subcover. -/
theorem componentPointStep
    (source : diagram.CovObject) (component : GeometricComponent source)
    {first second : GeometricPoint source}
    (firstBelongs : geometricComponentOf source first = component)
    (secondBelongs : geometricComponentOf source second = component)
    (step : GeometricPointStep source first second) :
    GeometricPointStep (componentCovObject source component)
      (componentPointOf source component first firstBelongs)
      (componentPointOf source component second secondBelongs) := by
  cases step with
  | localAction vertex element point =>
      have lifted := GeometricPointStep.localAction
        (source := componentCovObject source component)
        vertex element (⟨point, firstBelongs⟩ :
          ComponentVertexCarrier source component vertex)
      change GeometricPointStep (componentCovObject source component)
        (componentPointOf source component ⟨vertex, point⟩ firstBelongs)
        (componentPointOf source component
          ⟨vertex, element • point⟩ secondBelongs) at lifted
      exact lifted
  | @glue edge firstBranch secondBranch point =>
      have lifted := GeometricPointStep.glue
        (source := componentCovObject source component)
        firstBranch secondBranch
        (⟨point, firstBelongs⟩ :
          ComponentVertexCarrier source component firstBranch.vertex)
      change GeometricPointStep (componentCovObject source component)
        (componentPointOf source component
          ⟨firstBranch.vertex, point⟩ firstBelongs)
        (componentPointOf source component
          ⟨secondBranch.vertex,
            (source.glue firstBranch secondBranch).hom.hom.hom point⟩
          secondBelongs) at lifted
      exact lifted

/-- A source path whose endpoints lie in one component lifts to the literal
component subcover. -/
theorem reachable_componentPointOf
    (source : diagram.CovObject) (component : GeometricComponent source)
    {first second : GeometricPoint source}
    (path : GeometricallyReachable source first second)
    (firstBelongs : geometricComponentOf source first = component)
    (secondBelongs : geometricComponentOf source second = component) :
    GeometricallyReachable (componentCovObject source component)
      (componentPointOf source component first firstBelongs)
      (componentPointOf source component second secondBelongs) := by
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | @tail middle target path step inductionHypothesis =>
      have middleBelongs : geometricComponentOf source middle = component :=
        (Quotient.sound path).symm.trans firstBelongs
      exact
        (inductionHypothesis middleBelongs).tail
          (componentPointStep source component middleBelongs
            secondBelongs step)

/-- Every literal component subcover is intrinsically point-connected. -/
theorem componentCovObject_isPointConnected
    (source : diagram.CovObject) (component : GeometricComponent source) :
    IsPointConnected (componentCovObject source component)
      (componentBasePoint source component) := by
  rintro ⟨vertex, point⟩
  let target : GeometricPoint source := ⟨vertex, point.1⟩
  have componentEquality :
      geometricComponentOf source component.out =
        geometricComponentOf source target :=
    (Quotient.out_eq component).trans point.2.symm
  let path : GeometricallyReachable source component.out target :=
    Quotient.exact componentEquality
  have lifted := reachable_componentPointOf source component path
    (Quotient.out_eq component) point.2
  change GeometricallyReachable (componentCovObject source component)
    (componentBasePoint source component) ⟨vertex, point⟩ at lifted
  exact lifted

/-- Every literal component subcover is intrinsically connected. -/
theorem componentCovObject_isGeometricallyConnected
    (source : diagram.CovObject) (component : GeometricComponent source) :
    IsGeometricallyConnected (componentCovObject source component) :=
  ⟨componentBasePoint source component,
    componentCovObject_isPointConnected source component⟩

/-- Corrected temperedness restricts from a cover to each of its literal
connected components. -/
theorem componentCovObject_isTempered
    (root : diagram.base.Vertex) (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source)
    (component : GeometricComponent source) :
    SourceSemiGraphOfAnabelioids.CovObject.IsTempered diagram root
      (componentCovObject source component) := by
  intro basePoint
  let inclusion := componentInclusion source component
  let sourceBasePoint := geometricPointMap inclusion basePoint
  obtain ⟨splitter, split⟩ := tempered sourceBasePoint
  refine ⟨splitter, ?_⟩
  constructor
  · intro vertex element fixes point reachable
    apply Subtype.ext
    exact split.1 vertex element fixes point.1
      (reachable_map inclusion reachable)
  · intro edge
    dsimp only
    intro element fixes point reachable
    apply Subtype.ext
    exact split.2 edge element fixes point.1
      (reachable_map inclusion reachable)

/-- Every component of a corrected tempered cover has its own finite-level
connected-action presentation.  The selected level is allowed to depend on
the component, exactly as required by the corrected Definition 3.5(ii). -/
noncomputable def componentwiseTemperedClassification
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (source : diagram.CovObject)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsTempered
      diagram root source)
    (component : GeometricComponent source) :
    Σ level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
        diagram root,
      Σ action : SourceConnectedTemperoid (DeckGroup diagram root level),
        (((associatedTemperedFunctor diagram root level).obj action.obj).obj ≅
          componentCovObject source component) :=
  connectedTemperedClassification diagram root
    (componentCovObject source component)
    (componentCovObject_isTempered root source tempered component)
    (componentCovObject_isGeometricallyConnected source component)

end SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

end Iut
