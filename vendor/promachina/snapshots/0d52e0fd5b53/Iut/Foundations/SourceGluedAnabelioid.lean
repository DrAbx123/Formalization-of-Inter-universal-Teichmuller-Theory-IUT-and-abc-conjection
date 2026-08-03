/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.GaloisComplement
import Iut.Foundations.SourceSemiGraphOfAnabelioids
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# The glued category of a semi-graph of anabelioids

This file begins the literal construction denoted `B(G)` immediately after
Definition 2.1 of *Semi-graphs of Anabelioids*.  An object consists of one
object in every verticial constituent and coherent isomorphisms between its
two pullbacks to every edge constituent.  A morphism is a family of
constituent morphisms compatible with those gluing isomorphisms.

Using all incident branches, rather than choosing an ordering of the two
branches of each edge, makes the construction canonical.  On a closed edge
the coherence data is equivalent to the paper's single gluing isomorphism;
on an open edge it is forced, as it should be.  The isolated-edge case from
Definition 2.1 is treated separately from this verticial construction.
-/

namespace Iut

universe u v

open CategoryTheory
open CategoryTheory.Limits

namespace SourceSemiGraphOfAnabelioids

variable (diagram : Iut.SourceSemiGraphOfAnabelioids.{u})

/-- A branch of `edge` together with the vertex to which it abuts. -/
structure IncidentBranch (edge : diagram.base.Edge) where
  branch : diagram.base.Branch edge
  vertex : diagram.base.Vertex
  abuts : diagram.base.coincidence edge branch = some vertex

namespace IncidentBranch

variable {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {edge : diagram.base.Edge}

/-- Pullback from the verticial constituent to the edge constituent along an
incident branch. -/
def pullback (incident : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid incident.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (diagram.vertexAnabelioid incident.vertex).Cover ⥤
      (diagram.edgeAnabelioid edge).Cover :=
  (diagram.branchMorphism incident.branch incident.abuts).pullback

end IncidentBranch

/-- The object data `{S_v, phi_e}` defining the verticial case of `B(G)`.
The cocycle laws remove any dependence on an ordering of an edge's branches.
-/
structure GluedObject where
  vertexObject :
    ∀ vertex, (diagram.vertexAnabelioid vertex).Cover
  glue :
    ∀ {edge} (first second : diagram.IncidentBranch edge),
      letI := (diagram.vertexAnabelioid first.vertex).coverCategory
      letI := (diagram.vertexAnabelioid second.vertex).coverCategory
      letI := (diagram.edgeAnabelioid edge).coverCategory
      (first.pullback.obj (vertexObject first.vertex)) ≅
        (second.pullback.obj (vertexObject second.vertex))
  glue_refl :
    ∀ {edge} (branch : diagram.IncidentBranch edge),
      letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
      letI := (diagram.edgeAnabelioid edge).coverCategory
      glue branch branch = Iso.refl _
  glue_trans :
    ∀ {edge} (first second third : diagram.IncidentBranch edge),
      letI := (diagram.vertexAnabelioid first.vertex).coverCategory
      letI := (diagram.vertexAnabelioid second.vertex).coverCategory
      letI := (diagram.vertexAnabelioid third.vertex).coverCategory
      letI := (diagram.edgeAnabelioid edge).coverCategory
      (glue first second).trans (glue second third) = glue first third

namespace GluedObject

variable {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}

/-- A morphism of glued objects is a constituentwise morphism commuting with
every edge-gluing isomorphism. -/
structure Hom (source target : diagram.GluedObject) where
  app :
    ∀ vertex,
      letI := (diagram.vertexAnabelioid vertex).coverCategory
      source.vertexObject vertex ⟶ target.vertexObject vertex
  naturality :
    ∀ {edge} (first second : diagram.IncidentBranch edge),
      letI := (diagram.vertexAnabelioid first.vertex).coverCategory
      letI := (diagram.vertexAnabelioid second.vertex).coverCategory
      letI := (diagram.edgeAnabelioid edge).coverCategory
      (source.glue first second).hom ≫
          second.pullback.map (app second.vertex) =
        first.pullback.map (app first.vertex) ≫
          (target.glue first second).hom

namespace Hom

variable {source middle target : diagram.GluedObject}

@[ext]
theorem ext {first second : Hom source target}
    (app_eq : ∀ vertex, first.app vertex = second.app vertex) :
    first = second := by
  cases first with
  | mk firstApp firstNaturality =>
      cases second with
      | mk secondApp secondNaturality =>
          have equality : firstApp = secondApp := funext app_eq
          subst secondApp
          rfl

/-- Identity morphism of glued objects. -/
def id (source : diagram.GluedObject) : Hom source source where
  app := fun vertex =>
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    𝟙 _
  naturality := by
    intro edge first second
    letI := (diagram.edgeAnabelioid edge).coverCategory
    simp

/-- Composition of morphisms of glued objects. -/
def comp (first : Hom source middle) (second : Hom middle target) :
    Hom source target where
  app := fun vertex =>
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    first.app vertex ≫ second.app vertex
  naturality := by
    intro edge left right
    letI := (diagram.vertexAnabelioid left.vertex).coverCategory
    letI := (diagram.vertexAnabelioid right.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    rw [Functor.map_comp, Functor.map_comp]
    rw [← Category.assoc, first.naturality left right]
    rw [Category.assoc, second.naturality left right]
    rw [← Category.assoc]

end Hom

/-- The category whose objects and arrows are the literal gluing data of
Definition 2.1. -/
instance category : Category diagram.GluedObject where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro source target morphism
    ext vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    simp [Hom.comp, Hom.id]
  comp_id := by
    intro source target morphism
    ext vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    simp [Hom.comp, Hom.id]
  assoc := by
    intro first second third fourth f g h
    ext vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    simp [Hom.comp, Category.assoc]

@[simp]
theorem id_app (source : diagram.GluedObject) (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    Hom.app (𝟙 source) vertex = 𝟙 _ :=
  rfl

@[simp]
theorem comp_app {source middle target : diagram.GluedObject}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    Hom.app (first ≫ second) vertex =
      Hom.app first vertex ≫ Hom.app second vertex :=
  rfl

/-- A morphism whose every verticial component is invertible has the
componentwise inverse in the glued category. -/
noncomputable def componentwiseInverse
    {source target : diagram.GluedObject}
    (morphism : source ⟶ target)
    [∀ vertex,
      letI := (diagram.vertexAnabelioid vertex).coverCategory
      IsIso (morphism.app vertex)] : target ⟶ source where
  app := fun vertex => by
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact inv (morphism.app vertex)
  naturality := by
    intro edge first second
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    apply (cancel_mono
      (second.pullback.map (morphism.app second.vertex))).1
    calc
      ((target.glue first second).hom ≫
          second.pullback.map (inv (morphism.app second.vertex))) ≫
          second.pullback.map (morphism.app second.vertex) =
        (target.glue first second).hom := by
          rw [Category.assoc, ← Functor.map_comp,
            IsIso.inv_hom_id]
          simp
      _ = (first.pullback.map (inv (morphism.app first.vertex)) ≫
          (source.glue first second).hom) ≫
          second.pullback.map (morphism.app second.vertex) := by
        rw [Category.assoc, morphism.naturality, ← Category.assoc,
          ← Functor.map_comp, IsIso.inv_hom_id]
        simp

/-- Isomorphisms in the glued category are detected componentwise. -/
noncomputable instance isIsoOfComponentwiseIsIso
    {source target : diagram.GluedObject}
    (morphism : source ⟶ target)
    [∀ vertex,
      letI := (diagram.vertexAnabelioid vertex).coverCategory
      IsIso (morphism.app vertex)] : IsIso morphism := by
  apply IsIso.mk
  refine ⟨componentwiseInverse morphism, ?_, ?_⟩
  · apply Hom.ext
    intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact IsIso.hom_inv_id (morphism.app vertex)
  · apply Hom.ext
    intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    change inv (morphism.app vertex) ≫ morphism.app vertex = 𝟙 _
    exact IsIso.inv_hom_id (morphism.app vertex)

/-- Evaluation of a glued object at one verticial constituent. -/
def evaluation (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    diagram.GluedObject ⥤ (diagram.vertexAnabelioid vertex).Cover := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact
    { obj := fun object => object.vertexObject vertex
      map := fun morphism => morphism.app vertex
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }

/-- Invertibility of a morphism component propagates across an edge.  The
gluing square makes the neighboring pullback invertible, and exact pointed
branch pullback reflects isomorphisms. -/
theorem isIso_app_of_incident
    {source target : diagram.GluedObject}
    (morphism : source ⟶ target)
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge)
    [isIsoFirst :
      letI := (diagram.vertexAnabelioid first.vertex).coverCategory
      IsIso (morphism.app first.vertex)] :
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    IsIso (morphism.app second.vertex) := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI : second.pullback.ReflectsIsomorphisms := by
    change
      Functor.ReflectsIsomorphisms
        (diagram.branchMorphism second.branch second.abuts).pullback
    exact SourcePointedAnabelioidHom.pullbackReflectsIsomorphisms
      (diagram.branchMorphism second.branch second.abuts)
  haveI : IsIso (first.pullback.map (morphism.app first.vertex)) :=
    inferInstance
  haveI : IsIso
      (first.pullback.map (morphism.app first.vertex) ≫
        (target.glue first second).hom) := inferInstance
  haveI : IsIso
      ((source.glue first second).hom ≫
        second.pullback.map (morphism.app second.vertex)) := by
    rw [morphism.naturality first second]
    infer_instance
  haveI : IsIso
      (second.pullback.map (morphism.app second.vertex)) :=
    IsIso.of_isIso_comp_left
      (source.glue first second).hom
      (second.pullback.map (morphism.app second.vertex))
  exact isIso_of_reflects_iso
    (morphism.app second.vertex) second.pullback

/-- Invertibility propagates along a path in the underlying connected
semi-graph. -/
theorem isIso_app_of_path
    {source target : diagram.GluedObject}
    (morphism : source ⟶ target)
    {first second : diagram.base.Vertex}
    (path : Relation.ReflTransGen diagram.base.Adjacent first second)
    [isIsoFirst :
      letI := (diagram.vertexAnabelioid first).coverCategory
      IsIso (morphism.app first)] :
    letI := (diagram.vertexAnabelioid second).coverCategory
    IsIso (morphism.app second) := by
  induction path with
  | refl => infer_instance
  | @tail middle final path adjacent induction =>
      letI := (diagram.vertexAnabelioid middle).coverCategory
      letI := (diagram.vertexAnabelioid final).coverCategory
      haveI : IsIso (morphism.app middle) := induction
      rcases adjacent with
        ⟨edge, firstBranch, secondBranch, distinct,
          firstAbuts, secondAbuts⟩
      let firstIncident : diagram.IncidentBranch edge :=
        ⟨firstBranch, middle, firstAbuts⟩
      let secondIncident : diagram.IncidentBranch edge :=
        ⟨secondBranch, final, secondAbuts⟩
      exact isIso_app_of_incident morphism firstIncident secondIncident

/-- On a connected verticial semi-graph, evaluation at any vertex reflects
isomorphisms. -/
noncomputable instance evaluationReflectsIsomorphisms
    (root : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid root).coverCategory
    (evaluation (diagram := diagram) root).ReflectsIsomorphisms := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  exact
    { reflects := fun morphism _ => by
        haveI : IsIso (morphism.app root) := by
          change IsIso
            ((evaluation (diagram := diagram) root).map morphism)
          infer_instance
        rcases diagram.connected with verticial | isolated
        · letI componentsIsIso : ∀ vertex,
              letI :=
                (diagram.vertexAnabelioid vertex).coverCategory
              IsIso (morphism.app vertex) := fun vertex =>
            isIso_app_of_path morphism
              (verticial.2.2 root vertex)
          exact isIsoOfComponentwiseIsIso morphism
        · letI : IsEmpty diagram.base.Vertex := isolated.1
          exact False.elim (isEmptyElim root) }

/-- The gluing carried by every object is natural in that object.  Thus the
two ways of evaluating at the ends of an edge and pulling back to its edge
constituent are naturally isomorphic diagrams. -/
def branchComparison
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    evaluation (diagram := diagram) first.vertex ⋙ first.pullback ≅
      evaluation (diagram := diagram) second.vertex ⋙ second.pullback := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact NatIso.ofComponents
    (fun object => object.glue first second)
    (fun morphism => (morphism.naturality first second).symm)

theorem branchComparison_refl
    {edge : diagram.base.Edge}
    (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    branchComparison (diagram := diagram) branch branch = Iso.refl _ := by
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  ext object
  exact congrArg Iso.hom (object.glue_refl branch)

theorem branchComparison_trans
    {edge : diagram.base.Edge}
    (first second third : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.vertexAnabelioid third.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (branchComparison (diagram := diagram) first second).trans
        (branchComparison (diagram := diagram) second third) =
      branchComparison (diagram := diagram) first third := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.vertexAnabelioid third.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  ext object
  exact congrArg Iso.hom (object.glue_trans first second third)

/-! ## Pointwise finite limits -/

section FiniteLimits

variable {J : Type v} [SmallCategory J] [FinCategory J]

/-- The verticial component of the pointwise limit of a finite diagram of
glued objects. -/
noncomputable def limitVertexObject
    (family : J ⥤ diagram.GluedObject)
    (vertex : diagram.base.Vertex) :
    (diagram.vertexAnabelioid vertex).Cover := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI := (diagram.vertexAnabelioid vertex).galoisCategory
  exact limit (family ⋙ evaluation (diagram := diagram) vertex)

/-- Pullback preservation and the natural branch comparison canonically glue
the verticial limits over each edge. -/
noncomputable def limitGlue
    (family : J ⥤ diagram.GluedObject)
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    first.pullback.obj
        (limitVertexObject (diagram := diagram) family first.vertex) ≅
      second.pullback.obj
        (limitVertexObject (diagram := diagram) family second.vertex) := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.vertexAnabelioid first.vertex).galoisCategory
  letI := (diagram.vertexAnabelioid second.vertex).galoisCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI : PreservesFiniteLimits first.pullback :=
    (diagram.branchMorphism first.branch first.abuts).preservesFiniteLimits
  letI : PreservesFiniteLimits second.pullback :=
    (diagram.branchMorphism second.branch second.abuts).preservesFiniteLimits
  exact
    preservesLimitIso first.pullback
        (family ⋙ evaluation (diagram := diagram) first.vertex) ≪≫
      HasLimit.isoOfNatIso
        (Functor.isoWhiskerLeft family
          (branchComparison (diagram := diagram) first second)) ≪≫
      (preservesLimitIso second.pullback
        (family ⋙ evaluation (diagram := diagram) second.vertex)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The canonical edge gluing on a pointwise limit is characterized by its
composites with the limiting projections. -/
lemma limitGlue_hom_map_π
    (family : J ⥤ diagram.GluedObject)
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) (index : J) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    letI := (diagram.vertexAnabelioid first.vertex).galoisCategory
    letI := (diagram.vertexAnabelioid second.vertex).galoisCategory
    letI := (diagram.edgeAnabelioid edge).galoisCategory
    (limitGlue (diagram := diagram) family first second).hom ≫
        second.pullback.map
          (limit.π
            (family ⋙ evaluation (diagram := diagram) second.vertex)
            index) =
      first.pullback.map
        (limit.π
            (family ⋙ evaluation (diagram := diagram) first.vertex)
            index) ≫
        ((family.obj index).glue first second).hom := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.vertexAnabelioid first.vertex).galoisCategory
  letI := (diagram.vertexAnabelioid second.vertex).galoisCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI : PreservesFiniteLimits first.pullback :=
    (diagram.branchMorphism first.branch first.abuts).preservesFiniteLimits
  letI : PreservesFiniteLimits second.pullback :=
    (diagram.branchMorphism second.branch second.abuts).preservesFiniteLimits
  let comparison := Functor.isoWhiskerLeft family
    (branchComparison (diagram := diagram) first second)
  have comparisonProjection :
      (HasLimit.isoOfNatIso comparison).hom ≫
          limit.π
            ((family ⋙ evaluation (diagram := diagram) second.vertex) ⋙
              second.pullback) index =
        limit.π
            ((family ⋙ evaluation (diagram := diagram) first.vertex) ⋙
              first.pullback) index ≫
          ((family.obj index).glue first second).hom := by
    change (HasLimit.isoOfNatIso comparison).hom ≫
        limit.π _ index = limit.π _ index ≫ comparison.hom.app index
    exact HasLimit.isoOfNatIso_hom_π comparison index
  simp only [limitGlue, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [preservesLimitIso_inv_π second.pullback
    (family ⋙ evaluation (diagram := diagram) second.vertex) index]
  rw [comparisonProjection]
  rw [← Category.assoc]
  rw [preservesLimitIso_hom_π first.pullback
    (family ⋙ evaluation (diagram := diagram) first.vertex) index]

set_option backward.isDefEq.respectTransparency false in
lemma limitGlue_refl
    (family : J ⥤ diagram.GluedObject)
    {edge : diagram.base.Edge}
    (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    limitGlue (diagram := diagram) family branch branch = Iso.refl _ := by
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.vertexAnabelioid branch.vertex).galoisCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI : PreservesFiniteLimits branch.pullback :=
    (diagram.branchMorphism branch.branch branch.abuts).preservesFiniteLimits
  apply Iso.ext
  apply (isLimitOfPreserves branch.pullback
    (limit.isLimit
      (family ⋙ evaluation (diagram := diagram) branch.vertex))).hom_ext
  intro index
  simp only [Functor.mapCone_π_app]
  calc
    (limitGlue (diagram := diagram) family branch branch).hom ≫
          branch.pullback.map
            (limit.π
              (family ⋙ evaluation (diagram := diagram) branch.vertex)
              index) =
        branch.pullback.map
            (limit.π
              (family ⋙ evaluation (diagram := diagram) branch.vertex)
              index) ≫
          ((family.obj index).glue branch branch).hom :=
      limitGlue_hom_map_π (diagram := diagram) family branch branch index
    _ = (Iso.refl _).hom ≫
          branch.pullback.map
            (limit.π
              (family ⋙ evaluation (diagram := diagram) branch.vertex)
              index) := by
      rw [(family.obj index).glue_refl branch]
      let projection := branch.pullback.map
        (limit.π
          (family ⋙ evaluation (diagram := diagram) branch.vertex) index)
      calc
        projection ≫ (Iso.refl _).hom = projection :=
          Category.comp_id projection
        _ = (Iso.refl _).hom ≫ projection :=
          (Category.id_comp projection).symm

set_option backward.isDefEq.respectTransparency false in
lemma limitGlue_trans
    (family : J ⥤ diagram.GluedObject)
    {edge : diagram.base.Edge}
    (first second third : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.vertexAnabelioid third.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (limitGlue (diagram := diagram) family first second).trans
        (limitGlue (diagram := diagram) family second third) =
      limitGlue (diagram := diagram) family first third := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.vertexAnabelioid third.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.vertexAnabelioid first.vertex).galoisCategory
  letI := (diagram.vertexAnabelioid second.vertex).galoisCategory
  letI := (diagram.vertexAnabelioid third.vertex).galoisCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI : PreservesFiniteLimits first.pullback :=
    (diagram.branchMorphism first.branch first.abuts).preservesFiniteLimits
  letI : PreservesFiniteLimits second.pullback :=
    (diagram.branchMorphism second.branch second.abuts).preservesFiniteLimits
  letI : PreservesFiniteLimits third.pullback :=
    (diagram.branchMorphism third.branch third.abuts).preservesFiniteLimits
  apply Iso.ext
  apply (isLimitOfPreserves third.pullback
    (limit.isLimit
      (family ⋙ evaluation (diagram := diagram) third.vertex))).hom_ext
  intro index
  simp only [Iso.trans_hom, Functor.mapCone_π_app, Category.assoc]
  let firstProjection := limit.π
    (family ⋙ evaluation (diagram := diagram) first.vertex) index
  let secondProjection := limit.π
    (family ⋙ evaluation (diagram := diagram) second.vertex) index
  let thirdProjection := limit.π
    (family ⋙ evaluation (diagram := diagram) third.vertex) index
  calc
    (limitGlue (diagram := diagram) family first second).hom ≫
          (limitGlue (diagram := diagram) family second third).hom ≫
            third.pullback.map thirdProjection =
        (limitGlue (diagram := diagram) family first second).hom ≫
          ((limitGlue (diagram := diagram) family second third).hom ≫
            third.pullback.map thirdProjection) := by simp
    _ = (limitGlue (diagram := diagram) family first second).hom ≫
          (second.pullback.map secondProjection ≫
            ((family.obj index).glue second third).hom) := by
      rw [limitGlue_hom_map_π]
    _ = ((limitGlue (diagram := diagram) family first second).hom ≫
          second.pullback.map secondProjection) ≫
            ((family.obj index).glue second third).hom := by simp
    _ = (first.pullback.map firstProjection ≫
          ((family.obj index).glue first second).hom) ≫
            ((family.obj index).glue second third).hom := by
      rw [limitGlue_hom_map_π]
    _ = first.pullback.map firstProjection ≫
          (((family.obj index).glue first second).hom ≫
            ((family.obj index).glue second third).hom) := by simp
    _ = first.pullback.map firstProjection ≫
          ((family.obj index).glue first third).hom := by
      rw [← Iso.trans_hom]
      rw [(family.obj index).glue_trans first second third]
    _ = (limitGlue (diagram := diagram) family first third).hom ≫
          third.pullback.map thirdProjection :=
      (limitGlue_hom_map_π
        (diagram := diagram) family first third index).symm

/-- The pointwise finite limit, equipped with the canonical edge gluing. -/
noncomputable def limitObject
    (family : J ⥤ diagram.GluedObject) : diagram.GluedObject where
  vertexObject := limitVertexObject (diagram := diagram) family
  glue := limitGlue (diagram := diagram) family
  glue_refl := limitGlue_refl (diagram := diagram) family
  glue_trans := limitGlue_trans (diagram := diagram) family

/-- One leg of the pointwise limiting cone. -/
noncomputable def limitProjection
    (family : J ⥤ diagram.GluedObject) (index : J) :
    limitObject (diagram := diagram) family ⟶ family.obj index where
  app := fun vertex => by
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    letI := (diagram.vertexAnabelioid vertex).galoisCategory
    exact limit.π
      (family ⋙ evaluation (diagram := diagram) vertex) index
  naturality := by
    intro edge first second
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    letI := (diagram.vertexAnabelioid first.vertex).galoisCategory
    letI := (diagram.vertexAnabelioid second.vertex).galoisCategory
    letI := (diagram.edgeAnabelioid edge).galoisCategory
    letI : PreservesFiniteLimits first.pullback :=
      (diagram.branchMorphism first.branch first.abuts).preservesFiniteLimits
    letI : PreservesFiniteLimits second.pullback :=
      (diagram.branchMorphism second.branch second.abuts).preservesFiniteLimits
    exact limitGlue_hom_map_π
      (diagram := diagram) family first second index

/-- The pointwise limiting cone of a finite diagram of glued objects. -/
noncomputable def limitCone
    (family : J ⥤ diagram.GluedObject) : Cone family where
  pt := limitObject (diagram := diagram) family
  π :=
    { app := limitProjection (diagram := diagram) family
      naturality := by
        intro first second morphism
        apply Hom.ext
        intro vertex
        letI := (diagram.vertexAnabelioid vertex).coverCategory
        letI := (diagram.vertexAnabelioid vertex).galoisCategory
        simpa [limitProjection] using
          (limit.w
            (family ⋙ evaluation (diagram := diagram) vertex) morphism).symm }

/-- The constituentwise lift from any cone into the pointwise limit. -/
noncomputable def limitLift
    (family : J ⥤ diagram.GluedObject) (cone : Cone family) :
    cone.pt ⟶ limitObject (diagram := diagram) family where
  app := fun vertex => by
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    letI := (diagram.vertexAnabelioid vertex).galoisCategory
    exact limit.lift
      (family ⋙ evaluation (diagram := diagram) vertex)
      ((evaluation (diagram := diagram) vertex).mapCone cone)
  naturality := by
    intro edge first second
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    letI := (diagram.vertexAnabelioid first.vertex).galoisCategory
    letI := (diagram.vertexAnabelioid second.vertex).galoisCategory
    letI := (diagram.edgeAnabelioid edge).galoisCategory
    letI : PreservesFiniteLimits first.pullback :=
      (diagram.branchMorphism first.branch first.abuts).preservesFiniteLimits
    letI : PreservesFiniteLimits second.pullback :=
      (diagram.branchMorphism second.branch second.abuts).preservesFiniteLimits
    apply (isLimitOfPreserves second.pullback
      (limit.isLimit
        (family ⋙ evaluation (diagram := diagram) second.vertex))).hom_ext
    intro index
    simp only [Functor.mapCone_π_app]
    let firstVertexCone :=
      (evaluation (diagram := diagram) first.vertex).mapCone cone
    let secondVertexCone :=
      (evaluation (diagram := diagram) second.vertex).mapCone cone
    let firstProjection := limit.π
      (family ⋙ evaluation (diagram := diagram) first.vertex) index
    let secondProjection := limit.π
      (family ⋙ evaluation (diagram := diagram) second.vertex) index
    let firstLift := limit.lift
      (family ⋙ evaluation (diagram := diagram) first.vertex)
      firstVertexCone
    let secondLift := limit.lift
      (family ⋙ evaluation (diagram := diagram) second.vertex)
      secondVertexCone
    have firstLiftProjection :
        firstLift ≫ firstProjection = firstVertexCone.π.app index := by
      exact limit.lift_π
        firstVertexCone index
    have secondLiftProjection :
        secondLift ≫ secondProjection = secondVertexCone.π.app index := by
      exact limit.lift_π secondVertexCone index
    have firstMappedProjection :
        first.pullback.map firstLift ≫
            first.pullback.map firstProjection =
          first.pullback.map (firstVertexCone.π.app index) := by
      rw [← Functor.map_comp, firstLiftProjection]
      rfl
    have assembledRight :
        first.pullback.map
              (((evaluation (diagram := diagram) first.vertex).mapCone cone).π.app
                index) ≫
            ((family.obj index).glue first second).hom =
          first.pullback.map
              (limit.lift
                (family ⋙ evaluation (diagram := diagram) first.vertex)
                ((evaluation (diagram := diagram) first.vertex).mapCone cone)) ≫
            ((limitGlue (diagram := diagram) family first second).hom ≫
              second.pullback.map
                (limit.π
                  (family ⋙ evaluation (diagram := diagram) second.vertex)
                  index)) := by
      rw [← firstMappedProjection]
      calc
        (first.pullback.map firstLift ≫
              first.pullback.map firstProjection) ≫
            ((family.obj index).glue first second).hom =
          first.pullback.map firstLift ≫
            (first.pullback.map firstProjection ≫
              ((family.obj index).glue first second).hom) :=
          Category.assoc _ _ _
        _ = first.pullback.map firstLift ≫
            ((limitGlue (diagram := diagram) family first second).hom ≫
              second.pullback.map secondProjection) := by
          congr 1
          exact (limitGlue_hom_map_π
            (diagram := diagram) family first second index).symm
    have leftReduction :
        ((cone.pt.glue first second).hom ≫
            second.pullback.map secondLift) ≫
            second.pullback.map secondProjection =
          (cone.pt.glue first second).hom ≫
            second.pullback.map (secondVertexCone.π.app index) := by
      calc
        ((cone.pt.glue first second).hom ≫
            second.pullback.map secondLift) ≫
            second.pullback.map secondProjection =
          (cone.pt.glue first second).hom ≫
            second.pullback.map (secondLift ≫ secondProjection) := by
          rw [Functor.map_comp]
          exact Category.assoc _ _ _
        _ = (cone.pt.glue first second).hom ≫
            second.pullback.map (secondVertexCone.π.app index) := by
          exact congrArg
            (fun morphism =>
              (cone.pt.glue first second).hom ≫
                second.pullback.map morphism)
            secondLiftProjection
    have rightReduction :
        (first.pullback.map firstLift ≫
            (limitGlue (diagram := diagram) family first second).hom) ≫
            second.pullback.map secondProjection =
          first.pullback.map (firstVertexCone.π.app index) ≫
            ((family.obj index).glue first second).hom := by
      calc
        (first.pullback.map firstLift ≫
            (limitGlue (diagram := diagram) family first second).hom) ≫
            second.pullback.map secondProjection =
          first.pullback.map firstLift ≫
            ((limitGlue (diagram := diagram) family first second).hom ≫
              second.pullback.map secondProjection) :=
          Category.assoc _ _ _
        _ = first.pullback.map (firstVertexCone.π.app index) ≫
            ((family.obj index).glue first second).hom := assembledRight.symm
    exact leftReduction.trans <|
      ((cone.π.app index).naturality first second).trans rightReduction.symm

/-- The pointwise cone satisfies the universal property of the finite limit.
-/
noncomputable def limitConeIsLimit
    (family : J ⥤ diagram.GluedObject) :
    IsLimit (limitCone (diagram := diagram) family) where
  lift cone := limitLift (diagram := diagram) family cone
  fac cone index := by
    apply Hom.ext
    intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    letI := (diagram.vertexAnabelioid vertex).galoisCategory
    exact limit.lift_π
      ((evaluation (diagram := diagram) vertex).mapCone cone) index
  uniq cone morphism factorization := by
    apply Hom.ext
    intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    letI := (diagram.vertexAnabelioid vertex).galoisCategory
    apply limit.hom_ext
    intro index
    have componentEquality := congrArg
      (fun component : cone.pt ⟶ family.obj index => component.app vertex)
      (factorization index)
    change morphism.app vertex ≫
        limit.π
          (family ⋙ evaluation (diagram := diagram) vertex) index =
      (cone.π.app index).app vertex at componentEquality
    exact componentEquality.trans <|
      (limit.lift_π
        ((evaluation (diagram := diagram) vertex).mapCone cone) index).symm

/-- Every finite diagram of verticial glued objects has the constructed
pointwise limit. -/
noncomputable instance hasLimit
    (family : J ⥤ diagram.GluedObject) : HasLimit family :=
  HasLimit.mk
    { cone := limitCone (diagram := diagram) family
      isLimit := limitConeIsLimit (diagram := diagram) family }

end FiniteLimits

/-- The verticial glued category has all finite limits. -/
noncomputable instance hasFiniteLimits : HasFiniteLimits diagram.GluedObject where
  out := fun _ _ _ =>
    { has_limit := fun family =>
        hasLimit (diagram := diagram) family }

/-- Evaluation at a vertex preserves the pointwise finite limits constructed
above. -/
noncomputable instance evaluationPreservesFiniteLimits
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    PreservesFiniteLimits
      (evaluation (diagram := diagram) vertex) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI := (diagram.vertexAnabelioid vertex).galoisCategory
  exact
    { preservesFiniteLimits := fun J _ _ =>
        { preservesLimit := fun {family} =>
            preservesLimit_of_preserves_limit_cone
              (limitConeIsLimit (diagram := diagram) family)
              (by
                simpa [limitCone, limitProjection, limitObject,
                  limitVertexObject] using
                  limit.isLimit
                    (family ⋙ evaluation (diagram := diagram) vertex)) } }

/-- Pointwise preservation of pullbacks makes every vertex evaluation preserve
monomorphisms. -/
noncomputable instance evaluationPreservesMonomorphisms
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    (evaluation (diagram := diagram) vertex).PreservesMonomorphisms := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact
    { preserves := fun morphism _ => by
        rw [mono_iff_isPullback]
        simpa using
          ((mono_iff_isPullback morphism).mp inferInstance).map
            (evaluation (diagram := diagram) vertex) }

/-! ## Pointwise finite colimits -/

section FiniteColimits

variable {J : Type v} [SmallCategory J] [FinCategory J]

/-- Availability of the constituentwise colimits needed for a particular
finite diagram.  Pre-Galois categories provide the two shapes used below
(finite coproducts and finite-group quotients), but not arbitrary finite
colimits as a primitive axiom. -/
class HasPointwiseColimit (family : J ⥤ diagram.GluedObject) : Prop where
  hasColimit :
    ∀ vertex,
      letI := (diagram.vertexAnabelioid vertex).coverCategory
      letI := (diagram.vertexAnabelioid vertex).galoisCategory
      HasColimit (family ⋙ evaluation (diagram := diagram) vertex)

noncomputable instance pointwiseHasColimit
    (family : J ⥤ diagram.GluedObject) [HasPointwiseColimit family]
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    letI := (diagram.vertexAnabelioid vertex).galoisCategory
    HasColimit (family ⋙ evaluation (diagram := diagram) vertex) :=
  HasPointwiseColimit.hasColimit vertex

/-- A preserving functor sends a chosen colimit cone to a colimit cone.  We
materialize the resulting `HasColimit` instance locally where the canonical
comparison isomorphism is used. -/
@[reducible]
noncomputable def hasColimitCompOfPreserves
    {C : Type (u + 1)} [Category.{u} C]
    {D : Type (u + 1)} [Category.{u} D]
    (family : J ⥤ C) (functor : C ⥤ D)
    [HasColimit family] [PreservesColimit family functor] :
    HasColimit (family ⋙ functor) :=
  HasColimit.mk
    { cocone := functor.mapCocone (colimit.cocone family)
      isColimit := isColimitOfPreserves functor (colimit.isColimit family) }

/-- The verticial component of the pointwise colimit of a finite diagram of
glued objects. -/
noncomputable def colimitVertexObject
    (family : J ⥤ diagram.GluedObject) [HasPointwiseColimit family]
    (vertex : diagram.base.Vertex) :
    (diagram.vertexAnabelioid vertex).Cover := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI := (diagram.vertexAnabelioid vertex).galoisCategory
  exact colimit (family ⋙ evaluation (diagram := diagram) vertex)

/-- Exact branch pullbacks carry the constituentwise colimits to canonically
glued edge objects. -/
noncomputable def colimitGlue
    (family : J ⥤ diagram.GluedObject) [HasPointwiseColimit family]
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    first.pullback.obj
        (colimitVertexObject (diagram := diagram) family first.vertex) ≅
      second.pullback.obj
        (colimitVertexObject (diagram := diagram) family second.vertex) := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.vertexAnabelioid first.vertex).galoisCategory
  letI := (diagram.vertexAnabelioid second.vertex).galoisCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI : PreservesFiniteColimits first.pullback :=
    (diagram.branchMorphism first.branch first.abuts).preservesFiniteColimits
  letI : PreservesFiniteColimits second.pullback :=
    (diagram.branchMorphism second.branch second.abuts).preservesFiniteColimits
  letI : HasColimit
      ((family ⋙ evaluation (diagram := diagram) first.vertex) ⋙
        first.pullback) :=
    hasColimitCompOfPreserves
      (family ⋙ evaluation (diagram := diagram) first.vertex) first.pullback
  letI : HasColimit
      ((family ⋙ evaluation (diagram := diagram) second.vertex) ⋙
        second.pullback) :=
    hasColimitCompOfPreserves
      (family ⋙ evaluation (diagram := diagram) second.vertex) second.pullback
  exact
    preservesColimitIso first.pullback
        (family ⋙ evaluation (diagram := diagram) first.vertex) ≪≫
      HasColimit.isoOfNatIso
        ((Functor.associator family
            (evaluation (diagram := diagram) first.vertex)
            first.pullback) ≪≫
          Functor.isoWhiskerLeft family
            (branchComparison (diagram := diagram) first second) ≪≫
          (Functor.associator family
            (evaluation (diagram := diagram) second.vertex)
            second.pullback).symm) ≪≫
      (preservesColimitIso second.pullback
        (family ⋙ evaluation (diagram := diagram) second.vertex)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The colimit gluing is characterized by its composites with the
constituentwise coprojections. -/
lemma colimitGlue_map_ι
    (family : J ⥤ diagram.GluedObject) [HasPointwiseColimit family]
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) (index : J) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    letI := (diagram.vertexAnabelioid first.vertex).galoisCategory
    letI := (diagram.vertexAnabelioid second.vertex).galoisCategory
    letI := (diagram.edgeAnabelioid edge).galoisCategory
    ((family.obj index).glue first second).hom ≫
        second.pullback.map
          (colimit.ι
            (family ⋙ evaluation (diagram := diagram) second.vertex)
            index) =
      first.pullback.map
          (colimit.ι
            (family ⋙ evaluation (diagram := diagram) first.vertex)
            index) ≫
        (colimitGlue (diagram := diagram) family first second).hom := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.vertexAnabelioid first.vertex).galoisCategory
  letI := (diagram.vertexAnabelioid second.vertex).galoisCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI : PreservesFiniteColimits first.pullback :=
    (diagram.branchMorphism first.branch first.abuts).preservesFiniteColimits
  letI : PreservesFiniteColimits second.pullback :=
    (diagram.branchMorphism second.branch second.abuts).preservesFiniteColimits
  letI : HasColimit
      ((family ⋙ evaluation (diagram := diagram) first.vertex) ⋙
        first.pullback) :=
    hasColimitCompOfPreserves
      (family ⋙ evaluation (diagram := diagram) first.vertex) first.pullback
  letI : HasColimit
      ((family ⋙ evaluation (diagram := diagram) second.vertex) ⋙
        second.pullback) :=
    hasColimitCompOfPreserves
      (family ⋙ evaluation (diagram := diagram) second.vertex) second.pullback
  let comparison :=
    (Functor.associator family
      (evaluation (diagram := diagram) first.vertex) first.pullback) ≪≫
    Functor.isoWhiskerLeft family
      (branchComparison (diagram := diagram) first second) ≪≫
    (Functor.associator family
      (evaluation (diagram := diagram) second.vertex) second.pullback).symm
  have comparisonCoprojection :
      colimit.ι
            ((family ⋙ evaluation (diagram := diagram) first.vertex) ⋙
              first.pullback) index ≫
          (HasColimit.isoOfNatIso comparison).hom =
        ((family.obj index).glue first second).hom ≫
          colimit.ι
            ((family ⋙ evaluation (diagram := diagram) second.vertex) ⋙
              second.pullback) index := by
    simp [comparison, branchComparison]
  symm
  calc
    first.pullback.map
          (colimit.ι
            (family ⋙ evaluation (diagram := diagram) first.vertex)
            index) ≫
        (colimitGlue (diagram := diagram) family first second).hom =
      (first.pullback.map
            (colimit.ι
              (family ⋙ evaluation (diagram := diagram) first.vertex)
              index) ≫
          (preservesColimitIso first.pullback
            (family ⋙ evaluation (diagram := diagram) first.vertex)).hom) ≫
        (HasColimit.isoOfNatIso comparison).hom ≫
        (preservesColimitIso second.pullback
          (family ⋙ evaluation (diagram := diagram) second.vertex)).inv := by
      simp only [colimitGlue, comparison, Iso.trans_hom, Iso.symm_hom,
        Category.assoc]
    _ = colimit.ι
          ((family ⋙ evaluation (diagram := diagram) first.vertex) ⋙
            first.pullback) index ≫
        (HasColimit.isoOfNatIso comparison).hom ≫
        (preservesColimitIso second.pullback
          (family ⋙ evaluation (diagram := diagram) second.vertex)).inv := by
      rw [ι_preservesColimitIso_hom first.pullback
        (family ⋙ evaluation (diagram := diagram) first.vertex) index]
    _ = (((family.obj index).glue first second).hom ≫
          colimit.ι
            ((family ⋙ evaluation (diagram := diagram) second.vertex) ⋙
              second.pullback) index) ≫
        (preservesColimitIso second.pullback
          (family ⋙ evaluation (diagram := diagram) second.vertex)).inv := by
      simpa only [Category.assoc] using congrArg
        (fun morphism => morphism ≫
          (preservesColimitIso second.pullback
            (family ⋙ evaluation (diagram := diagram) second.vertex)).inv)
        comparisonCoprojection
    _ = ((family.obj index).glue first second).hom ≫
        (colimit.ι
            ((family ⋙ evaluation (diagram := diagram) second.vertex) ⋙
              second.pullback) index ≫
          (preservesColimitIso second.pullback
            (family ⋙ evaluation (diagram := diagram) second.vertex)).inv) :=
      Category.assoc _ _ _
    _ = ((family.obj index).glue first second).hom ≫
        second.pullback.map
          (colimit.ι
            (family ⋙ evaluation (diagram := diagram) second.vertex)
            index) := by
      rw [ι_preservesColimitIso_inv second.pullback
        (family ⋙ evaluation (diagram := diagram) second.vertex) index]

set_option backward.isDefEq.respectTransparency false in
lemma colimitGlue_refl
    (family : J ⥤ diagram.GluedObject) [HasPointwiseColimit family]
    {edge : diagram.base.Edge}
    (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    colimitGlue (diagram := diagram) family branch branch = Iso.refl _ := by
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.vertexAnabelioid branch.vertex).galoisCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI : PreservesFiniteColimits branch.pullback :=
    (diagram.branchMorphism branch.branch branch.abuts).preservesFiniteColimits
  letI : HasColimit
      ((family ⋙ evaluation (diagram := diagram) branch.vertex) ⋙
        branch.pullback) :=
    hasColimitCompOfPreserves
      (family ⋙ evaluation (diagram := diagram) branch.vertex) branch.pullback
  apply Iso.ext
  apply (isColimitOfPreserves branch.pullback
    (colimit.isColimit
      (family ⋙ evaluation (diagram := diagram) branch.vertex))).hom_ext
  intro index
  simp only [Functor.mapCocone_ι_app]
  calc
    branch.pullback.map
          (colimit.ι
            (family ⋙ evaluation (diagram := diagram) branch.vertex)
            index) ≫
        (colimitGlue (diagram := diagram) family branch branch).hom =
      ((family.obj index).glue branch branch).hom ≫
        branch.pullback.map
          (colimit.ι
            (family ⋙ evaluation (diagram := diagram) branch.vertex)
            index) :=
      (colimitGlue_map_ι
        (diagram := diagram) family branch branch index).symm
    _ = branch.pullback.map
          (colimit.ι
            (family ⋙ evaluation (diagram := diagram) branch.vertex)
            index) ≫ (Iso.refl _).hom := by
      rw [(family.obj index).glue_refl branch]
      exact (Category.id_comp _).trans (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
lemma colimitGlue_trans
    (family : J ⥤ diagram.GluedObject) [HasPointwiseColimit family]
    {edge : diagram.base.Edge}
    (first second third : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.vertexAnabelioid third.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (colimitGlue (diagram := diagram) family first second).trans
        (colimitGlue (diagram := diagram) family second third) =
      colimitGlue (diagram := diagram) family first third := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.vertexAnabelioid third.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.vertexAnabelioid first.vertex).galoisCategory
  letI := (diagram.vertexAnabelioid second.vertex).galoisCategory
  letI := (diagram.vertexAnabelioid third.vertex).galoisCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI : PreservesFiniteColimits first.pullback :=
    (diagram.branchMorphism first.branch first.abuts).preservesFiniteColimits
  letI : PreservesFiniteColimits second.pullback :=
    (diagram.branchMorphism second.branch second.abuts).preservesFiniteColimits
  letI : PreservesFiniteColimits third.pullback :=
    (diagram.branchMorphism third.branch third.abuts).preservesFiniteColimits
  letI : HasColimit
      ((family ⋙ evaluation (diagram := diagram) first.vertex) ⋙
        first.pullback) :=
    hasColimitCompOfPreserves
      (family ⋙ evaluation (diagram := diagram) first.vertex) first.pullback
  apply Iso.ext
  apply (isColimitOfPreserves first.pullback
    (colimit.isColimit
      (family ⋙ evaluation (diagram := diagram) first.vertex))).hom_ext
  intro index
  simp only [Iso.trans_hom, Functor.mapCocone_ι_app]
  let firstCoprojection := colimit.ι
    (family ⋙ evaluation (diagram := diagram) first.vertex) index
  let secondCoprojection := colimit.ι
    (family ⋙ evaluation (diagram := diagram) second.vertex) index
  let thirdCoprojection := colimit.ι
    (family ⋙ evaluation (diagram := diagram) third.vertex) index
  calc
    first.pullback.map firstCoprojection ≫
          (colimitGlue (diagram := diagram) family first second).hom ≫
          (colimitGlue (diagram := diagram) family second third).hom =
      (first.pullback.map firstCoprojection ≫
          (colimitGlue (diagram := diagram) family first second).hom) ≫
        (colimitGlue (diagram := diagram) family second third).hom :=
      (Category.assoc _ _ _).symm
    _ =
      (((family.obj index).glue first second).hom ≫
          second.pullback.map secondCoprojection) ≫
        (colimitGlue (diagram := diagram) family second third).hom := by
      rw [colimitGlue_map_ι]
    _ = ((family.obj index).glue first second).hom ≫
        (second.pullback.map secondCoprojection ≫
          (colimitGlue (diagram := diagram) family second third).hom) :=
      Category.assoc _ _ _
    _ = ((family.obj index).glue first second).hom ≫
        (((family.obj index).glue second third).hom ≫
          third.pullback.map thirdCoprojection) := by
      rw [colimitGlue_map_ι]
    _ = (((family.obj index).glue first second).hom ≫
          ((family.obj index).glue second third).hom) ≫
        third.pullback.map thirdCoprojection :=
      (Category.assoc _ _ _).symm
    _ = ((family.obj index).glue first third).hom ≫
        third.pullback.map thirdCoprojection := by
      rw [← Iso.trans_hom]
      rw [(family.obj index).glue_trans first second third]
    _ = first.pullback.map firstCoprojection ≫
        (colimitGlue (diagram := diagram) family first third).hom :=
      colimitGlue_map_ι (diagram := diagram) family first third index

/-- The pointwise finite colimit, equipped with canonical edge gluing. -/
noncomputable def colimitObject
    (family : J ⥤ diagram.GluedObject) [HasPointwiseColimit family] :
    diagram.GluedObject where
  vertexObject := colimitVertexObject (diagram := diagram) family
  glue := colimitGlue (diagram := diagram) family
  glue_refl := colimitGlue_refl (diagram := diagram) family
  glue_trans := colimitGlue_trans (diagram := diagram) family

/-- One leg of the pointwise colimiting cocone. -/
noncomputable def colimitInjection
    (family : J ⥤ diagram.GluedObject) [HasPointwiseColimit family]
    (index : J) :
    family.obj index ⟶ colimitObject (diagram := diagram) family where
  app := fun vertex => by
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    letI := (diagram.vertexAnabelioid vertex).galoisCategory
    exact colimit.ι
      (family ⋙ evaluation (diagram := diagram) vertex) index
  naturality := by
    intro edge first second
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    letI := (diagram.vertexAnabelioid first.vertex).galoisCategory
    letI := (diagram.vertexAnabelioid second.vertex).galoisCategory
    letI := (diagram.edgeAnabelioid edge).galoisCategory
    letI : PreservesFiniteColimits first.pullback :=
      (diagram.branchMorphism first.branch first.abuts).preservesFiniteColimits
    letI : PreservesFiniteColimits second.pullback :=
      (diagram.branchMorphism second.branch second.abuts).preservesFiniteColimits
    exact colimitGlue_map_ι
      (diagram := diagram) family first second index

/-- The pointwise colimiting cocone of a supported finite diagram of glued
objects. -/
noncomputable def colimitCocone
    (family : J ⥤ diagram.GluedObject) [HasPointwiseColimit family] :
    Cocone family where
  pt := colimitObject (diagram := diagram) family
  ι :=
    { app := colimitInjection (diagram := diagram) family
      naturality := by
        intro first second morphism
        apply Hom.ext
        intro vertex
        letI := (diagram.vertexAnabelioid vertex).coverCategory
        letI := (diagram.vertexAnabelioid vertex).galoisCategory
        simpa [colimitInjection] using
          colimit.w
            (family ⋙ evaluation (diagram := diagram) vertex) morphism }

/-- The constituentwise descent morphism from the pointwise colimit to any
cocone point. -/
noncomputable def colimitDesc
    (family : J ⥤ diagram.GluedObject) [HasPointwiseColimit family]
    (cocone : Cocone family) :
    colimitObject (diagram := diagram) family ⟶ cocone.pt where
  app := fun vertex => by
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    letI := (diagram.vertexAnabelioid vertex).galoisCategory
    exact colimit.desc
      (family ⋙ evaluation (diagram := diagram) vertex)
      ((evaluation (diagram := diagram) vertex).mapCocone cocone)
  naturality := by
    intro edge first second
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    letI := (diagram.vertexAnabelioid first.vertex).galoisCategory
    letI := (diagram.vertexAnabelioid second.vertex).galoisCategory
    letI := (diagram.edgeAnabelioid edge).galoisCategory
    letI : PreservesFiniteColimits first.pullback :=
      (diagram.branchMorphism first.branch first.abuts).preservesFiniteColimits
    letI : PreservesFiniteColimits second.pullback :=
      (diagram.branchMorphism second.branch second.abuts).preservesFiniteColimits
    letI : HasColimit
        ((family ⋙ evaluation (diagram := diagram) first.vertex) ⋙
          first.pullback) :=
      hasColimitCompOfPreserves
        (family ⋙ evaluation (diagram := diagram) first.vertex) first.pullback
    apply (isColimitOfPreserves first.pullback
      (colimit.isColimit
        (family ⋙ evaluation (diagram := diagram) first.vertex))).hom_ext
    intro index
    simp only [Functor.mapCocone_ι_app]
    let firstVertexCocone :=
      (evaluation (diagram := diagram) first.vertex).mapCocone cocone
    let secondVertexCocone :=
      (evaluation (diagram := diagram) second.vertex).mapCocone cocone
    let firstInjection := colimit.ι
      (family ⋙ evaluation (diagram := diagram) first.vertex) index
    let secondInjection := colimit.ι
      (family ⋙ evaluation (diagram := diagram) second.vertex) index
    let firstDesc := colimit.desc
      (family ⋙ evaluation (diagram := diagram) first.vertex)
      firstVertexCocone
    let secondDesc := colimit.desc
      (family ⋙ evaluation (diagram := diagram) second.vertex)
      secondVertexCocone
    let firstCoconeInjection :
        (family.obj index).vertexObject first.vertex ⟶
          cocone.pt.vertexObject first.vertex :=
      (cocone.ι.app index).app first.vertex
    let secondCoconeInjection :
        (family.obj index).vertexObject second.vertex ⟶
          cocone.pt.vertexObject second.vertex :=
      (cocone.ι.app index).app second.vertex
    have firstInjectionDesc :
        firstInjection ≫ firstDesc =
          firstCoconeInjection := by
      exact colimit.ι_desc firstVertexCocone index
    have secondInjectionDesc :
        secondInjection ≫ secondDesc =
          secondCoconeInjection := by
      exact colimit.ι_desc secondVertexCocone index
    have coconeInjectionNaturality :
        ((family.obj index).glue first second).hom ≫
            second.pullback.map secondCoconeInjection =
          first.pullback.map firstCoconeInjection ≫
            (cocone.pt.glue first second).hom :=
      (cocone.ι.app index).naturality first second
    have leftReduction :
        first.pullback.map firstInjection ≫
            ((colimitGlue (diagram := diagram) family first second).hom ≫
              second.pullback.map secondDesc) =
          ((family.obj index).glue first second).hom ≫
            second.pullback.map secondCoconeInjection := by
      rw [← Category.assoc]
      rw [← colimitGlue_map_ι]
      calc
        (((family.obj index).glue first second).hom ≫
              second.pullback.map secondInjection) ≫
            second.pullback.map secondDesc =
          ((family.obj index).glue first second).hom ≫
            (second.pullback.map secondInjection ≫
              second.pullback.map secondDesc) :=
          Category.assoc _ _ _
        _ = ((family.obj index).glue first second).hom ≫
            second.pullback.map (secondInjection ≫ secondDesc) := by
          rw [Functor.map_comp]
        _ = ((family.obj index).glue first second).hom ≫
            second.pullback.map secondCoconeInjection := by
          exact congrArg
            (fun morphism =>
              ((family.obj index).glue first second).hom ≫
                second.pullback.map morphism)
            secondInjectionDesc
    have rightReduction :
        first.pullback.map firstInjection ≫
            (first.pullback.map firstDesc ≫
              (cocone.pt.glue first second).hom) =
          first.pullback.map firstCoconeInjection ≫
            (cocone.pt.glue first second).hom := by
      rw [← Category.assoc, ← Functor.map_comp, firstInjectionDesc]
      rfl
    exact leftReduction.trans <|
      coconeInjectionNaturality.trans rightReduction.symm

/-- The pointwise cocone satisfies the universal property of its supported
finite colimit. -/
noncomputable def colimitCoconeIsColimit
    (family : J ⥤ diagram.GluedObject) [HasPointwiseColimit family] :
    IsColimit (colimitCocone (diagram := diagram) family) where
  desc cocone := colimitDesc (diagram := diagram) family cocone
  fac cocone index := by
    apply Hom.ext
    intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    letI := (diagram.vertexAnabelioid vertex).galoisCategory
    exact colimit.ι_desc
      ((evaluation (diagram := diagram) vertex).mapCocone cocone) index
  uniq cocone morphism factorization := by
    apply Hom.ext
    intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    letI := (diagram.vertexAnabelioid vertex).galoisCategory
    apply colimit.hom_ext
    intro index
    have componentEquality := congrArg
      (fun component : family.obj index ⟶ cocone.pt => component.app vertex)
      (factorization index)
    change colimit.ι
          (family ⋙ evaluation (diagram := diagram) vertex) index ≫
        morphism.app vertex =
      (cocone.ι.app index).app vertex at componentEquality
    exact componentEquality.trans <|
      (colimit.ι_desc
        ((evaluation (diagram := diagram) vertex).mapCocone cocone)
        index).symm

/-- A supported finite diagram has the constructed pointwise colimit. -/
noncomputable instance hasColimit
    (family : J ⥤ diagram.GluedObject) [HasPointwiseColimit family] :
    HasColimit family :=
  HasColimit.mk
    { cocone := colimitCocone (diagram := diagram) family
      isColimit := colimitCoconeIsColimit (diagram := diagram) family }

end FiniteColimits

/-- Constituent pre-Galois categories supply the pointwise colimits for a
finite discrete diagram. -/
noncomputable instance hasPointwiseFiniteCoproduct
    (n : Nat) (family : Discrete (Fin n) ⥤ diagram.GluedObject) :
    HasPointwiseColimit family where
  hasColimit vertex := by
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    letI := (diagram.vertexAnabelioid vertex).galoisCategory
    infer_instance

/-- The glued category has all finite coproducts, computed in each verticial
constituent. -/
noncomputable instance hasFiniteCoproducts :
    HasFiniteCoproducts diagram.GluedObject where
  out n :=
    { has_colimit := fun family => by
        exact hasColimit (diagram := diagram) family }

/-- Vertex evaluation preserves finite coproducts because both the cocone and
its universal property were constructed pointwise. -/
noncomputable instance evaluationPreservesFiniteCoproducts
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    PreservesFiniteCoproducts
      (evaluation (diagram := diagram) vertex) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI := (diagram.vertexAnabelioid vertex).galoisCategory
  exact
    { preserves := fun n =>
        { preservesColimit := fun {family} =>
            preservesColimit_of_preserves_colimit_cocone
              (colimitCoconeIsColimit (diagram := diagram) family)
              (by
                simpa [colimitCocone, colimitInjection, colimitObject,
                  colimitVertexObject] using
                  colimit.isColimit
                    (family ⋙ evaluation (diagram := diagram) vertex)) } }

/-- Constituent pre-Galois categories supply pointwise quotients by a small
finite group. -/
noncomputable instance hasPointwiseFiniteGroupQuotient
    (G : Type) [Group G] [Finite G]
    (family : SingleObj G ⥤ diagram.GluedObject) :
    HasPointwiseColimit family := by
  letI := Fintype.ofFinite G
  exact
    { hasColimit := fun vertex => by
        letI := (diagram.vertexAnabelioid vertex).coverCategory
        letI := (diagram.vertexAnabelioid vertex).galoisCategory
        infer_instance }

/-- Quotients by a finite group are computed in each verticial constituent.
-/
noncomputable instance hasQuotientsByFiniteGroupsSmall
    (G : Type) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) diagram.GluedObject where
  has_colimit family := by
    letI := Fintype.ofFinite G
    exact hasColimit (diagram := diagram) family

/-- Vertex evaluation preserves the pointwise quotient by a small finite
group. -/
noncomputable instance evaluationPreservesFiniteGroupQuotientSmall
    (vertex : diagram.base.Vertex)
    (G : Type) [Group G] [Finite G] :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    PreservesColimitsOfShape (SingleObj G)
      (evaluation (diagram := diagram) vertex) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI := (diagram.vertexAnabelioid vertex).galoisCategory
  letI := Fintype.ofFinite G
  exact
    { preservesColimit := fun {family} =>
        preservesColimit_of_preserves_colimit_cocone
          (colimitCoconeIsColimit (diagram := diagram) family)
          (by
            simpa [colimitCocone, colimitInjection, colimitObject,
              colimitVertexObject] using
              colimit.isColimit
                (family ⋙ evaluation (diagram := diagram) vertex)) }

/-- The small construction transports finite-group quotients from any
universe to a universe-zero model of the finite group. -/
@[reducible]
noncomputable def hasQuotientsByFiniteGroupsOfFinite
    (G : Type u) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) diagram.GluedObject := by
  let existence :
      ∃ (G' : Type) (_ : Group G') (_ : Fintype G'),
        Nonempty (G ≃* G') :=
    Finite.exists_type_univ_nonempty_mulEquiv G
  obtain ⟨G', groupG', fintypeG', ⟨equivalence⟩⟩ :=
    existence
  letI := groupG'
  letI := fintypeG'
  letI : HasColimitsOfShape (SingleObj G') diagram.GluedObject :=
    hasQuotientsByFiniteGroupsSmall (diagram := diagram) G'
  exact Limits.hasColimitsOfShape_of_equivalence
    equivalence.toSingleObjEquiv.symm

/-- Preservation of finite-group quotients transports from a universe-zero
model of the group. -/
@[reducible]
noncomputable def evaluationPreservesFiniteGroupQuotient
    (vertex : diagram.base.Vertex)
    (G : Type u) [Group G] [Finite G] :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    PreservesColimitsOfShape (SingleObj G)
      (evaluation (diagram := diagram) vertex) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  let existence :
      ∃ (G' : Type) (_ : Group G') (_ : Fintype G'),
        Nonempty (G ≃* G') :=
    Finite.exists_type_univ_nonempty_mulEquiv G
  obtain ⟨G', groupG', fintypeG', ⟨equivalence⟩⟩ := existence
  letI := groupG'
  letI := fintypeG'
  letI : PreservesColimitsOfShape (SingleObj G')
      (evaluation (diagram := diagram) vertex) :=
    evaluationPreservesFiniteGroupQuotientSmall
      (diagram := diagram) vertex G'
  exact Limits.preservesColimitsOfShape_of_equiv
    equivalence.toSingleObjEquiv.symm
    (evaluation (diagram := diagram) vertex)

/-! ## Direct-summand complements -/

section DirectSummands

variable {source target : diagram.GluedObject}
    (inclusion : source ⟶ target) [Mono inclusion]

/-- Every component of a monomorphism of glued objects is a monomorphism. -/
noncomputable instance inclusionAppMono (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    Mono (inclusion.app vertex) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  change Mono ((evaluation (diagram := diagram) vertex).map inclusion)
  infer_instance

/-- The direct-summand complement supplied by the constituent Galois
category at one vertex. -/
noncomputable def complementVertexObject
    (vertex : diagram.base.Vertex) :
    (diagram.vertexAnabelioid vertex).Cover := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI := (diagram.vertexAnabelioid vertex).galoisCategory
  exact Classical.choose
    (PreGaloisCategory.monoInducesIsoOnDirectSummand
      (inclusion.app vertex))

/-- Inclusion of the chosen constituent complement. -/
noncomputable def complementVertexInclusion
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    complementVertexObject (diagram := diagram) inclusion vertex ⟶
      target.vertexObject vertex := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI := (diagram.vertexAnabelioid vertex).galoisCategory
  exact Classical.choose (Classical.choose_spec
    (PreGaloisCategory.monoInducesIsoOnDirectSummand
      (inclusion.app vertex)))

/-- The chosen constituent decomposition is a binary coproduct. -/
noncomputable def complementVertexIsColimit
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    IsColimit (BinaryCofan.mk (inclusion.app vertex)
      (complementVertexInclusion (diagram := diagram) inclusion vertex)) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI := (diagram.vertexAnabelioid vertex).galoisCategory
  exact (Classical.choose_spec (Classical.choose_spec
    (PreGaloisCategory.monoInducesIsoOnDirectSummand
      (inclusion.app vertex)))).some

/-- Pulling a constituent decomposition to an incident edge preserves its
binary-coproduct universal property. -/
noncomputable def complementEdgeIsColimit
    {edge : diagram.base.Edge}
    (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    IsColimit (BinaryCofan.mk
      (branch.pullback.map (inclusion.app branch.vertex))
      (branch.pullback.map
        (complementVertexInclusion
          (diagram := diagram) inclusion branch.vertex))) := by
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI : PreservesFiniteColimits branch.pullback :=
    (diagram.branchMorphism branch.branch branch.abuts).preservesFiniteColimits
  exact mapIsColimitOfPreservesOfIsColimit branch.pullback _ _
    (complementVertexIsColimit (diagram := diagram) inclusion branch.vertex)

/-- The two pulled-back complement pieces on an edge are canonically
isomorphic.  This is the unique comparison commuting with their inclusions
into the glued target. -/
noncomputable def complementGlue
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    first.pullback.obj
        (complementVertexObject
          (diagram := diagram) inclusion first.vertex) ≅
      second.pullback.obj
        (complementVertexObject
          (diagram := diagram) inclusion second.vertex) := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI := (diagram.edgeAnabelioid edge).fiberFunctor
  exact PreGaloisCategory.complementComparisonIso
    (diagram.edgeAnabelioid edge).fiber
    (first.pullback.map (inclusion.app first.vertex))
    (first.pullback.map
      (complementVertexInclusion
        (diagram := diagram) inclusion first.vertex))
    (second.pullback.map (inclusion.app second.vertex))
    (second.pullback.map
      (complementVertexInclusion
        (diagram := diagram) inclusion second.vertex))
    (complementEdgeIsColimit (diagram := diagram) inclusion first)
    (complementEdgeIsColimit (diagram := diagram) inclusion second)
    (source.glue first second) (target.glue first second)
    (inclusion.naturality first second).symm

/-- The complement comparison is characterized by compatibility with the
target gluing. -/
lemma complementGlue_hom_comp
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (complementGlue (diagram := diagram) inclusion first second).hom ≫
        second.pullback.map
          (complementVertexInclusion
            (diagram := diagram) inclusion second.vertex) =
      first.pullback.map
          (complementVertexInclusion
            (diagram := diagram) inclusion first.vertex) ≫
        (target.glue first second).hom := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI := (diagram.edgeAnabelioid edge).fiberFunctor
  exact PreGaloisCategory.complementComparison_comp
    (diagram.edgeAnabelioid edge).fiber
    (first.pullback.map (inclusion.app first.vertex))
    (first.pullback.map
      (complementVertexInclusion
        (diagram := diagram) inclusion first.vertex))
    (second.pullback.map (inclusion.app second.vertex))
    (second.pullback.map
      (complementVertexInclusion
        (diagram := diagram) inclusion second.vertex))
    (complementEdgeIsColimit (diagram := diagram) inclusion first)
    (complementEdgeIsColimit (diagram := diagram) inclusion second)
    (source.glue first second) (target.glue first second)
    (inclusion.naturality first second).symm

lemma complementGlue_hom_comp_assoc
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge)
    {object : (diagram.edgeAnabelioid edge).Cover}
    (morphism :
      letI := (diagram.vertexAnabelioid second.vertex).coverCategory
      letI := (diagram.edgeAnabelioid edge).coverCategory
      second.pullback.obj (target.vertexObject second.vertex) ⟶ object) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (complementGlue (diagram := diagram) inclusion first second).hom ≫
        second.pullback.map
          (complementVertexInclusion
            (diagram := diagram) inclusion second.vertex) ≫ morphism =
      first.pullback.map
          (complementVertexInclusion
            (diagram := diagram) inclusion first.vertex) ≫
        (target.glue first second).hom ≫ morphism := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  rw [← Category.assoc, complementGlue_hom_comp]
  rw [Category.assoc]

/-- Canonical complement gluing is the identity on a repeated branch. -/
lemma complementGlue_refl
    {edge : diagram.base.Edge}
    (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    complementGlue (diagram := diagram) inclusion branch branch = Iso.refl _ := by
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI := (diagram.edgeAnabelioid edge).fiberFunctor
  let complementInclusion := branch.pullback.map
    (complementVertexInclusion
      (diagram := diagram) inclusion branch.vertex)
  letI : Mono complementInclusion :=
    PreGaloisCategory.mono_right_of_isColimit_binaryCofan
      (diagram.edgeAnabelioid edge).fiber _ complementInclusion
      (complementEdgeIsColimit (diagram := diagram) inclusion branch)
  apply Iso.ext
  apply (cancel_mono complementInclusion).1
  rw [complementGlue_hom_comp]
  rw [target.glue_refl branch]
  simp [complementInclusion]

/-- Canonical complement comparisons compose along the branches of an edge.
-/
lemma complementGlue_trans
    {edge : diagram.base.Edge}
    (first second third : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.vertexAnabelioid third.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (complementGlue (diagram := diagram) inclusion first second).trans
        (complementGlue (diagram := diagram) inclusion second third) =
      complementGlue (diagram := diagram) inclusion first third := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.vertexAnabelioid third.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI := (diagram.edgeAnabelioid edge).fiberFunctor
  let thirdInclusion := third.pullback.map
    (complementVertexInclusion
      (diagram := diagram) inclusion third.vertex)
  letI : Mono thirdInclusion :=
    PreGaloisCategory.mono_right_of_isColimit_binaryCofan
      (diagram.edgeAnabelioid edge).fiber _ thirdInclusion
      (complementEdgeIsColimit (diagram := diagram) inclusion third)
  apply Iso.ext
  apply (cancel_mono thirdInclusion).1
  simp only [Iso.trans_hom, Category.assoc]
  rw [complementGlue_hom_comp]
  rw [← Category.assoc, complementGlue_hom_comp]
  rw [Category.assoc]
  rw [← Iso.trans_hom, target.glue_trans first second third]
  exact (complementGlue_hom_comp
    (diagram := diagram) inclusion first third).symm

/-- The pointwise complements with their canonical edge comparisons form a
glued object. -/
noncomputable def complementObject : diagram.GluedObject where
  vertexObject := complementVertexObject (diagram := diagram) inclusion
  glue := complementGlue (diagram := diagram) inclusion
  glue_refl := complementGlue_refl (diagram := diagram) inclusion
  glue_trans := complementGlue_trans (diagram := diagram) inclusion

/-- Inclusion of the glued complement into the target object. -/
noncomputable def complementInclusion :
    complementObject (diagram := diagram) inclusion ⟶ target where
  app := complementVertexInclusion (diagram := diagram) inclusion
  naturality := complementGlue_hom_comp (diagram := diagram) inclusion

/-- Constituentwise descent out of the target decomposition. -/
noncomputable def complementDesc
    (cocone : BinaryCofan source
      (complementObject (diagram := diagram) inclusion)) :
    target ⟶ cocone.pt where
  app := fun vertex => by
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact BinaryCofan.IsColimit.desc
      (complementVertexIsColimit (diagram := diagram) inclusion vertex)
      (cocone.inl.app vertex) (cocone.inr.app vertex)
  naturality := by
    intro edge first second
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    letI : PreservesFiniteColimits first.pullback :=
      (diagram.branchMorphism first.branch first.abuts).preservesFiniteColimits
    let firstColimit :=
      complementVertexIsColimit (diagram := diagram) inclusion first.vertex
    let secondColimit :=
      complementVertexIsColimit (diagram := diagram) inclusion second.vertex
    let firstEdgeColimit :=
      complementEdgeIsColimit (diagram := diagram) inclusion first
    have firstInlDesc :
        inclusion.app first.vertex ≫
            BinaryCofan.IsColimit.desc firstColimit
              (cocone.inl.app first.vertex)
              (cocone.inr.app first.vertex) =
          cocone.inl.app first.vertex := by
      exact BinaryCofan.IsColimit.inl_desc firstColimit _ _
    have secondInlDesc :
        inclusion.app second.vertex ≫
            BinaryCofan.IsColimit.desc secondColimit
              (cocone.inl.app second.vertex)
              (cocone.inr.app second.vertex) =
          cocone.inl.app second.vertex := by
      exact BinaryCofan.IsColimit.inl_desc secondColimit _ _
    have firstInrDesc :
        complementVertexInclusion
              (diagram := diagram) inclusion first.vertex ≫
            BinaryCofan.IsColimit.desc
              (complementVertexIsColimit
                (diagram := diagram) inclusion first.vertex)
              (cocone.inl.app first.vertex)
              (cocone.inr.app first.vertex) =
          cocone.inr.app first.vertex := by
      exact BinaryCofan.IsColimit.inr_desc
        (complementVertexIsColimit
          (diagram := diagram) inclusion first.vertex) _ _
    have secondInrDesc :
        complementVertexInclusion
              (diagram := diagram) inclusion second.vertex ≫
            BinaryCofan.IsColimit.desc
              (complementVertexIsColimit
                (diagram := diagram) inclusion second.vertex)
              (cocone.inl.app second.vertex)
              (cocone.inr.app second.vertex) =
          cocone.inr.app second.vertex := by
      exact BinaryCofan.IsColimit.inr_desc
        (complementVertexIsColimit
          (diagram := diagram) inclusion second.vertex) _ _
    have complementNaturality :
        (complementGlue (diagram := diagram) inclusion first second).hom ≫
            second.pullback.map (cocone.inr.app second.vertex) =
          first.pullback.map (cocone.inr.app first.vertex) ≫
            (cocone.pt.glue first second).hom := by
      simpa [complementObject] using
        cocone.inr.naturality first second
    apply BinaryCofan.IsColimit.hom_ext firstEdgeColimit
    · simp only [BinaryCofan.mk_pt, BinaryCofan.mk_inl]
      calc
        first.pullback.map (inclusion.app first.vertex) ≫
              (target.glue first second).hom ≫
              second.pullback.map
                (BinaryCofan.IsColimit.desc secondColimit
                  (cocone.inl.app second.vertex)
                  (cocone.inr.app second.vertex)) =
            ((source.glue first second).hom ≫
              second.pullback.map (inclusion.app second.vertex)) ≫
              second.pullback.map
                (BinaryCofan.IsColimit.desc secondColimit
                  (cocone.inl.app second.vertex)
                  (cocone.inr.app second.vertex)) := by
          rw [← Category.assoc, ← inclusion.naturality first second]
        _ = (source.glue first second).hom ≫
              second.pullback.map
                (inclusion.app second.vertex ≫
                  BinaryCofan.IsColimit.desc secondColimit
                    (cocone.inl.app second.vertex)
                    (cocone.inr.app second.vertex)) := by
          simp only [Functor.map_comp, Category.assoc]
        _ = (source.glue first second).hom ≫
              second.pullback.map (cocone.inl.app second.vertex) := by
          rw [secondInlDesc]
        _ = first.pullback.map (inclusion.app first.vertex) ≫
              first.pullback.map
                (BinaryCofan.IsColimit.desc firstColimit
                  (cocone.inl.app first.vertex)
                  (cocone.inr.app first.vertex)) ≫
              (cocone.pt.glue first second).hom := by
          rw [← Category.assoc, ← Functor.map_comp, firstInlDesc]
          exact cocone.inl.naturality first second
    · simp only [BinaryCofan.mk_pt, BinaryCofan.mk_inr]
      let secondDesc := BinaryCofan.IsColimit.desc
        (complementVertexIsColimit
          (diagram := diagram) inclusion second.vertex)
        (cocone.inl.app second.vertex) (cocone.inr.app second.vertex)
      let firstDesc := BinaryCofan.IsColimit.desc
        (complementVertexIsColimit
          (diagram := diagram) inclusion first.vertex)
        (cocone.inl.app first.vertex) (cocone.inr.app first.vertex)
      have stepOne :
          first.pullback.map
                (complementVertexInclusion
                  (diagram := diagram) inclusion first.vertex) ≫
              (target.glue first second).hom ≫
              second.pullback.map secondDesc =
            (complementGlue
                (diagram := diagram) inclusion first second).hom ≫
              second.pullback.map
                (complementVertexInclusion
                  (diagram := diagram) inclusion second.vertex) ≫
              second.pullback.map secondDesc :=
        (complementGlue_hom_comp_assoc
          (diagram := diagram) inclusion first second
          (second.pullback.map secondDesc)).symm
      have stepTwo :
          (complementGlue
                (diagram := diagram) inclusion first second).hom ≫
              second.pullback.map
                (complementVertexInclusion
                  (diagram := diagram) inclusion second.vertex) ≫
              second.pullback.map secondDesc =
            (complementGlue
                (diagram := diagram) inclusion first second).hom ≫
              second.pullback.map (cocone.inr.app second.vertex) := by
        simp only [← Functor.map_comp]
        rw [secondInrDesc]
        rfl
      have stepFour :
          first.pullback.map (cocone.inr.app first.vertex) ≫
              (cocone.pt.glue first second).hom =
            first.pullback.map
                (complementVertexInclusion
                  (diagram := diagram) inclusion first.vertex) ≫
              first.pullback.map firstDesc ≫
              (cocone.pt.glue first second).hom := by
        simp only [← Category.assoc, ← Functor.map_comp]
        rw [firstInrDesc]
        rfl
      exact stepOne.trans <| stepTwo.trans <|
        complementNaturality.trans stepFour

/-- The inclusion and its glued complement exhibit the target as their
binary coproduct. -/
noncomputable def complementCofanIsColimit :
    IsColimit (BinaryCofan.mk inclusion
      (complementInclusion (diagram := diagram) inclusion)) :=
  BinaryCofan.isColimitMk
    (complementDesc (diagram := diagram) inclusion)
    (fun cocone => by
      apply Hom.ext
      intro vertex
      letI := (diagram.vertexAnabelioid vertex).coverCategory
      exact BinaryCofan.IsColimit.inl_desc
        (complementVertexIsColimit (diagram := diagram) inclusion vertex)
        (cocone.inl.app vertex) (cocone.inr.app vertex))
    (fun cocone => by
      apply Hom.ext
      intro vertex
      letI := (diagram.vertexAnabelioid vertex).coverCategory
      exact BinaryCofan.IsColimit.inr_desc
        (complementVertexIsColimit (diagram := diagram) inclusion vertex)
        (cocone.inl.app vertex) (cocone.inr.app vertex))
    (fun cocone morphism left right => by
      apply Hom.ext
      intro vertex
      letI := (diagram.vertexAnabelioid vertex).coverCategory
      apply BinaryCofan.IsColimit.hom_ext
        (complementVertexIsColimit (diagram := diagram) inclusion vertex)
      · have component := congrArg
          (fun arrow : source ⟶ cocone.pt => arrow.app vertex) left
        exact component.trans
          (BinaryCofan.IsColimit.inl_desc
            (complementVertexIsColimit
              (diagram := diagram) inclusion vertex)
            (cocone.inl.app vertex) (cocone.inr.app vertex)).symm
      · have component := congrArg
          (fun arrow : complementObject (diagram := diagram) inclusion ⟶
            cocone.pt => arrow.app vertex) right
        exact component.trans
          (BinaryCofan.IsColimit.inr_desc
            (complementVertexIsColimit
              (diagram := diagram) inclusion vertex)
            (cocone.inl.app vertex) (cocone.inr.app vertex)).symm)

end DirectSummands

/-- The verticial glued category satisfies the three structural axioms of a
pre-Galois category.  The direct-summand axiom is the only non-pointwise
part: its constituent complements are glued by their canonical comparisons.
-/
noncomputable instance preGaloisCategory :
    PreGaloisCategory diagram.GluedObject where
  hasTerminal := inferInstance
  hasPullbacks := inferInstance
  hasFiniteCoproducts := inferInstance
  hasQuotientsByFiniteGroups G _ _ :=
    hasQuotientsByFiniteGroupsOfFinite (diagram := diagram) G
  monoInducesIsoOnDirectSummand inclusion _ :=
    ⟨complementObject (diagram := diagram) inclusion,
      complementInclusion (diagram := diagram) inclusion,
      ⟨complementCofanIsColimit (diagram := diagram) inclusion⟩⟩

end GluedObject

end SourceSemiGraphOfAnabelioids

end Iut
