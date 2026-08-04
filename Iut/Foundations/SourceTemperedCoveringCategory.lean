/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceGluedFiniteEtaleCover
import Iut.Foundations.SourceTemperedDeckGroup
import Iut.Foundations.SourceTemperoid

/-!
# Geometric tempered coverings of a semi-graph of anabelioids

This file constructs the geometric category occurring in *Semi-graphs of
Anabelioids*, Definition 3.5 and Proposition 3.6(ii).  It deliberately keeps
the geometric construction separate from `SourceTemperoidAction`:

* `CovObject` is the literal countable constituent covering data
  `{S_v, phi_e}` defining `B^cov(G)`;
* `coverSemiGraph` is the covering semi-graph naturally associated to that
  data;
* the tempered full subcategory and its comparison with the action category
  are constructed below from the combinatorial universal covers.

Thus the eventual equivalence with continuous actions is a theorem about the
geometric category, not its definition.
-/

namespace Iut

universe u

open CategoryTheory
open scoped SourceCountableTypeCatDiscrete

namespace EtaleFundamentalGroup

/-- The finite-cover category of a connected anabelioid, embedded in its
temperification. -/
noncomputable def finiteTemperification (data : EtaleFundamentalGroup.{u}) :
    letI := data.coverCategory
    data.Cover ⥤ SourceTemperoidAction data.group := by
  letI := data.coverCategory
  exact (coverActionEquivalence data).functor ⋙
    SourceTemperoidAction.finiteInclusion data.group

noncomputable instance finiteTemperificationFull
    (data : EtaleFundamentalGroup.{u}) :
    letI := data.coverCategory
    data.finiteTemperification.Full := by
  letI := data.coverCategory
  change ((coverActionEquivalence data).functor ⋙
    SourceTemperoidAction.finiteInclusion data.group).Full
  infer_instance

noncomputable instance finiteTemperificationFaithful
    (data : EtaleFundamentalGroup.{u}) :
    letI := data.coverCategory
    data.finiteTemperification.Faithful := by
  letI := data.coverCategory
  change ((coverActionEquivalence data).functor ⋙
    SourceTemperoidAction.finiteInclusion data.group).Faithful
  infer_instance

end EtaleFundamentalGroup

namespace SourcePointedAnabelioidHom

/-- Exact pullback and restriction along the derived fundamental-group map
agree after passing from finite covers to countable constituent covers. -/
noncomputable def finiteTemperificationPullbackIso
    {source target : EtaleFundamentalGroup.{u}}
    (morphism : SourcePointedAnabelioidHom source target) :
    letI := source.coverCategory
    letI := target.coverCategory
    morphism.pullback ⋙ source.finiteTemperification ≅
      target.finiteTemperification ⋙
        ContAction.res SourceCountableTypeCat
          morphism.fundamentalGroupHom.hom := by
  letI := source.coverCategory
  letI := target.coverCategory
  letI := source.galoisCategory
  letI := target.galoisCategory
  letI := source.fiberFunctor
  letI := target.fiberFunctor
  refine NatIso.ofComponents (fun object ↦ ?_) ?_
  · apply ObjectProperty.isoMk
    refine Action.mkIso ?_ (comm := ?_)
    · exact
        { hom := SourceCountableTypeCat.homMk
            (morphism.fiberIso.hom.app object)
          inv := SourceCountableTypeCat.homMk
            (morphism.fiberIso.inv.app object)
          hom_inv_id := by
            apply ConcreteCategory.hom_ext
            intro point
            exact FintypeCat.hom_inv_id_apply
              (morphism.fiberIso.app object) point
          inv_hom_id := by
            apply ConcreteCategory.hom_ext
            intro point
            exact FintypeCat.inv_hom_id_apply
              (morphism.fiberIso.app object) point }
    · intro element
      apply ConcreteCategory.hom_ext
      intro point
      change morphism.fiberIso.hom.app object
          ((certifiedFundamentalGroupEquiv source element).hom.app _ point) =
        ((certifiedFundamentalGroupEquiv target
          (morphism.fundamentalGroupHom element)).hom.app _)
            (morphism.fiberIso.hom.app object point)
      rw [morphism.certifiedFundamentalGroupEquiv_fundamentalGroupHom]
      exact (morphism.fiberIso_equivariant
        (certifiedFundamentalGroupEquiv source element) object point).symm
  · intro first second map
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    exact ConcreteCategory.congr_hom
      (morphism.fiberIso.hom.naturality map) point

end SourcePointedAnabelioidHom

namespace SourceSemiGraphOfAnabelioids

variable (diagram : Iut.SourceSemiGraphOfAnabelioids.{u})

/-- Pull a countable constituent cover from a vertex to an incident edge.
This is restriction along the fundamental-group homomorphism derived from
the pointed branch morphism. -/
noncomputable def IncidentBranch.temperoidPullback
    {edge : diagram.base.Edge}
    (incident : diagram.IncidentBranch edge) :
    SourceTemperoidAction.{u, u}
        (diagram.vertexAnabelioid incident.vertex).group ⥤
      SourceTemperoidAction.{u, u} (diagram.edgeAnabelioid edge).group :=
  ContAction.res SourceCountableTypeCat
    (diagram.branchMorphism incident.branch incident.abuts).fundamentalGroupHom.hom

/-- The literal object data `{S_v, phi_e}` of `B^cov(G)` in the verticial
case.  Each constituent object is a countable discrete continuous action,
i.e. an object of the temperification of the constituent anabelioid. -/
structure CovObject where
  vertexObject :
    ∀ vertex, SourceTemperoidAction.{u, u}
      (diagram.vertexAnabelioid vertex).group
  glue :
    ∀ {edge} (first second : diagram.IncidentBranch edge),
      first.temperoidPullback.obj (vertexObject first.vertex) ≅
        second.temperoidPullback.obj (vertexObject second.vertex)
  glue_refl :
    ∀ {edge} (branch : diagram.IncidentBranch edge),
      glue branch branch = Iso.refl _
  glue_trans :
    ∀ {edge} (first second third : diagram.IncidentBranch edge),
      (glue first second).trans (glue second third) = glue first third

namespace CovObject

variable {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}

/-- A morphism of countable glued covers is a constituentwise morphism
commuting with every edge-gluing isomorphism. -/
structure Hom (source target : diagram.CovObject) where
  app : ∀ vertex, source.vertexObject vertex ⟶ target.vertexObject vertex
  naturality :
    ∀ {edge} (first second : diagram.IncidentBranch edge),
      (source.glue first second).hom ≫
          second.temperoidPullback.map (app second.vertex) =
        first.temperoidPullback.map (app first.vertex) ≫
          (target.glue first second).hom

namespace Hom

variable {source middle target : diagram.CovObject}

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

/-- Identity morphism of geometric countable covers. -/
def id (source : diagram.CovObject) : Hom source source where
  app := fun _ ↦ 𝟙 _
  naturality := by simp

/-- Composition of geometric countable-cover morphisms. -/
def comp (first : Hom source middle) (second : Hom middle target) :
    Hom source target where
  app := fun vertex ↦ first.app vertex ≫ second.app vertex
  naturality := by
    intro edge left right
    rw [Functor.map_comp, Functor.map_comp]
    rw [← Category.assoc, first.naturality left right]
    rw [Category.assoc, second.naturality left right]
    rw [← Category.assoc]

end Hom

/-- `B^cov(G)` in the verticial case, as a literal category of gluing data. -/
instance category : Category diagram.CovObject where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro source target morphism
    ext vertex
    simp [Hom.comp, Hom.id]
  comp_id := by
    intro source target morphism
    ext vertex
    simp [Hom.comp, Hom.id]
  assoc := by
    intro first second third fourth f g h
    ext vertex
    simp [Hom.comp, Category.assoc]

@[simp]
theorem id_app (source : diagram.CovObject) (vertex : diagram.base.Vertex) :
    Hom.app (𝟙 source) vertex = 𝟙 _ :=
  rfl

@[simp]
theorem comp_app {source middle target : diagram.CovObject}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (vertex : diagram.base.Vertex) :
    Hom.app (first ≫ second) vertex =
      Hom.app first vertex ≫ Hom.app second vertex :=
  rfl

/-- A geometric cover `target` is a subcover of `source` when the structural
map to the base factors through an actual morphism `source ⟶ target` in
`B^cov(G)`.  Since every object of `CovObject` already lies over the fixed
base diagram, this is exactly the factorization datum used in the proof of
Proposition 3.6(ii). -/
def IsSubcoverOf (target source : diagram.CovObject) : Prop :=
  Nonempty (source ⟶ target)

/-- A displayed morphism from a dominating cover exhibits its codomain as a
subcover. -/
theorem isSubcoverOf_of_hom {source target : diagram.CovObject}
    (map : source ⟶ target) : IsSubcoverOf target source :=
  ⟨map⟩

/-- Evaluation of a geometric countable cover at a vertex constituent. -/
def evaluation (vertex : diagram.base.Vertex) :
    diagram.CovObject ⥤
      SourceTemperoidAction (diagram.vertexAnabelioid vertex).group where
  obj object := object.vertexObject vertex
  map morphism := morphism.app vertex
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## The associated covering semi-graph -/

/-- Orbit components of a countable continuous group action. -/
abbrev ActionComponent {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (object : SourceTemperoidAction G) : Type u :=
  MulAction.orbitRel.Quotient G object.obj.V.obj

noncomputable instance actionComponentCountable
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction G) : Countable (ActionComponent object) :=
  inferInstance

/-- An equivariant morphism sends orbit components to orbit components. -/
noncomputable def actionComponentMap
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {first second : SourceTemperoidAction G} (map : first ⟶ second) :
    ActionComponent first → ActionComponent second :=
  Quotient.map' map.hom.hom (by
    intro firstPoint secondPoint relation
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at relation ⊢
    obtain ⟨element, equality⟩ := relation
    refine ⟨element, ?_⟩
    rw [← equality]
    have hnatural :=
      (ConcreteCategory.congr_hom (map.hom.comm element) secondPoint).symm
    change
      element • map.hom.hom secondPoint =
        map.hom.hom (element • secondPoint) at hnatural
    exact hnatural)

@[simp]
theorem actionComponentMap_mk
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {first second : SourceTemperoidAction G} (map : first ⟶ second)
    (point : first.obj.V.obj) :
    actionComponentMap map (Quotient.mk'' point) =
      Quotient.mk'' (map.hom.hom point) :=
  rfl

/-- Component maps preserve composition of equivariant morphisms. -/
theorem actionComponentMap_comp
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {first second third : SourceTemperoidAction G}
    (firstMap : first ⟶ second) (secondMap : second ⟶ third)
    (component : ActionComponent first) :
    actionComponentMap (firstMap ≫ secondMap) component =
      actionComponentMap secondMap (actionComponentMap firstMap component) := by
  induction component using Quotient.inductionOn' with
  | _ point => rfl

/-- An equivariant isomorphism induces a bijection on orbit components. -/
noncomputable def actionComponentEquiv
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {first second : SourceTemperoidAction G} (identification : first ≅ second) :
    ActionComponent first ≃ ActionComponent second := by
  let forward : ActionComponent first → ActionComponent second :=
    Quotient.map' identification.hom.hom.hom (by
      intro firstPoint secondPoint relation
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at relation ⊢
      obtain ⟨element, equality⟩ := relation
      refine ⟨element, ?_⟩
      rw [← equality]
      have hnatural := (ConcreteCategory.congr_hom
        (identification.hom.hom.comm element) secondPoint).symm
      change
        element • identification.hom.hom.hom secondPoint =
          identification.hom.hom.hom (element • secondPoint) at hnatural
      exact hnatural)
  let reverse : ActionComponent second → ActionComponent first :=
    Quotient.map' identification.inv.hom.hom (by
      intro firstPoint secondPoint relation
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at relation ⊢
      obtain ⟨element, equality⟩ := relation
      refine ⟨element, ?_⟩
      rw [← equality]
      have hnatural := (ConcreteCategory.congr_hom
        (identification.inv.hom.comm element) secondPoint).symm
      change
        element • identification.inv.hom.hom secondPoint =
          identification.inv.hom.hom (element • secondPoint) at hnatural
      exact hnatural)
  exact
    { toFun := forward
      invFun := reverse
      left_inv := by
        intro component
        induction component using Quotient.inductionOn' with
        | _ point =>
            apply congrArg Quotient.mk''
            have equality := congrArg
              (fun morphism : first ⟶ first ↦ morphism.hom.hom point)
              identification.hom_inv_id
            exact equality
      right_inv := by
        intro component
        induction component using Quotient.inductionOn' with
        | _ point =>
            apply congrArg Quotient.mk''
            have equality := congrArg
              (fun morphism : second ⟶ second ↦ morphism.hom.hom point)
              identification.inv_hom_id
            exact equality }

/-- The component map induced by an equivariant isomorphism is its canonical
component equivalence. -/
theorem actionComponentEquiv_apply
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {first second : SourceTemperoidAction G} (identification : first ≅ second)
    (component : ActionComponent first) :
    actionComponentEquiv identification component =
      actionComponentMap identification.hom component :=
  rfl

/-- Forgetting from an edge-group orbit to the larger vertex-group orbit. -/
noncomputable def restrictionComponentMap
    {source target : Type u}
    [Group source] [TopologicalSpace source] [IsTopologicalGroup source]
    [Group target] [TopologicalSpace target] [IsTopologicalGroup target]
    (homomorphism : source →ₜ* target)
    (object : SourceTemperoidAction target) :
    ActionComponent ((ContAction.res SourceCountableTypeCat homomorphism).obj object) →
      ActionComponent object :=
  Quotient.map' id (by
    intro first second relation
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at relation ⊢
    obtain ⟨element, equality⟩ := relation
    exact ⟨homomorphism element, equality⟩)

variable (diagram)

/-- A chosen incident branch on every edge. -/
noncomputable def coverReferenceBranch
    (root : diagram.base.Vertex) (edge : diagram.base.Edge) :
    diagram.IncidentBranch edge :=
  SourceSemiGraphOfAnabelioids.GluedObject.coverReferenceBranch
    diagram root edge

/-! ## The finite-cover embedding -/

/-- Identify the restriction of one finite constituent cover with the
canonical edge representative used by the countable glued object. -/
noncomputable def finiteEdgeIdentification
    (root : diagram.base.Vertex) (object : diagram.GluedObject)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    let reference := coverReferenceBranch diagram root edge
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    branch.temperoidPullback.obj
        ((diagram.vertexAnabelioid branch.vertex).finiteTemperification.obj
          (object.vertexObject branch.vertex)) ≅
      (diagram.edgeAnabelioid edge).finiteTemperification.obj
        (reference.pullback.obj
          (object.vertexObject reference.vertex)) := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact
    ((SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
      (diagram.branchMorphism branch.branch branch.abuts)).app
        (object.vertexObject branch.vertex)).symm ≪≫
      (diagram.edgeAnabelioid edge).finiteTemperification.mapIso
        (object.glue branch reference)

/-- The finite edge identification is natural in a morphism of finite glued
covers. -/
theorem finiteEdgeIdentification_naturality
    (root : diagram.base.Vertex)
    {source target : diagram.GluedObject} (map : source ⟶ target)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    let reference := coverReferenceBranch diagram root edge
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (finiteEdgeIdentification diagram root source branch).hom ≫
        (diagram.edgeAnabelioid edge).finiteTemperification.map
          (reference.pullback.map (map.app reference.vertex)) =
      branch.temperoidPullback.map
          ((diagram.vertexAnabelioid branch.vertex).finiteTemperification.map
            (map.app branch.vertex)) ≫
        (finiteEdgeIdentification diagram root target branch).hom := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  let edgeFunctor :=
    (diagram.edgeAnabelioid edge).finiteTemperification
  let comparison :=
    (SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
      (diagram.branchMorphism branch.branch branch.abuts)).app
        (source.vertexObject branch.vertex)
  let targetComparison :=
    (SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
      (diagram.branchMorphism branch.branch branch.abuts)).app
        (target.vertexObject branch.vertex)
  change
    (comparison.inv ≫ edgeFunctor.map
        (source.glue branch reference).hom) ≫
          edgeFunctor.map (reference.pullback.map (map.app reference.vertex)) =
      branch.temperoidPullback.map
          ((diagram.vertexAnabelioid branch.vertex).finiteTemperification.map
            (map.app branch.vertex)) ≫
        targetComparison.inv ≫
          edgeFunctor.map (target.glue branch reference).hom
  calc
    _ = comparison.inv ≫
        (edgeFunctor.map (source.glue branch reference).hom ≫
          edgeFunctor.map
            (reference.pullback.map (map.app reference.vertex))) :=
      Category.assoc _ _ _
    _ = comparison.inv ≫ edgeFunctor.map
        ((source.glue branch reference).hom ≫
          reference.pullback.map (map.app reference.vertex)) := by
      exact congrArg (fun arrow ↦ comparison.inv ≫ arrow)
        (edgeFunctor.map_comp _ _).symm
    _ = comparison.inv ≫ edgeFunctor.map
        (branch.pullback.map (map.app branch.vertex) ≫
          (target.glue branch reference).hom) := by
      exact congrArg
        (fun arrow ↦ comparison.inv ≫ edgeFunctor.map arrow)
        (map.naturality branch reference)
    _ = comparison.inv ≫
        (edgeFunctor.map (branch.pullback.map (map.app branch.vertex)) ≫
          edgeFunctor.map (target.glue branch reference).hom) := by
      exact congrArg (fun arrow ↦ comparison.inv ≫ arrow)
        (edgeFunctor.map_comp _ _)
    _ = (comparison.inv ≫
          edgeFunctor.map (branch.pullback.map (map.app branch.vertex))) ≫
        edgeFunctor.map (target.glue branch reference).hom :=
      (Category.assoc _ _ _).symm
    _ = (branch.temperoidPullback.map
          ((diagram.vertexAnabelioid branch.vertex).finiteTemperification.map
            (map.app branch.vertex)) ≫ targetComparison.inv) ≫
        edgeFunctor.map (target.glue branch reference).hom := by
      exact congrArg
        (fun arrow ↦ arrow ≫
          edgeFunctor.map (target.glue branch reference).hom)
        ((SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
          (diagram.branchMorphism branch.branch branch.abuts)).inv.naturality
            (map.app branch.vertex)).symm
    _ = _ := Category.assoc _ _ _

/-- Naturality of the inverse finite edge identification. -/
theorem finiteEdgeIdentification_inv_naturality
    (root : diagram.base.Vertex)
    {source target : diagram.GluedObject} (map : source ⟶ target)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    let reference := coverReferenceBranch diagram root edge
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (finiteEdgeIdentification diagram root source branch).inv ≫
        branch.temperoidPullback.map
          ((diagram.vertexAnabelioid branch.vertex).finiteTemperification.map
            (map.app branch.vertex)) =
      (diagram.edgeAnabelioid edge).finiteTemperification.map
          (reference.pullback.map (map.app reference.vertex)) ≫
        (finiteEdgeIdentification diagram root target branch).inv := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  apply (cancel_mono
    (finiteEdgeIdentification diagram root target branch).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← finiteEdgeIdentification_naturality diagram root map branch]
  simp only [Iso.inv_hom_id_assoc]

/-- An ordinary finite glued cover, regarded as literal countable covering
data. -/
noncomputable def finiteCovObject
    (root : diagram.base.Vertex) (object : diagram.GluedObject) :
    diagram.CovObject where
  vertexObject := fun vertex ↦ by
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact (diagram.vertexAnabelioid vertex).finiteTemperification.obj
      (object.vertexObject vertex)
  glue := fun first second ↦
    (finiteEdgeIdentification diagram root object first).trans
      (finiteEdgeIdentification diagram root object second).symm
  glue_refl := by
    intro edge branch
    ext
    simp
  glue_trans := by
    intro edge first second third
    ext
    simp

/-- The countable-cover morphism induced by a finite glued-cover morphism. -/
noncomputable def finiteCovMap
    (root : diagram.base.Vertex)
    {source target : diagram.GluedObject} (map : source ⟶ target) :
    finiteCovObject diagram root source ⟶
      finiteCovObject diagram root target where
  app := fun vertex ↦ by
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact (diagram.vertexAnabelioid vertex).finiteTemperification.map
      (map.app vertex)
  naturality := by
    intro edge first second
    let reference := coverReferenceBranch diagram root edge
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    change
      ((finiteEdgeIdentification diagram root source first).hom ≫
          (finiteEdgeIdentification diagram root source second).inv) ≫
          second.temperoidPullback.map
            ((diagram.vertexAnabelioid second.vertex).finiteTemperification.map
              (map.app second.vertex)) =
        first.temperoidPullback.map
            ((diagram.vertexAnabelioid first.vertex).finiteTemperification.map
              (map.app first.vertex)) ≫
          (finiteEdgeIdentification diagram root target first).hom ≫
            (finiteEdgeIdentification diagram root target second).inv
    rw [Category.assoc,
      finiteEdgeIdentification_inv_naturality diagram root map second]
    rw [← Category.assoc,
      finiteEdgeIdentification_naturality diagram root map first]
    rw [Category.assoc]

/-- The natural embedding `B(G) → B^cov(G)` in Definition 3.5. -/
noncomputable def finiteInclusion
    (root : diagram.base.Vertex) :
    diagram.GluedObject ⥤ diagram.CovObject where
  obj := finiteCovObject diagram root
  map := finiteCovMap diagram root
  map_id object := by
    apply Hom.ext
    intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact (diagram.vertexAnabelioid vertex).finiteTemperification.map_id _
  map_comp first second := by
    apply Hom.ext
    intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact (diagram.vertexAnabelioid vertex).finiteTemperification.map_comp
      (first.app vertex) (second.app vertex)

instance finiteInclusionFaithful
    (root : diagram.base.Vertex) :
    (finiteInclusion diagram root).Faithful where
  map_injective {source target first second} equality := by
    apply SourceSemiGraphOfAnabelioids.GluedObject.Hom.ext
    intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    apply (diagram.vertexAnabelioid vertex).finiteTemperification.map_injective
    have component := congrArg
      (fun map : (finiteInclusion diagram root).obj source ⟶
          (finiteInclusion diagram root).obj target ↦ map.app vertex)
      equality
    exact component

/-- The reference-branch formula for the finite inclusion reduces to the
direct pairwise glue transported through the pullback comparisons. -/
theorem finiteCovObject_glue_hom
    (root : diagram.base.Vertex) (object : diagram.GluedObject)
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ((finiteCovObject diagram root object).glue first second).hom =
      ((SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
        (diagram.branchMorphism first.branch first.abuts)).app
          (object.vertexObject first.vertex)).inv ≫
        (diagram.edgeAnabelioid edge).finiteTemperification.map
          (object.glue first second).hom ≫
        ((SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
          (diagram.branchMorphism second.branch second.abuts)).app
            (object.vertexObject second.vertex)).hom := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  simp only [finiteCovObject, finiteEdgeIdentification, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, IncidentBranch.temperoidPullback]
  have glueCancellation :
      (object.glue first reference).hom ≫
          (object.glue second reference).inv =
        (object.glue first second).hom := by
    have coherence := congrArg Iso.hom
      (object.glue_trans first second reference)
    rw [Iso.trans_hom] at coherence
    rw [← coherence, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have mappedCancellation :
      (diagram.edgeAnabelioid edge).finiteTemperification.map
          (object.glue first reference).hom ≫
        (diagram.edgeAnabelioid edge).finiteTemperification.map
          (object.glue second reference).inv =
      (diagram.edgeAnabelioid edge).finiteTemperification.map
        (object.glue first second).hom := by
    rw [← Functor.map_comp, glueCancellation]
  have htransport := congrArg
    (fun middle ↦
      ((SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
        (diagram.branchMorphism first.branch first.abuts)).app
          (object.vertexObject first.vertex)).inv ≫ middle ≫
        ((SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
          (diagram.branchMorphism second.branch second.abuts)).app
            (object.vertexObject second.vertex)).hom)
    mappedCancellation
  change
    ((SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
          (diagram.branchMorphism first.branch first.abuts)).app
        (object.vertexObject first.vertex)).inv ≫
        ((diagram.edgeAnabelioid edge).finiteTemperification.map
              (object.glue first reference).hom ≫
            (diagram.edgeAnabelioid edge).finiteTemperification.map
              (object.glue second reference).inv) ≫
          ((SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
              (diagram.branchMorphism second.branch second.abuts)).app
            (object.vertexObject second.vertex)).hom =
      ((SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
          (diagram.branchMorphism first.branch first.abuts)).app
        (object.vertexObject first.vertex)).inv ≫
        (diagram.edgeAnabelioid edge).finiteTemperification.map
            (object.glue first second).hom ≫
          ((SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
              (diagram.branchMorphism second.branch second.abuts)).app
            (object.vertexObject second.vertex)).hom
  exact htransport

noncomputable instance finiteInclusionFull
    (root : diagram.base.Vertex) :
    (finiteInclusion diagram root).Full where
  map_surjective {source target} map := by
    let component : ∀ vertex,
        letI := (diagram.vertexAnabelioid vertex).coverCategory
        source.vertexObject vertex ⟶ target.vertexObject vertex :=
      fun vertex ↦ by
        letI := (diagram.vertexAnabelioid vertex).coverCategory
        exact (diagram.vertexAnabelioid vertex).finiteTemperification.preimage
          (map.app vertex)
    let lifted : source ⟶ target :=
      { app := component
        naturality := by
          intro edge first second
          let reference := coverReferenceBranch diagram root edge
          letI := (diagram.vertexAnabelioid first.vertex).coverCategory
          letI := (diagram.vertexAnabelioid second.vertex).coverCategory
          letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
          letI := (diagram.edgeAnabelioid edge).coverCategory
          apply (diagram.edgeAnabelioid edge).finiteTemperification.map_injective
          rw [Functor.map_comp, Functor.map_comp]
          let edgeFunctor :=
            (diagram.edgeAnabelioid edge).finiteTemperification
          let sourceFirstComparison :=
            (SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
              (diagram.branchMorphism first.branch first.abuts)).app
                (source.vertexObject first.vertex)
          let targetFirstComparison :=
            (SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
              (diagram.branchMorphism first.branch first.abuts)).app
                (target.vertexObject first.vertex)
          let sourceSecondComparison :=
            (SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
              (diagram.branchMorphism second.branch second.abuts)).app
                (source.vertexObject second.vertex)
          let targetSecondComparison :=
            (SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
              (diagram.branchMorphism second.branch second.abuts)).app
                (target.vertexObject second.vertex)
          have secondCompatibility :
              edgeFunctor.map
                    (second.pullback.map (component second.vertex)) ≫
                  targetSecondComparison.hom =
                  sourceSecondComparison.hom ≫
                  second.temperoidPullback.map (map.app second.vertex) := by
            have hnatural :=
              (SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
                (diagram.branchMorphism second.branch second.abuts)).hom.naturality
                  (component second.vertex)
            simp only [Functor.comp_map, component, Functor.map_preimage]
              at hnatural
            change
              edgeFunctor.map
                    (second.pullback.map (component second.vertex)) ≫
                  targetSecondComparison.hom =
                sourceSecondComparison.hom ≫
                  second.temperoidPullback.map (map.app second.vertex)
                at hnatural
            exact hnatural
          have firstCompatibility :
              sourceFirstComparison.inv ≫
                  edgeFunctor.map
                    (first.pullback.map (component first.vertex)) =
                first.temperoidPullback.map (map.app first.vertex) ≫
                  targetFirstComparison.inv := by
            have hnatural :=
              ((SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
                (diagram.branchMorphism first.branch first.abuts)).inv.naturality
                  (component first.vertex)).symm
            simp only [Functor.comp_map, component, Functor.map_preimage]
              at hnatural
            change
              sourceFirstComparison.inv ≫
                    edgeFunctor.map
                      (first.pullback.map (component first.vertex)) =
                first.temperoidPullback.map (map.app first.vertex) ≫
                  targetFirstComparison.inv at hnatural
            exact hnatural
          have countableNaturality := map.naturality first second
          change
            ((finiteCovObject diagram root source).glue first second).hom ≫
                second.temperoidPullback.map (map.app second.vertex) =
              first.temperoidPullback.map (map.app first.vertex) ≫
                ((finiteCovObject diagram root target).glue first second).hom
            at countableNaturality
          rw [finiteCovObject_glue_hom diagram root source first second,
            finiteCovObject_glue_hom diagram root target first second]
            at countableNaturality
          change
            (sourceFirstComparison.inv ≫
                edgeFunctor.map (source.glue first second).hom ≫
                sourceSecondComparison.hom) ≫
                second.temperoidPullback.map (map.app second.vertex) =
              first.temperoidPullback.map (map.app first.vertex) ≫
                targetFirstComparison.inv ≫
                edgeFunctor.map (target.glue first second).hom ≫
                targetSecondComparison.hom at countableNaturality
          have leftTransport :
              (sourceFirstComparison.inv ≫
                  edgeFunctor.map (source.glue first second).hom ≫
                  edgeFunctor.map
                    (second.pullback.map (component second.vertex))) ≫
                  targetSecondComparison.hom =
                (sourceFirstComparison.inv ≫
                  edgeFunctor.map (source.glue first second).hom ≫
                  sourceSecondComparison.hom) ≫
                  second.temperoidPullback.map (map.app second.vertex) := by
            simp only [Category.assoc] at secondCompatibility ⊢
            rw [secondCompatibility]
            rfl
          have rightTransport :
              (sourceFirstComparison.inv ≫
                  edgeFunctor.map
                    (first.pullback.map (component first.vertex))) ≫
                  edgeFunctor.map (target.glue first second).hom ≫
                  targetSecondComparison.hom =
                (first.temperoidPullback.map (map.app first.vertex) ≫
                  targetFirstComparison.inv) ≫
                  edgeFunctor.map (target.glue first second).hom ≫
                  targetSecondComparison.hom := by
            exact congrArg
              (fun leading ↦ leading ≫
                edgeFunctor.map (target.glue first second).hom ≫
                targetSecondComparison.hom)
              firstCompatibility
          have middleEquality :
              (sourceFirstComparison.inv ≫
                  edgeFunctor.map (source.glue first second).hom ≫
                  sourceSecondComparison.hom) ≫
                  second.temperoidPullback.map (map.app second.vertex) =
                (first.temperoidPullback.map (map.app first.vertex) ≫
                  targetFirstComparison.inv) ≫
                  edgeFunctor.map (target.glue first second).hom ≫
                  targetSecondComparison.hom := by
            calc
              _ = first.temperoidPullback.map (map.app first.vertex) ≫
                    targetFirstComparison.inv ≫
                    edgeFunctor.map (target.glue first second).hom ≫
                    targetSecondComparison.hom := countableNaturality
              _ = _ := by rw [Category.assoc]
          apply (cancel_epi sourceFirstComparison.inv).1
          apply (cancel_mono targetSecondComparison.hom).1
          exact leftTransport.trans (middleEquality.trans rightTransport.symm) }
    refine ⟨lifted, ?_⟩
    apply Hom.ext
    intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact (diagram.vertexAnabelioid vertex).finiteTemperification.map_preimage _

/-- The finite objects of `B^cov(G)` recover `B(G)` fully faithfully. -/
noncomputable def finiteInclusionFullyFaithful
    (root : diagram.base.Vertex) :
    (finiteInclusion diagram root).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful (finiteInclusion diagram root)

/-- The representative edge action obtained from the chosen incident branch. -/
noncomputable def coverEdgeObject
    (root : diagram.base.Vertex) (object : diagram.CovObject)
    (edge : diagram.base.Edge) :
    SourceTemperoidAction (diagram.edgeAnabelioid edge).group :=
  let reference := coverReferenceBranch diagram root edge
  reference.temperoidPullback.obj (object.vertexObject reference.vertex)

/-- Orbit components of a vertex restriction. -/
abbrev CoverVertexComponent (object : diagram.CovObject)
    (vertex : diagram.base.Vertex) : Type u :=
  ActionComponent (object.vertexObject vertex)

/-- Orbit components of the chosen edge restriction. -/
abbrev CoverEdgeComponent (root : diagram.base.Vertex)
    (object : diagram.CovObject) (edge : diagram.base.Edge) : Type u :=
  ActionComponent (coverEdgeObject diagram root object edge)

/-- Incidence from an edge orbit component to an incident vertex orbit
component. -/
noncomputable def coverComponentMap
    (root : diagram.base.Vertex) (object : diagram.CovObject)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    CoverEdgeComponent diagram root object edge →
      CoverVertexComponent diagram object branch.vertex :=
  let reference := coverReferenceBranch diagram root edge
  let identification :
      coverEdgeObject diagram root object edge ≅
        branch.temperoidPullback.obj (object.vertexObject branch.vertex) :=
    object.glue reference branch
  restrictionComponentMap
      (diagram.branchMorphism branch.branch branch.abuts).fundamentalGroupHom.hom
      (object.vertexObject branch.vertex) ∘
    actionComponentEquiv identification

/-- A morphism of geometric covers sends each vertex orbit component to its
image component. -/
noncomputable def coverVertexComponentMap
    {source target : diagram.CovObject} (map : source ⟶ target)
    (vertex : diagram.base.Vertex) :
    CoverVertexComponent diagram source vertex →
      CoverVertexComponent diagram target vertex :=
  actionComponentMap (map.app vertex)

/-- A morphism of geometric covers sends each representative edge orbit
component to its image component. -/
noncomputable def coverEdgeComponentMap
    (root : diagram.base.Vertex)
    {source target : diagram.CovObject} (map : source ⟶ target)
    (edge : diagram.base.Edge) :
    CoverEdgeComponent diagram root source edge →
      CoverEdgeComponent diagram root target edge := by
  let reference := coverReferenceBranch diagram root edge
  exact actionComponentMap
    (reference.temperoidPullback.map (map.app reference.vertex))

/-- Component incidence is natural under a morphism of geometric covers. -/
theorem coverComponentMap_naturality
    (root : diagram.base.Vertex)
    {source target : diagram.CovObject} (map : source ⟶ target)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge)
    (component : CoverEdgeComponent diagram root source edge) :
    coverVertexComponentMap diagram map branch.vertex
        (coverComponentMap diagram root source branch component) =
      coverComponentMap diagram root target branch
        (coverEdgeComponentMap diagram root map edge component) := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  induction component using Quotient.inductionOn' with
  | _ point =>
      apply congrArg Quotient.mk''
      exact ConcreteCategory.congr_hom
        (map.naturality reference branch) point

/-- Vertices of the covering semi-graph associated to countable gluing data. -/
abbrev CoverVertex (object : diagram.CovObject) : Type u :=
  Σ vertex, CoverVertexComponent diagram object vertex

/-- Edges of the covering semi-graph associated to countable gluing data. -/
abbrev CoverEdge (root : diagram.base.Vertex)
    (object : diagram.CovObject) : Type u :=
  Σ edge, CoverEdgeComponent diagram root object edge

/-- The countable covering semi-graph associated to an object of `B^cov(G)`. -/
noncomputable def coverSemiGraph
    (root : diagram.base.Vertex) (object : diagram.CovObject) :
    SourceSemiGraph.{u} where
  Vertex := CoverVertex diagram object
  Edge := CoverEdge diagram root object
  Branch := fun edge ↦ diagram.base.Branch edge.1
  branchFintype := fun edge ↦ diagram.base.branchFintype edge.1
  branch_card := fun edge ↦ diagram.base.branch_card edge.1
  coincidence := fun edge branch ↦
    match abuts : diagram.base.coincidence edge.1 branch with
    | none => none
    | some vertex =>
        some ⟨vertex, coverComponentMap diagram root object
          ⟨branch, vertex, abuts⟩ edge.2⟩

/-- A morphism of geometric covers induces the corresponding morphism of
their component semi-graphs. -/
noncomputable def coverSemiGraphMap
    (root : diagram.base.Vertex)
    {source target : diagram.CovObject} (map : source ⟶ target) :
    (coverSemiGraph diagram root source).Hom
      (coverSemiGraph diagram root target) where
  vertexMap := fun vertex =>
    ⟨vertex.1, coverVertexComponentMap diagram map vertex.1 vertex.2⟩
  edgeMap := fun edge =>
    ⟨edge.1, coverEdgeComponentMap diagram root map edge.1 edge.2⟩
  branchEquiv := fun _ => Equiv.refl _
  map_coincidence := by
    rintro ⟨edge, component⟩ branch ⟨vertex, vertexComponent⟩ coincidence
    change (match sourceAbuts : diagram.base.coincidence edge branch with
      | none => none
      | some targetVertex => some (⟨targetVertex,
          coverComponentMap diagram root source
            ⟨branch, targetVertex, sourceAbuts⟩ component⟩ :
              CoverVertex diagram source)) =
        some (⟨vertex, vertexComponent⟩ : CoverVertex diagram source)
      at coincidence
    split at coincidence
    next noVertex => cases coincidence
    next targetVertex sourceAbuts =>
        have vertexEquality : targetVertex = vertex :=
          Sigma.mk.inj_iff.mp (Option.some.inj coincidence) |>.1
        subst targetVertex
        have componentEquality :
            coverComponentMap diagram root source
                ⟨branch, vertex, sourceAbuts⟩ component = vertexComponent :=
          eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj coincidence) |>.2)
        change (coverSemiGraph diagram root target).coincidence
            ⟨edge, coverEdgeComponentMap diagram root map edge component⟩
              branch =
          some (⟨vertex,
            coverVertexComponentMap diagram map vertex vertexComponent⟩ :
              CoverVertex diagram target)
        change (match targetAbuts : diagram.base.coincidence edge branch with
          | none => none
          | some targetVertex => some (⟨targetVertex,
              coverComponentMap diagram root target
                ⟨branch, targetVertex, targetAbuts⟩
                (coverEdgeComponentMap diagram root map edge component)⟩ :
                  CoverVertex diagram target)) = _
        split
        next targetNone =>
          rw [sourceAbuts] at targetNone
          cases targetNone
        next targetVertex targetAbuts =>
          have targetVertexEquality : targetVertex = vertex :=
            Option.some.inj (targetAbuts.symm.trans sourceAbuts)
          subst targetVertex
          apply congrArg some
          refine Sigma.ext rfl ?_
          exact heq_of_eq <| by
            rw [← componentEquality]
            exact (coverComponentMap_naturality diagram root map
              ⟨branch, vertex, targetAbuts⟩ component).symm

/-- On vertices, the component-semigraph construction preserves composition
of geometric-cover morphisms. -/
theorem coverSemiGraphMap_vertex_comp
    (root : diagram.base.Vertex)
    {first second third : diagram.CovObject}
    (firstMap : first ⟶ second) (secondMap : second ⟶ third)
    (vertex : (coverSemiGraph diagram root first).Vertex) :
    (coverSemiGraphMap diagram root (firstMap ≫ secondMap)).vertexMap vertex =
      (coverSemiGraphMap diagram root secondMap).vertexMap
        ((coverSemiGraphMap diagram root firstMap).vertexMap vertex) := by
  rcases vertex with ⟨vertex, component⟩
  refine Sigma.ext rfl ?_
  exact heq_of_eq
    (actionComponentMap_comp
      (firstMap.app vertex) (secondMap.app vertex) component)

/-- On edges, the component-semigraph construction preserves composition of
geometric-cover morphisms. -/
theorem coverSemiGraphMap_edge_comp
    (root : diagram.base.Vertex)
    {first second third : diagram.CovObject}
    (firstMap : first ⟶ second) (secondMap : second ⟶ third)
    (edge : (coverSemiGraph diagram root first).Edge) :
    (coverSemiGraphMap diagram root (firstMap ≫ secondMap)).edgeMap edge =
      (coverSemiGraphMap diagram root secondMap).edgeMap
        ((coverSemiGraphMap diagram root firstMap).edgeMap edge) := by
  rcases edge with ⟨edge, component⟩
  refine Sigma.ext rfl ?_
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  change HEq
    (actionComponentMap
      (reference.temperoidPullback.map
        ((firstMap ≫ secondMap).app reference.vertex)) component)
    (actionComponentMap
      (reference.temperoidPullback.map (secondMap.app reference.vertex))
      (actionComponentMap
        (reference.temperoidPullback.map (firstMap.app reference.vertex))
        component))
  rw [show reference.temperoidPullback.map
      ((firstMap ≫ secondMap).app reference.vertex) =
        reference.temperoidPullback.map (firstMap.app reference.vertex) ≫
          reference.temperoidPullback.map
            (secondMap.app reference.vertex) by
    exact reference.temperoidPullback.map_comp _ _]
  exact heq_of_eq
    (actionComponentMap_comp
      (reference.temperoidPullback.map (firstMap.app reference.vertex))
      (reference.temperoidPullback.map (secondMap.app reference.vertex))
      component)

/-- The projection of the associated countable covering semi-graph. -/
noncomputable def coverProjection
    (root : diagram.base.Vertex) (object : diagram.CovObject) :
    (coverSemiGraph diagram root object).Hom diagram.base where
  vertexMap := Sigma.fst
  edgeMap := Sigma.fst
  branchEquiv := fun _ ↦ Equiv.refl _
  map_coincidence := by
    intro liftedEdge branch liftedVertex coincidence
    rcases liftedEdge with ⟨edge, component⟩
    rcases liftedVertex with ⟨vertex, vertexComponent⟩
    change diagram.base.coincidence edge branch = some vertex
    change (match abuts : diagram.base.coincidence edge branch with
      | none => none
      | some target => some (⟨target,
          coverComponentMap diagram root object
            ⟨branch, target, abuts⟩ component⟩ :
              CoverVertex diagram object)) =
        some (⟨vertex, vertexComponent⟩ : CoverVertex diagram object)
          at coincidence
    split at coincidence
    · cases coincidence
    · next target abuts =>
        have vertexEquality : target = vertex :=
          Sigma.mk.inj_iff.mp (Option.some.inj coincidence) |>.1
        exact abuts.trans (congrArg some vertexEquality)

/-- Countability of the base and constituent fibers makes the associated
covering semi-graph countable. -/
theorem coverSemiGraph_isCountable
    (countable : diagram.base.IsCountable)
    (root : diagram.base.Vertex) (object : diagram.CovObject) :
    (coverSemiGraph diagram root object).IsCountable := by
  letI : Countable diagram.base.Vertex := countable.1
  letI : Countable diagram.base.Edge := countable.2
  change Countable (CoverVertex diagram object) ∧
    Countable (CoverEdge diagram root object)
  constructor <;> infer_instance

/-! ## Geometric connected components -/

namespace AssociatedQuotient

/-- A point of one vertex constituent, with its vertex retained. -/
abbrev GeometricPoint {diagram : SourceSemiGraphOfAnabelioids.{u}}
    (source : diagram.CovObject) :=
  Σ vertex, (source.vertexObject vertex).obj.V.obj

/-- Elementary geometric motion in a glued cover: either move inside one
local group orbit or cross one branch-gluing isomorphism. -/
inductive GeometricPointStep {diagram : SourceSemiGraphOfAnabelioids.{u}}
    (source : diagram.CovObject) :
    GeometricPoint source → GeometricPoint source → Prop
  | localAction (vertex : diagram.base.Vertex)
      (element : (diagram.vertexAnabelioid vertex).group)
      (point : (source.vertexObject vertex).obj.V.obj) :
      GeometricPointStep source ⟨vertex, point⟩ ⟨vertex, element • point⟩
  | glue {edge : diagram.base.Edge}
      (first second : diagram.IncidentBranch edge)
      (point : (first.temperoidPullback.obj
        (source.vertexObject first.vertex)).obj.V.obj) :
      GeometricPointStep source
        ⟨first.vertex, point⟩
        ⟨second.vertex, (source.glue first second).hom.hom.hom point⟩

/-- Reachability inside one connected component of a geometric cover. -/
abbrev GeometricallyReachable
    {diagram : SourceSemiGraphOfAnabelioids.{u}} (source : diagram.CovObject)
    (first second : GeometricPoint source) : Prop :=
  Relation.ReflTransGen (GeometricPointStep source) first second

/-- Every geometric point can be reached from the chosen point by local
constituent motion and branch gluing. -/
def IsPointConnected {diagram : SourceSemiGraphOfAnabelioids.{u}}
    (source : diagram.CovObject)
    (basePoint : GeometricPoint source) : Prop :=
  ∀ point, GeometricallyReachable source basePoint point

/-- Intrinsic connectedness of a geometric cover: it has a geometric point
from which every other point is reachable. -/
def IsGeometricallyConnected {diagram : SourceSemiGraphOfAnabelioids.{u}}
    (source : diagram.CovObject) : Prop :=
  ∃ basePoint, IsPointConnected source basePoint

end AssociatedQuotient

/-! ## The geometric tempered full subcategory -/

/-- The global kernel of `splitter` acts trivially on `target`. -/
def ActionKernelFixes
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (splitter target : SourceTemperoidAction G) : Prop :=
  ∀ g : G,
    (∀ point : splitter.obj.V.obj, g • point = point) →
      ∀ point : target.obj.V.obj, g • point = point

theorem actionKernelFixes_self
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (object : SourceTemperoidAction G) :
    ActionKernelFixes object object := by
  intro g fixes point
  exact fixes point

/-- A finite glued cover splits every constituent of a countable glued cover.
This is the globally bounded special case of corrected Definition 3.5(ii). -/
def IsSplitBy
    (root : diagram.base.Vertex)
    (splitter : diagram.GluedObject) (target : diagram.CovObject) : Prop :=
  (∀ vertex,
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    ActionKernelFixes
      ((finiteCovObject diagram root splitter).vertexObject vertex)
      (target.vertexObject vertex)) ∧
  (∀ edge,
    let reference := coverReferenceBranch diagram root edge
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ActionKernelFixes
      (coverEdgeObject diagram root (finiteCovObject diagram root splitter) edge)
      (coverEdgeObject diagram root target edge))

/-- A finite cover splits the connected component containing `basePoint`.
The component is represented intrinsically by geometric reachability, so no
separate component subobject or arbitrary output field is stored. -/
def IsComponentSplitBy
    (root : diagram.base.Vertex)
    (splitter : diagram.GluedObject) (target : diagram.CovObject)
    (basePoint : AssociatedQuotient.GeometricPoint target) : Prop :=
  (∀ vertex,
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    ∀ element : (diagram.vertexAnabelioid vertex).group,
      (∀ point : ((finiteCovObject diagram root splitter).vertexObject
          vertex).obj.V.obj, element • point = point) →
      ∀ point : (target.vertexObject vertex).obj.V.obj,
        AssociatedQuotient.GeometricallyReachable target basePoint
          ⟨vertex, point⟩ →
        element • point = point) ∧
  (∀ edge,
    let reference := coverReferenceBranch diagram root edge
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ∀ element : (diagram.edgeAnabelioid edge).group,
      (∀ point : (coverEdgeObject diagram root
          (finiteCovObject diagram root splitter) edge).obj.V.obj,
        element • point = point) →
      ∀ point : (coverEdgeObject diagram root target edge).obj.V.obj,
        AssociatedQuotient.GeometricallyReachable target basePoint
          ⟨reference.vertex, point⟩ →
        element • point = point)

/-- The pre-correction globally bounded condition: one finite cover splits
all connected components simultaneously. It remains useful for finite-level
constructions but is stronger than corrected Definition 3.5(ii). -/
def IsGloballyTempered
    (root : diagram.base.Vertex) (target : diagram.CovObject) : Prop :=
  ∃ splitter : diagram.GluedObject, IsSplitBy diagram root splitter target

/-- Corrected Definition 3.5(ii): each connected component of a countable
geometric cover may choose its own finite étale splitting cover. This is the
correction in item (11) of the May 2020 comments on *Semi-graphs of
Anabelioids*. -/
def IsTempered
    (root : diagram.base.Vertex) (target : diagram.CovObject) : Prop :=
  ∀ basePoint : AssociatedQuotient.GeometricPoint target,
    ∃ splitter : diagram.GluedObject,
      IsComponentSplitBy diagram root splitter target basePoint

/-- A global splitting witness restricts to every connected component. -/
theorem isComponentSplitBy_of_isSplitBy
    (root : diagram.base.Vertex) {splitter : diagram.GluedObject}
    {target : diagram.CovObject}
    (split : IsSplitBy diagram root splitter target)
    (basePoint : AssociatedQuotient.GeometricPoint target) :
    IsComponentSplitBy diagram root splitter target basePoint := by
  constructor
  · intro vertex element fixes point _
    exact split.1 vertex element fixes point
  · intro edge
    dsimp only
    intro element fixes point _
    exact split.2 edge element fixes point

/-- Every globally bounded cover is tempered in the corrected componentwise
sense. -/
theorem IsGloballyTempered.isTempered
    (root : diagram.base.Vertex) {target : diagram.CovObject}
    (tempered : IsGloballyTempered diagram root target) :
    IsTempered diagram root target := by
  obtain ⟨splitter, split⟩ := tempered
  intro basePoint
  exact ⟨splitter,
    isComponentSplitBy_of_isSplitBy diagram root split basePoint⟩

/-- A displayed global splitting witness proves corrected temperedness. -/
theorem isTempered_of_isSplitBy
    (root : diagram.base.Vertex) {splitter : diagram.GluedObject}
    {target : diagram.CovObject}
    (split : IsSplitBy diagram root splitter target) :
    IsTempered diagram root target :=
  IsGloballyTempered.isTempered diagram root ⟨splitter, split⟩

/-- On a point-connected target, a splitter of its chosen component splits
the entire cover. -/
theorem IsComponentSplitBy.isSplitBy_of_isPointConnected
    (root : diagram.base.Vertex) {splitter : diagram.GluedObject}
    {target : diagram.CovObject}
    {basePoint : AssociatedQuotient.GeometricPoint target}
    (split : IsComponentSplitBy diagram root splitter target basePoint)
    (connected : AssociatedQuotient.IsPointConnected target basePoint) :
    IsSplitBy diagram root splitter target := by
  constructor
  · intro vertex element fixes point
    exact split.1 vertex element fixes point (connected ⟨vertex, point⟩)
  · intro edge
    dsimp only
    intro element fixes point
    exact split.2 edge element fixes point
      (connected
        ⟨(coverReferenceBranch diagram root edge).vertex, point⟩)

/-- A corrected temperedness witness becomes globally bounded whenever the
target is connected at the chosen point. -/
theorem IsTempered.exists_isSplitBy_of_isPointConnected
    (root : diagram.base.Vertex) {target : diagram.CovObject}
    (tempered : IsTempered diagram root target)
    (basePoint : AssociatedQuotient.GeometricPoint target)
    (connected : AssociatedQuotient.IsPointConnected target basePoint) :
    ∃ splitter : diagram.GluedObject,
      IsSplitBy diagram root splitter target := by
  obtain ⟨splitter, split⟩ := tempered basePoint
  exact ⟨splitter,
    IsComponentSplitBy.isSplitBy_of_isPointConnected
      diagram root split connected⟩

/-- The tempered-object property on the literal covering category. -/
abbrev temperedObjectProperty
    (root : diagram.base.Vertex) : ObjectProperty diagram.CovObject :=
  IsTempered diagram root

/-- `B^temp(G)` as the full geometric subcategory of `B^cov(G)`. -/
abbrev TemperedCover (root : diagram.base.Vertex) :=
  (temperedObjectProperty diagram root).FullSubcategory

/-- Every finite glued cover is tempered: its own finite global kernels split
all of its constituent actions. -/
theorem finiteCovObject_isTempered
    (root : diagram.base.Vertex) (object : diagram.GluedObject) :
    IsTempered diagram root (finiteCovObject diagram root object) := by
  apply IsGloballyTempered.isTempered diagram root
  refine ⟨object, ?_⟩
  constructor
  · intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact actionKernelFixes_self _
  · intro edge
    let reference := coverReferenceBranch diagram root edge
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    exact actionKernelFixes_self _

/-- The natural full embedding `B(G) → B^temp(G)`. -/
noncomputable def finiteTemperedInclusion
    (root : diagram.base.Vertex) :
    diagram.GluedObject ⥤ TemperedCover diagram root :=
  (temperedObjectProperty diagram root).lift
    (finiteInclusion diagram root)
    (finiteCovObject_isTempered diagram root)

instance finiteTemperedInclusionFaithful
    (root : diagram.base.Vertex) :
    (finiteTemperedInclusion diagram root).Faithful := by
  letI := finiteInclusionFaithful diagram root
  apply Functor.Faithful.of_comp_iso
    ((temperedObjectProperty diagram root).liftCompιIso
      (finiteInclusion diagram root)
      (finiteCovObject_isTempered diagram root))

instance finiteTemperedInclusionFull
    (root : diagram.base.Vertex) :
    (finiteTemperedInclusion diagram root).Full := by
  letI := finiteInclusionFull diagram root
  apply Functor.Full.of_comp_faithful_iso
    ((temperedObjectProperty diagram root).liftCompιIso
      (finiteInclusion diagram root)
      (finiteCovObject_isTempered diagram root))

/-- The finite-to-tempered embedding is fully faithful. -/
noncomputable def finiteTemperedInclusionFullyFaithful
    (root : diagram.base.Vertex) :
    (finiteTemperedInclusion diagram root).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful
    (finiteTemperedInclusion diagram root)

/-- The natural full embedding `B^temp(G) → B^cov(G)`. -/
abbrev temperedCovInclusion
    (root : diagram.base.Vertex) :
    TemperedCover diagram root ⥤ diagram.CovObject :=
  (temperedObjectProperty diagram root).ι

/-- The geometric tempered category is a full subcategory of the literal
countable covering category. -/
def temperedCovInclusionFullyFaithful
    (root : diagram.base.Vertex) :
    (temperedCovInclusion diagram root).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

end CovObject

end SourceSemiGraphOfAnabelioids

end Iut
