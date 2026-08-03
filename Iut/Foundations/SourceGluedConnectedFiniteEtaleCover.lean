/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceGluedFiniteEtaleTransition

/-!
# Connected finite-etale levels of a glued anabelioid

The finite-etale semigraph attached to an object of `B(G)` is built from the
connected components of its constituent restrictions.  This file develops
the source-derived path-lifting boundary needed to prove that a connected
object produces a connected semigraph: constituent component maps are
surjective, hence every closed-edge path in the base lifts from any chosen
vertex component.
-/

namespace CategoryTheory.PreGaloisCategory

universe v

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type (v + 1)} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{v}) [FiberFunctor F]

/-- The unique point of a second subobject lying over the transported image
of a point of the first subobject. -/
noncomputable def subobjectComparisonPoint
    {X₁ Y₁ X₂ Y₂ : C}
    (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂)
    (y : Y₁ ≅ Y₂)
    (rangeForward : ∀ point : F.obj X₁,
      F.map y.hom (F.map i₁ point) ∈ Set.range (F.map i₂))
    (point : F.obj X₁) : F.obj X₂ :=
  Classical.choose (rangeForward point)

omit [GaloisCategory C] [FiberFunctor F] in
theorem subobjectComparisonPoint_spec
    {X₁ Y₁ X₂ Y₂ : C}
    (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂)
    (y : Y₁ ≅ Y₂)
    (rangeForward : ∀ point : F.obj X₁,
      F.map y.hom (F.map i₁ point) ∈ Set.range (F.map i₂))
    (point : F.obj X₁) :
    F.map i₂ (subobjectComparisonPoint F i₁ i₂ y rangeForward point) =
      F.map y.hom (F.map i₁ point) :=
  Classical.choose_spec (rangeForward point)

/-- Equal fiberwise subobjects under a target isomorphism determine an
equivariant comparison of their canonical fundamental-group actions. -/
noncomputable def subobjectComparisonActionHom
    {X₁ Y₁ X₂ Y₂ : C}
    (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) [Mono i₂]
    (y : Y₁ ≅ Y₂)
    (rangeForward : ∀ point : F.obj X₁,
      F.map y.hom (F.map i₁ point) ∈ Set.range (F.map i₂)) :
    (functorToAction F).obj X₁ ⟶ (functorToAction F).obj X₂ := by
  let lift := subobjectComparisonPoint F i₁ i₂ y rangeForward
  have inclusionInjective : Function.Injective (F.map i₂) := by
    apply (mono_iff_injective (FintypeCat.incl.map (F.map i₂))).mp
    infer_instance
  refine
    { hom := FintypeCat.homMk lift
      comm := fun automorphism => ?_ }
  ext point
  apply inclusionInjective
  change F.map i₂ (lift (automorphism.hom.app X₁ point)) =
    F.map i₂ (automorphism.hom.app X₂ (lift point))
  calc
    F.map i₂ (lift (automorphism.hom.app X₁ point)) =
        F.map y.hom (F.map i₁ (automorphism.hom.app X₁ point)) :=
      subobjectComparisonPoint_spec F i₁ i₂ y rangeForward _
    _ = F.map y.hom (automorphism.hom.app Y₁ (F.map i₁ point)) := by
      exact congrArg (fun value => F.map y.hom value)
        (ConcreteCategory.congr_hom
          (automorphism.hom.naturality i₁) point).symm
    _ = automorphism.hom.app Y₂ (F.map y.hom (F.map i₁ point)) := by
      exact (ConcreteCategory.congr_hom
        (automorphism.hom.naturality y.hom) (F.map i₁ point)).symm
    _ = automorphism.hom.app Y₂ (F.map i₂ (lift point)) := by
      rw [subobjectComparisonPoint_spec F i₁ i₂ y rangeForward]
    _ = F.map i₂ (automorphism.hom.app X₂ (lift point)) :=
      ConcreteCategory.congr_hom
        (automorphism.hom.naturality i₂) (lift point)

theorem subobjectComparisonActionHom_comp
    {X₁ Y₁ X₂ Y₂ : C}
    (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) [Mono i₂]
    (y : Y₁ ≅ Y₂)
    (rangeForward : ∀ point : F.obj X₁,
      F.map y.hom (F.map i₁ point) ∈ Set.range (F.map i₂)) :
    subobjectComparisonActionHom F i₁ i₂ y rangeForward ≫
        (functorToAction F).map i₂ =
      (functorToAction F).map i₁ ≫ (functorToAction F).map y.hom := by
  ext point
  exact subobjectComparisonPoint_spec F i₁ i₂ y rangeForward point

/-- Two monomorphisms whose fiberwise ranges correspond under a target
isomorphism have canonically isomorphic sources. -/
noncomputable def subobjectComparisonIso
    {X₁ Y₁ X₂ Y₂ : C}
    (i₁ : X₁ ⟶ Y₁) [Mono i₁]
    (i₂ : X₂ ⟶ Y₂) [Mono i₂]
    (y : Y₁ ≅ Y₂)
    (sameRange : ∀ point : F.obj Y₁,
      F.map y.hom point ∈ Set.range (F.map i₂) ↔
        point ∈ Set.range (F.map i₁)) : X₁ ≅ X₂ := by
  let H := functorToAction F
  have forwardRange (point : F.obj X₁) :
      F.map y.hom (F.map i₁ point) ∈ Set.range (F.map i₂) :=
    (sameRange (F.map i₁ point)).2 ⟨point, rfl⟩
  have reverseRange (point : F.obj X₂) :
      F.map y.inv (F.map i₂ point) ∈ Set.range (F.map i₁) := by
    apply (sameRange (F.map y.inv (F.map i₂ point))).1
    have cancellation :
        F.map y.hom (F.map y.inv (F.map i₂ point)) = F.map i₂ point := by
      simp only [← FintypeCat.comp_apply, ← F.map_comp,
        Category.assoc, y.inv_hom_id, Category.comp_id]
    rw [cancellation]
    exact ⟨point, rfl⟩
  let forward := subobjectComparisonActionHom F i₁ i₂ y forwardRange
  let reverse := subobjectComparisonActionHom F i₂ i₁ y.symm reverseRange
  let actionIso : H.obj X₁ ≅ H.obj X₂ :=
    { hom := forward
      inv := reverse
      hom_inv_id := by
        apply (cancel_mono (H.map i₁)).1
        rw [Category.assoc]
        rw [subobjectComparisonActionHom_comp F i₂ i₁ y.symm reverseRange]
        rw [← Category.assoc]
        rw [subobjectComparisonActionHom_comp F i₁ i₂ y forwardRange]
        simp
        rfl
      inv_hom_id := by
        apply (cancel_mono (H.map i₂)).1
        rw [Category.assoc]
        rw [subobjectComparisonActionHom_comp F i₁ i₂ y forwardRange]
        rw [← Category.assoc]
        rw [subobjectComparisonActionHom_comp F i₂ i₁ y.symm reverseRange]
        simp
        rfl }
  exact H.preimageIso actionIso

theorem subobjectComparisonIso_hom_comp
    {X₁ Y₁ X₂ Y₂ : C}
    (i₁ : X₁ ⟶ Y₁) [Mono i₁]
    (i₂ : X₂ ⟶ Y₂) [Mono i₂]
    (y : Y₁ ≅ Y₂)
    (sameRange : ∀ point : F.obj Y₁,
      F.map y.hom point ∈ Set.range (F.map i₂) ↔
        point ∈ Set.range (F.map i₁)) :
    (subobjectComparisonIso F i₁ i₂ y sameRange).hom ≫ i₂ =
      i₁ ≫ y.hom := by
  let H := functorToAction F
  let forwardRange (point : F.obj X₁) :
      F.map y.hom (F.map i₁ point) ∈ Set.range (F.map i₂) :=
    (sameRange (F.map i₁ point)).2 ⟨point, rfl⟩
  let forward := subobjectComparisonActionHom F i₁ i₂ y forwardRange
  apply H.map_injective
  rw [Functor.map_comp, Functor.map_comp]
  change H.map (H.preimage forward) ≫ H.map i₂ =
    H.map i₁ ≫ H.map y.hom
  rw [H.map_preimage]
  exact subobjectComparisonActionHom_comp F i₁ i₂ y forwardRange

end CategoryTheory.PreGaloisCategory

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace EtaleFundamentalGroup

/-- A pointed anabelioid pullback is surjective on connected-component
orbit sets.  This is a consequence of the chosen fiber equivalence, not an
extra hypothesis on the morphism. -/
theorem fiberComponentMap_surjective
    {source target : EtaleFundamentalGroup.{u}}
    (morphism : SourcePointedAnabelioidHom source target)
    (object : target.Cover) :
    Function.Surjective (fiberComponentMap morphism object) := by
  letI := target.coverCategory
  letI := source.coverCategory
  letI := target.galoisCategory
  letI := source.galoisCategory
  letI := target.fiberFunctor
  letI := source.fiberFunctor
  intro component
  refine Quotient.inductionOn' component ?_
  intro point
  let preimage : source.fiber.obj (morphism.pullback.obj object) :=
    morphism.fiberIso.inv.app object point
  refine ⟨Quotient.mk'
    (s := MulAction.orbitRel (Aut source.fiber)
      (source.fiber.obj (morphism.pullback.obj object))) preimage, ?_⟩
  apply Quotient.sound
  change _ ∈ MulAction.orbit (Aut target.fiber) point
  have cancellation :
      morphism.fiberIso.hom.app object preimage = point :=
    FintypeCat.inv_hom_id_apply (morphism.fiberIso.app object) point
  have cancellation' :
      (fun value => morphism.fiberIso.hom.app object value) preimage = point :=
    cancellation
  rw [cancellation']
  exact MulAction.mem_orbit_self (M := Aut target.fiber) point

end EtaleFundamentalGroup

namespace SourceSemiGraphOfAnabelioids.GluedObject

variable (diagram : Iut.SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (object : diagram.GluedObject)

/-- The gluing isomorphism across an edge, together with the two pointed
branch comparisons, identifies the fiber functors obtained by evaluating at
its incident vertices. -/
noncomputable def incidentRootFiberIso
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    rootFiber diagram first.vertex ≅ rootFiber diagram second.vertex := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  let firstEvaluation := evaluation (diagram := diagram) first.vertex
  let secondEvaluation := evaluation (diagram := diagram) second.vertex
  let firstPullback := first.pullback
  let secondPullback := second.pullback
  let edgeFiber := (diagram.edgeAnabelioid edge).fiber
  exact
    (Functor.isoWhiskerLeft firstEvaluation
      (diagram.branchMorphism first.branch first.abuts).fiberIso).symm ≪≫
    (Functor.associator firstEvaluation firstPullback edgeFiber).symm ≪≫
    Functor.isoWhiskerRight (branchComparison first second) edgeFiber ≪≫
    Functor.associator secondEvaluation secondPullback edgeFiber ≪≫
    Functor.isoWhiskerLeft secondEvaluation
      (diagram.branchMorphism second.branch second.abuts).fiberIso

/-- An adjacency of base vertices admits the corresponding comparison of
their evaluation fiber functors. -/
theorem adjacentRootFiberIso_nonempty
    {first second : diagram.base.Vertex}
    (adjacent : diagram.base.Adjacent first second) :
    Nonempty (rootFiber diagram first ≅ rootFiber diagram second) := by
  rcases adjacent with
    ⟨edge, firstBranch, secondBranch, _branchesDistinct,
      firstAbuts, secondAbuts⟩
  exact ⟨incidentRootFiberIso diagram
    ⟨firstBranch, first, firstAbuts⟩
    ⟨secondBranch, second, secondAbuts⟩⟩

/-- A selected comparison of evaluation fiber functors across an adjacency. -/
noncomputable def adjacentRootFiberIso
    {first second : diagram.base.Vertex}
    (adjacent : diagram.base.Adjacent first second) :
    rootFiber diagram first ≅ rootFiber diagram second :=
  Classical.choice (adjacentRootFiberIso_nonempty diagram adjacent)

/-- A closed-edge path in the base admits a comparison of its endpoint fiber
functors. -/
theorem pathRootFiberIso_nonempty
    {first second : diagram.base.Vertex}
    (path : Relation.ReflTransGen diagram.base.Adjacent first second) :
    Nonempty (rootFiber diagram first ≅ rootFiber diagram second) := by
  induction path with
  | refl => exact ⟨Iso.refl _⟩
  | @tail middle final path adjacent inductionHypothesis =>
      exact ⟨Classical.choice inductionHypothesis ≪≫
        adjacentRootFiberIso diagram adjacent⟩

/-- Fiber-functor transport along a closed-edge path in the base semigraph. -/
noncomputable def pathRootFiberIso
    {first second : diagram.base.Vertex}
    (path : Relation.ReflTransGen diagram.base.Adjacent first second) :
    rootFiber diagram first ≅ rootFiber diagram second :=
  Classical.choice (pathRootFiberIso_nonempty diagram path)

/-- Connectedness supplies a comparison between the evaluation fiber
functors at any two vertices. -/
theorem connectedRootFiberIso_nonempty
    (first second : diagram.base.Vertex) :
    Nonempty (rootFiber diagram first ≅ rootFiber diagram second) := by
  rcases diagram.connected with connected | isolated
  · exact pathRootFiberIso_nonempty diagram (connected.2.2 first second)
  · letI : IsEmpty diagram.base.Vertex := isolated.1
    exact isEmptyElim first

/-- A selected comparison of evaluation fiber functors at two vertices of a
connected base semigraph. -/
noncomputable def connectedRootFiberIso
    (first second : diagram.base.Vertex) :
    rootFiber diagram first ≅ rootFiber diagram second :=
  Classical.choice (connectedRootFiberIso_nonempty diagram first second)

/-- Incidence from an edge component to any incident vertex component is
surjective. -/
theorem coverComponentMap_surjective
    {edge : diagram.base.Edge}
    (branch : diagram.IncidentBranch edge) :
    Function.Surjective (coverComponentMap diagram root object branch) := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  apply Function.Surjective.comp
    (EtaleFundamentalGroup.fiberComponentMap_surjective
      (diagram.branchMorphism branch.branch branch.abuts)
      (object.vertexObject branch.vertex))
  exact (EtaleFundamentalGroup.fiberComponentEquiv
    (diagram.edgeAnabelioid edge)
    (coverEdgeIdentification diagram root object branch)).surjective

/-- Lift one adjacency step of the base semigraph from a selected component
over its initial vertex. -/
theorem exists_adjacent_lift
    {first second : diagram.base.Vertex}
    (component : CoverVertexComponent diagram object first)
    (adjacent : diagram.base.Adjacent first second) :
    ∃ targetComponent : CoverVertexComponent diagram object second,
      (finiteEtaleCoverSemiGraph diagram root object).Adjacent
        ⟨first, component⟩ ⟨second, targetComponent⟩ := by
  rcases adjacent with
    ⟨edge, firstBranch, secondBranch, branchesDistinct,
      firstAbuts, secondAbuts⟩
  let firstIncident : diagram.IncidentBranch edge :=
    ⟨firstBranch, first, firstAbuts⟩
  let secondIncident : diagram.IncidentBranch edge :=
    ⟨secondBranch, second, secondAbuts⟩
  obtain ⟨edgeComponent, mapsToComponent⟩ :=
    coverComponentMap_surjective diagram root object firstIncident component
  let targetComponent :=
    coverComponentMap diagram root object secondIncident edgeComponent
  refine ⟨targetComponent, ⟨⟨edge, edgeComponent⟩,
    firstBranch, secondBranch, branchesDistinct, ?_, ?_⟩⟩
  · change (finiteEtaleCoverSemiGraph diagram root object).coincidence
      ⟨edge, edgeComponent⟩ firstBranch = some ⟨first, component⟩
    rw [finiteEtaleCoverSemiGraph_coincidence_of_some
      diagram root object firstAbuts]
    apply congrArg some
    refine Sigma.ext rfl ?_
    exact heq_of_eq mapsToComponent
  · change (finiteEtaleCoverSemiGraph diagram root object).coincidence
      ⟨edge, edgeComponent⟩ secondBranch = some ⟨second, targetComponent⟩
    exact finiteEtaleCoverSemiGraph_coincidence_of_some
      diagram root object secondAbuts

/-- Every closed-edge path in the base lifts from a chosen vertex component.
The endpoint component is constructed rather than supplied. -/
theorem exists_path_lift
    {first second : diagram.base.Vertex}
    (component : CoverVertexComponent diagram object first)
    (path : Relation.ReflTransGen diagram.base.Adjacent first second) :
    ∃ targetComponent : CoverVertexComponent diagram object second,
      Relation.ReflTransGen
        (finiteEtaleCoverSemiGraph diagram root object).Adjacent
        ⟨first, component⟩ ⟨second, targetComponent⟩ := by
  induction path with
  | refl =>
      exact ⟨component, Relation.ReflTransGen.refl⟩
  | @tail middle final path adjacent inductionHypothesis =>
      obtain ⟨middleComponent, liftedPath⟩ := inductionHypothesis
      obtain ⟨finalComponent, liftedAdjacent⟩ :=
        exists_adjacent_lift diagram root object middleComponent adjacent
      exact ⟨finalComponent,
        Relation.ReflTransGen.tail liftedPath liftedAdjacent⟩

/-- Every lifted vertex can be joined to some lifted vertex above the chosen
root.  Thus the remaining connectedness question is entirely within one
root fiber. -/
theorem exists_path_to_root
    (vertex : CoverVertex diagram object) :
    ∃ rootComponent : CoverVertexComponent diagram object root,
      Relation.ReflTransGen
        (finiteEtaleCoverSemiGraph diagram root object).Adjacent
        vertex ⟨root, rootComponent⟩ := by
  rcases vertex with ⟨baseVertex, component⟩
  rcases diagram.connected with connected | isolated
  · exact exists_path_lift diagram root object component
      (connected.2.2 baseVertex root)
  · letI : IsEmpty diagram.base.Vertex := isolated.1
    exact isEmptyElim root

/-! ## A semigraph component as constituent subobjects -/

/-- Adjacency in the finite-etale semigraph is symmetric. -/
theorem coverAdjacent_symm
    {first second : CoverVertex diagram object}
    (adjacent :
      (finiteEtaleCoverSemiGraph diagram root object).Adjacent first second) :
    (finiteEtaleCoverSemiGraph diagram root object).Adjacent second first := by
  rcases adjacent with
    ⟨edge, firstBranch, secondBranch, branchesDistinct,
      firstAbuts, secondAbuts⟩
  exact ⟨edge, secondBranch, firstBranch, branchesDistinct.symm,
    secondAbuts, firstAbuts⟩

/-- Membership in the connected component of a chosen lifted vertex. -/
def CoverReachableFrom
    (base current : CoverVertex diagram object) : Prop :=
  Relation.ReflTransGen
    (finiteEtaleCoverSemiGraph diagram root object).Adjacent base current

/-- Reachability is preserved by one adjacency step. -/
theorem coverReachableFrom_of_adjacent
    {base first second : CoverVertex diagram object}
    (reachable : CoverReachableFrom diagram root object base first)
    (adjacent :
      (finiteEtaleCoverSemiGraph diagram root object).Adjacent first second) :
    CoverReachableFrom diagram root object base second :=
  Relation.ReflTransGen.tail reachable adjacent

/-- Reachability can be transported backwards across one adjacency step. -/
theorem coverReachableFrom_of_adjacent_symm
    {base first second : CoverVertex diagram object}
    (reachable : CoverReachableFrom diagram root object base second)
    (adjacent :
      (finiteEtaleCoverSemiGraph diagram root object).Adjacent first second) :
    CoverReachableFrom diagram root object base first :=
  coverReachableFrom_of_adjacent diagram root object reachable
    (coverAdjacent_symm diagram root object adjacent)

/-- The points over one base vertex whose local orbit belongs to a fixed
connected component of the finite-etale semigraph form an invariant subset
of the constituent fiber. -/
noncomputable def reachableVertexSubaction
    (base : CoverVertex diagram object)
    (vertex : diagram.base.Vertex) :
    let data := diagram.vertexAnabelioid vertex
    letI := data.coverCategory
    letI := data.galoisCategory
    letI := data.fiberFunctor
    SubMulAction (Aut data.fiber)
      (data.fiber.obj (object.vertexObject vertex)) := by
  let data := diagram.vertexAnabelioid vertex
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  refine
    { carrier := {point | CoverReachableFrom diagram root object base
        ⟨vertex, Quotient.mk'' point⟩}
      smul_mem' := ?_ }
  intro automorphism point reachable
  have componentEquality :
      (Quotient.mk'' (automorphism • point) :
          CoverVertexComponent diagram object vertex) =
        Quotient.mk'' point := by
    apply Quotient.sound
    change automorphism • point ∈
      MulAction.orbit (Aut data.fiber) point
    exact MulAction.mem_orbit point automorphism
  have vertexEquality :
      (⟨vertex, Quotient.mk'' (automorphism • point)⟩ :
          CoverVertex diagram object) =
        ⟨vertex, Quotient.mk'' point⟩ := by
    exact Sigma.ext rfl (heq_of_eq componentEquality)
  change CoverReachableFrom diagram root object base
    ⟨vertex, Quotient.mk'' (automorphism • point)⟩
  rw [vertexEquality]
  exact reachable

/-- The finite action carried by the reachable points over one vertex. -/
noncomputable def reachableVertexAction
    (base : CoverVertex diagram object)
    (vertex : diagram.base.Vertex) :
    let data := diagram.vertexAnabelioid vertex
    letI := data.coverCategory
    letI := data.galoisCategory
    letI := data.fiberFunctor
    Action FintypeCat (Aut data.fiber) := by
  let data := diagram.vertexAnabelioid vertex
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  let selected := reachableVertexSubaction
    (diagram := diagram) (root := root) (object := object) base vertex
  letI : Fintype selected := Fintype.ofFinite selected
  exact Action.FintypeCat.ofMulAction (Aut data.fiber)
    (FintypeCat.of selected)

/-- Inclusion of the reachable-point action into the complete constituent
fiber action. -/
noncomputable def reachableVertexActionInclusion
    (base : CoverVertex diagram object)
    (vertex : diagram.base.Vertex) :
    let data := diagram.vertexAnabelioid vertex
    letI := data.coverCategory
    letI := data.galoisCategory
    letI := data.fiberFunctor
    reachableVertexAction
        (diagram := diagram) (root := root) (object := object) base vertex ⟶
      (PreGaloisCategory.functorToAction data.fiber).obj
        (object.vertexObject vertex) := by
  let data := diagram.vertexAnabelioid vertex
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  exact
    { hom := FintypeCat.homMk Subtype.val
      comm := fun _ => rfl }

noncomputable instance reachableVertexActionInclusion_mono
    (base : CoverVertex diagram object)
    (vertex : diagram.base.Vertex) :
    let data := diagram.vertexAnabelioid vertex
    letI := data.coverCategory
    letI := data.galoisCategory
    letI := data.fiberFunctor
    Mono (reachableVertexActionInclusion
      (diagram := diagram) (root := root) (object := object) base vertex) := by
  let data := diagram.vertexAnabelioid vertex
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  apply ConcreteCategory.mono_of_injective
  exact Subtype.val_injective

/-- The Galois-category lift of the reachable-point subaction. -/
noncomputable def reachableVertexLift
    (base : CoverVertex diagram object)
    (vertex : diagram.base.Vertex) :
    let data := diagram.vertexAnabelioid vertex
    letI := data.coverCategory
    letI := data.galoisCategory
    letI := data.fiberFunctor
    ∃ (selected : data.Cover) (inclusion : selected ⟶ object.vertexObject vertex)
      (comparison : reachableVertexAction
          (diagram := diagram) (root := root) (object := object) base vertex ≅
        (PreGaloisCategory.functorToAction data.fiber).obj selected),
      Mono inclusion ∧
        comparison.hom ≫
            (PreGaloisCategory.functorToAction data.fiber).map inclusion =
          reachableVertexActionInclusion
            (diagram := diagram) (root := root) (object := object) base vertex := by
  let data := diagram.vertexAnabelioid vertex
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  exact PreGaloisCategory.exists_lift_of_mono data.fiber
    (object.vertexObject vertex)
    (reachableVertexAction
      (diagram := diagram) (root := root) (object := object) base vertex)
    (reachableVertexActionInclusion
      (diagram := diagram) (root := root) (object := object) base vertex)

/-- The selected constituent subobject over a vertex. -/
noncomputable def reachableVertexObject
    (base : CoverVertex diagram object)
    (vertex : diagram.base.Vertex) :
    (diagram.vertexAnabelioid vertex).Cover := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact Classical.choose
    (reachableVertexLift
      (diagram := diagram) (root := root) (object := object) base vertex)

/-- Inclusion of the selected constituent subobject. -/
noncomputable def reachableVertexInclusion
    (base : CoverVertex diagram object)
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    reachableVertexObject
        (diagram := diagram) (root := root) (object := object) base vertex ⟶
      object.vertexObject vertex := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact Classical.choose (Classical.choose_spec
    (reachableVertexLift
      (diagram := diagram) (root := root) (object := object) base vertex))

noncomputable instance reachableVertexInclusion_mono
    (base : CoverVertex diagram object)
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    Mono (reachableVertexInclusion
      (diagram := diagram) (root := root) (object := object) base vertex) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec
      (reachableVertexLift
        (diagram := diagram) (root := root) (object := object) base vertex)))).1

/-- The action-level comparison supplied by the constituent lift. -/
noncomputable def reachableVertexComparison
    (base : CoverVertex diagram object)
    (vertex : diagram.base.Vertex) :
    let data := diagram.vertexAnabelioid vertex
    letI := data.coverCategory
    letI := data.galoisCategory
    letI := data.fiberFunctor
    reachableVertexAction
        (diagram := diagram) (root := root) (object := object) base vertex ≅
      (PreGaloisCategory.functorToAction data.fiber).obj
        (reachableVertexObject
          (diagram := diagram) (root := root) (object := object) base vertex) := by
  let data := diagram.vertexAnabelioid vertex
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  exact Classical.choose (Classical.choose_spec (Classical.choose_spec
    (reachableVertexLift
      (diagram := diagram) (root := root) (object := object) base vertex)))

/-- The selected-action comparison commutes with its inclusion into the
complete constituent fiber. -/
theorem reachableVertexComparison_hom_comp
    (base : CoverVertex diagram object)
    (vertex : diagram.base.Vertex) :
    let data := diagram.vertexAnabelioid vertex
    letI := data.coverCategory
    letI := data.galoisCategory
    letI := data.fiberFunctor
    (reachableVertexComparison
          (diagram := diagram) (root := root) (object := object) base vertex).hom ≫
        (PreGaloisCategory.functorToAction data.fiber).map
          (reachableVertexInclusion
            (diagram := diagram) (root := root) (object := object) base vertex) =
      reachableVertexActionInclusion
        (diagram := diagram) (root := root) (object := object) base vertex := by
  let data := diagram.vertexAnabelioid vertex
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  exact (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec
      (reachableVertexLift
        (diagram := diagram) (root := root) (object := object) base vertex)))).2

/-- A constituent-fiber point lies in the lifted subobject exactly when its
local component belongs to the selected semigraph component. -/
theorem mem_range_reachableVertexInclusion_iff
    (base : CoverVertex diagram object)
    (vertex : diagram.base.Vertex) :
    let data := diagram.vertexAnabelioid vertex
    letI := data.coverCategory
    letI := data.galoisCategory
    letI := data.fiberFunctor
    ∀ point : data.fiber.obj (object.vertexObject vertex),
      point ∈ Set.range (data.fiber.map
          (reachableVertexInclusion
            (diagram := diagram) (root := root) (object := object) base vertex)) ↔
        CoverReachableFrom diagram root object base
          ⟨vertex, Quotient.mk'' point⟩ := by
  let data := diagram.vertexAnabelioid vertex
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  let comparison := reachableVertexComparison
    (diagram := diagram) (root := root) (object := object) base vertex
  have comparisonSquare := reachableVertexComparison_hom_comp
    (diagram := diagram) (root := root) (object := object) base vertex
  dsimp only
  intro point
  constructor
  · rintro ⟨selectedPoint, rfl⟩
    let actionPoint := comparison.inv.hom selectedPoint
    have actionCancellation : comparison.hom.hom actionPoint = selectedPoint := by
      have cancellation := congrArg (fun morphism => morphism.hom)
        comparison.inv_hom_id
      have cancellationAt := ConcreteCategory.congr_hom cancellation selectedPoint
      simpa only [Action.comp_hom, FintypeCat.comp_apply,
        Action.id_hom, FintypeCat.id_apply] using cancellationAt
    have squareAt := congrArg
      (fun morphism => morphism.hom.hom actionPoint) comparisonSquare
    have valueEquality :
        data.fiber.map
            (reachableVertexInclusion
              (diagram := diagram) (root := root) (object := object) base vertex)
            selectedPoint = actionPoint.1 := by
      change data.fiber.map
          (reachableVertexInclusion
            (diagram := diagram) (root := root) (object := object) base vertex)
          (comparison.hom.hom actionPoint) = actionPoint.1 at squareAt
      rw [actionCancellation] at squareAt
      exact squareAt
    rw [valueEquality]
    exact actionPoint.2
  · intro reachable
    let actionPoint :
        (reachableVertexAction
          (diagram := diagram) (root := root) (object := object) base vertex).V :=
      ⟨point, reachable⟩
    refine ⟨comparison.hom.hom actionPoint, ?_⟩
    have squareAt := congrArg
      (fun morphism => morphism.hom.hom actionPoint) comparisonSquare
    change data.fiber.map
        (reachableVertexInclusion
          (diagram := diagram) (root := root) (object := object) base vertex)
        (comparison.hom.hom actionPoint) = actionPoint.1 at squareAt
    exact squareAt

/-- The canonical edge component represented by a point in the pullback at
an arbitrary incident branch. -/
noncomputable def coverEdgeComponentOfBranchPoint
    {edge : diagram.base.Edge}
    (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (diagram.edgeAnabelioid edge).fiber.obj
        (branch.pullback.obj (object.vertexObject branch.vertex)) →
      CoverEdgeComponent diagram root object edge := by
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid
    (coverReferenceBranch diagram root edge).vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI := (diagram.edgeAnabelioid edge).fiberFunctor
  intro point
  exact Quotient.mk''
    ((diagram.edgeAnabelioid edge).fiber.map
      (coverEdgeIdentification diagram root object branch).inv point)

/-- Incidence of the edge component represented by a branch point is the
local orbit of that point after the pointed branch comparison. -/
theorem coverComponentMap_coverEdgeComponentOfBranchPoint
    {edge : diagram.base.Edge}
    (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ∀ point : (diagram.edgeAnabelioid edge).fiber.obj
        (branch.pullback.obj (object.vertexObject branch.vertex)),
      coverComponentMap diagram root object branch
          (coverEdgeComponentOfBranchPoint
            (diagram := diagram) (root := root) (object := object) branch point) =
        Quotient.mk''
          ((diagram.branchMorphism branch.branch branch.abuts).fiberIso.hom.app
            (object.vertexObject branch.vertex) point) := by
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.vertexAnabelioid
    (coverReferenceBranch diagram root edge).vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.vertexAnabelioid branch.vertex).galoisCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI := (diagram.vertexAnabelioid branch.vertex).fiberFunctor
  letI := (diagram.edgeAnabelioid edge).fiberFunctor
  intro point
  apply Quotient.sound
  change _ ∈ MulAction.orbit
    (Aut (diagram.vertexAnabelioid branch.vertex).fiber)
    ((diagram.branchMorphism branch.branch branch.abuts).fiberIso.hom.app
      (object.vertexObject branch.vertex) point)
  have edgeCancellation :
      (diagram.edgeAnabelioid edge).fiber.map
          (coverEdgeIdentification diagram root object branch).hom
          ((diagram.edgeAnabelioid edge).fiber.map
            (coverEdgeIdentification diagram root object branch).inv point) =
        point := by
    simp only [← FintypeCat.comp_apply, ← Functor.map_comp,
      (coverEdgeIdentification diagram root object branch).inv_hom_id,
      Functor.map_id_apply]
  change
    (diagram.branchMorphism branch.branch branch.abuts).fiberIso.hom.app
        (object.vertexObject branch.vertex)
        ((diagram.edgeAnabelioid edge).fiber.map
          (coverEdgeIdentification diagram root object branch).hom
          ((diagram.edgeAnabelioid edge).fiber.map
            (coverEdgeIdentification diagram root object branch).inv point)) ∈
      MulAction.orbit
        (Aut (diagram.vertexAnabelioid branch.vertex).fiber)
        ((diagram.branchMorphism branch.branch branch.abuts).fiberIso.hom.app
          (object.vertexObject branch.vertex) point)
  rw [edgeCancellation]
  exact MulAction.mem_orbit_self
    (M := Aut (diagram.vertexAnabelioid branch.vertex).fiber) _

/-- Transporting a branch point through the glued object's edge
identification does not change the represented canonical edge component. -/
theorem coverEdgeComponentOfBranchPoint_glue
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ∀ point : (diagram.edgeAnabelioid edge).fiber.obj
        (first.pullback.obj (object.vertexObject first.vertex)),
      coverEdgeComponentOfBranchPoint
          (diagram := diagram) (root := root) (object := object) second
          ((diagram.edgeAnabelioid edge).fiber.map
            (object.glue first second).hom point) =
        coverEdgeComponentOfBranchPoint
          (diagram := diagram) (root := root) (object := object) first point := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI := (diagram.edgeAnabelioid edge).fiberFunctor
  intro point
  have morphismEquality :
      (object.glue first second).hom ≫
          (coverEdgeIdentification diagram root object second).inv =
        (coverEdgeIdentification diagram root object first).inv := by
    apply (cancel_epi
      (coverEdgeIdentification diagram root object first).hom).1
    change
      (object.glue reference first).hom ≫
          (object.glue first second).hom ≫
          (object.glue reference second).inv =
        (object.glue reference first).hom ≫
          (object.glue reference first).inv
    rw [← Category.assoc, ← Iso.trans_hom,
      object.glue_trans reference first second]
    simp
  apply Quotient.sound
  change _ ∈ MulAction.orbit (Aut (diagram.edgeAnabelioid edge).fiber) _
  have pointEquality :
      (diagram.edgeAnabelioid edge).fiber.map
          (coverEdgeIdentification diagram root object second).inv
          ((diagram.edgeAnabelioid edge).fiber.map
            (object.glue first second).hom point) =
        (diagram.edgeAnabelioid edge).fiber.map
          (coverEdgeIdentification diagram root object first).inv point := by
    simp only [← FintypeCat.comp_apply, ← Functor.map_comp,
      morphismEquality]
  rw [pointEquality]
  exact MulAction.mem_orbit_self
    (M := Aut (diagram.edgeAnabelioid edge).fiber) _

/-- The two local components represented by points identified across one
edge lie in the same connected component of the finite-etale semigraph. -/
theorem coverReachableFrom_glue_iff
    (base : CoverVertex diagram object)
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ∀ point : (diagram.edgeAnabelioid edge).fiber.obj
        (first.pullback.obj (object.vertexObject first.vertex)),
      CoverReachableFrom diagram root object base
          ⟨second.vertex, Quotient.mk''
            ((diagram.branchMorphism second.branch second.abuts).fiberIso.hom.app
              (object.vertexObject second.vertex)
              ((diagram.edgeAnabelioid edge).fiber.map
                (object.glue first second).hom point))⟩ ↔
        CoverReachableFrom diagram root object base
          ⟨first.vertex, Quotient.mk''
            ((diagram.branchMorphism first.branch first.abuts).fiberIso.hom.app
              (object.vertexObject first.vertex) point)⟩ := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.vertexAnabelioid
    (coverReferenceBranch diagram root edge).vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.vertexAnabelioid first.vertex).galoisCategory
  letI := (diagram.vertexAnabelioid second.vertex).galoisCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI := (diagram.vertexAnabelioid first.vertex).fiberFunctor
  letI := (diagram.vertexAnabelioid second.vertex).fiberFunctor
  letI := (diagram.edgeAnabelioid edge).fiberFunctor
  intro point
  by_cases branchesDistinct : first.branch ≠ second.branch
  · let edgeComponent := coverEdgeComponentOfBranchPoint
      (diagram := diagram) (root := root) (object := object) first point
    let secondPoint := (diagram.edgeAnabelioid edge).fiber.map
      (object.glue first second).hom point
    let firstComponent : CoverVertexComponent diagram object first.vertex :=
      Quotient.mk''
        ((diagram.branchMorphism first.branch first.abuts).fiberIso.hom.app
          (object.vertexObject first.vertex) point)
    let secondComponent : CoverVertexComponent diagram object second.vertex :=
      Quotient.mk''
        ((diagram.branchMorphism second.branch second.abuts).fiberIso.hom.app
          (object.vertexObject second.vertex) secondPoint)
    have firstComponentEquality :
        coverComponentMap diagram root object first edgeComponent =
          firstComponent :=
      coverComponentMap_coverEdgeComponentOfBranchPoint
        (diagram := diagram) (root := root) (object := object) first point
    have secondComponentEquality :
        coverComponentMap diagram root object second edgeComponent =
          secondComponent := by
      have representedEquality := coverEdgeComponentOfBranchPoint_glue
        (diagram := diagram) (root := root) (object := object)
        first second point
      have componentEquality :=
        coverComponentMap_coverEdgeComponentOfBranchPoint
          (diagram := diagram) (root := root) (object := object)
          second secondPoint
      rw [representedEquality] at componentEquality
      exact componentEquality
    have adjacent :
        (finiteEtaleCoverSemiGraph diagram root object).Adjacent
          ⟨first.vertex, firstComponent⟩ ⟨second.vertex, secondComponent⟩ := by
      refine ⟨⟨edge, edgeComponent⟩,
        first.branch, second.branch, branchesDistinct, ?_, ?_⟩
      · change (finiteEtaleCoverSemiGraph diagram root object).coincidence
          ⟨edge, edgeComponent⟩ first.branch =
            some ⟨first.vertex, firstComponent⟩
        rw [finiteEtaleCoverSemiGraph_coincidence_of_some
          diagram root object first.abuts]
        apply congrArg some
        exact Sigma.ext rfl (heq_of_eq firstComponentEquality)
      · change (finiteEtaleCoverSemiGraph diagram root object).coincidence
          ⟨edge, edgeComponent⟩ second.branch =
            some ⟨second.vertex, secondComponent⟩
        rw [finiteEtaleCoverSemiGraph_coincidence_of_some
          diagram root object second.abuts]
        apply congrArg some
        exact Sigma.ext rfl (heq_of_eq secondComponentEquality)
    constructor
    · intro secondReachable
      exact coverReachableFrom_of_adjacent_symm diagram root object
        secondReachable adjacent
    · intro firstReachable
      exact coverReachableFrom_of_adjacent diagram root object
        firstReachable adjacent
  · have branchesEqual : first.branch = second.branch :=
      not_ne_iff.mp branchesDistinct
    have incidentEquality : first = second := by
      rcases first with ⟨firstBranch, firstVertex, firstAbuts⟩
      rcases second with ⟨secondBranch, secondVertex, secondAbuts⟩
      dsimp only at branchesEqual
      subst secondBranch
      have vertexEquality : firstVertex = secondVertex :=
        Option.some.inj (firstAbuts.symm.trans secondAbuts)
      subst secondVertex
      rfl
    subst second
    rw [object.glue_refl first]
    simp

/-- Pulling a selected constituent subobject to an incident edge selects
exactly the edge-fiber points whose incident vertex component is reachable. -/
theorem mem_range_pullback_reachableVertexInclusion_iff
    (base : CoverVertex diagram object)
    {edge : diagram.base.Edge}
    (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ∀ point : (diagram.edgeAnabelioid edge).fiber.obj
        (branch.pullback.obj (object.vertexObject branch.vertex)),
      point ∈ Set.range ((diagram.edgeAnabelioid edge).fiber.map
          (branch.pullback.map
            (reachableVertexInclusion
              (diagram := diagram) (root := root) (object := object)
              base branch.vertex))) ↔
        CoverReachableFrom diagram root object base
          ⟨branch.vertex, Quotient.mk''
            ((diagram.branchMorphism branch.branch branch.abuts).fiberIso.hom.app
              (object.vertexObject branch.vertex) point)⟩ := by
  let vertexData := diagram.vertexAnabelioid branch.vertex
  let edgeData := diagram.edgeAnabelioid edge
  letI := vertexData.coverCategory
  letI := edgeData.coverCategory
  letI := vertexData.galoisCategory
  letI := edgeData.galoisCategory
  letI := vertexData.fiberFunctor
  letI := edgeData.fiberFunctor
  intro point
  let inclusion := reachableVertexInclusion
    (diagram := diagram) (root := root) (object := object) base branch.vertex
  let comparison :=
    (diagram.branchMorphism branch.branch branch.abuts).fiberIso
  have selectedRange := mem_range_reachableVertexInclusion_iff
    (diagram := diagram) (root := root) (object := object)
    base branch.vertex
  constructor
  · rintro ⟨selectedPoint, rfl⟩
    apply (selectedRange _).1
    refine ⟨comparison.hom.app
      (reachableVertexObject
        (diagram := diagram) (root := root) (object := object)
        base branch.vertex) selectedPoint, ?_⟩
    have naturalityAt := ConcreteCategory.congr_hom
      (comparison.hom.naturality inclusion) selectedPoint
    exact naturalityAt.symm
  · intro reachable
    obtain ⟨vertexPoint, vertexPointMaps⟩ := (selectedRange _).2 reachable
    let selectedObject := reachableVertexObject
      (diagram := diagram) (root := root) (object := object)
      base branch.vertex
    let edgePoint := comparison.inv.app selectedObject vertexPoint
    refine ⟨edgePoint, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso
      (comparison.hom.app (object.vertexObject branch.vertex))).1
    have naturalityAt := ConcreteCategory.congr_hom
      (comparison.hom.naturality inclusion) edgePoint
    have comparisonCancellation :
        comparison.hom.app selectedObject edgePoint = vertexPoint := by
      exact FintypeCat.inv_hom_id_apply (comparison.app selectedObject) vertexPoint
    calc
      comparison.hom.app (object.vertexObject branch.vertex)
          (edgeData.fiber.map (branch.pullback.map inclusion) edgePoint) =
        vertexData.fiber.map inclusion
          (comparison.hom.app selectedObject edgePoint) := naturalityAt
      _ = vertexData.fiber.map inclusion vertexPoint := by
        rw [comparisonCancellation]
      _ = comparison.hom.app (object.vertexObject branch.vertex) point :=
        vertexPointMaps

/-- Canonical gluing of the constituent subobjects selected by one
semigraph connected component. -/
noncomputable def reachableGlue
    (base : CoverVertex diagram object)
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    first.pullback.obj
        (reachableVertexObject
          (diagram := diagram) (root := root) (object := object)
          base first.vertex) ≅
      second.pullback.obj
        (reachableVertexObject
          (diagram := diagram) (root := root) (object := object)
          base second.vertex) := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI := (diagram.edgeAnabelioid edge).fiberFunctor
  letI : PreservesFiniteLimits first.pullback :=
    (diagram.branchMorphism first.branch first.abuts).preservesFiniteLimits
  letI : PreservesFiniteLimits second.pullback :=
    (diagram.branchMorphism second.branch second.abuts).preservesFiniteLimits
  let firstInclusion := first.pullback.map
    (reachableVertexInclusion
      (diagram := diagram) (root := root) (object := object)
      base first.vertex)
  let secondInclusion := second.pullback.map
    (reachableVertexInclusion
      (diagram := diagram) (root := root) (object := object)
      base second.vertex)
  apply PreGaloisCategory.subobjectComparisonIso
    (diagram.edgeAnabelioid edge).fiber
    firstInclusion secondInclusion (object.glue first second)
  intro point
  rw [mem_range_pullback_reachableVertexInclusion_iff
    (diagram := diagram) (root := root) (object := object) base second]
  rw [mem_range_pullback_reachableVertexInclusion_iff
    (diagram := diagram) (root := root) (object := object) base first]
  exact coverReachableFrom_glue_iff
    (diagram := diagram) (root := root) (object := object)
    base first second point

/-- The selected gluing commutes with the constituent inclusions into the
original glued object. -/
theorem reachableGlue_hom_comp_inclusion
    (base : CoverVertex diagram object)
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (reachableGlue
          (diagram := diagram) (root := root) (object := object)
          base first second).hom ≫
        second.pullback.map
          (reachableVertexInclusion
            (diagram := diagram) (root := root) (object := object)
            base second.vertex) =
      first.pullback.map
          (reachableVertexInclusion
            (diagram := diagram) (root := root) (object := object)
            base first.vertex) ≫
        (object.glue first second).hom := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI := (diagram.edgeAnabelioid edge).fiberFunctor
  letI : PreservesFiniteLimits first.pullback :=
    (diagram.branchMorphism first.branch first.abuts).preservesFiniteLimits
  letI : PreservesFiniteLimits second.pullback :=
    (diagram.branchMorphism second.branch second.abuts).preservesFiniteLimits
  exact PreGaloisCategory.subobjectComparisonIso_hom_comp
    (diagram.edgeAnabelioid edge).fiber
    (first.pullback.map
      (reachableVertexInclusion
        (diagram := diagram) (root := root) (object := object)
        base first.vertex))
    (second.pullback.map
      (reachableVertexInclusion
        (diagram := diagram) (root := root) (object := object)
        base second.vertex))
    (object.glue first second)
    (fun point => by
      rw [mem_range_pullback_reachableVertexInclusion_iff
        (diagram := diagram) (root := root) (object := object) base second]
      rw [mem_range_pullback_reachableVertexInclusion_iff
        (diagram := diagram) (root := root) (object := object) base first]
      exact coverReachableFrom_glue_iff
        (diagram := diagram) (root := root) (object := object)
        base first second point)

/-- Selected gluing is the identity on a repeated incident branch. -/
theorem reachableGlue_refl
    (base : CoverVertex diagram object)
    {edge : diagram.base.Edge}
    (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    reachableGlue
        (diagram := diagram) (root := root) (object := object)
        base branch branch = Iso.refl _ := by
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI : PreservesFiniteLimits branch.pullback :=
    (diagram.branchMorphism branch.branch branch.abuts).preservesFiniteLimits
  apply Iso.ext
  apply (cancel_mono
    (branch.pullback.map
      (reachableVertexInclusion
        (diagram := diagram) (root := root) (object := object)
        base branch.vertex))).1
  rw [reachableGlue_hom_comp_inclusion]
  rw [object.glue_refl branch]
  simp

/-- Selected gluing composes coherently among the branches of an edge. -/
theorem reachableGlue_trans
    (base : CoverVertex diagram object)
    {edge : diagram.base.Edge}
    (first second third : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.vertexAnabelioid third.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (reachableGlue
        (diagram := diagram) (root := root) (object := object)
        base first second).trans
      (reachableGlue
        (diagram := diagram) (root := root) (object := object)
        base second third) =
      reachableGlue
        (diagram := diagram) (root := root) (object := object)
        base first third := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.vertexAnabelioid third.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI : PreservesFiniteLimits third.pullback :=
    (diagram.branchMorphism third.branch third.abuts).preservesFiniteLimits
  apply Iso.ext
  apply (cancel_mono
    (third.pullback.map
      (reachableVertexInclusion
        (diagram := diagram) (root := root) (object := object)
        base third.vertex))).1
  simp only [Iso.trans_hom, Category.assoc]
  rw [reachableGlue_hom_comp_inclusion
    (diagram := diagram) (root := root) (object := object)
    base second third]
  rw [← Category.assoc]
  rw [reachableGlue_hom_comp_inclusion
    (diagram := diagram) (root := root) (object := object)
    base first second]
  rw [Category.assoc, ← Iso.trans_hom]
  rw [object.glue_trans first second third]
  exact (reachableGlue_hom_comp_inclusion
    (diagram := diagram) (root := root) (object := object)
    base first third).symm

/-- The constituent subobjects selected by one semigraph component assemble
to a genuine object of the glued category. -/
noncomputable def reachableObject
    (base : CoverVertex diagram object) : diagram.GluedObject where
  vertexObject := reachableVertexObject
    (diagram := diagram) (root := root) (object := object) base
  glue := reachableGlue
    (diagram := diagram) (root := root) (object := object) base
  glue_refl := reachableGlue_refl
    (diagram := diagram) (root := root) (object := object) base
  glue_trans := reachableGlue_trans
    (diagram := diagram) (root := root) (object := object) base

/-- Inclusion of one selected semigraph component into the original glued
object. -/
noncomputable def reachableInclusion
    (base : CoverVertex diagram object) :
    reachableObject
        (diagram := diagram) (root := root) (object := object) base ⟶ object where
  app := reachableVertexInclusion
    (diagram := diagram) (root := root) (object := object) base
  naturality := reachableGlue_hom_comp_inclusion
    (diagram := diagram) (root := root) (object := object) base

noncomputable instance reachableInclusion_mono
    (base : CoverVertex diagram object) :
    Mono (reachableInclusion
      (diagram := diagram) (root := root) (object := object) base) := by
  letI : ∀ vertex,
      letI := (diagram.vertexAnabelioid vertex).coverCategory
      Mono ((reachableInclusion
        (diagram := diagram) (root := root) (object := object) base).app vertex) :=
    fun vertex => reachableVertexInclusion_mono
      (diagram := diagram) (root := root) (object := object) base vertex
  apply mono_of_componentwise_mono

/-- The selected glued subobject is noninitial because its chosen semigraph
component reaches a component over the root, whose representative lifts to
the selected root fiber. -/
theorem reachableObject_notInitial
    (base : CoverVertex diagram object) :
    IsInitial (reachableObject
      (diagram := diagram) (root := root) (object := object) base) → False := by
  letI : GaloisCategory diagram.GluedObject :=
    galoisCategory diagram root
  letI := (diagram.vertexAnabelioid root).coverCategory
  letI := (diagram.vertexAnabelioid root).galoisCategory
  letI := (diagram.vertexAnabelioid root).fiberFunctor
  letI : PreGaloisCategory.FiberFunctor (rootFiber diagram root) :=
    rootFiberFunctor diagram root
  obtain ⟨rootComponent, pathToRoot⟩ :=
    exists_path_to_root diagram root object base
  let rootPoint : (diagram.vertexAnabelioid root).fiber.obj
      (object.vertexObject root) := rootComponent.out
  have rootPointComponent :
      (Quotient.mk'' rootPoint : CoverVertexComponent diagram object root) =
        rootComponent :=
    Quotient.out_eq' rootComponent
  have rootPointReachable :
      CoverReachableFrom diagram root object base
        ⟨root, Quotient.mk'' rootPoint⟩ := by
    rw [rootPointComponent]
    exact pathToRoot
  obtain ⟨selectedPoint, _selectedPointMaps⟩ :=
    (mem_range_reachableVertexInclusion_iff
      (diagram := diagram) (root := root) (object := object)
      base root rootPoint).2 rootPointReachable
  intro selectedInitial
  have emptyRootFiber :
      IsEmpty ((rootFiber diagram root).obj
        (reachableObject
          (diagram := diagram) (root := root) (object := object) base)) :=
    (PreGaloisCategory.initial_iff_fiber_empty (rootFiber diagram root)
      (reachableObject
        (diagram := diagram) (root := root) (object := object) base)).1
      ⟨selectedInitial⟩
  exact emptyRootFiber.false selectedPoint

/-- If the original glued object is connected, the noninitial subobject
selected by any semigraph component must be the whole object. -/
noncomputable instance reachableInclusion_isIso
    (base : CoverVertex diagram object)
    [PreGaloisCategory.IsConnected object] :
    IsIso (reachableInclusion
      (diagram := diagram) (root := root) (object := object) base) := by
  apply PreGaloisCategory.IsConnected.noTrivialComponent
  exact reachableObject_notInitial
    (diagram := diagram) (root := root) (object := object) base

/-- Reachability in the finite-etale semigraph is symmetric. -/
theorem coverReachableFrom_symmetric
    {first second : CoverVertex diagram object}
    (path : CoverReachableFrom diagram root object first second) :
    CoverReachableFrom diagram root object second first :=
  Relation.ReflTransGen.symmetric
    (fun _ _ adjacent => coverAdjacent_symm diagram root object adjacent) path

/-- A connected object of the literal glued category produces a connected
finite-etale semigraph, as asserted after Definition 2.1. -/
theorem finiteEtaleCoverSemiGraph_isConnected_of_isConnected
    [PreGaloisCategory.IsConnected object] :
    (finiteEtaleCoverSemiGraph diagram root object).IsConnected := by
  letI : GaloisCategory diagram.GluedObject :=
    galoisCategory diagram root
  letI := (diagram.vertexAnabelioid root).coverCategory
  letI := (diagram.vertexAnabelioid root).galoisCategory
  letI := (diagram.vertexAnabelioid root).fiberFunctor
  letI : PreGaloisCategory.FiberFunctor (rootFiber diagram root) :=
    rootFiberFunctor diagram root
  obtain ⟨rootPoint⟩ :=
    PreGaloisCategory.nonempty_fiber_of_isConnected
      (rootFiber diagram root) object
  let anchor : CoverVertex diagram object :=
    ⟨root, Quotient.mk'' rootPoint⟩
  refine Or.inl ⟨⟨anchor⟩, ?_, ?_⟩
  · intro liftedEdge
    rcases liftedEdge with ⟨edge, edgeComponent⟩
    let branch := coverReferenceBranch diagram root edge
    refine ⟨⟨branch.vertex,
      coverComponentMap diagram root object branch edgeComponent⟩,
      ⟨branch.branch, ?_⟩⟩
    change (finiteEtaleCoverSemiGraph diagram root object).coincidence
      ⟨edge, edgeComponent⟩ branch.branch =
        some ⟨branch.vertex,
          coverComponentMap diagram root object branch edgeComponent⟩
    exact finiteEtaleCoverSemiGraph_coincidence_of_some
      diagram root object branch.abuts
  · intro first second
    have reachableFromAnchor :
        ∀ current : CoverVertex diagram object,
          CoverReachableFrom diagram root object anchor current := by
      intro current
      rcases current with ⟨vertex, component⟩
      letI := (diagram.vertexAnabelioid vertex).coverCategory
      letI := (diagram.vertexAnabelioid vertex).galoisCategory
      letI := (diagram.vertexAnabelioid vertex).fiberFunctor
      let point : (diagram.vertexAnabelioid vertex).fiber.obj
          (object.vertexObject vertex) := component.out
      have pointComponent :
          (Quotient.mk'' point : CoverVertexComponent diagram object vertex) =
            component :=
        Quotient.out_eq' component
      let inclusion := reachableVertexInclusion
        (diagram := diagram) (root := root) (object := object)
        anchor vertex
      haveI : IsIso
          (reachableInclusion
            (diagram := diagram) (root := root) (object := object) anchor) :=
        reachableInclusion_isIso
          (diagram := diagram) (root := root) (object := object) anchor
      haveI : IsIso inclusion := by
        change IsIso ((evaluation (diagram := diagram) vertex).map
          (reachableInclusion
            (diagram := diagram) (root := root) (object := object) anchor))
        infer_instance
      have pointInRange :
          point ∈ Set.range
            ((diagram.vertexAnabelioid vertex).fiber.map inclusion) :=
        (ConcreteCategory.bijective_of_isIso
          ((diagram.vertexAnabelioid vertex).fiber.map inclusion)).2 point
      have reachablePoint :=
        (mem_range_reachableVertexInclusion_iff
          (diagram := diagram) (root := root) (object := object)
          anchor vertex point).1 pointInRange
      rw [pointComponent] at reachablePoint
      exact reachablePoint
    exact Relation.ReflTransGen.trans
      (coverReachableFrom_symmetric diagram root object
        (reachableFromAnchor first))
      (reachableFromAnchor second)

end SourceSemiGraphOfAnabelioids.GluedObject

end Iut
