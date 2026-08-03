/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedDeckGroup
import Iut.Foundations.SourceTemperedDeckTransitionSurjectivity
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final.Type

/-!
# Surjectivity of the literal tempered deck-group projections

Surjective transition maps between arbitrary inverse systems of countable
groups do not, by themselves, make every limit projection surjective.  The
deck system has additional finite-branching geometry: a transformation is
determined by one finite Galois symmetry and the image of one vertex in a
locally finite universal tree, and the transition lifting construction may
be chosen without increasing that vertex's depth.

This file isolates the corresponding bounded inverse-limit argument.  The
finite cofiltered-system theorem is applied only to bounded lift fibers,
which are genuinely finite; no compactness assertion is made for arbitrary
countable inverse systems.
-/

namespace Iut

universe u v w

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {Index : Type u} [Category.{w} Index]

/-- A cofiltered system whose bounded transition-lift fibers are finite and
nonempty has surjective evaluation maps on its space of sections. -/
theorem eval_section_surjective_of_bounded_lifts
    [IsCofiltered Index]
    (system : Index ⥤ Type v)
    (height : ∀ level, system.obj level → ℕ)
    (map_height : ∀ {finer coarser : Index} (map : finer ⟶ coarser)
      (value : system.obj finer),
      height coarser (system.map map value) ≤ height finer value)
    (bounded_fiber_finite : ∀ {finer coarser : Index}
      (map : finer ⟶ coarser) (target : system.obj coarser),
      Finite {source : system.obj finer //
        system.map map source = target ∧
          height finer source ≤ height coarser target})
    (bounded_lift : ∀ {finer coarser : Index} (map : finer ⟶ coarser)
      (target : system.obj coarser),
      ∃ source : system.obj finer,
        system.map map source = target ∧
          height finer source ≤ height coarser target)
    (level : Index) :
    Function.Surjective (fun compatible : system.sections ↦
      compatible.val level) := by
  intro target
  let identity : Index ⥤ Index := 𝟭 Index
  let Slice := CostructuredArrow identity level
  let projection : Slice ⥤ Index := CostructuredArrow.proj identity level
  let lifts : CostructuredArrow identity level ⥤ Type v :=
    { obj := fun refinement ↦
      { value : system.obj refinement.left //
        system.map refinement.hom value = target ∧
          height refinement.left value ≤ height level target }
      map := fun {first second} refinement ↦
        ↾fun (value : { value : system.obj first.left //
            system.map first.hom value = target ∧
              height first.left value ≤ height level target }) ↦
        ⟨system.map refinement.left value.1, by
          constructor
          · have triangle : refinement.left ≫ second.hom = first.hom := by
              exact CostructuredArrow.w refinement
            exact (system.map_comp_apply refinement.left second.hom value.1).symm.trans
              ((congrArg (fun map ↦ system.map map value.1) triangle).trans
                value.2.1)
          · exact (map_height refinement.left value.1).trans value.2.2⟩
      map_id := by
        intro refinement
        apply ConcreteCategory.hom_ext
        intro value
        apply Subtype.ext
        simp
      map_comp := by
        intro first second third firstMap secondMap
        apply ConcreteCategory.hom_ext
        intro value
        apply Subtype.ext
        simp }
  haveI finite_lifts (refinement : Slice) : Finite (lifts.obj refinement) := by
    exact bounded_fiber_finite refinement.hom target
  haveI nonempty_lifts (refinement : Slice) : Nonempty (lifts.obj refinement) := by
    obtain ⟨source, maps, bounded⟩ := bounded_lift refinement.hom target
    exact ⟨⟨source, maps, bounded⟩⟩
  haveI : IsCofiltered Slice := by
    change IsCofiltered (CostructuredArrow identity level)
    exact (Functor.initial_iff_isCofiltered_costructuredArrow identity).mp
      (inferInstance : identity.Initial) level
  obtain ⟨liftValues, liftCompatible⟩ :=
    nonempty_sections_of_finite_cofiltered_system lifts
  let liftSection : lifts.sections := ⟨liftValues, liftCompatible⟩
  let restrictedSection : (projection ⋙ system).sections :=
    ⟨fun refinement ↦ (liftSection.val refinement).1,
      fun {_ _} map ↦ by
        change system.map map.left (liftSection.val _).1 =
          (liftSection.val _).1
        exact congrArg Subtype.val (liftSection.property map)⟩
  haveI : projection.Initial := by
    dsimp only [projection]
    infer_instance
  obtain ⟨globalSection, sectionRestricts⟩ :=
    (projection.bijective_sectionsPrecomp system).2 restrictedSection
  refine ⟨globalSection, ?_⟩
  let identityRefinement : Slice := CostructuredArrow.mk (𝟙 level)
  have atIdentity := congrFun (congrArg Subtype.val sectionRestricts)
    identityRefinement
  change globalSection.val level =
    (liftSection.val identityRefinement).1 at atIdentity
  exact atIdentity.trans (by
    have maps := (liftSection.val identityRefinement).2.1
    exact (system.map_id_apply level _).symm.trans maps)

end CategoryTheory.Functor

namespace Function

variable {Source : Type u} {Target : Type v}

/-- Lists whose pointwise image is one prescribed target list. -/
def ListMapFiber (map : Source → Target) (target : List Target) :=
  {source : List Source // source.map map = target}

/-- A pointwise map with finite fibers has finite fibers on lists. -/
theorem listMapFiber_finite
    (map : Source → Target)
    (fiber_finite : ∀ target, Finite {source // map source = target})
    (target : List Target) : Finite (ListMapFiber map target) := by
  induction target with
  | nil =>
      let encode : ListMapFiber map [] → PUnit := fun _ ↦ PUnit.unit
      exact Finite.of_injective encode (by
        intro first second equality
        apply Subtype.ext
        have first_nil : first.1 = [] := by
          cases values_eq : first.1 with
          | nil => rfl
          | cons head tail =>
              have maps := first.2
              rw [values_eq] at maps
              simp at maps
        have second_nil : second.1 = [] := by
          cases values_eq : second.1 with
          | nil => rfl
          | cons head tail =>
              have maps := second.2
              rw [values_eq] at maps
              simp at maps
        exact first_nil.trans second_nil.symm)
  | cons head tail induction =>
      let encode : ListMapFiber map (head :: tail) →
          {source // map source = head} × ListMapFiber map tail :=
        fun source ↦ by
          rcases source with ⟨values, maps⟩
          cases values with
          | nil => simp at maps
          | cons first rest =>
              exact
                (⟨first, (List.cons.inj maps).1⟩,
                  ⟨rest, (List.cons.inj maps).2⟩)
      letI : Finite {source // map source = head} := fiber_finite head
      letI : Finite (ListMapFiber map tail) := induction
      exact Finite.of_injective encode (by
        rintro ⟨firstValues, firstMaps⟩ ⟨secondValues, secondMaps⟩ equality
        apply Subtype.ext
        cases firstValues with
        | nil => simp at firstMaps
        | cons firstHead firstTail =>
            cases secondValues with
            | nil => simp at secondMaps
            | cons secondHead secondTail =>
                have head_eq : firstHead = secondHead :=
                  congrArg (fun value ↦ value.1.1) equality
                have tail_eq : firstTail = secondTail :=
                  congrArg (fun value ↦ value.2.1) equality
                exact congrArg₂ List.cons head_eq tail_eq)

/-- Fibers of a map on a disjoint union. -/
def SumMapFiber {LeftSource RightSource LeftTarget RightTarget : Type*}
    (leftMap : LeftSource → LeftTarget)
    (rightMap : RightSource → RightTarget)
    (target : LeftTarget ⊕ RightTarget) :=
  {source : LeftSource ⊕ RightSource //
    Sum.map leftMap rightMap source = target}

/-- A disjoint-union map has finite fibers when both constituent maps do. -/
theorem sumMapFiber_finite
    {LeftSource RightSource LeftTarget RightTarget : Type*}
    (leftMap : LeftSource → LeftTarget)
    (rightMap : RightSource → RightTarget)
    (left_finite : ∀ target, Finite {source // leftMap source = target})
    (right_finite : ∀ target, Finite {source // rightMap source = target})
    (target : LeftTarget ⊕ RightTarget) :
    Finite (SumMapFiber leftMap rightMap target) := by
  cases target with
  | inl target =>
      let encode : SumMapFiber leftMap rightMap (Sum.inl target) →
          {source // leftMap source = target} := fun source ↦ by
        rcases source with ⟨source, maps⟩
        cases source with
        | inl source => exact ⟨source, Sum.inl.inj maps⟩
        | inr source => cases maps
      letI : Finite {source // leftMap source = target} := left_finite target
      exact Finite.of_injective encode (by
        rintro ⟨first, firstMaps⟩ ⟨second, secondMaps⟩ equality
        apply Subtype.ext
        cases first with
        | inl first =>
            cases second with
            | inl second =>
                exact congrArg Sum.inl (congrArg Subtype.val equality)
            | inr second => cases secondMaps
        | inr first => cases firstMaps)
  | inr target =>
      let encode : SumMapFiber leftMap rightMap (Sum.inr target) →
          {source // rightMap source = target} := fun source ↦ by
        rcases source with ⟨source, maps⟩
        cases source with
        | inl source => cases maps
        | inr source => exact ⟨source, Sum.inr.inj maps⟩
      letI : Finite {source // rightMap source = target} := right_finite target
      exact Finite.of_injective encode (by
        rintro ⟨first, firstMaps⟩ ⟨second, secondMaps⟩ equality
        apply Subtype.ext
        cases first with
        | inl first => cases firstMaps
        | inr first =>
            cases second with
            | inl second => cases secondMaps
            | inr second =>
                exact congrArg Sum.inr (congrArg Subtype.val equality))

end Function

namespace SourceSemiGraph.Hom

variable {source target : SourceSemiGraph.{u}}

/-- A total-branch map has finite fibers as soon as the underlying edge map
does: the source edge has finitely many choices and each branch set has two
elements. -/
theorem totalBranchMap_fiber_finite
    (hom : source.Hom target)
    (edge_finite : ∀ edge, Finite (hom.EdgeFiber edge))
    (targetBranch : target.TotalBranch) :
    Finite {sourceBranch // hom.totalBranchMap sourceBranch = targetBranch} := by
  let FiberCode :=
    Σ edge : hom.EdgeFiber targetBranch.1, source.Branch edge.1
  letI : Finite (hom.EdgeFiber targetBranch.1) := edge_finite targetBranch.1
  letI (edge : hom.EdgeFiber targetBranch.1) :
      Finite (source.Branch edge.1) :=
    @Finite.of_fintype _ (source.branchFintype edge.1)
  letI : Finite FiberCode := inferInstance
  let encode :
      {sourceBranch // hom.totalBranchMap sourceBranch = targetBranch} →
        FiberCode := fun sourceBranch ↦
    ⟨⟨sourceBranch.1.1, congrArg Sigma.fst sourceBranch.2⟩,
      sourceBranch.1.2⟩
  exact Finite.of_injective encode (by
    intro first second equality
    apply Subtype.ext
    exact congrArg
      (fun value : FiberCode ↦
        (⟨value.1.1, value.2⟩ : source.TotalBranch)) equality)

/-- The proper map on nonverticial branches inherits finite fibers from the
total-branch map. -/
theorem nonVerticialMap_fiber_finite
    (hom : source.Hom target) (proper : hom.IsProper)
    (edge_finite : ∀ edge, Finite (hom.EdgeFiber edge))
    (targetBranch : target.NonVerticialBranch) :
    Finite {sourceBranch //
      SourceCombinatorialUniversalCover.IncidenceNode.nonVerticialMap
        source hom proper sourceBranch =
        targetBranch} := by
  letI : Finite
      {sourceBranch // hom.totalBranchMap sourceBranch = targetBranch.1} :=
    totalBranchMap_fiber_finite hom edge_finite targetBranch.1
  let encode :
      {sourceBranch //
        SourceCombinatorialUniversalCover.IncidenceNode.nonVerticialMap
          source hom proper sourceBranch =
          targetBranch} →
        {sourceBranch // hom.totalBranchMap sourceBranch = targetBranch.1} :=
    fun sourceBranch ↦
      ⟨sourceBranch.1.1, congrArg Subtype.val sourceBranch.2⟩
  exact Finite.of_injective encode (by
    intro first second equality
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun value ↦ value.1) equality)

end SourceSemiGraph.Hom

namespace SourceCombinatorialUniversalCover.IncidenceNode

variable {source target : SourceSemiGraph.{u}}

/-- A proper incidence-node map has finite fibers whenever the underlying
vertex and edge maps do. -/
theorem properMap_fiber_finite
    (hom : source.Hom target) (proper : hom.IsProper)
    (vertex_finite : ∀ vertex, Finite (hom.VertexFiber vertex))
    (edge_finite : ∀ edge, Finite (hom.EdgeFiber edge))
    (targetNode : IncidenceNode target) :
    Finite {sourceNode // properMap source hom proper sourceNode = targetNode} := by
  let compactMap : source.CompactVertex → target.CompactVertex :=
    Sum.map hom.vertexMap (nonVerticialMap source hom proper)
  let remainderMap : source.Edge ⊕ source.TotalBranch →
      target.Edge ⊕ target.TotalBranch :=
    Sum.map hom.edgeMap hom.totalBranchMap
  have compact_finite : ∀ targetVertex,
      Finite {sourceVertex // compactMap sourceVertex = targetVertex} := by
    intro targetVertex
    exact Function.sumMapFiber_finite hom.vertexMap
      (nonVerticialMap source hom proper) vertex_finite
      (SourceSemiGraph.Hom.nonVerticialMap_fiber_finite
        hom proper edge_finite) targetVertex
  have remainder_finite : ∀ targetValue,
      Finite {sourceValue // remainderMap sourceValue = targetValue} := by
    intro targetValue
    exact Function.sumMapFiber_finite hom.edgeMap hom.totalBranchMap
      edge_finite
      (SourceSemiGraph.Hom.totalBranchMap_fiber_finite hom edge_finite)
      targetValue
  let targetSum := (incidenceNodeEquiv target).symm targetNode
  letI : Finite
      (Function.SumMapFiber compactMap remainderMap targetSum) :=
    Function.sumMapFiber_finite compactMap remainderMap compact_finite
      remainder_finite targetSum
  let encode :
      {sourceNode // properMap source hom proper sourceNode = targetNode} →
        Function.SumMapFiber compactMap remainderMap targetSum :=
    fun sourceNode ↦
      ⟨(incidenceNodeEquiv source).symm sourceNode.1, by
        dsimp only [compactMap, remainderMap, targetSum]
        apply (incidenceNodeEquiv target).injective
        rw [(incidenceNodeEquiv target).apply_symm_apply]
        change properMap source hom proper sourceNode.1 = targetNode
        exact sourceNode.2⟩
  exact Finite.of_injective encode (by
    intro first second equality
    apply Subtype.ext
    apply (incidenceNodeEquiv source).symm.injective
    exact congrArg Subtype.val equality)

end SourceCombinatorialUniversalCover.IncidenceNode

namespace SourceCombinatorialUniversalCover.UniversalVertex

variable {Vertex : Type u} (graph : SimpleGraph Vertex) (root : Vertex)

/-- Changing a root along an equality preserves reduced-walk depth. -/
@[simp]
theorem castRoot_depth {first second : Vertex} (rootsEqual : first = second)
    (point : UniversalVertex graph first) :
    (castRoot graph rootsEqual point).depth = point.depth := by
  subst second
  rfl

/-- Changing the root along an equality does not change the retained walk
vertices. -/
@[simp]
theorem castRoot_walk_vertices {first second : Vertex}
    (rootsEqual : first = second) (point : UniversalVertex graph first) :
    (castRoot graph rootsEqual point).walk.vertices = point.walk.vertices := by
  subst second
  rfl

/-- The retained endpoint list has one more vertex than the reduced walk has
edges. -/
@[simp]
theorem walk_vertices_length (point : UniversalVertex graph root) :
    point.walk.vertices.length = point.depth + 1 := by
  rcases point with ⟨previous, current, walk⟩
  induction walk with
  | nil => rfl
  | step walk adjacent notBacktrack induction =>
      simp only [ReducedWalk.vertices_step, List.length_cons, depth,
        ReducedWalk.length]
      rw [induction]
      rfl

/-- Removing the last reduced-walk step removes the head of the retained
reverse endpoint list. -/
theorem walk_vertices_of_parent
    {point parent : UniversalVertex graph root}
    (parent_eq : point.parent = some parent) :
    point.walk.vertices = point.endpoint :: parent.walk.vertices := by
  rcases point with ⟨previous, current, walk⟩
  cases walk with
  | nil => simp [UniversalVertex.parent] at parent_eq
  | @step before prior next walk adjacent notBacktrack =>
      simp only [UniversalVertex.parent, Option.some.injEq] at parent_eq
      cases parent_eq
      rfl

/-- Along one universal-tree edge, depth can increase by at most one. -/
theorem depth_le_add_one_of_adj
    {first second : UniversalVertex graph root}
    (adjacent : (tree graph root).Adj first second) :
    second.depth ≤ first.depth + 1 := by
  rcases (tree_adj_iff (graph := graph) (root := root)).mp adjacent with
    ⟨_, child | parent⟩
  · rw [depth_eq_parent_add_one graph root child]
  · have depthEquality := depth_eq_parent_add_one graph root parent
    omega

/-- Mapping a reduced walk may cancel steps, but cannot increase depth. -/
theorem mapHom_depth_le {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (point : UniversalVertex graph root) :
    (mapHom graph root targetGraph hom point).depth ≤ point.depth := by
  rcases point with ⟨previous, current, walk⟩
  change (mapHomWalk graph root targetGraph hom walk).1.depth ≤ walk.length
  induction walk with
  | nil => exact le_rfl
  | @step previous current next walk adjacent notBacktrack induction =>
      change
        (liftNeighbor targetGraph (hom root)
          (mapHomWalk graph root targetGraph hom walk).1 (hom next) _).depth ≤
          walk.length + 1
      have mappedAdjacent : targetGraph.Adj
          (mapHomWalk graph root targetGraph hom walk).1.endpoint (hom next) := by
        rw [(mapHomWalk graph root targetGraph hom walk).2]
        exact hom.map_rel adjacent
      have adjacentLift := adjacent_liftNeighbor targetGraph (hom root)
        (mapHomWalk graph root targetGraph hom walk).1 (hom next)
          mappedAdjacent
      exact (depth_le_add_one_of_adj targetGraph (hom root) adjacentLift).trans
        (Nat.add_le_add_right induction 1)

/-- If lifting one neighbor increases depth, it appended that endpoint rather
than cancelling the preceding step. -/
theorem liftNeighbor_walk_vertices_of_depth_eq
    (next : Vertex) (point : UniversalVertex graph root)
    (adjacent : graph.Adj point.endpoint next)
    (depth_eq : (liftNeighbor graph root point next adjacent).depth =
      point.depth + 1) :
    (liftNeighbor graph root point next adjacent).walk.vertices =
      next :: point.walk.vertices := by
  classical
  rcases point with ⟨previous, current, walk⟩
  cases walk with
  | nil => rfl
  | @step before prior current parentWalk parentAdjacent notBacktrack =>
      simp only [liftNeighbor] at depth_eq ⊢
      by_cases backtracks : next = prior
      · rw [dif_pos backtracks] at depth_eq ⊢
        simp only [depth, ReducedWalk.length] at depth_eq
        omega
      · rw [dif_neg backtracks]
        rfl

/-- When mapping a reduced walk causes no loss of depth, the retained vertex
list is mapped pointwise, so no hidden cancellation occurred. -/
theorem mapHom_walk_vertices_of_depth_eq {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (point : UniversalVertex graph root)
    (depth_eq : (mapHom graph root targetGraph hom point).depth =
      point.depth) :
    (mapHom graph root targetGraph hom point).walk.vertices =
      point.walk.vertices.map hom := by
  rcases point with ⟨previous, current, walk⟩
  induction walk with
  | nil => rfl
  | @step before prior next walk adjacent notBacktrack induction =>
      let previousPoint : UniversalVertex graph root :=
        ⟨before, prior, walk⟩
      let mappedPrevious :=
        mapHom graph root targetGraph hom previousPoint
      have mappedPreviousDepthLe : mappedPrevious.depth ≤ previousPoint.depth :=
        mapHom_depth_le graph root targetGraph hom previousPoint
      have mappedAdjacent : targetGraph.Adj mappedPrevious.endpoint (hom next) := by
        rw [mapHom_endpoint]
        exact hom.map_rel adjacent
      have finalAdjacent :
          (tree targetGraph (hom root)).Adj mappedPrevious
            (liftNeighbor targetGraph (hom root) mappedPrevious
              (hom next) mappedAdjacent) :=
        adjacent_liftNeighbor targetGraph (hom root) mappedPrevious
          (hom next) mappedAdjacent
      have finalDepthLe :
          (liftNeighbor targetGraph (hom root) mappedPrevious
              (hom next) mappedAdjacent).depth ≤ mappedPrevious.depth + 1 :=
        depth_le_add_one_of_adj targetGraph (hom root) finalAdjacent
      have finalDepthEq :
          (liftNeighbor targetGraph (hom root) mappedPrevious
              (hom next) mappedAdjacent).depth = previousPoint.depth + 1 := by
        have hdepth := depth_eq
        change
          (liftNeighbor targetGraph (hom root) mappedPrevious
              (hom next) mappedAdjacent).depth = previousPoint.depth + 1
            at hdepth
        exact hdepth
      have mappedPreviousDepthEq :
          mappedPrevious.depth = previousPoint.depth := by
        omega
      have appendDepth :
          (liftNeighbor targetGraph (hom root) mappedPrevious
              (hom next) mappedAdjacent).depth = mappedPrevious.depth + 1 := by
        omega
      change
        (liftNeighbor targetGraph (hom root) mappedPrevious
            (hom next) mappedAdjacent).walk.vertices =
          hom next :: previousPoint.walk.vertices.map hom
      rw [liftNeighbor_walk_vertices_of_depth_eq targetGraph (hom root)
        (hom next) mappedPrevious mappedAdjacent appendDepth]
      exact congrArg (List.cons (hom next))
        (induction mappedPreviousDepthEq)

/-- The canonical walk from a universal-tree vertex to the root has length
equal to that vertex's reduced-walk depth. -/
@[simp]
theorem walkToBase_length (point : UniversalVertex graph root) :
    (walkToBase graph root point).length = point.depth := by
  rcases point with ⟨previous, current, walk⟩
  induction walk with
  | nil =>
      unfold walkToBase depth
      rfl
  | @step previous current next walk adjacent notBacktrack induction =>
      simp [walkToBase, depth, ReducedWalk.length, induction]

/-- Local surjectivity lifts a target universal-tree vertex without using a
source vertex deeper than the target. -/
theorem mapHom_bounded_surjective {Target : Type u}
    (targetGraph : SimpleGraph Target) (hom : graph →g targetGraph)
    (locallySurjective : IsLocallySurjective graph targetGraph hom)
    (target : UniversalVertex targetGraph (hom root)) :
    ∃ source : UniversalVertex graph root,
      mapHom graph root targetGraph hom source = target ∧
        source.depth ≤ target.depth := by
  let targetPath := (walkToBase targetGraph (hom root) target).reverse
  have liftAlong : ∀ {source destination}
      (path : (tree targetGraph (hom root)).Walk source destination)
      (preimage : UniversalVertex graph root),
      mapHom graph root targetGraph hom preimage = source →
        ∃ result,
          mapHom graph root targetGraph hom result = destination ∧
            result.depth ≤ preimage.depth + path.length := by
    intro source destination path
    induction path with
    | nil =>
        intro preimage equality
        exact ⟨preimage, equality, by simp⟩
    | @cons source neighbor destination adjacent tail inductionHypothesis =>
        intro preimage equality
        have endpointAdjacent :
            targetGraph.Adj (hom preimage.endpoint) neighbor.endpoint := by
          rw [← mapHom_endpoint graph root targetGraph hom preimage, equality]
          exact endpoint_adj targetGraph (hom root) adjacent
        obtain ⟨nextEndpoint, nextEndpointAdjacent, mappedEndpoint⟩ :=
          locallySurjective endpointAdjacent
        let next : UniversalVertex graph root :=
          liftNeighbor graph root preimage nextEndpoint nextEndpointAdjacent
        have nextAdjacent : (tree graph root).Adj preimage next :=
          adjacent_liftNeighbor graph root _ _ _
        have mappedNextAdjacent :
            (tree targetGraph (hom root)).Adj source
              (mapHom graph root targetGraph hom next) := by
          rw [← equality]
          exact mapHom_adj graph root targetGraph hom nextAdjacent
        have mappedNextEndpoint :
            (mapHom graph root targetGraph hom next).endpoint =
              neighbor.endpoint := by
          rw [mapHom_endpoint, liftNeighbor_endpoint, mappedEndpoint]
        have mappedNext :
            mapHom graph root targetGraph hom next = neighbor :=
          neighbor_eq_of_endpoint_eq targetGraph (hom root)
            mappedNextAdjacent adjacent mappedNextEndpoint
        obtain ⟨result, resultMaps, resultBound⟩ :=
          inductionHypothesis next mappedNext
        refine ⟨result, resultMaps, ?_⟩
        have nextBound : next.depth ≤ preimage.depth + 1 :=
          depth_le_add_one_of_adj graph root nextAdjacent
        have pathLength :
            (SimpleGraph.Walk.cons adjacent tail).length = tail.length + 1 :=
          rfl
        omega
  obtain ⟨source, maps, bounded⟩ := liftAlong targetPath
    (base graph root) (mapHom_base graph root targetGraph hom)
  refine ⟨source, maps, ?_⟩
  have bounded' : source.depth ≤ targetPath.length := by
    simpa [depth, base, ReducedWalk.length] using bounded
  simpa only [targetPath, SimpleGraph.Walk.length_reverse,
    walkToBase_length] using bounded'

/-- Every non-base universal-tree vertex has a parent. -/
theorem exists_parent_of_ne_base (point : UniversalVertex graph root)
    (notBase : point ≠ base graph root) :
    ∃ parent, point.parent = some parent := by
  rcases point with ⟨previous, current, walk⟩
  cases walk with
  | nil => exact (notBase rfl).elim
  | @step before prior current walk adjacent notBacktrack =>
      exact ⟨⟨before, prior, walk⟩, rfl⟩

/-- A reduced-walk vertex is determined by its reverse list of visited
vertices. -/
theorem eq_of_walk_vertices_eq
    {first second : UniversalVertex graph root}
    (vertices_eq : first.walk.vertices = second.walk.vertices) :
    first = second := by
  have depth_eq : first.depth = second.depth := by
    have lengths := congrArg List.length vertices_eq
    simpa only [walk_vertices_length, Nat.add_right_cancel_iff] using lengths
  induction depth_eqn : first.depth using Nat.strong_induction_on
      generalizing first second with
  | h depth induction =>
      by_cases depth_zero : depth = 0
      · have first_depth_zero : first.depth = 0 := depth_eqn.trans depth_zero
        have second_depth_zero : second.depth = 0 :=
          depth_eq.symm.trans first_depth_zero
        exact
          (eq_base_of_depth_eq_zero graph root first first_depth_zero).trans
            (eq_base_of_depth_eq_zero graph root second
              second_depth_zero).symm
      · have first_not_base : first ≠ base graph root := by
          intro equality
          subst first
          exact depth_zero depth_eqn.symm
        have second_not_base : second ≠ base graph root := by
          intro equality
          subst second
          exact depth_zero (depth_eqn.symm.trans depth_eq)
        obtain ⟨firstParent, first_parent⟩ :=
          exists_parent_of_ne_base graph root first first_not_base
        obtain ⟨secondParent, second_parent⟩ :=
          exists_parent_of_ne_base graph root second second_not_base
        have decomposed := vertices_eq
        rw [walk_vertices_of_parent graph root first_parent,
          walk_vertices_of_parent graph root second_parent] at decomposed
        have endpoint_eq : first.endpoint = second.endpoint :=
          (List.cons.inj decomposed).1
        have parent_vertices_eq :
            firstParent.walk.vertices = secondParent.walk.vertices :=
          (List.cons.inj decomposed).2
        have parent_depth_eq : firstParent.depth = secondParent.depth := by
          have lengths := congrArg List.length parent_vertices_eq
          simpa only [walk_vertices_length, Nat.add_right_cancel_iff] using lengths
        have first_parent_depth : firstParent.depth < depth := by
          have relation := depth_eq_parent_add_one graph root first_parent
          omega
        have parent_eq : firstParent = secondParent :=
          induction firstParent.depth first_parent_depth parent_vertices_eq
            parent_depth_eq rfl
        subst secondParent
        apply neighbor_eq_of_endpoint_eq graph root
          (point := firstParent)
        · exact (tree_adj_iff (graph := graph) (root := root)).mpr
            ⟨by
              intro equality
              subst first
              have relation := depth_eq_parent_add_one graph root first_parent
              omega,
              Or.inl first_parent⟩
        · exact (tree_adj_iff (graph := graph) (root := root)).mpr
            ⟨by
              intro equality
              subst second
              have relation := depth_eq_parent_add_one graph root second_parent
              omega,
              Or.inl second_parent⟩
        · exact endpoint_eq

/-- A finite base graph has only finitely many reduced-walk vertices up to
any fixed depth. -/
theorem finite_bounded_depth [Finite Vertex] (bound : ℕ) :
    Finite {point : UniversalVertex graph root // point.depth ≤ bound} := by
  classical
  letI : Fintype Vertex := Fintype.ofFinite Vertex
  induction bound with
  | zero =>
      let encode : {point : UniversalVertex graph root // point.depth ≤ 0} →
          PUnit := fun _ ↦ PUnit.unit
      exact Finite.of_injective encode (by
        intro first second _
        apply Subtype.ext
        exact (eq_base_of_depth_eq_zero graph root first.1
          (Nat.eq_zero_of_le_zero first.2)).trans
            (eq_base_of_depth_eq_zero graph root second.1
              (Nat.eq_zero_of_le_zero second.2)).symm)
  | succ bound induction =>
      let ball := {point : UniversalVertex graph root // point.depth ≤ bound}
      let choices := Option (Σ point : ball,
        (tree graph root).neighborSet point.1)
      haveI neighborFinite (point : ball) :
          Finite ((tree graph root).neighborSet point.1) :=
        Finite.of_equiv (graph.neighborSet point.1.endpoint)
          (neighborEquiv graph root point.1)
      haveI : Finite choices := inferInstance
      let decode : choices →
          {point : UniversalVertex graph root // point.depth ≤ bound + 1}
        | none => ⟨base graph root, Nat.zero_le _⟩
        | some choice => ⟨choice.2.1, by
            exact (depth_le_add_one_of_adj graph root choice.2.2).trans
              (Nat.add_le_add_right choice.1.2 1)⟩
      apply Finite.of_surjective decode
      intro point
      by_cases atBase : point.1 = base graph root
      · refine ⟨none, ?_⟩
        exact Subtype.ext atBase.symm
      · obtain ⟨parent, parent_eq⟩ :=
          exists_parent_of_ne_base graph root point.1 atBase
        have pointDepth := depth_eq_parent_add_one graph root parent_eq
        have parentBound : parent.depth ≤ bound := by omega
        let parentInBall : ball := ⟨parent, parentBound⟩
        let pointNeighbor : (tree graph root).neighborSet parent :=
          ⟨point.1, by
            change (tree graph root).Adj parent point.1
            apply (tree_adj_iff (graph := graph) (root := root)).mpr
            refine ⟨?_, Or.inl parent_eq⟩
            intro equality
            rw [equality] at pointDepth
            omega⟩
        refine ⟨some ⟨parentInBall, pointNeighbor⟩, ?_⟩
        rfl

end SourceCombinatorialUniversalCover.UniversalVertex

namespace SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

open SourceSemiGraphOfAnabelioids.GluedObject

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)

/-- A pointed Galois refinement has finite vertex fibers even when the base
semigraph itself is merely countable. -/
theorem transition_vertexFiber_finite
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) (targetVertex : coarser.semiGraph.Vertex) :
    Finite ((GaloisLevel.transition diagram root refinement).VertexFiber
      targetVertex) := by
  let projection := finer.projection
  letI : Finite
      (projection.VertexFiber (coarser.projection.vertexMap targetVertex)) :=
    SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverVertexFiberFinite
      diagram root finer.object _
  let encode :
      (GaloisLevel.transition diagram root refinement).VertexFiber
          targetVertex →
        projection.VertexFiber
          (coarser.projection.vertexMap targetVertex) :=
    fun sourceVertex ↦ ⟨sourceVertex.1, by
      exact
        (GaloisLevel.transition_vertex_over_base diagram root refinement
          sourceVertex.1).symm.trans
          (congrArg coarser.projection.vertexMap sourceVertex.2)⟩
  exact Finite.of_injective encode (by
    intro first second equality
    apply Subtype.ext
    exact congrArg
      (fun value : projection.VertexFiber
        (coarser.projection.vertexMap targetVertex) ↦ value.1) equality)

/-- A pointed Galois refinement has finite edge fibers even when the base
semigraph itself is merely countable. -/
theorem transition_edgeFiber_finite
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) (targetEdge : coarser.semiGraph.Edge) :
    Finite ((GaloisLevel.transition diagram root refinement).EdgeFiber
      targetEdge) := by
  let projection := finer.projection
  letI : Finite
      (projection.EdgeFiber (coarser.projection.edgeMap targetEdge)) :=
    SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverEdgeFiberFinite
      diagram root finer.object _
  let encode :
      (GaloisLevel.transition diagram root refinement).EdgeFiber targetEdge →
        projection.EdgeFiber (coarser.projection.edgeMap targetEdge) :=
    fun sourceEdge ↦ ⟨sourceEdge.1, by
      exact
        (GaloisLevel.transition_edge_over_base diagram root refinement
          sourceEdge.1).symm.trans
          (congrArg coarser.projection.edgeMap sourceEdge.2)⟩
  exact Finite.of_injective encode (by
    intro first second equality
    apply Subtype.ext
    exact congrArg
      (fun value : projection.EdgeFiber
        (coarser.projection.edgeMap targetEdge) ↦ value.1) equality)

/-- The faithful incidence map of a pointed Galois refinement has finite
fibers componentwise; no global finiteness of either semigraph is used. -/
theorem refinementIncidenceMap_fiber_finite
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (targetNode : IncidenceNode (LevelSemiGraph diagram root coarser)) :
    Finite {sourceNode //
      RefinementIncidenceMap diagram root refinement sourceNode = targetNode} := by
  change Finite {sourceNode //
    IncidenceNode.properMap finer.semiGraph
      (GaloisLevel.transition diagram root refinement)
      (GaloisLevel.transition_isProper diagram root refinement) sourceNode =
        targetNode}
  exact IncidenceNode.properMap_fiber_finite
    (GaloisLevel.transition diagram root refinement)
    (GaloisLevel.transition_isProper diagram root refinement)
    (transition_vertexFiber_finite diagram root refinement)
    (transition_edgeFiber_finite diagram root refinement) targetNode

/-- Refinement of universal incidence trees cannot increase reduced-walk
depth. -/
theorem refinementTreeMap_depth_le
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (point : IncidenceTreeVertex diagram root finer) :
    (RefinementTreeMap diagram root refinement point).depth ≤ point.depth := by
  unfold RefinementTreeMap
  rw [UniversalVertex.castRoot_depth]
  exact UniversalVertex.mapHom_depth_le
    (IncidenceGraph diagram root finer) (IncidenceRoot diagram root finer)
    (IncidenceGraph diagram root coarser)
    (RefinementIncidenceMap diagram root refinement) point

/-- The path-lifting proof for a refinement supplies a preimage no deeper
than the requested coarser tree vertex. -/
theorem refinementTreeMap_bounded_surjective
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (target : IncidenceTreeVertex diagram root coarser) :
    ∃ source : IncidenceTreeVertex diagram root finer,
      RefinementTreeMap diagram root refinement source = target ∧
        source.depth ≤ target.depth := by
  let rootsEqual := refinementIncidenceMap_root diagram root refinement
  obtain ⟨intermediate, intermediateMaps⟩ :=
    UniversalVertex.castRoot_surjective
      (IncidenceGraph diagram root coarser) rootsEqual target
  obtain ⟨source, sourceMaps, sourceBound⟩ :=
    UniversalVertex.mapHom_bounded_surjective
      (IncidenceGraph diagram root finer) (IncidenceRoot diagram root finer)
      (IncidenceGraph diagram root coarser)
      (RefinementIncidenceMap diagram root refinement)
      (refinementIncidenceMap_isLocallySurjective diagram root refinement)
      intermediate
  refine ⟨source, ?_, ?_⟩
  · unfold RefinementTreeMap
    rw [sourceMaps, intermediateMaps]
  · exact sourceBound.trans_eq (by
      rw [← intermediateMaps, UniversalVertex.castRoot_depth])

/-- For one prescribed target tree vertex, the depth-preserving refinement
lifts form a finite type.  Countability of the complete graph is irrelevant:
only the finitely many incidence nodes along the target walk are lifted. -/
theorem refinementTreeMap_boundedFiber_finite
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (target : IncidenceTreeVertex diagram root coarser) :
    Finite {source : IncidenceTreeVertex diagram root finer //
      RefinementTreeMap diagram root refinement source = target ∧
        source.depth ≤ target.depth} := by
  let incidenceMap := RefinementIncidenceMap diagram root refinement
  have incidence_finite : ∀ targetNode,
      Finite {sourceNode // incidenceMap sourceNode = targetNode} :=
    refinementIncidenceMap_fiber_finite diagram root refinement
  letI : Finite
      (Function.ListMapFiber incidenceMap target.walk.vertices) :=
    Function.listMapFiber_finite incidenceMap incidence_finite
      target.walk.vertices
  let encode :
      {source : IncidenceTreeVertex diagram root finer //
        RefinementTreeMap diagram root refinement source = target ∧
          source.depth ≤ target.depth} →
        Function.ListMapFiber incidenceMap target.walk.vertices :=
    fun source ↦ ⟨source.1.walk.vertices, by
      have mappedDepth_eq :
          (RefinementTreeMap diagram root refinement source.1).depth =
            target.depth :=
        congrArg
          (UniversalVertex.depth (IncidenceGraph diagram root coarser)
            (IncidenceRoot diagram root coarser)) source.2.1
      have targetDepthLe : target.depth ≤ source.1.depth := by
        exact mappedDepth_eq.symm.le.trans
          (refinementTreeMap_depth_le diagram root refinement source.1)
      have depth_eq : source.1.depth = target.depth :=
        le_antisymm source.2.2 targetDepthLe
      let rawMap := UniversalVertex.mapHom
        (IncidenceGraph diagram root finer) (IncidenceRoot diagram root finer)
        (IncidenceGraph diagram root coarser) incidenceMap source.1
      have rawDepth_eq : rawMap.depth = source.1.depth := by
        calc
          rawMap.depth =
              (RefinementTreeMap diagram root refinement source.1).depth := by
            unfold RefinementTreeMap rawMap
            rw [UniversalVertex.castRoot_depth]
          _ = target.depth := mappedDepth_eq
          _ = source.1.depth := depth_eq.symm
      have rawVertices :=
        UniversalVertex.mapHom_walk_vertices_of_depth_eq
          (IncidenceGraph diagram root finer) (IncidenceRoot diagram root finer)
          (IncidenceGraph diagram root coarser) incidenceMap source.1
          rawDepth_eq
      calc
        source.1.walk.vertices.map incidenceMap = rawMap.walk.vertices :=
          rawVertices.symm
        _ = (RefinementTreeMap diagram root refinement source.1).walk.vertices := by
          unfold RefinementTreeMap rawMap
          rw [UniversalVertex.castRoot_walk_vertices]
        _ = target.walk.vertices :=
          congrArg (fun point ↦ point.walk.vertices) source.2.1⟩
  exact Finite.of_injective encode (by
    intro first second equality
    apply Subtype.ext
    apply UniversalVertex.eq_of_walk_vertices_eq
    exact congrArg
      (fun value : Function.ListMapFiber incidenceMap target.walk.vertices ↦
        value.1) equality)

/-- Depth of the image of the distinguished root under one complete deck
transformation. -/
noncomputable def deckDepth (level : GaloisLevel diagram root)
    (transformation : DeckGroup diagram root level) : ℕ :=
  (UniversalVertex.CompositeDeckTransformation.treePerm transformation
    (UniversalVertex.base (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level))).depth

/-- Deck transitions cannot increase the root-image depth. -/
theorem deckDepth_transition_le
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (transformation : DeckGroup diagram root finer) :
    deckDepth diagram root coarser
        (deckTransition diagram root refinement transformation) ≤
      deckDepth diagram root finer transformation := by
  unfold deckDepth
  rw [deckTransition_apply, deckTransitionToFun_base, TransitionedBaseImage]
  exact refinementTreeMap_depth_le diagram root refinement _

/-- Every coarser complete deck transformation has a finer lift whose
root-image depth is no larger. -/
theorem deckTransition_bounded_preimage
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (targetTransformation : DeckGroup diagram root coarser) :
    ∃ sourceTransformation : DeckGroup diagram root finer,
      deckTransition diagram root refinement sourceTransformation =
          targetTransformation ∧
        deckDepth diagram root finer sourceTransformation ≤
          deckDepth diagram root coarser targetTransformation := by
  let targetRoot := IncidenceRoot diagram root coarser
  let targetBase :=
    UniversalVertex.base (IncidenceGraph diagram root coarser) targetRoot
  let targetSymmetry :=
    UniversalVertex.CompositeDeckTransformation.baseSymmetry
      targetTransformation
  let targetBaseImage :=
    UniversalVertex.CompositeDeckTransformation.treePerm
      targetTransformation targetBase
  obtain ⟨sourceSymmetry, symmetryMaps⟩ :=
    GaloisLevel.automorphismTransition_surjective diagram root refinement
      targetSymmetry
  obtain ⟨sourceBaseImage, baseImageMaps, baseImageBound⟩ :=
    refinementTreeMap_bounded_surjective diagram root refinement
      targetBaseImage
  have endpointImagesEqual :
      RefinementIncidenceMap diagram root refinement
          (IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
            sourceSymmetry (IncidenceRoot diagram root finer)) =
        RefinementIncidenceMap diagram root refinement
          sourceBaseImage.endpoint := by
    calc
      RefinementIncidenceMap diagram root refinement
          (IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
            sourceSymmetry (IncidenceRoot diagram root finer)) =
          IncidenceNode.incidencePerm coarser.semiGraph
            coarser.automorphismAction targetSymmetry
              (RefinementIncidenceMap diagram root refinement
                (IncidenceRoot diagram root finer)) := by
                  rw [refinement_incidence_commutes diagram root refinement,
                    symmetryMaps]
      _ = IncidenceNode.incidencePerm coarser.semiGraph
            coarser.automorphismAction targetSymmetry targetRoot := by
              rw [refinementIncidenceMap_root diagram root refinement]
      _ = targetBaseImage.endpoint := by
              exact (UniversalVertex.CompositeDeckTransformation.endpoint_apply
                targetTransformation targetBase).symm
      _ = (RefinementTreeMap diagram root refinement
            sourceBaseImage).endpoint :=
              congrArg
                (fun point : IncidenceTreeVertex diagram root coarser ↦
                  point.endpoint) baseImageMaps.symm
      _ = RefinementIncidenceMap diagram root refinement
            sourceBaseImage.endpoint :=
              refinementTreeMap_endpoint diagram root refinement sourceBaseImage
  obtain ⟨kernelSymmetry, kernelMaps, endpointCorrection⟩ :=
    refinementIncidenceMap_kernel_transitive diagram root refinement
      (IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
        sourceSymmetry (IncidenceRoot diagram root finer))
      sourceBaseImage.endpoint endpointImagesEqual
  let correctedSymmetry := kernelSymmetry * sourceSymmetry
  have correctedSymmetryMaps :
      GaloisLevel.automorphismTransition diagram root refinement
          correctedSymmetry = targetSymmetry := by
    change GaloisLevel.automorphismTransition diagram root refinement
        (kernelSymmetry * sourceSymmetry) = targetSymmetry
    rw [map_mul, kernelMaps, symmetryMaps, one_mul]
  have correctedEndpoint :
      (IncidenceActionHom diagram root finer correctedSymmetry).1
          (IncidenceRoot diagram root finer) = sourceBaseImage.endpoint := by
    change IncidenceNode.incidencePerm finer.semiGraph finer.automorphismAction
        (kernelSymmetry * sourceSymmetry) (IncidenceRoot diagram root finer) =
      sourceBaseImage.endpoint
    rw [IncidenceNode.incidencePerm_mul, Equiv.Perm.mul_apply]
    exact endpointCorrection
  let sourceBase := UniversalVertex.base
    (IncidenceGraph diagram root finer) (IncidenceRoot diagram root finer)
  let sourceTransformation : DeckGroup diagram root finer :=
    UniversalVertex.CompositeDeckTransformation.between
      correctedSymmetry sourceBase sourceBaseImage correctedEndpoint
  refine ⟨sourceTransformation, ?_, ?_⟩
  · apply UniversalVertex.CompositeDeckTransformation.encoding_injective
      targetBase
    apply Prod.ext
    · change GaloisLevel.automorphismTransition diagram root refinement
          correctedSymmetry = targetSymmetry
      exact correctedSymmetryMaps
    · change UniversalVertex.CompositeDeckTransformation.treePerm
          (deckTransitionToFun diagram root refinement sourceTransformation)
            targetBase = targetBaseImage
      rw [deckTransitionToFun_base]
      change RefinementTreeMap diagram root refinement
          (UniversalVertex.CompositeDeckTransformation.treePerm
            sourceTransformation sourceBase) = targetBaseImage
      rw [UniversalVertex.CompositeDeckTransformation.between_apply_first]
      exact baseImageMaps
  · unfold deckDepth
    change
      (UniversalVertex.CompositeDeckTransformation.treePerm
        sourceTransformation sourceBase).depth ≤ targetBaseImage.depth
    rw [UniversalVertex.CompositeDeckTransformation.between_apply_first]
    exact baseImageBound

/-- For one prescribed target deck transformation, its depth-bounded lifts
through a Galois refinement form a finite type.  The proof records only the
finite Galois symmetry and a lift of the target root image, rather than a
globally finite ball in the (possibly infinite) universal tree. -/
theorem deckTransition_boundedFiber_finite
    {finer coarser : GaloisLevel diagram root}
    (refinement : finer ⟶ coarser)
    (targetTransformation : DeckGroup diagram root coarser) :
    Finite {sourceTransformation : DeckGroup diagram root finer //
      deckTransition diagram root refinement sourceTransformation =
          targetTransformation ∧
        deckDepth diagram root finer sourceTransformation ≤
          deckDepth diagram root coarser targetTransformation} := by
  letI : GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root) :=
    SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram root
  letI : PreGaloisCategory.IsGalois finer.object := finer.isGalois
  let sourceBase := UniversalVertex.base
    (IncidenceGraph diagram root finer) (IncidenceRoot diagram root finer)
  let targetBase := UniversalVertex.base
    (IncidenceGraph diagram root coarser) (IncidenceRoot diagram root coarser)
  let targetBaseImage :=
    UniversalVertex.CompositeDeckTransformation.treePerm
      targetTransformation targetBase
  let boundedTreeFiber :=
    {source : IncidenceTreeVertex diagram root finer //
      RefinementTreeMap diagram root refinement source = targetBaseImage ∧
        source.depth ≤ targetBaseImage.depth}
  letI : Finite boundedTreeFiber :=
    refinementTreeMap_boundedFiber_finite diagram root refinement
      targetBaseImage
  let encode :
      {sourceTransformation : DeckGroup diagram root finer //
        deckTransition diagram root refinement sourceTransformation =
            targetTransformation ∧
          deckDepth diagram root finer sourceTransformation ≤
            deckDepth diagram root coarser targetTransformation} →
        Aut finer.object × boundedTreeFiber :=
    fun sourceTransformation ↦
      (UniversalVertex.CompositeDeckTransformation.baseSymmetry
          sourceTransformation.1,
        ⟨UniversalVertex.CompositeDeckTransformation.treePerm
            sourceTransformation.1 sourceBase,
          by
            have maps := congrArg
              (fun transformation : DeckGroup diagram root coarser ↦
                UniversalVertex.CompositeDeckTransformation.treePerm
                  transformation targetBase)
              sourceTransformation.2.1
            change
              UniversalVertex.CompositeDeckTransformation.treePerm
                  (deckTransitionToFun diagram root refinement
                    sourceTransformation.1)
                  (UniversalVertex.base (IncidenceGraph diagram root coarser)
                    (IncidenceRoot diagram root coarser)) =
                UniversalVertex.CompositeDeckTransformation.treePerm
                  targetTransformation
                  (UniversalVertex.base (IncidenceGraph diagram root coarser)
                    (IncidenceRoot diagram root coarser)) at maps
            rw [deckTransitionToFun_base, TransitionedBaseImage] at maps
            exact maps,
          sourceTransformation.2.2⟩)
  exact Finite.of_injective encode (by
    intro first second equality
    apply Subtype.ext
    apply UniversalVertex.CompositeDeckTransformation.encoding_injective
      sourceBase
    apply Prod.ext
    · exact congrArg
        (fun value : Aut finer.object × boundedTreeFiber ↦ value.1)
        equality
    · exact congrArg
        (fun value : Aut finer.object × boundedTreeFiber ↦ value.2.1)
        equality)

/-- At one finite Galois level, complete deck transformations with bounded
root-image depth form a finite type. -/
theorem deckGroup_finite_bounded_depth
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : GaloisLevel diagram root) (bound : ℕ) :
    Finite {transformation : DeckGroup diagram root level //
      deckDepth diagram root level transformation ≤ bound} := by
  letI : GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root) :=
    SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram root
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  letI : Finite (LevelSemiGraph diagram root level).Vertex :=
    GaloisLevel.vertex_finite diagram root level
  letI : Finite (LevelSemiGraph diagram root level).Edge :=
    GaloisLevel.edge_finite diagram root level
  letI : Finite (IncidenceNode (LevelSemiGraph diagram root level)) :=
    inferInstance
  let basePoint := UniversalVertex.base (IncidenceGraph diagram root level)
    (IncidenceRoot diagram root level)
  let boundedTree :=
    {point : IncidenceTreeVertex diagram root level // point.depth ≤ bound}
  haveI : Finite boundedTree :=
    UniversalVertex.finite_bounded_depth
      (IncidenceGraph diagram root level) (IncidenceRoot diagram root level)
        bound
  let encode :
      {transformation : DeckGroup diagram root level //
        deckDepth diagram root level transformation ≤ bound} →
        Aut level.object × boundedTree :=
    fun transformation ↦
      (UniversalVertex.CompositeDeckTransformation.baseSymmetry
          transformation.1,
        ⟨UniversalVertex.CompositeDeckTransformation.treePerm
            transformation.1 basePoint,
          transformation.2⟩)
  exact Finite.of_injective encode (by
    intro first second equality
    apply Subtype.ext
    apply UniversalVertex.CompositeDeckTransformation.encoding_injective
      basePoint
    apply Prod.ext
    · exact congrArg (fun value : Aut level.object × boundedTree ↦ value.1)
        equality
    · exact congrArg (fun value : Aut level.object × boundedTree ↦ value.2.1)
        equality)

/-- Evaluation of a compatible family in the underlying literal deck
diagram is surjective at every Galois level. -/
theorem deckTypeDiagram_eval_section_surjective
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (level : GaloisLevel diagram root) :
    Function.Surjective
      (fun compatible :
          (deckDiagram diagram root ⋙ forget GrpCat).sections ↦
        compatible.val level) := by
  let typeDiagram := deckDiagram diagram root ⋙ forget GrpCat
  let height : ∀ level, typeDiagram.obj level → ℕ :=
    fun level transformation ↦
      deckDepth diagram root level transformation.down
  apply CategoryTheory.Functor.eval_section_surjective_of_bounded_lifts
    typeDiagram height
  · intro finer coarser refinement transformation
    rcases transformation with ⟨transformation⟩
    change deckDepth diagram root coarser
        (deckTransition diagram root refinement transformation) ≤
      deckDepth diagram root finer transformation
    exact deckDepth_transition_le diagram root refinement transformation
  · intro finer coarser refinement target
    rcases target with ⟨target⟩
    let forgetLift :
        {source : typeDiagram.obj finer //
          typeDiagram.map refinement source = ULift.up target ∧
            height finer source ≤ height coarser (ULift.up target)} →
          {source : DeckGroup diagram root finer //
            deckTransition diagram root refinement source = target ∧
              deckDepth diagram root finer source ≤
                deckDepth diagram root coarser target} :=
      fun source ↦ ⟨source.1.down, by
        constructor
        · exact congrArg ULift.down source.2.1
        · exact source.2.2⟩
    letI : Finite
        {source : DeckGroup diagram root finer //
          deckTransition diagram root refinement source = target ∧
            deckDepth diagram root finer source ≤
              deckDepth diagram root coarser target} :=
      deckTransition_boundedFiber_finite diagram root refinement target
    exact Finite.of_injective forgetLift (by
      intro first second equality
      apply Subtype.ext
      apply ULift.ext
      exact congrArg Subtype.val equality)
  · intro finer coarser refinement target
    rcases target with ⟨target⟩
    obtain ⟨source, maps, bounded⟩ :=
      deckTransition_bounded_preimage diagram root refinement target
    exact ⟨ULift.up source, congrArg ULift.up maps, bounded⟩

/-- The underlying carrier of the literal group limit is the compatible
section type of the underlying deck diagram. -/
noncomputable def rawDeckLimitEquivSections
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge] :
    (countableDeckSystem diagram root).RawLimit ≃
      (deckDiagram diagram root ⋙ forget GrpCat).sections :=
  (preservesLimitIso (forget GrpCat) (deckDiagram diagram root)).toEquiv.trans
    (Types.limitEquivSections
      (deckDiagram diagram root ⋙ forget GrpCat))

/-- The section equivalence reads the same coordinate as the literal raw
deck-limit projection. -/
@[simp]
theorem rawDeckLimitEquivSections_apply
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (value : (countableDeckSystem diagram root).RawLimit)
    (level : GaloisLevel diagram root) :
    (rawDeckLimitEquivSections diagram root value).val level =
      (countableDeckSystem diagram root).rawProjection level value := by
  change limit.π (deckDiagram diagram root ⋙ forget GrpCat) level
      ((preservesLimitIso (forget GrpCat)
        (deckDiagram diagram root)).hom value) =
    (limit.π (deckDiagram diagram root) level).hom value
  exact ConcreteCategory.congr_hom
    (preservesLimitIso_hom_π (forget GrpCat)
      (deckDiagram diagram root) level) value

/-- Every literal deck group occurs as a coordinate of a compatible family
in the complete raw inverse limit. -/
theorem rawDeckProjection_surjective
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (level : GaloisLevel diagram root) :
    Function.Surjective
      ((countableDeckSystem diagram root).rawProjection level) := by
  intro target
  obtain ⟨compatible, atLevel⟩ :=
    deckTypeDiagram_eval_section_surjective diagram root level target
  let value : (countableDeckSystem diagram root).RawLimit :=
    (rawDeckLimitEquivSections diagram root).symm compatible
  refine ⟨value, ?_⟩
  rw [← rawDeckLimitEquivSections_apply diagram root value level]
  exact congrArg (fun compatibleSection ↦ compatibleSection.val level)
      ((rawDeckLimitEquivSections diagram root).apply_symm_apply compatible) |>.trans
    atLevel

/-- The literal full deck groups and their proven-surjective transitions
directly form the source's tempered-group presentation. -/
noncomputable def literalTemperedPresentation
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge] :
    SourceTemperedGroupPresentation (GaloisLevel diagram root) where
  diagram := deckDiagram diagram root
  transition_surjective := by
    intro finer coarser refinement target
    rcases target with ⟨target⟩
    obtain ⟨source, maps⟩ :=
      deckTransition_surjective diagram root refinement target
    exact ⟨ULift.up source, congrArg ULift.up maps⟩
  level_countable := fun level ↦ deckDiagram_obj_countable diagram root level

/-- Every coordinate projection of the literal tempered presentation is
surjective. -/
theorem literalTemperedPresentation_projection_surjective
    [Countable diagram.base.Vertex] [Countable diagram.base.Edge]
    (level : GaloisLevel diagram root) :
    Function.Surjective
      ((literalTemperedPresentation diagram root).projection level) :=
  rawDeckProjection_surjective diagram root level

end SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

end Iut
