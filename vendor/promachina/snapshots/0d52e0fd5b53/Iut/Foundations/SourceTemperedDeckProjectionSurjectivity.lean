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

/-- A cofiltered system with finite bounded parts and bounded transition
lifts has surjective evaluation maps on its space of sections. -/
theorem eval_section_surjective_of_bounded_lifts
    [IsCofiltered Index]
    (system : Index ⥤ Type v)
    (height : ∀ level, system.obj level → ℕ)
    (map_height : ∀ {finer coarser : Index} (map : finer ⟶ coarser)
      (value : system.obj finer),
      height coarser (system.map map value) ≤ height finer value)
    (bounded_finite : ∀ (level : Index) (bound : ℕ),
      Finite {value : system.obj level // height level value ≤ bound})
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
    let forgetBound : lifts.obj refinement →
        { value : system.obj refinement.left //
          height refinement.left value ≤ height level target } :=
      fun value ↦ ⟨value.1, value.2.2⟩
    exact Finite.of_injective forgetBound (by
      intro first second equality
      apply Subtype.ext
      exact congrArg
        (fun value : { value : system.obj refinement.left //
          height refinement.left value ≤ height level target } ↦ value.1)
        equality)
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

namespace SourceCombinatorialUniversalCover.UniversalVertex

variable {Vertex : Type u} (graph : SimpleGraph Vertex) (root : Vertex)

/-- Changing a root along an equality preserves reduced-walk depth. -/
@[simp]
theorem castRoot_depth {first second : Vertex} (rootsEqual : first = second)
    (point : UniversalVertex graph first) :
    (castRoot graph rootsEqual point).depth = point.depth := by
  subst second
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
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
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
  · intro boundedLevel bound
    let forgetLift :
        {transformation : typeDiagram.obj boundedLevel //
          height boundedLevel transformation ≤ bound} →
          {transformation : DeckGroup diagram root boundedLevel //
            deckDepth diagram root boundedLevel transformation ≤ bound} :=
      fun transformation ↦ ⟨transformation.1.down, transformation.2⟩
    letI : Finite
        {transformation : DeckGroup diagram root boundedLevel //
          deckDepth diagram root boundedLevel transformation ≤ bound} :=
      deckGroup_finite_bounded_depth diagram root boundedLevel bound
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
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    (countableDeckSystem diagram root).RawLimit ≃
      (deckDiagram diagram root ⋙ forget GrpCat).sections :=
  (preservesLimitIso (forget GrpCat) (deckDiagram diagram root)).toEquiv.trans
    (Types.limitEquivSections
      (deckDiagram diagram root ⋙ forget GrpCat))

/-- The section equivalence reads the same coordinate as the literal raw
deck-limit projection. -/
@[simp]
theorem rawDeckLimitEquivSections_apply
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
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
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
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
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
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
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : GaloisLevel diagram root) :
    Function.Surjective
      ((literalTemperedPresentation diagram root).projection level) :=
  rawDeckProjection_surjective diagram root level

end SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

end Iut
