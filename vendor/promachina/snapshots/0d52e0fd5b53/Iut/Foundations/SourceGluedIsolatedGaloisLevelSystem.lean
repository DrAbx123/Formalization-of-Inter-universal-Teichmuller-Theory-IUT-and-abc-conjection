/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceGluedIsolatedFiniteEtaleCover
import Iut.Foundations.SourceConnectedAnabelioidSlice
import Mathlib.CategoryTheory.Galois.Prorepresentability
import Mathlib.CategoryTheory.Galois.Topology

/-!
# Galois levels for the isolated-edge total anabelioid

The vertex-free connected case of Definition 2.1 consists of one isolated
edge, and its total anabelioid is the edge anabelioid.  This file constructs
the pointed cofiltered Galois system in that case.  The full automorphism
group of a level is retained even though its action on the one-component
underlying semigraph can be trivial; this distinction is needed by the
composite deck group constructed before Proposition 3.6.
-/

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace SourceSemiGraphOfAnabelioids

noncomputable section

variable (diagram : Iut.SourceSemiGraphOfAnabelioids.{u})
    (noVertex : ¬Nonempty diagram.base.Vertex)

local instance isolatedCoverCategory :
    Category (isolatedAnabelioid diagram noVertex).Cover :=
  (isolatedAnabelioid diagram noVertex).coverCategory

local instance isolatedGaloisCategory :
    GaloisCategory (isolatedAnabelioid diagram noVertex).Cover :=
  (isolatedAnabelioid diagram noVertex).galoisCategory

local instance isolatedFiberFunctor :
    PreGaloisCategory.FiberFunctor
      (isolatedAnabelioid diagram noVertex).fiber :=
  (isolatedAnabelioid diagram noVertex).fiberFunctor

/-- A pointed connected Galois object of the total anabelioid in the
isolated-edge case. -/
structure IsolatedGaloisLevel where
  object : (isolatedAnabelioid diagram noVertex).Cover
  point : (isolatedAnabelioid diagram noVertex).fiber.obj object
  isGalois : PreGaloisCategory.IsGalois object

namespace IsolatedGaloisLevel

/-- Point-preserving refinements of isolated-edge Galois levels. -/
@[ext]
structure Hom (finer coarser : IsolatedGaloisLevel diagram noVertex) where
  val : finer.object ⟶ coarser.object
  comp : (isolatedAnabelioid diagram noVertex).fiber.map val finer.point =
    coarser.point := by simp

instance : Category (IsolatedGaloisLevel diagram noVertex) where
  Hom := Hom diagram noVertex
  id level := ⟨𝟙 level.object, by simp⟩
  comp first second := ⟨first.val ≫ second.val, by
    simp only [Functor.map_comp, FintypeCat.comp_apply, first.comp, second.comp]⟩

@[simp]
theorem id_val (level : IsolatedGaloisLevel diagram noVertex) :
    (𝟙 level : level ⟶ level).val = 𝟙 level.object := rfl

@[simp]
theorem comp_val {first middle last : IsolatedGaloisLevel diagram noVertex}
    (f : first ⟶ middle) (g : middle ⟶ last) :
    (f ≫ g).val = f.val ≫ g.val := rfl

/-- The finite-etale semigraph attached to an isolated Galois level. -/
noncomputable abbrev semiGraph
    (level : IsolatedGaloisLevel diagram noVertex) : SourceSemiGraph.{u} :=
  isolatedFiniteEtaleCoverSemiGraph diagram noVertex level.object

/-- Its proper finite-etale projection to the base semigraph. -/
noncomputable abbrev projection
    (level : IsolatedGaloisLevel diagram noVertex) :
    level.semiGraph.Hom diagram.base :=
  isolatedFiniteEtaleCoverProjection diagram noVertex level.object

/-- The point selects the unique connected edge component of the level. -/
noncomputable def rootEdge
    (level : IsolatedGaloisLevel diagram noVertex) : level.semiGraph.Edge :=
  Quotient.mk'' level.point

/-- The semigraph of an isolated Galois level is connected. -/
theorem semiGraph_connected
    (level : IsolatedGaloisLevel diagram noVertex) :
    level.semiGraph.IsConnected := by
  letI := (isolatedAnabelioid diagram noVertex).coverCategory
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  exact isolatedFiniteEtaleCoverSemiGraph_isConnected
    diagram noVertex level.object

/-- Its projection is proper. -/
theorem projection_isProper
    (level : IsolatedGaloisLevel diagram noVertex) :
    level.projection.IsProper :=
  isolatedFiniteEtaleCoverProjection_isProper diagram noVertex level.object

/-- A pointed refinement induces the finite-etale semigraph transition. -/
noncomputable def transition
    {finer coarser : IsolatedGaloisLevel diagram noVertex}
    (refinement : finer ⟶ coarser) :
    finer.semiGraph.Hom coarser.semiGraph :=
  isolatedFiniteEtaleCoverTransition diagram noVertex refinement.val

/-- Pointed refinement preserves the selected edge component. -/
theorem transition_rootEdge
    {finer coarser : IsolatedGaloisLevel diagram noVertex}
    (refinement : finer ⟶ coarser) :
    (transition diagram noVertex refinement).edgeMap finer.rootEdge =
      coarser.rootEdge := by
  change Quotient.mk''
      ((isolatedAnabelioid diagram noVertex).fiber.map refinement.val
        finer.point) = Quotient.mk'' coarser.point
  exact congrArg Quotient.mk'' refinement.comp

/-- Isolated transitions are functorial on edges. -/
theorem transition_edge_comp
    {first middle last : IsolatedGaloisLevel diagram noVertex}
    (firstMap : first ⟶ middle) (secondMap : middle ⟶ last)
    (edge : first.semiGraph.Edge) :
    (transition diagram noVertex (firstMap ≫ secondMap)).edgeMap edge =
      (transition diagram noVertex secondMap).edgeMap
        ((transition diagram noVertex firstMap).edgeMap edge) :=
  isolatedFiniteEtaleCoverTransition_edgeMap_comp
    diagram noVertex firstMap.val secondMap.val edge

/-- Identity refinement acts identically on edges. -/
theorem transition_edge_id
    (level : IsolatedGaloisLevel diagram noVertex)
    (edge : level.semiGraph.Edge) :
    (transition diagram noVertex (𝟙 level)).edgeMap edge = edge :=
  isolatedFiniteEtaleCoverTransition_edgeMap_id
    diagram noVertex level.object edge

/-- Every pointed connected object is dominated by a pointed Galois level. -/
theorem exists_galoisLevel_over_connected
    (object : (isolatedAnabelioid diagram noVertex).Cover)
    [PreGaloisCategory.IsConnected object]
    (point : (isolatedAnabelioid diagram noVertex).fiber.obj object) :
    ∃ (level : IsolatedGaloisLevel diagram noVertex)
        (morphism : level.object ⟶ object),
      (isolatedAnabelioid diagram noVertex).fiber.map morphism level.point =
        point := by
  letI := (isolatedAnabelioid diagram noVertex).coverCategory
  letI := (isolatedAnabelioid diagram noVertex).galoisCategory
  letI := (isolatedAnabelioid diagram noVertex).fiberFunctor
  obtain ⟨galoisObject, morphism, galoisPoint, isGalois, pointMaps⟩ :=
    PreGaloisCategory.exists_hom_from_galois_of_fiber
      (isolatedAnabelioid diagram noVertex).fiber object point
  exact ⟨⟨galoisObject, galoisPoint, isGalois⟩, morphism, pointMaps⟩

/-- A pointed refinement between two isolated levels is unique. -/
theorem refinement_unique
    {finer coarser : IsolatedGaloisLevel diagram noVertex}
    (first second : finer ⟶ coarser) : first = second := by
  apply Hom.ext
  letI := (isolatedAnabelioid diagram noVertex).coverCategory
  letI := (isolatedAnabelioid diagram noVertex).galoisCategory
  letI := (isolatedAnabelioid diagram noVertex).fiberFunctor
  letI : PreGaloisCategory.IsGalois finer.object := finer.isGalois
  apply PreGaloisCategory.evaluation_injective_of_isConnected
    (isolatedAnabelioid diagram noVertex).fiber
    finer.object coarser.object finer.point
  exact first.comp.trans second.comp.symm

/-- Pointed isolated-edge Galois levels form a cofiltered system. -/
noncomputable instance isCofilteredOrEmpty :
    IsCofilteredOrEmpty (IsolatedGaloisLevel diagram noVertex) where
  cone_objs := fun first second => by
    letI := (isolatedAnabelioid diagram noVertex).coverCategory
    letI := (isolatedAnabelioid diagram noVertex).galoisCategory
    letI := (isolatedAnabelioid diagram noVertex).fiberFunctor
    obtain ⟨common, morphism, point, isGalois, pointMaps⟩ :=
      PreGaloisCategory.exists_hom_from_galois_of_fiber
        (isolatedAnabelioid diagram noVertex).fiber
        (first.object ⨯ second.object)
        ((PreGaloisCategory.fiberBinaryProductEquiv
          (isolatedAnabelioid diagram noVertex).fiber
          first.object second.object).symm (first.point, second.point))
    refine ⟨⟨common, point, isGalois⟩,
      ⟨morphism ≫ prod.fst, ?_⟩, ⟨morphism ≫ prod.snd, ?_⟩, trivial⟩
    · simp only [Functor.map_comp, pointMaps, FintypeCat.comp_apply,
        PreGaloisCategory.fiberBinaryProductEquiv_symm_fst_apply]
    · simp only [Functor.map_comp, pointMaps, FintypeCat.comp_apply,
        PreGaloisCategory.fiberBinaryProductEquiv_symm_snd_apply]
  cone_maps := fun {first second} firstMap secondMap => by
    letI := (isolatedAnabelioid diagram noVertex).coverCategory
    letI := (isolatedAnabelioid diagram noVertex).galoisCategory
    letI := (isolatedAnabelioid diagram noVertex).fiberFunctor
    obtain ⟨common, morphism, point, isGalois, pointMaps⟩ :=
      PreGaloisCategory.exists_hom_from_galois_of_fiber
        (isolatedAnabelioid diagram noVertex).fiber first.object first.point
    let commonLevel : IsolatedGaloisLevel diagram noVertex :=
      ⟨common, point, isGalois⟩
    let commonMap : commonLevel ⟶ first := ⟨morphism, pointMaps⟩
    exact ⟨commonLevel, commonMap,
      refinement_unique diagram noVertex
        (commonMap ≫ firstMap) (commonMap ≫ secondMap)⟩

/-- The isolated-edge Galois indexing category is inhabited. -/
noncomputable instance level_nonempty :
    Nonempty (IsolatedGaloisLevel diagram noVertex) := by
  let data := isolatedAnabelioid diagram noVertex
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  let terminalObject := ⊤_ data.Cover
  letI : PreGaloisCategory.IsConnected terminalObject :=
    sourceGaloisCategory_isConnected_of_isTerminal
      terminalObject terminalIsTerminal
  let point := Classical.choice
    (inferInstance : Nonempty (data.fiber.obj terminalObject))
  obtain ⟨level, _morphism, _pointMaps⟩ :=
    exists_galoisLevel_over_connected
      diagram noVertex terminalObject point
  exact ⟨level⟩

/-- Thus the isolated-edge level system is genuinely cofiltered. -/
noncomputable instance isCofiltered :
    IsCofiltered (IsolatedGaloisLevel diagram noVertex) where
  cone_objs := IsCofilteredOrEmpty.cone_objs
  cone_maps := IsCofilteredOrEmpty.cone_maps
  nonempty := inferInstance

/-! ## Normal-open quotient and full finite Galois symmetry -/

/-- The point stabilizer represented by an isolated-edge Galois level. -/
noncomputable def openNormalStabilizer
    (level : IsolatedGaloisLevel diagram noVertex) :
    OpenNormalSubgroup (Aut (isolatedAnabelioid diagram noVertex).fiber) := by
  let data := isolatedAnabelioid diagram noVertex
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  letI : TopologicalSpace (data.fiber.obj level.object) := ⊥
  letI : DiscreteTopology (data.fiber.obj level.object) := ⟨rfl⟩
  exact
    { toOpenSubgroup :=
        { toSubgroup := MulAction.stabilizer (Aut data.fiber) level.point
          isOpen' := stabilizer_isOpen (Aut data.fiber) level.point }
      isNormal' := PreGaloisCategory.stabilizer_normal_of_isGalois
        data.fiber level.object level.point }

/-- The fiber is the coset set of the represented normal-open subgroup. -/
noncomputable def fiberCosetEquiv
    (level : IsolatedGaloisLevel diagram noVertex) :
    Aut ((isolatedAnabelioid diagram noVertex).fiber) ⧸
        (level.openNormalStabilizer :
          Subgroup (Aut ((isolatedAnabelioid diagram noVertex).fiber))) ≃
      (isolatedAnabelioid diagram noVertex).fiber.obj level.object := by
  let data := isolatedAnabelioid diagram noVertex
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  letI : MulAction.IsPretransitive
      (Aut data.fiber) (data.fiber.obj level.object) :=
    PreGaloisCategory.FiberFunctor.isPretransitive_of_isGalois
      data.fiber level.object
  exact
    (MulAction.orbitEquivQuotientStabilizer
      (Aut data.fiber) level.point).symm |>.trans
      ((Equiv.setCongr
        (MulAction.orbit_eq_univ (Aut data.fiber) level.point)).trans
        (Equiv.Set.univ (data.fiber.obj level.object)))

/-- The full object automorphism induces the (possibly nonfaithful) visible
permutation of the isolated level's edge components.  Keeping the source
automorphism as the acting element, rather than replacing it by the image of
this permutation, preserves constituent symmetries invisible to incidence. -/
noncomputable def automorphismEdgePerm
    (level : IsolatedGaloisLevel diagram noVertex)
    (automorphism : Aut level.object) : Equiv.Perm level.semiGraph.Edge where
  toFun := (isolatedFiniteEtaleCoverTransition diagram noVertex
    automorphism.hom).edgeMap
  invFun := (isolatedFiniteEtaleCoverTransition diagram noVertex
    automorphism.inv).edgeMap
  left_inv edge := by
    rw [← isolatedFiniteEtaleCoverTransition_edgeMap_comp
      diagram noVertex automorphism.hom automorphism.inv edge,
      automorphism.hom_inv_id]
    exact isolatedFiniteEtaleCoverTransition_edgeMap_id
      diagram noVertex level.object edge
  right_inv edge := by
    rw [← isolatedFiniteEtaleCoverTransition_edgeMap_comp
      diagram noVertex automorphism.inv automorphism.hom edge,
      automorphism.inv_hom_id]
    exact isolatedFiniteEtaleCoverTransition_edgeMap_id
      diagram noVertex level.object edge

/-- The visible edge permutations form an action of the complete finite
Galois automorphism group. -/
noncomputable def automorphismEdgeAction
    (level : IsolatedGaloisLevel diagram noVertex) :
    Aut level.object →* Equiv.Perm level.semiGraph.Edge where
  toFun := automorphismEdgePerm diagram noVertex level
  map_one' := by
    apply Equiv.ext
    exact transition_edge_id diagram noVertex level
  map_mul' first second := by
    apply Equiv.ext
    intro edge
    change EtaleFundamentalGroup.fiberComponentHomMap
        (isolatedAnabelioid diagram noVertex) (first * second).hom edge =
      EtaleFundamentalGroup.fiberComponentHomMap
        (isolatedAnabelioid diagram noVertex) first.hom
        (EtaleFundamentalGroup.fiberComponentHomMap
          (isolatedAnabelioid diagram noVertex) second.hom edge)
    rw [Aut.Aut_mul_def]
    exact EtaleFundamentalGroup.fiberComponentHomMap_comp_apply
      (isolatedAnabelioid diagram noVertex) second.hom first.hom edge

/-- The full automorphism group acts on all isolated semigraph incidence
data. -/
noncomputable def automorphismAction
    (level : IsolatedGaloisLevel diagram noVertex) :
    level.semiGraph.Action (Aut level.object) where
  vertexAction := 1
  edgeAction := automorphismEdgeAction diagram noVertex level
  branchAction :=
    { toFun := fun automorphism =>
        { toFun := fun branch ↦
            ⟨(automorphismEdgeAction diagram noVertex level)
              automorphism branch.edge, branch.2⟩
          invFun := fun branch ↦
            ⟨(automorphismEdgeAction diagram noVertex level)
              automorphism⁻¹ branch.edge, branch.2⟩
          left_inv := fun branch ↦ by
            rcases branch with ⟨edge, branch⟩
            refine Sigma.ext ?_ ?_
            · exact (automorphismEdgeAction diagram noVertex level
                automorphism).symm_apply_apply edge
            · rfl
          right_inv := fun branch ↦ by
            rcases branch with ⟨edge, branch⟩
            refine Sigma.ext ?_ ?_
            · exact (automorphismEdgeAction diagram noVertex level
                automorphism).apply_symm_apply edge
            · rfl }
      map_one' := by
        apply Equiv.ext
        rintro ⟨edge, branch⟩
        refine Sigma.ext ?_ ?_
        · change (automorphismEdgeAction diagram noVertex level) 1 edge = edge
          exact congrArg (fun permutation : Equiv.Perm level.semiGraph.Edge =>
            permutation edge) (map_one
              (automorphismEdgeAction diagram noVertex level))
        · rfl
      map_mul' := by
        intro first second
        apply Equiv.ext
        rintro ⟨edge, branch⟩
        refine Sigma.ext ?_ ?_
        · change (automorphismEdgeAction diagram noVertex level)
              (first * second) edge =
            (automorphismEdgeAction diagram noVertex level) first
              ((automorphismEdgeAction diagram noVertex level) second edge)
          exact congrArg (fun permutation : Equiv.Perm level.semiGraph.Edge =>
            permutation edge) (map_mul
              (automorphismEdgeAction diagram noVertex level) first second)
        · rfl }
  branch_edge := by
    intro automorphism branch
    rfl
  coincidence_action := by
    intro _ branch
    change none = Option.map _ none
    rfl

/-- The visible Galois action is transitive on the unique nonempty edge
fiber. -/
theorem edgeAction_transitive_on_projection_fiber
    (level : IsolatedGaloisLevel diagram noVertex)
    (first second : level.semiGraph.Edge)
    (_sameBase : level.projection.edgeMap first =
      level.projection.edgeMap second) :
    ∃ automorphism : Aut level.object,
      (automorphismAction diagram noVertex level).edgeAction
        automorphism first = second := by
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  letI : PreGaloisCategory.IsConnected level.object :=
    level.isGalois.toIsConnected
  letI : Subsingleton level.semiGraph.Edge :=
    EtaleFundamentalGroup.fiberComponentSubsingletonOfIsConnected
      (isolatedAnabelioid diagram noVertex) level.object
  have components : first = second := Subsingleton.elim first second
  subst second
  exact ⟨1, by simp⟩

/-- Refinement descends the full object automorphism group. -/
noncomputable def automorphismTransition
    {finer coarser : IsolatedGaloisLevel diagram noVertex}
    (refinement : finer ⟶ coarser) :
    Aut finer.object →* Aut coarser.object := by
  let data := isolatedAnabelioid diagram noVertex
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  letI : PreGaloisCategory.IsGalois finer.object := finer.isGalois
  letI : PreGaloisCategory.IsGalois coarser.object := coarser.isGalois
  exact PreGaloisCategory.autMapHom refinement.val

/-- Every coarser isolated-level symmetry lifts along refinement. -/
theorem automorphismTransition_surjective
    {finer coarser : IsolatedGaloisLevel diagram noVertex}
    (refinement : finer ⟶ coarser) :
    Function.Surjective (automorphismTransition diagram noVertex refinement) := by
  let data := isolatedAnabelioid diagram noVertex
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  letI : PreGaloisCategory.IsGalois finer.object := finer.isGalois
  letI : PreGaloisCategory.IsGalois coarser.object := coarser.isGalois
  exact PreGaloisCategory.autMap_surjective_of_isGalois refinement.val

/-- Refinement intertwines the derived full Galois actions on the isolated
edge component. -/
theorem transition_edge_automorphism
    {finer coarser : IsolatedGaloisLevel diagram noVertex}
    (refinement : finer ⟶ coarser)
    (automorphism : Aut finer.object) (edge : finer.semiGraph.Edge) :
    (transition diagram noVertex refinement).edgeMap
        ((automorphismAction diagram noVertex finer).edgeAction
          automorphism edge) =
      (automorphismAction diagram noVertex coarser).edgeAction
        (automorphismTransition diagram noVertex refinement automorphism)
        ((transition diagram noVertex refinement).edgeMap edge) := by
  let data := isolatedAnabelioid diagram noVertex
  letI : PreGaloisCategory.IsGalois finer.object := finer.isGalois
  letI : PreGaloisCategory.IsGalois coarser.object := coarser.isGalois
  change EtaleFundamentalGroup.fiberComponentHomMap data refinement.val
      (EtaleFundamentalGroup.fiberComponentHomMap data
        automorphism.hom edge) =
    EtaleFundamentalGroup.fiberComponentHomMap data
      (PreGaloisCategory.autMap refinement.val automorphism).hom
      (EtaleFundamentalGroup.fiberComponentHomMap data refinement.val edge)
  rw [← EtaleFundamentalGroup.fiberComponentHomMap_comp_apply
      data automorphism.hom refinement.val edge,
    ← EtaleFundamentalGroup.fiberComponentHomMap_comp_apply
      data refinement.val
        (PreGaloisCategory.autMap refinement.val automorphism).hom edge,
    PreGaloisCategory.comp_autMap]

/-- The same equivariance holds for total branches; their branch labels are
unchanged and only their edge component moves. -/
theorem transition_branch_automorphism
    {finer coarser : IsolatedGaloisLevel diagram noVertex}
    (refinement : finer ⟶ coarser)
    (automorphism : Aut finer.object)
    (branch : finer.semiGraph.TotalBranch) :
    (transition diagram noVertex refinement).totalBranchMap
        ((automorphismAction diagram noVertex finer).branchAction
          automorphism branch) =
      (automorphismAction diagram noVertex coarser).branchAction
        (automorphismTransition diagram noVertex refinement automorphism)
        ((transition diagram noVertex refinement).totalBranchMap branch) := by
  rcases branch with ⟨edge, branch⟩
  refine Sigma.ext
    (transition_edge_automorphism diagram noVertex
      refinement automorphism edge) ?_
  rfl

end IsolatedGaloisLevel

end

end SourceSemiGraphOfAnabelioids

end Iut
