/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceGluedFiniteEtaleTransition
import Iut.Foundations.SourceGluedTotalAnabelioid

/-!
# Finite-etale levels in the isolated-edge case

When a connected base semigraph has no vertices, Definition 2.1 forces one
isolated edge and identifies `B(G)` with its edge anabelioid.  The semigraph
attached to an object has no vertices and one lifted edge for each connected
component of that object.  A connected object has exactly one such component,
so its attached semigraph is connected without an extra hypothesis field.
-/

namespace Iut

universe u

open CategoryTheory

namespace EtaleFundamentalGroup

/-- The connected-component orbit set of a connected object is nonempty. -/
noncomputable instance fiberComponentNonemptyOfIsConnected
    (data : EtaleFundamentalGroup.{u}) (object : data.Cover)
    [letI := data.coverCategory; PreGaloisCategory.IsConnected object] :
    Nonempty (data.FiberComponent object) := by
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  obtain ⟨point⟩ := PreGaloisCategory.nonempty_fiber_of_isConnected
    data.fiber object
  exact ⟨Quotient.mk'
    (s := MulAction.orbitRel (Aut data.fiber) (data.fiber.obj object)) point⟩

/-- A connected object has exactly one connected component. -/
noncomputable instance fiberComponentSubsingletonOfIsConnected
    (data : EtaleFundamentalGroup.{u}) (object : data.Cover)
    [letI := data.coverCategory; PreGaloisCategory.IsConnected object] :
    Subsingleton (data.FiberComponent object) := by
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  constructor
  intro first second
  refine Quotient.inductionOn' first ?_
  intro firstPoint
  refine Quotient.inductionOn' second ?_
  intro secondPoint
  apply Quotient.sound
  change (MulAction.orbitRel (Aut data.fiber)
    (data.fiber.obj object)) firstPoint secondPoint
  rw [MulAction.orbitRel_apply]
  exact MulAction.exists_smul_eq (Aut data.fiber) secondPoint firstPoint

end EtaleFundamentalGroup

namespace SourceSemiGraphOfAnabelioids

variable (diagram : Iut.SourceSemiGraphOfAnabelioids.{u})
    (noVertex : ¬Nonempty diagram.base.Vertex)

section Isolated

/-- The unique isolated base edge. -/
noncomputable def isolatedBaseEdge : diagram.base.Edge := by
  letI : IsEmpty diagram.base.Vertex := not_nonempty_iff.mp noVertex
  exact diagram.connected.uniqueEdge

/-- The edge anabelioid which is `B(G)` in the vertex-free case. -/
noncomputable abbrev isolatedAnabelioid : EtaleFundamentalGroup.{u} :=
  diagram.edgeAnabelioid (isolatedBaseEdge diagram noVertex)

/-- The semigraph attached to an object of the isolated-edge total
anabelioid. -/
noncomputable def isolatedFiniteEtaleCoverSemiGraph
    (object : (isolatedAnabelioid diagram noVertex).Cover) :
    SourceSemiGraph.{u} where
  Vertex := PEmpty.{u + 1}
  Edge := (isolatedAnabelioid diagram noVertex).FiberComponent object
  Branch := fun _ => diagram.base.Branch (isolatedBaseEdge diagram noVertex)
  branchFintype := fun _ =>
    diagram.base.branchFintype (isolatedBaseEdge diagram noVertex)
  branch_card := fun _ =>
    diagram.base.branch_card (isolatedBaseEdge diagram noVertex)
  coincidence := fun _ _ => none

/-- The proper projection of an isolated-edge finite-etale level to its base. -/
noncomputable def isolatedFiniteEtaleCoverProjection
    (object : (isolatedAnabelioid diagram noVertex).Cover) :
    (isolatedFiniteEtaleCoverSemiGraph diagram noVertex object).Hom
      diagram.base where
  vertexMap := PEmpty.elim
  edgeMap := fun _ => isolatedBaseEdge diagram noVertex
  branchEquiv := fun _ => Equiv.refl _
  map_coincidence := by
    intro _ _ vertex
    exact PEmpty.elim vertex

/-- The isolated-edge projection is proper. -/
theorem isolatedFiniteEtaleCoverProjection_isProper
    (object : (isolatedAnabelioid diagram noVertex).Cover) :
    (isolatedFiniteEtaleCoverProjection diagram noVertex object).IsProper := by
  letI : IsEmpty diagram.base.Vertex := not_nonempty_iff.mp noVertex
  intro edge branch
  constructor
  · rintro ⟨vertex, coincidence⟩
    exact PEmpty.elim vertex
  · rintro ⟨vertex, coincidence⟩
    exact isEmptyElim vertex

/-- Every vertex fiber is finite, vacuously. -/
instance isolatedFiniteEtaleCoverVertexFiberFinite
    (object : (isolatedAnabelioid diagram noVertex).Cover)
    (vertex : diagram.base.Vertex) :
    Finite ((isolatedFiniteEtaleCoverProjection diagram noVertex object).VertexFiber
      vertex) := by
  exact False.elim (noVertex ⟨vertex⟩)

/-- The sole base-edge fiber is the finite component set of the object. -/
noncomputable instance isolatedFiniteEtaleCoverEdgeFiberFinite
    (object : (isolatedAnabelioid diagram noVertex).Cover)
    (edge : diagram.base.Edge) :
    Finite ((isolatedFiniteEtaleCoverProjection diagram noVertex object).EdgeFiber
      edge) := by
  letI : IsEmpty diagram.base.Vertex := not_nonempty_iff.mp noVertex
  letI : Subsingleton diagram.base.Edge :=
    diagram.connected.subsingletonEdge_of_isEmpty
  let equivalence :
      (isolatedFiniteEtaleCoverProjection diagram noVertex object).EdgeFiber edge ≃
        (isolatedAnabelioid diagram noVertex).FiberComponent object :=
    { toFun := fun point => point.1
      invFun := fun component =>
        ⟨component, Subsingleton.elim
          (isolatedBaseEdge diagram noVertex) edge⟩
      left_inv := fun point => by
        apply Subtype.ext
        rfl
      right_inv := fun _ => rfl }
  exact Finite.of_equiv _ equivalence.symm

/-- A connected object of the isolated-edge anabelioid produces a connected
finite-etale semigraph level. -/
theorem isolatedFiniteEtaleCoverSemiGraph_isConnected
    (object : (isolatedAnabelioid diagram noVertex).Cover)
    [letI := (isolatedAnabelioid diagram noVertex).coverCategory
     PreGaloisCategory.IsConnected object] :
    (isolatedFiniteEtaleCoverSemiGraph diagram noVertex object).IsConnected := by
  letI : IsEmpty diagram.base.Vertex := not_nonempty_iff.mp noVertex
  right
  constructor
  · change IsEmpty PEmpty
    infer_instance
  · constructor
    · change Nonempty
        ((isolatedAnabelioid diagram noVertex).FiberComponent object)
      infer_instance
    · change Subsingleton
        ((isolatedAnabelioid diagram noVertex).FiberComponent object)
      infer_instance

/-- A morphism in the isolated-edge total anabelioid induces the refinement
map on its component semigraphs. -/
noncomputable def isolatedFiniteEtaleCoverTransition
    {source target : (isolatedAnabelioid diagram noVertex).Cover}
    (morphism :
      letI := (isolatedAnabelioid diagram noVertex).coverCategory
      source ⟶ target) :
    (isolatedFiniteEtaleCoverSemiGraph diagram noVertex source).Hom
      (isolatedFiniteEtaleCoverSemiGraph diagram noVertex target) where
  vertexMap := PEmpty.elim
  edgeMap := EtaleFundamentalGroup.fiberComponentHomMap
    (isolatedAnabelioid diagram noVertex) morphism
  branchEquiv := fun _ => Equiv.refl _
  map_coincidence := by
    intro _ _ vertex
    exact PEmpty.elim vertex

/-- Isolated-edge refinements preserve identity maps on edges. -/
theorem isolatedFiniteEtaleCoverTransition_edgeMap_id
    (object : (isolatedAnabelioid diagram noVertex).Cover)
    (edge : (isolatedFiniteEtaleCoverSemiGraph diagram noVertex object).Edge) :
    (isolatedFiniteEtaleCoverTransition diagram noVertex
      (letI := (isolatedAnabelioid diagram noVertex).coverCategory
       𝟙 object)).edgeMap edge = edge :=
  EtaleFundamentalGroup.fiberComponentHomMap_id_apply
    (isolatedAnabelioid diagram noVertex) object edge

/-- Isolated-edge refinement maps respect composition on edges. -/
theorem isolatedFiniteEtaleCoverTransition_edgeMap_comp
    {first middle target : (isolatedAnabelioid diagram noVertex).Cover}
    (firstMap :
      letI := (isolatedAnabelioid diagram noVertex).coverCategory
      first ⟶ middle)
    (secondMap :
      letI := (isolatedAnabelioid diagram noVertex).coverCategory
      middle ⟶ target)
    (edge : (isolatedFiniteEtaleCoverSemiGraph diagram noVertex first).Edge) :
    (isolatedFiniteEtaleCoverTransition diagram noVertex
      (letI := (isolatedAnabelioid diagram noVertex).coverCategory
       firstMap ≫ secondMap)).edgeMap edge =
      (isolatedFiniteEtaleCoverTransition diagram noVertex secondMap).edgeMap
        ((isolatedFiniteEtaleCoverTransition diagram noVertex firstMap).edgeMap
          edge) :=
  EtaleFundamentalGroup.fiberComponentHomMap_comp_apply
    (isolatedAnabelioid diagram noVertex) firstMap secondMap edge

end Isolated

end SourceSemiGraphOfAnabelioids

end Iut
