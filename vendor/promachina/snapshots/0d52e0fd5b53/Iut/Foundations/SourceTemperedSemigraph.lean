/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Topology.Algebra.Group.Basic
import Iut.Foundations.SourceSemiGraph
import Iut.Foundations.SourceSemiGraphAction
import Iut.Foundations.SourceProfiniteSemiGraphSystem

/-!
# Tempered semi-graph source mathematics

This module starts the source-faithful reconstruction of the semi-graph results
used by IUT I, Proposition 2.4 and Corollary 2.5.  It formalizes the finite-group
fixed-component, unique-geodesic, and subjoint results in *Semi-graphs of
Anabelioids*, Lemma 1.8(ii)(a-c), and the subgroup-conjugation argument that
derives the cuspidal portion of IUT I, Corollary 2.5 from Proposition 2.4(i).

For the first step of *Semi-graphs of Anabelioids*, Theorem 3.7(iii), it also
proves that the continuous image of a compact group in a discrete deck group
is finite, applies Lemma 1.8 to obtain a fixed component, and uses the
over-base branch map to upgrade it to a fixed original vertex.  It also proves
the Definition 2.4(iv) estranged-branch contradiction once the subgroup
containments supplied by Remark 2.2.1 are available.  That group-containment
passage, its stabilizer-to-verticial-subgroup identification, the
maximal-compact/verticial classification, and the inverse-limit passage in IUT
I, Proposition 2.4(i), are not asserted here.
-/

namespace Iut

universe u v w

namespace SourceFiniteTree

variable {Vertex : Type v} {graph : SimpleGraph Vertex}

/-- A finite tree with at least three vertices has a vertex that is not a
leaf. -/
theorem exists_degree_ne_one
    [Fintype Vertex] [DecidableRel graph.Adj]
    (tree : graph.IsTree)
    (three_le : 3 ≤ Fintype.card Vertex) :
    ∃ vertex, graph.degree vertex ≠ 1 := by
  by_contra h
  push Not at h
  have degreeSum := graph.sum_degrees_eq_twice_card_edges
  have edgeCount := tree.card_edgeFinset
  simp only [h, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] at degreeSum
  omega

/-- Removing every leaf from a finite tree with at least three vertices leaves
a nonempty connected induced subtree. -/
theorem induce_degree_ne_one_connected
    [Fintype Vertex] [DecidableRel graph.Adj]
    (tree : graph.IsTree)
    (three_le : 3 ≤ Fintype.card Vertex) :
    (graph.induce { vertex | graph.degree vertex ≠ 1 }).Connected := by
  let internal : Set Vertex :=
    { vertex | graph.degree vertex ≠ 1 }
  obtain ⟨root, root_internal⟩ :=
    exists_degree_ne_one tree three_le
  refine (SimpleGraph.connected_iff _).mpr ⟨?_, ⟨root, root_internal⟩⟩
  intro first second
  obtain ⟨path, path_isPath⟩ :=
    tree.connected.exists_isPath first.1 second.1
  have support_internal :
      ∀ vertex ∈ path.support, vertex ∈ internal := by
    intro vertex vertex_mem
    by_cases first_eq : vertex = first.1
    · rw [first_eq]
      exact first.2
    by_cases second_eq : vertex = second.1
    · rw [second_eq]
      exact second.2
    change graph.degree vertex ≠ 1
    intro degree_eq
    obtain ⟨neighbor, neighbor_adj, neighbor_unique⟩ :=
      SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp degree_eq
    have neighborSet_subsingleton :
        (graph.neighborSet vertex).Subsingleton := by
      intro left left_mem right right_mem
      exact
        (neighbor_unique left
            ((graph.mem_neighborSet vertex left).mp left_mem)).trans
          (neighbor_unique right
            ((graph.mem_neighborSet vertex right).mp right_mem)).symm
    exact
      (path_isPath.isTrail.not_mem_support_of_subsingleton_neighborSet
        first_eq second_eq neighborSet_subsingleton) vertex_mem
  exact
    ⟨(path.induce internal support_internal).copy
      (Subtype.ext rfl) (Subtype.ext rfl)⟩

end SourceFiniteTree

/-- An action on the vertices of a simple graph by graph automorphisms. -/
structure SourceGraphAction
    (Acting Vertex : Type*)
    [Group Acting]
    (graph : SimpleGraph Vertex) where
  action : Acting →* Equiv.Perm Vertex
  map_adj_iff :
    ∀ g first second,
      graph.Adj (action g first) (action g second) ↔
        graph.Adj first second

namespace SourceGraphAction

variable
  {Acting : Type u} {Vertex : Type v}
  [Group Acting]
  {graph : SimpleGraph Vertex}
  (data : SourceGraphAction Acting Vertex graph)

/-- The graph isomorphism induced by an acting element. -/
def graphIso (g : Acting) : graph ≃g graph where
  toEquiv := data.action g
  map_rel_iff' := by
    intro first second
    exact data.map_adj_iff g first second

@[simp]
theorem graphIso_apply (g : Acting) (vertex : Vertex) :
    graphIso data g vertex = data.action g vertex :=
  rfl

@[simp]
theorem graphIso_one_apply (vertex : Vertex) :
    graphIso data 1 vertex = vertex := by
  simp [graphIso]

@[simp]
theorem graphIso_mul_apply (first second : Acting) (vertex : Vertex) :
    graphIso data (first * second) vertex =
      graphIso data first (graphIso data second vertex) := by
  change data.action (first * second) vertex =
    data.action first (data.action second vertex)
  rw [map_mul]
  rfl

@[simp]
theorem graphIso_inv_apply_apply (g : Acting) (vertex : Vertex) :
    graphIso data g⁻¹ (graphIso data g vertex) = vertex := by
  change data.action g⁻¹ (data.action g vertex) = vertex
  rw [map_inv]
  exact (data.action g).symm_apply_apply vertex

@[simp]
theorem graphIso_apply_inv_apply (g : Acting) (vertex : Vertex) :
    graphIso data g (graphIso data g⁻¹ vertex) = vertex := by
  simpa only [inv_inv] using
    graphIso_inv_apply_apply data g⁻¹ vertex

/-- A graph automorphism cannot increase graph distance. -/
theorem dist_image_le (g : Acting) (first second : Vertex) :
    graph.dist (graphIso data g first) (graphIso data g second) ≤
      graph.dist first second := by
  by_cases hreachable : graph.Reachable first second
  · obtain ⟨path, hpath⟩ :=
      hreachable.exists_walk_length_eq_dist
    calc
      graph.dist (graphIso data g first) (graphIso data g second) ≤
          (path.map (graphIso data g).toHom).length :=
        graph.dist_le _
      _ = path.length := SimpleGraph.Walk.length_map _ _
      _ = graph.dist first second := hpath
  · have himage_not_reachable :
        ¬ graph.Reachable
            (graphIso data g first) (graphIso data g second) := by
      intro himage
      obtain ⟨imagePath⟩ := himage
      apply hreachable
      exact
        ⟨(imagePath.map (graphIso data g⁻¹).toHom).copy
          (graphIso_inv_apply_apply data g first)
          (graphIso_inv_apply_apply data g second)⟩
    rw [graph.dist_eq_zero_of_not_reachable hreachable]
    rw [graph.dist_eq_zero_of_not_reachable himage_not_reachable]

/-- Graph automorphisms preserve graph distance exactly. -/
theorem dist_image (g : Acting) (first second : Vertex) :
    graph.dist (graphIso data g first) (graphIso data g second) =
      graph.dist first second := by
  apply le_antisymm (dist_image_le data g first second)
  have inverseBound :=
    dist_image_le data g⁻¹
      (graphIso data g first) (graphIso data g second)
  simpa using inverseBound

/-- On a tree, graph automorphisms preserve extended distance exactly. -/
theorem edist_image
    (tree : graph.IsTree)
    (g : Acting) (first second : Vertex) :
    graph.edist (graphIso data g first) (graphIso data g second) =
      graph.edist first second := by
  rw [← (tree.connected
    (graphIso data g first) (graphIso data g second)).coe_dist_eq_edist]
  rw [← (tree.connected first second).coe_dist_eq_edist]
  exact_mod_cast dist_image data g first second

/-- Applying a graph automorphism cannot increase vertex eccentricity. -/
theorem eccent_image_le
    (tree : graph.IsTree)
    (g : Acting) (vertex : Vertex) :
    graph.eccent (graphIso data g vertex) ≤ graph.eccent vertex := by
  rw [graph.eccent_le_iff]
  intro target
  calc
    graph.edist (graphIso data g vertex) target =
        graph.edist (graphIso data g vertex)
          (graphIso data g (graphIso data g⁻¹ target)) := by
      rw [graphIso_apply_inv_apply]
    _ = graph.edist vertex (graphIso data g⁻¹ target) :=
      edist_image data tree g vertex (graphIso data g⁻¹ target)
    _ ≤ graph.eccent vertex := graph.edist_le_eccent

/-- Graph automorphisms preserve eccentricity exactly. -/
theorem eccent_image
    (tree : graph.IsTree)
    (g : Acting) (vertex : Vertex) :
    graph.eccent (graphIso data g vertex) = graph.eccent vertex := by
  apply le_antisymm (eccent_image_le data tree g vertex)
  have inverseBound :=
    eccent_image_le data tree g⁻¹ (graphIso data g vertex)
  simpa using inverseBound

/-- The center of a finite tree is invariant under every acting element. -/
theorem center_stable
    (tree : graph.IsTree)
    (g : Acting) (vertex : Vertex) :
    graphIso data g vertex ∈ graph.center ↔ vertex ∈ graph.center := by
  simp only [graph.mem_center_iff, eccent_image data tree g vertex]

/-- The fixed-point alternative for an action on a tree.  An edge is fixed
setwise, so its endpoints may be exchanged. -/
def FixesVertexOrEdge : Prop :=
  (∃ vertex, ∀ g : Acting,
      graphIso data g vertex = vertex) ∨
    ∃ first second,
      graph.Adj first second ∧
        ∀ g : Acting,
          (graphIso data g first = first ∧
              graphIso data g second = second) ∨
            (graphIso data g first = second ∧
              graphIso data g second = first)

/-- Restriction of a graph automorphism to a stable induced subgraph. -/
def inducedGraphIso
    (vertices : Set Vertex)
    (stable : ∀ g vertex,
      graphIso data g vertex ∈ vertices ↔ vertex ∈ vertices)
    (g : Acting) :
    graph.induce vertices ≃g graph.induce vertices where
  toEquiv :=
    { toFun := fun vertex =>
        ⟨graphIso data g vertex.1,
          (stable g vertex.1).mpr vertex.2⟩
      invFun := fun vertex =>
        ⟨graphIso data g⁻¹ vertex.1,
          (stable g⁻¹ vertex.1).mpr vertex.2⟩
      left_inv := fun vertex => by
        apply Subtype.ext
        exact graphIso_inv_apply_apply data g vertex.1
      right_inv := fun vertex => by
        apply Subtype.ext
        exact graphIso_apply_inv_apply data g vertex.1 }
  map_rel_iff' := by
    intro first second
    exact data.map_adj_iff g first.1 second.1

@[simp]
theorem inducedGraphIso_apply
    (vertices : Set Vertex)
    (stable : ∀ g vertex,
      graphIso data g vertex ∈ vertices ↔ vertex ∈ vertices)
    (g : Acting) (vertex : vertices) :
    (inducedGraphIso data vertices stable g vertex).1 =
      graphIso data g vertex.1 :=
  rfl

/-- Restriction of a graph action to a stable induced subgraph. -/
def restrict
    (vertices : Set Vertex)
    (stable : ∀ g vertex,
      graphIso data g vertex ∈ vertices ↔ vertex ∈ vertices) :
    SourceGraphAction Acting vertices (graph.induce vertices) where
  action :=
    { toFun := fun g => (inducedGraphIso data vertices stable g).toEquiv
      map_one' := by
        ext vertex
        change graphIso data 1 vertex.1 = vertex.1
        exact graphIso_one_apply data vertex.1
      map_mul' := by
        intro first second
        ext vertex
        change graphIso data (first * second) vertex.1 =
          graphIso data first (graphIso data second vertex.1)
        exact graphIso_mul_apply data first second vertex.1 }
  map_adj_iff := by
    intro g first second
    exact data.map_adj_iff g first.1 second.1

/-- A finite, nonempty, connected induced subtree that is stable under the
action. -/
def IsFiniteInvariantSubtree
    (vertices : Finset Vertex) : Prop :=
  vertices.Nonempty ∧
    (graph.induce (vertices : Set Vertex)).Connected ∧
      ∀ g vertex,
        graphIso data g vertex ∈ vertices ↔ vertex ∈ vertices

/-- A finite group acting on a finite tree has a nonempty invariant connected
subtree with at most two vertices.  The proof chooses a minimal invariant
subtree and removes all of its leaves if it has at least three vertices. -/
theorem exists_invariant_subtree_card_le_two
    [Finite Acting] [Finite Vertex]
    (tree : graph.IsTree) :
    ∃ vertices : Finset Vertex,
      IsFiniteInvariantSubtree data vertices ∧ vertices.card ≤ 2 := by
  classical
  letI : Fintype Acting := Fintype.ofFinite Acting
  letI : Fintype Vertex := Fintype.ofFinite Vertex
  letI : Nonempty Vertex := tree.connected.nonempty
  let candidate : Set (Finset Vertex) :=
    { vertices | IsFiniteInvariantSubtree data vertices }
  have univ_candidate : (Finset.univ : Finset Vertex) ∈ candidate := by
    refine ⟨Finset.univ_nonempty, ?_, ?_⟩
    · rw [show (↑(Finset.univ : Finset Vertex) : Set Vertex) =
          Set.univ by ext; simp]
      exact (SimpleGraph.induceUnivIso graph).connected_iff.mpr
        tree.connected
    · intro g vertex
      simp
  obtain ⟨vertices, minimal⟩ :=
    candidate.toFinite.exists_minimalFor Finset.card candidate
      ⟨Finset.univ, univ_candidate⟩
  refine ⟨vertices, minimal.1, ?_⟩
  by_contra card_not_le
  have three_le : 3 ≤ vertices.card := by omega
  rcases minimal.1 with
    ⟨vertices_nonempty, vertices_connected, vertices_stable⟩
  let subtree : SimpleGraph vertices :=
    graph.induce (vertices : Set Vertex)
  have subtree_tree : subtree.IsTree :=
    ⟨vertices_connected,
      tree.isAcyclic.induce (vertices : Set Vertex)⟩
  have subtree_three_le : 3 ≤ Fintype.card vertices := by
    simpa using three_le
  let nonleaves : Finset vertices :=
    Finset.univ.filter fun vertex => subtree.degree vertex ≠ 1
  have nonleaves_nonempty : nonleaves.Nonempty := by
    obtain ⟨vertex, vertex_nonleaf⟩ :=
      SourceFiniteTree.exists_degree_ne_one subtree_tree subtree_three_le
    exact ⟨vertex, by simp [nonleaves, vertex_nonleaf]⟩
  let inclusion : vertices ↪ Vertex :=
    Function.Embedding.subtype (· ∈ (vertices : Set Vertex))
  let pruned : Finset Vertex := nonleaves.map inclusion
  have pruned_nonempty : pruned.Nonempty := by
    simpa [pruned] using nonleaves_nonempty.map (f := inclusion)
  have mem_pruned_iff (vertex : Vertex) :
      vertex ∈ pruned ↔
        ∃ vertex_mem : vertex ∈ vertices,
          subtree.degree ⟨vertex, vertex_mem⟩ ≠ 1 := by
    simp only [pruned, nonleaves, Finset.mem_map,
      Finset.mem_filter, Finset.mem_univ, true_and, inclusion]
    constructor
    · rintro ⟨source, source_nonleaf, rfl⟩
      exact ⟨source.2, source_nonleaf⟩
    · rintro ⟨vertex_mem, vertex_nonleaf⟩
      exact ⟨⟨vertex, vertex_mem⟩, vertex_nonleaf, rfl⟩
  have pruned_connected :
      (graph.induce (pruned : Set Vertex)).Connected := by
    have internal_connected :=
      SourceFiniteTree.induce_degree_ne_one_connected
        subtree_tree subtree_three_le
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    obtain ⟨root⟩ := internal_connected.nonempty
    let root' : pruned :=
      ⟨root.1.1,
        (mem_pruned_iff root.1.1).mpr ⟨root.1.2, root.2⟩⟩
    refine ⟨root', ?_⟩
    intro target
    obtain ⟨target_mem, target_nonleaf⟩ :=
      (mem_pruned_iff target.1).mp target.2
    let target' : { vertex : vertices // subtree.degree vertex ≠ 1 } :=
      ⟨⟨target.1, target_mem⟩, target_nonleaf⟩
    let prunedHom :
        subtree.induce { vertex | subtree.degree vertex ≠ 1 } →g
          graph.induce (pruned : Set Vertex) :=
      { toFun := fun vertex =>
          ⟨vertex.1.1,
            (mem_pruned_iff vertex.1.1).mpr
              ⟨vertex.1.2, vertex.2⟩⟩
        map_rel' := by
          intro first second adjacent
          exact adjacent }
    obtain ⟨path⟩ := internal_connected root target'
    exact
      ⟨(path.map prunedHom).copy
        (Subtype.ext rfl) (Subtype.ext rfl)⟩
  have pruned_forward
      (g : Acting) (vertex : Vertex)
      (vertex_mem : vertex ∈ pruned) :
      graphIso data g vertex ∈ pruned := by
    obtain ⟨vertex_mem_tree, vertex_nonleaf⟩ :=
      (mem_pruned_iff vertex).mp vertex_mem
    let source : vertices := ⟨vertex, vertex_mem_tree⟩
    let target : vertices :=
      ⟨graphIso data g vertex,
        (vertices_stable g vertex).mpr vertex_mem_tree⟩
    have degree_eq :=
      (inducedGraphIso data (vertices : Set Vertex)
        vertices_stable g).degree_eq source
    apply (mem_pruned_iff (graphIso data g vertex)).mpr
    refine ⟨target.2, ?_⟩
    change subtree.degree target ≠ 1
    have target_eq :
        target = inducedGraphIso data (vertices : Set Vertex)
          vertices_stable g source := by
      apply Subtype.ext
      rfl
    rw [target_eq, degree_eq]
    exact vertex_nonleaf
  have pruned_stable :
      ∀ g vertex,
        graphIso data g vertex ∈ pruned ↔ vertex ∈ pruned := by
    intro g vertex
    constructor
    · intro image_mem
      have inverse_mem :=
        pruned_forward g⁻¹ (graphIso data g vertex) image_mem
      simpa using inverse_mem
    · exact pruned_forward g vertex
  have pruned_candidate : pruned ∈ candidate :=
    ⟨pruned_nonempty, pruned_connected, pruned_stable⟩
  letI : Nontrivial vertices :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have exists_leaf :=
    subtree_tree.exists_vert_degree_one_of_nontrivial
  obtain ⟨leaf, leaf_degree⟩ := exists_leaf
  have nonleaves_ssubset :
      nonleaves ⊂ (Finset.univ : Finset vertices) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
    intro nonleaves_eq
    have : leaf ∈ nonleaves := by rw [nonleaves_eq]; simp
    simp [nonleaves, leaf_degree] at this
  have pruned_card_lt : pruned.card < vertices.card := by
    calc
      pruned.card = nonleaves.card :=
        by
          simp [pruned]
      _ < (Finset.univ : Finset vertices).card :=
        Finset.card_lt_card nonleaves_ssubset
      _ = vertices.card := Fintype.card_coe vertices
  exact (minimal.not_lt pruned_candidate) pruned_card_lt

/-- Finite-vertex form of *Semi-graphs of Anabelioids*, Lemma 1.8(ii)(a):
a finite group action on a finite tree fixes a vertex or fixes an edge setwise. -/
theorem finite_fixesVertexOrEdge
    [Finite Acting] [Finite Vertex]
    (tree : graph.IsTree) :
    FixesVertexOrEdge data := by
  classical
  letI : Fintype Acting := Fintype.ofFinite Acting
  letI : Fintype Vertex := Fintype.ofFinite Vertex
  obtain ⟨vertices, invariant, card_le_two⟩ :=
    exists_invariant_subtree_card_le_two data tree
  rcases invariant with
    ⟨vertices_nonempty, vertices_connected, vertices_stable⟩
  have card_pos : 0 < vertices.card := Finset.card_pos.mpr vertices_nonempty
  have card_one_or_two : vertices.card = 1 ∨ vertices.card = 2 := by
    omega
  rcases card_one_or_two with card_one | card_two
  · obtain ⟨vertex, vertices_eq⟩ := Finset.card_eq_one.mp card_one
    left
    refine ⟨vertex, ?_⟩
    intro g
    have image_mem : graphIso data g vertex ∈ vertices :=
      (vertices_stable g vertex).mpr (by simp [vertices_eq])
    simpa [vertices_eq] using image_mem
  · obtain ⟨first, second, first_ne_second, vertices_eq⟩ :=
      Finset.card_eq_two.mp card_two
    have first_mem : first ∈ vertices := by simp [vertices_eq]
    have second_mem : second ∈ vertices := by simp [vertices_eq]
    let firstVertex : vertices := ⟨first, first_mem⟩
    let secondVertex : vertices := ⟨second, second_mem⟩
    have firstVertex_ne_secondVertex : firstVertex ≠ secondVertex := by
      intro equality
      exact first_ne_second (congrArg Subtype.val equality)
    have first_support :
        firstVertex ∈
          (graph.induce (vertices : Set Vertex)).support :=
      SimpleGraph.mem_support_of_reachable
        firstVertex_ne_secondVertex
        (vertices_connected firstVertex secondVertex)
    obtain ⟨neighbor, first_adj_neighbor⟩ :=
      (SimpleGraph.mem_support
        (graph.induce (vertices : Set Vertex))).mp first_support
    have neighbor_cases : neighbor.1 = first ∨ neighbor.1 = second := by
      have neighbor_mem_pair :
          neighbor.1 ∈ ({first, second} : Finset Vertex) := by
        rw [← vertices_eq]
        exact neighbor.2
      simpa using neighbor_mem_pair
    have first_adj_second : graph.Adj first second := by
      rcases neighbor_cases with neighbor_eq | neighbor_eq
      · exfalso
        apply first_adj_neighbor.ne
        apply Subtype.ext
        exact neighbor_eq.symm
      · simpa [firstVertex, neighbor_eq] using first_adj_neighbor
    right
    refine ⟨first, second, first_adj_second, ?_⟩
    intro g
    have first_image_mem : graphIso data g first ∈ vertices :=
      (vertices_stable g first).mpr first_mem
    have second_image_mem : graphIso data g second ∈ vertices :=
      (vertices_stable g second).mpr second_mem
    have first_image_cases :
        graphIso data g first = first ∨
          graphIso data g first = second := by
      rw [vertices_eq] at first_image_mem
      simpa using first_image_mem
    have second_image_cases :
        graphIso data g second = first ∨
          graphIso data g second = second := by
      rw [vertices_eq] at second_image_mem
      simpa using second_image_mem
    rcases first_image_cases with first_fixed | first_swapped
    · rcases second_image_cases with second_collapsed | second_fixed
      · exact False.elim <| first_ne_second <|
          (graphIso data g).injective
            (first_fixed.trans second_collapsed.symm)
      · exact Or.inl ⟨first_fixed, second_fixed⟩
    · rcases second_image_cases with second_swapped | second_collapsed
      · exact Or.inr ⟨first_swapped, second_swapped⟩
      · exact False.elim <| first_ne_second <|
          (graphIso data g).injective
            (first_swapped.trans second_collapsed.symm)

/-- *Semi-graphs of Anabelioids*, Lemma 1.8(ii)(a), for the closed-edge
simple-graph model: a finite group acting on an arbitrary tree fixes a vertex
or fixes an edge setwise.  The finite subtree needed by the center-pruning
argument is constructed from a connected hull of one finite orbit. -/
theorem fixesVertexOrEdge
    [Finite Acting]
    (tree : graph.IsTree) :
    FixesVertexOrEdge data := by
  classical
  letI : Fintype Acting := Fintype.ofFinite Acting
  letI : Nonempty Vertex := tree.connected.nonempty
  let root : Vertex := Classical.choice inferInstance
  let orbit : Finset Vertex :=
    Finset.univ.image fun g : Acting => graphIso data g root
  have orbit_mem (g : Acting) : graphIso data g root ∈ orbit := by
    exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩
  have orbit_nonempty : orbit.Nonempty :=
    ⟨root, by simpa [orbit] using orbit_mem (1 : Acting)⟩
  obtain ⟨seed, orbit_subset_seed, seed_connected⟩ :=
    SimpleGraph.extend_finset_to_connected
      tree.connected.preconnected orbit_nonempty
  let hull : Finset Vertex :=
    Finset.univ.biUnion fun g : Acting =>
      seed.image fun vertex => graphIso data g vertex
  have mem_hull_iff (vertex : Vertex) :
      vertex ∈ hull ↔
        ∃ g : Acting, ∃ source ∈ seed,
          graphIso data g source = vertex := by
    simp [hull]
  have root_mem_seed : root ∈ seed :=
    orbit_subset_seed (by simpa using orbit_mem (1 : Acting))
  have root_mem_hull : root ∈ hull := by
    apply (mem_hull_iff root).mpr
    exact ⟨1, root, root_mem_seed,
      graphIso_one_apply data root⟩
  have hull_forward
      (g : Acting) (vertex : Vertex)
      (vertex_mem : vertex ∈ hull) :
      graphIso data g vertex ∈ hull := by
    obtain ⟨h, source, source_mem, rfl⟩ :=
      (mem_hull_iff vertex).mp vertex_mem
    apply (mem_hull_iff _).mpr
    exact ⟨g * h, source, source_mem,
      graphIso_mul_apply data g h source⟩
  have hull_stable :
      ∀ g vertex,
        graphIso data g vertex ∈ hull ↔ vertex ∈ hull := by
    intro g vertex
    constructor
    · intro image_mem
      have inverse_mem :=
        hull_forward g⁻¹ (graphIso data g vertex) image_mem
      simpa using inverse_mem
    · exact hull_forward g vertex
  have hull_connected :
      (graph.induce (hull : Set Vertex)).Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    let rootVertex : hull := ⟨root, root_mem_hull⟩
    refine ⟨rootVertex, ?_⟩
    intro target
    obtain ⟨g, source, source_mem, source_eq⟩ :=
      (mem_hull_iff target.1).mp target.2
    let seedRoot : seed :=
      ⟨graphIso data g⁻¹ root,
        orbit_subset_seed (orbit_mem g⁻¹)⟩
    let seedTarget : seed := ⟨source, source_mem⟩
    obtain ⟨path⟩ := seed_connected seedRoot seedTarget
    let mapToHull :
        graph.induce (seed : Set Vertex) →g
          graph.induce (hull : Set Vertex) :=
      { toFun := fun vertex =>
          ⟨graphIso data g vertex.1,
            (mem_hull_iff _).mpr ⟨g, vertex.1, vertex.2, rfl⟩⟩
        map_rel' := by
          intro first second adjacent
          exact (data.map_adj_iff g first.1 second.1).mpr adjacent }
    refine ⟨(path.map mapToHull).copy ?_ ?_⟩
    · apply Subtype.ext
      exact graphIso_apply_inv_apply data g root
    · apply Subtype.ext
      exact source_eq
  let restricted := restrict data (hull : Set Vertex) hull_stable
  have hull_tree :
      (graph.induce (hull : Set Vertex)).IsTree :=
    ⟨hull_connected, tree.isAcyclic.induce (hull : Set Vertex)⟩
  have fixed := finite_fixesVertexOrEdge restricted hull_tree
  rcases fixed with ⟨vertex, vertex_fixed⟩ |
      ⟨first, second, adjacent, edge_fixed⟩
  · left
    refine ⟨vertex.1, ?_⟩
    intro g
    have fixed_subtype := congrArg Subtype.val (vertex_fixed g)
    exact fixed_subtype
  · right
    refine ⟨first.1, second.1, adjacent, ?_⟩
    intro g
    rcases edge_fixed g with fixed_pointwise | swapped
    · left
      exact ⟨congrArg Subtype.val fixed_pointwise.1,
        congrArg Subtype.val fixed_pointwise.2⟩
    · right
      exact ⟨congrArg Subtype.val swapped.1,
        congrArg Subtype.val swapped.2⟩

private theorem list_map_eq_self_fixed
    {α : Type*} {f : α → α} {values : List α}
    (hmap : values.map f = values) :
    ∀ value ∈ values, f value = value := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      have hhead : f head = head := by
        simpa using congrArg List.head? hmap
      have htail : tail.map f = tail := by
        simpa using congrArg List.tail hmap
      intro value hvalue
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact hhead
      · exact ih htail value hvalue

/-- If an automorphism fixes the endpoints of a path in a tree, it fixes every
vertex of that path.  This is the unique-geodesic argument of *Semi-graphs of
Anabelioids*, Lemma 1.8(ii)(b). -/
theorem fixes_path_pointwise
    (tree : graph.IsTree)
    (g : Acting)
    {first second : Vertex}
    (first_fixed : graphIso data g first = first)
    (second_fixed : graphIso data g second = second)
    (path : graph.Walk first second)
    (path_isPath : path.IsPath) :
    ∀ vertex ∈ path.support,
      graphIso data g vertex = vertex := by
  let mapped : graph.Walk first second :=
    (path.map (graphIso data g).toHom).copy
      first_fixed second_fixed
  have mapped_isPath : mapped.IsPath := by
    dsimp [mapped]
    rw [SimpleGraph.Walk.isPath_copy]
    exact SimpleGraph.Walk.map_isPath_of_injective
      (graphIso data g).injective path_isPath
  have mapped_eq : mapped = path :=
    (tree.existsUnique_path first second).unique
      mapped_isPath path_isPath
  have support_eq :
      path.support.map (graphIso data g).toHom = path.support := by
    calc
      path.support.map (graphIso data g).toHom =
          (path.map (graphIso data g).toHom).support := by
        rw [SimpleGraph.Walk.support_map]
      _ = mapped.support := by
        simp [mapped]
      _ = path.support := congrArg SimpleGraph.Walk.support mapped_eq
  exact list_map_eq_self_fixed support_eq

/-- The action of a subgroup fixes the unique geodesic pointwise whenever it
fixes both endpoints. -/
theorem subgroup_fixes_geodesic_pointwise
    (tree : graph.IsTree)
    (subgroup : Subgroup Acting)
    {first second : Vertex}
    (first_fixed :
      ∀ g : subgroup, graphIso data g.1 first = first)
    (second_fixed :
      ∀ g : subgroup, graphIso data g.1 second = second) :
    ∃ path : graph.Walk first second,
      path.IsPath ∧
        ∀ g : subgroup, ∀ vertex ∈ path.support,
          graphIso data g.1 vertex = vertex := by
  obtain ⟨path, path_isPath, _⟩ :=
    tree.connected.exists_path_of_dist first second
  exact
    ⟨path, path_isPath, fun g =>
      fixes_path_pointwise data tree g.1
        (first_fixed g) (second_fixed g) path path_isPath⟩

end SourceGraphAction

/-- A semi-graph tree represented exactly by the compactification construction
in *Semi-graphs of Anabelioids*, Section 1.  `vertexSet` consists of the
original vertices; the remaining vertices are the points appended at
non-verticial branches.  Such boundary vertices have degree one. -/
structure SourceSemiGraphTree (Point : Type v) where
  compactification : SimpleGraph Point
  vertexSet : Set Point
  boundary_unique_neighbor :
    ∀ point, point ∉ vertexSet →
      ∃! neighbor, compactification.Adj point neighbor
  compactification_isTree : compactification.IsTree

namespace SourceSemiGraphTree

variable {Point : Type v} (semiGraph : SourceSemiGraphTree Point)

/-- An edge of the compactification is open in the original semi-graph exactly
when at least one endpoint was appended during compactification. -/
def IsOpenEdge (first second : Point) : Prop :=
  semiGraph.compactification.Adj first second ∧
    (first ∉ semiGraph.vertexSet ∨ second ∉ semiGraph.vertexSet)

/-- Every compactification edge has an original vertex as an endpoint once the
semi-graph has a vertex.  If both endpoints were appended boundary points,
their unique-neighbor properties would make them an isolated two-vertex
component, contradicting connectedness. -/
theorem edge_abuts_vertex
    (vertex_nonempty : semiGraph.vertexSet.Nonempty)
    {first second : Point}
    (adjacent : semiGraph.compactification.Adj first second) :
    first ∈ semiGraph.vertexSet ∨ second ∈ semiGraph.vertexSet := by
  by_contra neither_vertex
  rw [not_or] at neither_vertex
  obtain ⟨_, _, first_unique⟩ :=
    semiGraph.boundary_unique_neighbor first neither_vertex.1
  obtain ⟨_, _, second_unique⟩ :=
    semiGraph.boundary_unique_neighbor second neither_vertex.2
  have first_neighbor_unique :
      ∀ point, semiGraph.compactification.Adj first point → point = second := by
    intro point point_adjacent
    exact (first_unique point point_adjacent).trans
      (first_unique second adjacent).symm
  have second_neighbor_unique :
      ∀ point, semiGraph.compactification.Adj second point → point = first := by
    intro point point_adjacent
    exact (second_unique point point_adjacent).trans
      (second_unique first adjacent.symm).symm
  have walk_endpoint :
      ∀ {start target : Point},
        semiGraph.compactification.Walk start target →
          (start = first ∨ start = second) →
            target = first ∨ target = second := by
    intro start target walk
    induction walk with
    | nil =>
        exact fun start_endpoint => start_endpoint
    | @cons start next target head tail ih =>
        intro start_endpoint
        apply ih
        rcases start_endpoint with rfl | rfl
        · exact Or.inr (first_neighbor_unique next head)
        · exact Or.inl (second_neighbor_unique next head)
  obtain ⟨vertex, vertex_mem⟩ := vertex_nonempty
  obtain ⟨path, _path_isPath⟩ :=
    semiGraph.compactification_isTree.connected.exists_isPath first vertex
  rcases walk_endpoint path (Or.inl rfl) with vertex_eq | vertex_eq
  · exact neither_vertex.1 (vertex_eq ▸ vertex_mem)
  · exact neither_vertex.2 (vertex_eq ▸ vertex_mem)

/-- A group action on a semi-graph tree, expressed on its compactification and
required to preserve the subset of original vertices. -/
structure Action (Acting : Type u) [Group Acting] where
  toGraphAction :
    SourceGraphAction Acting Point semiGraph.compactification
  vertexSet_stable :
    ∀ g point,
      SourceGraphAction.graphIso toGraphAction g point ∈
          semiGraph.vertexSet ↔
        point ∈ semiGraph.vertexSet

namespace Action

variable
  {Acting : Type u} [Group Acting]
  (data : semiGraph.Action Acting)

/-- An action over the base semi-graph.  The projection is recorded on
oriented branches of compactification edges: this retains the distinction
between the two branches even when both abut the same base vertex. -/
structure OverBase (BaseBranch : Type*) where
  branchProjection :
    ∀ first second,
      semiGraph.compactification.Adj first second → BaseBranch
  branchProjection_action :
    ∀ g first second
      (adjacent : semiGraph.compactification.Adj first second),
      branchProjection
          (SourceGraphAction.graphIso data.toGraphAction g first)
          (SourceGraphAction.graphIso data.toGraphAction g second)
          ((data.toGraphAction.map_adj_iff g first second).mpr adjacent) =
        branchProjection first second adjacent
  opposite_branches_ne :
    ∀ first second
      (adjacent : semiGraph.compactification.Adj first second),
      branchProjection first second adjacent ≠
        branchProjection second first adjacent.symm

namespace OverBase

variable {BaseBranch : Type*}

/-- A deck transformation over the base cannot exchange the two oriented
branches of an edge. -/
theorem not_swap_edge
    (overBase : data.OverBase semiGraph BaseBranch)
    (g : Acting) {first second : Point}
    (adjacent : semiGraph.compactification.Adj first second) :
    ¬(SourceGraphAction.graphIso data.toGraphAction g first = second ∧
        SourceGraphAction.graphIso data.toGraphAction g second = first) := by
  intro swapped
  apply OverBase.opposite_branches_ne (data := data) overBase
    first second adjacent
  simpa only [swapped.1, swapped.2] using
    (OverBase.branchProjection_action (data := data) overBase
      g first second adjacent).symm

end OverBase

/-- Restrict the acting group to a subgroup without changing its action on the
semi-graph compactification. -/
def restrictActing (subgroup : Subgroup Acting) :
    semiGraph.Action subgroup where
  toGraphAction :=
    { action := data.toGraphAction.action.comp subgroup.subtype
      map_adj_iff := fun g first second =>
        data.toGraphAction.map_adj_iff g.1 first second }
  vertexSet_stable := fun g point => data.vertexSet_stable g.1 point

@[simp]
theorem restrictActing_graphIso_apply
    (subgroup : Subgroup Acting)
    (g : subgroup) (point : Point) :
    SourceGraphAction.graphIso
        (data.restrictActing semiGraph subgroup).toGraphAction g point =
      SourceGraphAction.graphIso data.toGraphAction g.1 point :=
  rfl

/-- The fixed-component conclusion in the source semi-graph, distinguishing
genuine vertices from the boundary vertices of its compactification. -/
def FixesVertexOrEdge : Prop :=
  (∃ vertex ∈ semiGraph.vertexSet,
      ∀ g : Acting,
        SourceGraphAction.graphIso data.toGraphAction g vertex = vertex) ∨
    ∃ first second,
      semiGraph.compactification.Adj first second ∧
        ∀ g : Acting,
          (SourceGraphAction.graphIso data.toGraphAction g first = first ∧
              SourceGraphAction.graphIso data.toGraphAction g second = second) ∨
            (SourceGraphAction.graphIso data.toGraphAction g first = second ∧
              SourceGraphAction.graphIso data.toGraphAction g second = first)

/-- The set of original vertices fixed by the entire acting group. -/
def fixedVertexSet : Set Point :=
  {point | point ∈ semiGraph.vertexSet ∧
    ∀ g : Acting,
      SourceGraphAction.graphIso data.toGraphAction g point = point}

/-- An original vertex fixed by the entire acting group. -/
def FixedVertex :=
  {point : Point // point ∈ fixedVertexSet semiGraph data}

/-- If the fixed original vertex set consists of two distinct vertices, those
vertices are joined by a single closed edge.  Otherwise the internal vertex of
their unique geodesic would be a third fixed original vertex.  This is the
application of Lemma 1.8(ii)(b) in Theorem 3.7(iii). -/
theorem adjacent_of_fixedVertexSet_eq_pair
    {first second : Point}
    (first_ne_second : first ≠ second)
    (fixed_vertices :
      fixedVertexSet semiGraph data = {first, second}) :
    semiGraph.compactification.Adj first second := by
  have first_mem : first ∈ fixedVertexSet semiGraph data := by
    rw [fixed_vertices]
    simp
  have second_mem : second ∈ fixedVertexSet semiGraph data := by
    rw [fixed_vertices]
    simp
  obtain ⟨path, path_isPath⟩ :=
    semiGraph.compactification_isTree.connected.exists_isPath first second
  by_contra not_adjacent
  have path_length_pos : 0 < path.length := by
    by_contra not_positive
    have path_length_zero : path.length = 0 := by omega
    exact first_ne_second
      (SimpleGraph.Walk.eq_of_length_eq_zero path_length_zero)
  have path_length_ne_one : path.length ≠ 1 := by
    intro path_length_one
    exact not_adjacent
      (SimpleGraph.Walk.adj_of_length_eq_one path_length_one)
  have two_le_path_length : 2 ≤ path.length := by omega
  let left := path.getVert 0
  let center := path.getVert 1
  let right := path.getVert 2
  have left_adj_center :
      semiGraph.compactification.Adj left center := by
    exact path.adj_getVert_succ (by omega : 0 < path.length)
  have center_adj_right :
      semiGraph.compactification.Adj center right := by
    simpa [center, right] using
      path.adj_getVert_succ (i := 1) (by omega : 1 < path.length)
  have left_ne_right : left ≠ right := by
    intro equality
    have support_nodup := path_isPath.support_nodup
    have zero_bound : 0 < path.support.length := by
      rw [path.length_support]
      omega
    have two_bound : 2 < path.support.length := by
      rw [path.length_support]
      omega
    have support_eq : path.support[0] = path.support[2] := by
      rw [path.support_getElem_eq_getVert zero_bound]
      rw [path.support_getElem_eq_getVert two_bound]
      exact equality
    have index_eq : (0 : Nat) = 2 :=
      (List.Nodup.getElem_inj_iff support_nodup).mp support_eq
    omega
  have center_vertex : center ∈ semiGraph.vertexSet := by
    by_contra center_not_vertex
    obtain ⟨neighbor, _, neighbor_unique⟩ :=
      semiGraph.boundary_unique_neighbor center center_not_vertex
    have left_eq : left = neighbor :=
      neighbor_unique left left_adj_center.symm
    have right_eq : right = neighbor :=
      neighbor_unique right center_adj_right
    exact left_ne_right (left_eq.trans right_eq.symm)
  have center_fixed :
      ∀ g : Acting,
        SourceGraphAction.graphIso data.toGraphAction g center = center := by
    intro g
    exact SourceGraphAction.fixes_path_pointwise data.toGraphAction
      semiGraph.compactification_isTree g (first_mem.2 g) (second_mem.2 g)
      path path_isPath center (path.getVert_mem_support 1)
  have center_mem : center ∈ fixedVertexSet semiGraph data :=
    ⟨center_vertex, center_fixed⟩
  rw [fixed_vertices] at center_mem
  have first_adj_center :
      semiGraph.compactification.Adj first center := by
    simpa [left] using left_adj_center
  rcases center_mem with center_eq_first | center_eq_second
  · exact first_adj_center.ne center_eq_first.symm
  · exact not_adjacent (center_eq_second ▸ first_adj_center)

/-- The fixed-component alternative upgrades to a fixed original vertex for
an action over the base on a connected semi-graph with a vertex.  This is the
second step of the proof of Theorem 3.7(iii). -/
theorem OverBase.fixedVertex_of_fixesVertexOrEdge
    {BaseBranch : Type*}
    (overBase : data.OverBase semiGraph BaseBranch)
    (vertex_nonempty : semiGraph.vertexSet.Nonempty)
    (fixedComponent : FixesVertexOrEdge semiGraph data) :
    ∃ vertex ∈ semiGraph.vertexSet,
      ∀ g : Acting,
        SourceGraphAction.graphIso data.toGraphAction g vertex = vertex := by
  rcases fixedComponent with fixedVertex |
      ⟨first, second, adjacent, edge_fixed⟩
  · exact fixedVertex
  rcases semiGraph.edge_abuts_vertex vertex_nonempty adjacent with
      first_vertex | second_vertex
  · refine ⟨first, first_vertex, ?_⟩
    intro g
    rcases edge_fixed g with fixed | swapped
    · exact fixed.1
    · exact
        (OverBase.not_swap_edge semiGraph data overBase g adjacent swapped).elim
  · refine ⟨second, second_vertex, ?_⟩
    intro g
    rcases edge_fixed g with fixed | swapped
    · exact fixed.2
    · exact
        (OverBase.not_swap_edge semiGraph data overBase g adjacent swapped).elim

/-- A fixed boundary point determines a fixed open edge: its unique neighbor
is fixed because graph automorphisms preserve adjacency. -/
theorem fixedOpenEdge_of_fixed_boundary
    {boundary : Point}
    (boundary_not_vertex : boundary ∉ semiGraph.vertexSet)
    (boundary_fixed :
      ∀ g : Acting,
        SourceGraphAction.graphIso data.toGraphAction g boundary = boundary) :
    ∃ neighbor,
      semiGraph.IsOpenEdge boundary neighbor ∧
        ∀ g : Acting,
          SourceGraphAction.graphIso data.toGraphAction g boundary = boundary ∧
            SourceGraphAction.graphIso data.toGraphAction g neighbor = neighbor := by
  obtain ⟨neighbor, boundary_adjacent, neighbor_unique⟩ :=
    semiGraph.boundary_unique_neighbor boundary boundary_not_vertex
  refine ⟨neighbor, ⟨boundary_adjacent, Or.inl boundary_not_vertex⟩, ?_⟩
  intro g
  refine ⟨boundary_fixed g, ?_⟩
  apply neighbor_unique
  have image_adjacent :=
    (data.toGraphAction.map_adj_iff g boundary neighbor).mpr
      boundary_adjacent
  change semiGraph.compactification.Adj
    (SourceGraphAction.graphIso data.toGraphAction g boundary)
    (SourceGraphAction.graphIso data.toGraphAction g neighbor) at image_adjacent
  rw [boundary_fixed g] at image_adjacent
  exact image_adjacent

/-- Full fixed-component alternative of *Semi-graphs of Anabelioids*,
Lemma 1.8(ii)(a), in the marked-compactification encoding of a semi-graph tree.
A fixed appended vertex is converted back into its fixed open edge. -/
theorem fixesVertexOrEdge
    [Finite Acting] :
    FixesVertexOrEdge semiGraph data := by
  rcases SourceGraphAction.fixesVertexOrEdge data.toGraphAction
      semiGraph.compactification_isTree with
    ⟨point, point_fixed⟩ |
      ⟨first, second, adjacent, edge_fixed⟩
  · by_cases point_is_vertex : point ∈ semiGraph.vertexSet
    · exact Or.inl ⟨point, point_is_vertex, point_fixed⟩
    · right
      obtain ⟨neighbor, openEdge, edge_fixed⟩ :=
        fixedOpenEdge_of_fixed_boundary semiGraph data
          point_is_vertex point_fixed
      exact ⟨point, neighbor, openEdge.1, fun g =>
        Or.inl (edge_fixed g)⟩
  · exact Or.inr ⟨first, second, adjacent, edge_fixed⟩

/-- A fixed subjoint is an original center vertex and two distinct incident
branches fixed pointwise by the acting group.  Passing to the corresponding
sub-semi-graph truncates the two selected compactification edges at their
other endpoints, so they become the two open edges of the joint. -/
@[ext]
structure FixedSubjoint where
  center : Point
  center_vertex : center ∈ semiGraph.vertexSet
  first : Point
  second : Point
  first_ne_second : first ≠ second
  center_adj_first : semiGraph.compactification.Adj center first
  center_adj_second : semiGraph.compactification.Adj center second
  fixed_pointwise :
    ∀ g : Acting,
      SourceGraphAction.graphIso data.toGraphAction g center = center ∧
        SourceGraphAction.graphIso data.toGraphAction g first = first ∧
        SourceGraphAction.graphIso data.toGraphAction g second = second

/-- The acting group fixes some subjoint. -/
def FixesSubjoint : Prop :=
  Nonempty (FixedSubjoint semiGraph data)

noncomputable instance [Finite Point] :
    Finite (FixedSubjoint semiGraph data) := by
  apply Finite.of_injective
    (fun subjoint =>
      (subjoint.center, subjoint.first, subjoint.second))
  intro first second equality
  apply FixedSubjoint.ext
  · exact congrArg (fun points => points.1) equality
  · exact congrArg (fun points => points.2.1) equality
  · exact congrArg (fun points => points.2.2) equality

/-- *Semi-graphs of Anabelioids*, Lemma 1.8(ii)(c): if a group fixes three
distinct original vertices of a semi-graph tree, it acts trivially on a
subjoint.  Once the three vertices are fixed, the proof does not use finiteness
of the acting group.  It extracts consecutive edges from fixed geodesics and
uses the degree-one boundary condition to show that their common point is an
original vertex. -/
theorem fixesSubjoint_of_three_fixed_vertices
    {first second third : Point}
    (first_vertex : first ∈ semiGraph.vertexSet)
    (_second_vertex : second ∈ semiGraph.vertexSet)
    (_third_vertex : third ∈ semiGraph.vertexSet)
    (first_ne_second : first ≠ second)
    (first_ne_third : first ≠ third)
    (second_ne_third : second ≠ third)
    (first_fixed :
      ∀ g : Acting,
        SourceGraphAction.graphIso data.toGraphAction g first = first)
    (second_fixed :
      ∀ g : Acting,
        SourceGraphAction.graphIso data.toGraphAction g second = second)
    (third_fixed :
      ∀ g : Acting,
        SourceGraphAction.graphIso data.toGraphAction g third = third) :
    FixesSubjoint semiGraph data := by
  let graph := semiGraph.compactification
  have subjoint_of_long_path
      {start finish : Point}
      (path : graph.Walk start finish)
      (path_isPath : path.IsPath)
      (two_le : 2 ≤ path.length)
      (start_fixed :
        ∀ g : Acting,
          SourceGraphAction.graphIso data.toGraphAction g start = start)
      (finish_fixed :
        ∀ g : Acting,
          SourceGraphAction.graphIso data.toGraphAction g finish = finish) :
      FixesSubjoint semiGraph data := by
    let left := path.getVert 0
    let center := path.getVert 1
    let right := path.getVert 2
    have left_adj_center : graph.Adj left center := by
      exact path.adj_getVert_succ (by omega : 0 < path.length)
    have center_adj_right : graph.Adj center right := by
      simpa [center, right] using
        path.adj_getVert_succ (i := 1) (by omega : 1 < path.length)
    have left_ne_right : left ≠ right := by
      intro equality
      have support_nodup := path_isPath.support_nodup
      have zero_bound : 0 < path.support.length := by
        rw [path.length_support]
        omega
      have two_bound : 2 < path.support.length := by
        rw [path.length_support]
        omega
      have support_eq : path.support[0] = path.support[2] := by
        rw [path.support_getElem_eq_getVert zero_bound]
        rw [path.support_getElem_eq_getVert two_bound]
        exact equality
      have index_eq : (0 : Nat) = 2 := by
        exact (List.Nodup.getElem_inj_iff support_nodup).mp support_eq
      omega
    have center_vertex : center ∈ semiGraph.vertexSet := by
      by_contra center_not_vertex
      obtain ⟨neighbor, _, neighbor_unique⟩ :=
        semiGraph.boundary_unique_neighbor center center_not_vertex
      have left_eq : left = neighbor :=
        neighbor_unique left left_adj_center.symm
      have right_eq : right = neighbor :=
        neighbor_unique right center_adj_right
      exact left_ne_right (left_eq.trans right_eq.symm)
    refine ⟨⟨center, center_vertex, left, right, left_ne_right,
      left_adj_center.symm, center_adj_right, ?_⟩⟩
    intro g
    have path_fixed :=
      SourceGraphAction.fixes_path_pointwise data.toGraphAction
        semiGraph.compactification_isTree g
        (start_fixed g) (finish_fixed g) path path_isPath
    exact
      ⟨path_fixed center (path.getVert_mem_support 1),
        path_fixed left (path.getVert_mem_support 0),
        path_fixed right (path.getVert_mem_support 2)⟩
  obtain ⟨firstSecondPath, firstSecondIsPath⟩ :=
    semiGraph.compactification_isTree.connected.exists_isPath first second
  by_cases firstSecondLong : 2 ≤ firstSecondPath.length
  · exact subjoint_of_long_path firstSecondPath firstSecondIsPath
      firstSecondLong first_fixed second_fixed
  have firstSecondPositive : 0 < firstSecondPath.length := by
    by_contra not_positive
    have length_zero : firstSecondPath.length = 0 := by omega
    exact first_ne_second
      (SimpleGraph.Walk.eq_of_length_eq_zero length_zero)
  have firstSecondLength : firstSecondPath.length = 1 := by omega
  have first_adj_second : graph.Adj first second :=
    SimpleGraph.Walk.adj_of_length_eq_one firstSecondLength
  obtain ⟨firstThirdPath, firstThirdIsPath⟩ :=
    semiGraph.compactification_isTree.connected.exists_isPath first third
  by_cases firstThirdLong : 2 ≤ firstThirdPath.length
  · exact subjoint_of_long_path firstThirdPath firstThirdIsPath
      firstThirdLong first_fixed third_fixed
  have firstThirdPositive : 0 < firstThirdPath.length := by
    by_contra not_positive
    have length_zero : firstThirdPath.length = 0 := by omega
    exact first_ne_third
      (SimpleGraph.Walk.eq_of_length_eq_zero length_zero)
  have firstThirdLength : firstThirdPath.length = 1 := by omega
  have first_adj_third : graph.Adj first third :=
    SimpleGraph.Walk.adj_of_length_eq_one firstThirdLength
  exact ⟨⟨first, first_vertex, second, third, second_ne_third,
    first_adj_second, first_adj_third, fun g =>
      ⟨first_fixed g, second_fixed g, third_fixed g⟩⟩⟩

/-- A locally injective equivariant map between marked semi-graph trees.  These
are the exact properties of a covering transition needed to transport fixed
subjoints. -/
structure EquivariantLocalMap
    {TargetPoint : Type w}
    (targetSemiGraph : SourceSemiGraphTree TargetPoint)
    (targetData : targetSemiGraph.Action Acting) where
  pointMap : Point → TargetPoint
  map_vertex :
    ∀ {point}, point ∈ semiGraph.vertexSet →
      pointMap point ∈ targetSemiGraph.vertexSet
  map_adjacent :
    ∀ {first second}, semiGraph.compactification.Adj first second →
      targetSemiGraph.compactification.Adj
        (pointMap first) (pointMap second)
  locally_injective :
    ∀ {center first second},
      semiGraph.compactification.Adj center first →
      semiGraph.compactification.Adj center second →
      pointMap first = pointMap second → first = second
  equivariant :
    ∀ g point,
      SourceGraphAction.graphIso targetData.toGraphAction g (pointMap point) =
        pointMap (SourceGraphAction.graphIso data.toGraphAction g point)

namespace FixedSubjoint

variable
  {TargetPoint : Type w}
  {targetSemiGraph : SourceSemiGraphTree TargetPoint}
  {targetData : targetSemiGraph.Action Acting}

/-- Transport a fixed subjoint along an equivariant locally injective
semi-graph map. -/
def map
    (transition : data.EquivariantLocalMap
      semiGraph targetSemiGraph targetData)
    (subjoint : FixedSubjoint semiGraph data) :
    FixedSubjoint targetSemiGraph targetData where
  center := transition.pointMap subjoint.center
  center_vertex := transition.map_vertex subjoint.center_vertex
  first := transition.pointMap subjoint.first
  second := transition.pointMap subjoint.second
  first_ne_second := by
    intro equality
    exact subjoint.first_ne_second
      (transition.locally_injective
        subjoint.center_adj_first subjoint.center_adj_second equality)
  center_adj_first := transition.map_adjacent subjoint.center_adj_first
  center_adj_second := transition.map_adjacent subjoint.center_adj_second
  fixed_pointwise := fun g =>
    ⟨(transition.equivariant g subjoint.center).trans
        (congrArg transition.pointMap (subjoint.fixed_pointwise g).1),
      (transition.equivariant g subjoint.first).trans
        (congrArg transition.pointMap (subjoint.fixed_pointwise g).2.1),
      (transition.equivariant g subjoint.second).trans
        (congrArg transition.pointMap (subjoint.fixed_pointwise g).2.2)⟩

end FixedSubjoint

namespace FixedVertex

variable
  {TargetPoint : Type w}
  {targetSemiGraph : SourceSemiGraphTree TargetPoint}
  {targetData : targetSemiGraph.Action Acting}

/-- Transport a fixed original vertex along an equivariant local semi-graph
map. -/
def map
    (transition : data.EquivariantLocalMap
      semiGraph targetSemiGraph targetData)
    (vertex : FixedVertex semiGraph data) :
    FixedVertex targetSemiGraph targetData :=
  ⟨transition.pointMap vertex.1,
    transition.map_vertex vertex.2.1,
    fun g =>
      (transition.equivariant g vertex.1).trans
        (congrArg transition.pointMap (vertex.2.2 g))⟩

end FixedVertex

end Action

end SourceSemiGraphTree

/-- The compact-to-discrete action that begins the proof of *Semi-graphs of
Anabelioids*, Theorem 3.7(iii).  The compact group acts through the discrete
deck group of a covering semi-graph. -/
structure SourceCompactSemiGraphAction
    (CompactGroup : Type u) (DeckGroup : Type v) (Point : Type*)
    [TopologicalSpace CompactGroup] [Group CompactGroup]
    [CompactSpace CompactGroup]
    [TopologicalSpace DeckGroup] [Group DeckGroup]
    [DiscreteTopology DeckGroup]
    (semiGraph : SourceSemiGraphTree Point) where
  deckMap : CompactGroup →* DeckGroup
  continuous_deckMap : Continuous deckMap
  deckAction : semiGraph.Action DeckGroup

namespace SourceCompactSemiGraphAction

variable
  {CompactGroup : Type u} {DeckGroup : Type v} {Point : Type*}
  [TopologicalSpace CompactGroup] [Group CompactGroup]
  [CompactSpace CompactGroup]
  [TopologicalSpace DeckGroup] [Group DeckGroup]
  [DiscreteTopology DeckGroup]
  {semiGraph : SourceSemiGraphTree Point}
  (data : SourceCompactSemiGraphAction
    CompactGroup DeckGroup Point semiGraph)

/-- Pull the deck action back to the compact group. -/
def compactAction : semiGraph.Action CompactGroup where
  toGraphAction :=
    { action := data.deckAction.toGraphAction.action.comp data.deckMap
      map_adj_iff := fun g first second =>
        data.deckAction.toGraphAction.map_adj_iff
          (data.deckMap g) first second }
  vertexSet_stable := fun g point =>
    data.deckAction.vertexSet_stable (data.deckMap g) point

@[simp]
theorem compactAction_graphIso_apply
    (g : CompactGroup) (point : Point) :
    SourceGraphAction.graphIso data.compactAction.toGraphAction g point =
      SourceGraphAction.graphIso data.deckAction.toGraphAction
        (data.deckMap g) point :=
  rfl

/-- Pull the branch projection over the base back along the compact-to-deck
homomorphism. -/
def compactActionOverBase
    {BaseBranch : Type*}
    (overBase : data.deckAction.OverBase semiGraph BaseBranch) :
    data.compactAction.OverBase semiGraph BaseBranch where
  branchProjection :=
    SourceSemiGraphTree.Action.OverBase.branchProjection
      (data := data.deckAction) overBase
  branchProjection_action := fun g first second adjacent =>
    SourceSemiGraphTree.Action.OverBase.branchProjection_action
      (data := data.deckAction) overBase
      (data.deckMap g) first second adjacent
  opposite_branches_ne := fun first second adjacent =>
    SourceSemiGraphTree.Action.OverBase.opposite_branches_ne
      (data := data.deckAction) overBase first second adjacent

/-- The image of a compact group in a discrete deck group is finite. -/
theorem deckMap_range_finite :
    (data.deckMap.range : Set DeckGroup).Finite := by
  rw [MonoidHom.coe_range]
  exact (isCompact_range data.continuous_deckMap).finite_of_discrete

/-- First fixed-vertex step in Theorem 3.7(iii): a compact subgroup acting
continuously through a discrete deck group fixes an original vertex or an edge
of the covering semi-graph. -/
theorem fixesVertexOrEdge :
    SourceSemiGraphTree.Action.FixesVertexOrEdge
      semiGraph data.compactAction := by
  let image : Subgroup DeckGroup := data.deckMap.range
  letI : Finite image := data.deckMap_range_finite.to_subtype
  have image_fixed :=
    SourceSemiGraphTree.Action.fixesVertexOrEdge semiGraph
      (data.deckAction.restrictActing semiGraph image)
  rcases image_fixed with ⟨vertex, vertex_mem, vertex_fixed⟩ |
      ⟨first, second, adjacent, edge_fixed⟩
  · left
    refine ⟨vertex, vertex_mem, ?_⟩
    intro g
    let imageElement : image :=
      ⟨data.deckMap g, ⟨g, rfl⟩⟩
    exact vertex_fixed imageElement
  · right
    refine ⟨first, second, adjacent, ?_⟩
    intro g
    let imageElement : image :=
      ⟨data.deckMap g, ⟨g, rfl⟩⟩
    exact edge_fixed imageElement

/-- The compact subgroup fixes an original vertex when the deck action is over
the base semi-graph and the covering semi-graph has a vertex. -/
theorem fixesVertex
    {BaseBranch : Type*}
    (overBase : data.deckAction.OverBase semiGraph BaseBranch)
    (vertex_nonempty : semiGraph.vertexSet.Nonempty) :
    ∃ vertex ∈ semiGraph.vertexSet,
      ∀ g : CompactGroup,
        SourceGraphAction.graphIso
          data.compactAction.toGraphAction g vertex = vertex :=
  SourceSemiGraphTree.Action.OverBase.fixedVertex_of_fixesVertexOrEdge
    semiGraph data.compactAction (data.compactActionOverBase overBase)
      vertex_nonempty data.fixesVertexOrEdge

/-- Three distinct original vertices fixed by the compact group determine a
subjoint fixed pointwise by that compact group. -/
theorem fixesSubjoint_of_three_fixed_vertices
    {first second third : Point}
    (first_vertex : first ∈ semiGraph.vertexSet)
    (second_vertex : second ∈ semiGraph.vertexSet)
    (third_vertex : third ∈ semiGraph.vertexSet)
    (first_ne_second : first ≠ second)
    (first_ne_third : first ≠ third)
    (second_ne_third : second ≠ third)
    (first_fixed :
      ∀ g : CompactGroup,
        SourceGraphAction.graphIso
          data.compactAction.toGraphAction g first = first)
    (second_fixed :
      ∀ g : CompactGroup,
        SourceGraphAction.graphIso
          data.compactAction.toGraphAction g second = second)
    (third_fixed :
      ∀ g : CompactGroup,
        SourceGraphAction.graphIso
          data.compactAction.toGraphAction g third = third) :
    SourceSemiGraphTree.Action.FixesSubjoint
      semiGraph data.compactAction :=
  SourceSemiGraphTree.Action.fixesSubjoint_of_three_fixed_vertices
    semiGraph data.compactAction first_vertex second_vertex third_vertex
      first_ne_second first_ne_third second_ne_third
      first_fixed second_fixed third_fixed

end SourceCompactSemiGraphAction

open CategoryTheory CategoryTheory.FunctorToTypes

/-- The finite fixed-subjoint inverse system used in the middle of the proof
of *Semi-graphs of Anabelioids*, Theorem 3.7(iii).  Its transition functor is
required to agree with actual equivariant locally injective maps of the
covering semi-graphs. -/
structure SourceCofilteredFixedSubjointSystem
    (Index : Type u) [Category.{w} Index] [IsCofilteredOrEmpty Index]
    (Acting : Type u) [Group Acting] where
  CoverPoint : Index → Type v
  FinitePoint : Index → Type v
  coverSemiGraph : ∀ index, SourceSemiGraphTree (CoverPoint index)
  finiteSemiGraph : ∀ index, SourceSemiGraphTree (FinitePoint index)
  coverAction : ∀ index, (coverSemiGraph index).Action Acting
  finiteAction : ∀ index, (finiteSemiGraph index).Action Acting
  quotientMap :
    ∀ index,
      (coverAction index).EquivariantLocalMap
        (coverSemiGraph index) (finiteSemiGraph index) (finiteAction index)
  fixedSubjoints : Index ⥤ Type v
  realize :
    ∀ index,
      fixedSubjoints.obj index ≃
        SourceSemiGraphTree.Action.FixedSubjoint
          (finiteSemiGraph index) (finiteAction index)
  transition :
    ∀ {source target} (_map : source ⟶ target),
      (finiteAction source).EquivariantLocalMap
        (finiteSemiGraph source) (finiteSemiGraph target) (finiteAction target)
  transition_realize :
    ∀ {source target} (map : source ⟶ target)
      (subjoint : fixedSubjoints.obj source),
      realize target (fixedSubjoints.map map subjoint) =
        SourceSemiGraphTree.Action.FixedSubjoint.map
          (finiteSemiGraph source) (finiteAction source)
          (transition map) (realize source subjoint)
  finite_points : ∀ index, Finite (FinitePoint index)
  first : ∀ index, CoverPoint index
  second : ∀ index, CoverPoint index
  third : ∀ index, CoverPoint index
  first_vertex :
    ∀ index, first index ∈ (coverSemiGraph index).vertexSet
  second_vertex :
    ∀ index, second index ∈ (coverSemiGraph index).vertexSet
  third_vertex :
    ∀ index, third index ∈ (coverSemiGraph index).vertexSet
  first_ne_second : ∀ index, first index ≠ second index
  first_ne_third : ∀ index, first index ≠ third index
  second_ne_third : ∀ index, second index ≠ third index
  first_fixed :
    ∀ index g,
      SourceGraphAction.graphIso
        (coverAction index).toGraphAction g (first index) = first index
  second_fixed :
    ∀ index g,
      SourceGraphAction.graphIso
        (coverAction index).toGraphAction g (second index) = second index
  third_fixed :
    ∀ index g,
      SourceGraphAction.graphIso
        (coverAction index).toGraphAction g (third index) = third index

namespace SourceCofilteredFixedSubjointSystem

variable
  {Index : Type u} [Category.{w} Index] [IsCofilteredOrEmpty Index]
  {Acting : Type u} [Group Acting]
  (system : SourceCofilteredFixedSubjointSystem Index Acting)

/-- Nonempty finite fixed-subjoint sets over a cofiltered system admit a
compatible choice.  This is the finite inverse-limit argument used in
Theorem 3.7(iii), rather than a separately assumed compatible system. -/
theorem exists_compatible_fixedSubjoints :
    system.fixedSubjoints.sections.Nonempty := by
  letI (index : Index) : Finite (system.FinitePoint index) :=
    system.finite_points index
  letI (index : Index) : Finite (system.fixedSubjoints.obj index) :=
    Finite.of_equiv
      (SourceSemiGraphTree.Action.FixedSubjoint
        (system.finiteSemiGraph index) (system.finiteAction index))
      (system.realize index).symm
  letI (index : Index) : Nonempty (system.fixedSubjoints.obj index) :=
    let coverSubjoint :=
      SourceSemiGraphTree.Action.fixesSubjoint_of_three_fixed_vertices
        (system.coverSemiGraph index) (system.coverAction index)
          (system.first_vertex index) (system.second_vertex index)
          (system.third_vertex index) (system.first_ne_second index)
          (system.first_ne_third index) (system.second_ne_third index)
          (system.first_fixed index) (system.second_fixed index)
          (system.third_fixed index)
    Nonempty.map (system.realize index).symm
      (Nonempty.map
        (SourceSemiGraphTree.Action.FixedSubjoint.map
          (system.coverSemiGraph index) (system.coverAction index)
          (system.quotientMap index)) coverSubjoint)
  exact nonempty_sections_of_finite_cofiltered_system system.fixedSubjoints

end SourceCofilteredFixedSubjointSystem

/-- The fixed-vertex inverse system in the final paragraph of the proof of
*Semi-graphs of Anabelioids*, Theorem 3.7(iii).  Its transitions agree with
actual equivariant local maps, and every fixed set is bounded by two vertices.
-/
structure SourceCofilteredFixedVertexSystem
    (Index : Type u) [Category.{w} Index] [IsCofilteredOrEmpty Index]
    (Acting : Type u) [Group Acting] where
  Point : Index → Type v
  semiGraph : ∀ index, SourceSemiGraphTree (Point index)
  action : ∀ index, (semiGraph index).Action Acting
  fixedVertices : Index ⥤ Type v
  realize :
    ∀ index,
      fixedVertices.obj index ≃
        SourceSemiGraphTree.Action.FixedVertex
          (semiGraph index) (action index)
  transition :
    ∀ {source target} (_map : source ⟶ target),
      (action source).EquivariantLocalMap
        (semiGraph source) (semiGraph target) (action target)
  transition_realize :
    ∀ {source target} (map : source ⟶ target)
      (vertex : fixedVertices.obj source),
      realize target (fixedVertices.map map vertex) =
        SourceSemiGraphTree.Action.FixedVertex.map
          (semiGraph source) (action source)
          (transition map) (realize source vertex)
  fixed_vertex_nonempty :
    ∀ index,
      Nonempty
        (SourceSemiGraphTree.Action.FixedVertex
          (semiGraph index) (action index))
  fixed_vertices_le_pair :
    ∀ index,
      ∃ first second,
        SourceSemiGraphTree.Action.fixedVertexSet
            (semiGraph index) (action index) ⊆
          {first, second}

namespace SourceCofilteredFixedVertexSystem

variable
  {Index : Type u} [Category.{w} Index] [IsCofilteredOrEmpty Index]
  {Acting : Type u} [Group Acting]
  (system : SourceCofilteredFixedVertexSystem Index Acting)

/-- Nonempty fixed-vertex sets bounded by two points admit a compatible
choice over the cofiltered system. -/
theorem exists_compatible_fixedVertices :
    system.fixedVertices.sections.Nonempty := by
  letI (index : Index) :
      Finite
        (SourceSemiGraphTree.Action.FixedVertex
          (system.semiGraph index) (system.action index)) := by
    obtain ⟨first, second, fixed_le⟩ :=
      system.fixed_vertices_le_pair index
    exact (((Set.finite_singleton second).insert first).subset
      fixed_le).to_subtype
  letI (index : Index) : Finite (system.fixedVertices.obj index) :=
    Finite.of_equiv
      (SourceSemiGraphTree.Action.FixedVertex
        (system.semiGraph index) (system.action index))
      (system.realize index).symm
  letI (index : Index) : Nonempty (system.fixedVertices.obj index) :=
    Nonempty.map (system.realize index).symm
      (system.fixed_vertex_nonempty index)
  exact nonempty_sections_of_finite_cofiltered_system system.fixedVertices

/-- There are at most two compatible fixed-vertex systems.  Three pairwise
distinct sections would remain pairwise distinct at a common cofiltered
predecessor, contradicting the two-point bound in that fiber. -/
theorem three_compatible_fixedVertices_not_pairwise_distinct
    (first second third : system.fixedVertices.sections) :
    first = second ∨ first = third ∨ second = third := by
  classical
  by_cases first_eq_second : first = second
  · exact Or.inl first_eq_second
  by_cases first_eq_third : first = third
  · exact Or.inr (Or.inl first_eq_third)
  by_cases second_eq_third : second = third
  · exact Or.inr (Or.inr second_eq_third)
  have exists_ne_index
      {left right : system.fixedVertices.sections}
      (not_equal : left ≠ right) :
      ∃ index, left.1 index ≠ right.1 index := by
    have not_all : ¬∀ index, left.1 index = right.1 index :=
      fun all_equal => not_equal
        (CategoryTheory.Functor.sections_ext_iff.mpr all_equal)
    push Not at not_all
    exact not_all
  obtain ⟨firstSecondIndex, firstSecond_ne⟩ :=
    exists_ne_index first_eq_second
  obtain ⟨firstThirdIndex, firstThird_ne⟩ :=
    exists_ne_index first_eq_third
  obtain ⟨secondThirdIndex, secondThird_ne⟩ :=
    exists_ne_index second_eq_third
  let pairIndex :=
    CategoryTheory.IsCofiltered.min firstSecondIndex firstThirdIndex
  let commonIndex :=
    CategoryTheory.IsCofiltered.min pairIndex secondThirdIndex
  let commonToPair : commonIndex ⟶ pairIndex :=
    CategoryTheory.IsCofiltered.minToLeft pairIndex secondThirdIndex
  let commonToFirstSecond : commonIndex ⟶ firstSecondIndex :=
    commonToPair ≫
      CategoryTheory.IsCofiltered.minToLeft
        firstSecondIndex firstThirdIndex
  let commonToFirstThird : commonIndex ⟶ firstThirdIndex :=
    commonToPair ≫
      CategoryTheory.IsCofiltered.minToRight
        firstSecondIndex firstThirdIndex
  let commonToSecondThird : commonIndex ⟶ secondThirdIndex :=
    CategoryTheory.IsCofiltered.minToRight pairIndex secondThirdIndex
  have ne_at_common
      (left right : system.fixedVertices.sections)
      {target : Index} (map : commonIndex ⟶ target)
      (ne_at_target : left.1 target ≠ right.1 target) :
      left.1 commonIndex ≠ right.1 commonIndex := by
    intro equal_at_common
    apply ne_at_target
    rw [← left.property map, ← right.property map, equal_at_common]
  have firstSecond_ne_common :
      first.1 commonIndex ≠ second.1 commonIndex :=
    ne_at_common first second commonToFirstSecond firstSecond_ne
  have firstThird_ne_common :
      first.1 commonIndex ≠ third.1 commonIndex :=
    ne_at_common first third commonToFirstThird firstThird_ne
  have secondThird_ne_common :
      second.1 commonIndex ≠ third.1 commonIndex :=
    ne_at_common second third commonToSecondThird secondThird_ne
  obtain ⟨leftPoint, rightPoint, fixed_le⟩ :=
    system.fixed_vertices_le_pair commonIndex
  let firstVertex := system.realize commonIndex (first.1 commonIndex)
  let secondVertex := system.realize commonIndex (second.1 commonIndex)
  let thirdVertex := system.realize commonIndex (third.1 commonIndex)
  have first_side : firstVertex.1 = leftPoint ∨ firstVertex.1 = rightPoint :=
    fixed_le firstVertex.2
  have second_side : secondVertex.1 = leftPoint ∨ secondVertex.1 = rightPoint :=
    fixed_le secondVertex.2
  have third_side : thirdVertex.1 = leftPoint ∨ thirdVertex.1 = rightPoint :=
    fixed_le thirdVertex.2
  have value_eq_of_point_eq
      {left right : system.fixedVertices.obj commonIndex}
      (point_eq :
        (system.realize commonIndex left).1 =
          (system.realize commonIndex right).1) :
      left = right := by
    apply (system.realize commonIndex).injective
    exact Subtype.ext point_eq
  rcases first_side with first_left | first_right
  · rcases second_side with second_left | second_right
    · exact firstSecond_ne_common
        (value_eq_of_point_eq (first_left.trans second_left.symm)) |>.elim
    · rcases third_side with third_left | third_right
      · exact firstThird_ne_common
          (value_eq_of_point_eq (first_left.trans third_left.symm)) |>.elim
      · exact secondThird_ne_common
          (value_eq_of_point_eq (second_right.trans third_right.symm)) |>.elim
  · rcases second_side with second_left | second_right
    · rcases third_side with third_left | third_right
      · exact secondThird_ne_common
          (value_eq_of_point_eq (second_left.trans third_left.symm)) |>.elim
      · exact firstThird_ne_common
          (value_eq_of_point_eq (first_right.trans third_right.symm)) |>.elim
    · exact firstSecond_ne_common
        (value_eq_of_point_eq (first_right.trans second_right.symm)) |>.elim

end SourceCofilteredFixedVertexSystem

open scoped Pointwise

/-- The incident-branch subgroup formulation of *Semi-graphs of
Anabelioids*, Definition 2.4(iv), at a fixed vertex.  Distinct branches have
trivial intersection after arbitrary conjugation; a branch also has trivial
intersection with a conjugate by an element outside that branch subgroup. -/
structure SourceEstrangedIncidentBranchSystem
    (Ambient : Type u) [Group Ambient] where
  Branch : Type v
  branchSubgroup : Branch → Subgroup Ambient
  estranged_intersection :
    ∀ (first second : Branch) (conjugator : Ambient),
      (first ≠ second ∨
        (first = second ∧ conjugator ∉ branchSubgroup first)) →
      branchSubgroup first ⊓
          MulAut.conj conjugator • branchSubgroup second = ⊥

namespace SourceEstrangedIncidentBranchSystem

variable
  {Ambient : Type u} [Group Ambient]
  (data : SourceEstrangedIncidentBranchSystem Ambient)

/-- A subgroup contained in two estranged incident branch images is trivial.
This is the algebraic contradiction used in Theorem 3.7(iii) after applying
Remark 2.2.1 to a compatible fixed-subjoint system. -/
theorem subgroup_eq_bot_of_le_branch_intersection
    (subgroup : Subgroup Ambient)
    (first second : data.Branch) (conjugator : Ambient)
    (branches_separated :
      first ≠ second ∨
        (first = second ∧
          conjugator ∉ data.branchSubgroup first))
    (le_first : subgroup ≤ data.branchSubgroup first)
    (le_second :
      subgroup ≤
        MulAut.conj conjugator • data.branchSubgroup second) :
    subgroup = ⊥ := by
  apply le_antisymm
  · rw [← data.estranged_intersection
      first second conjugator branches_separated]
    exact le_inf le_first le_second
  · exact bot_le

/-- Hence a nontrivial subgroup cannot be contained in two estranged incident
branch images. -/
theorem not_le_two_branches_of_ne_bot
    (subgroup : Subgroup Ambient)
    (subgroup_ne_bot : subgroup ≠ ⊥)
    (first second : data.Branch) (conjugator : Ambient)
    (branches_separated :
      first ≠ second ∨
        (first = second ∧
          conjugator ∉ data.branchSubgroup first)) :
    ¬(subgroup ≤ data.branchSubgroup first ∧
      subgroup ≤ MulAut.conj conjugator • data.branchSubgroup second) := by
  rintro ⟨le_first, le_second⟩
  exact subgroup_ne_bot
    (data.subgroup_eq_bot_of_le_branch_intersection subgroup
      first second conjugator branches_separated le_first le_second)

end SourceEstrangedIncidentBranchSystem

/-- The exact subgroup configuration of IUT I, Proposition 2.4(i).

`geometricTempered = arithmeticTempered ⊓ geometric` records the geometric
kernel inside the arithmetic tempered group.  The final field is precisely the
compact-conjugate rigidity conclusion of Proposition 2.4(i), not Corollary 2.5. -/
structure SourceIUTIProposition24PartI
    (Ambient : Type u)
    [Group Ambient] [TopologicalSpace Ambient] where
  geometric : Subgroup Ambient
  arithmeticTempered : Subgroup Ambient
  geometricTempered : Subgroup Ambient
  geometric_normal : geometric.Normal
  geometricTempered_eq :
    geometricTempered = arithmeticTempered ⊓ geometric
  compactConjugateRigidity :
    ∀ (compact : Subgroup Ambient),
      compact ≤ geometricTempered →
      compact ≠ ⊥ →
      IsCompact (compact : Set Ambient) →
      ∀ conjugator : Ambient,
        MulAut.conj conjugator • compact ≤ geometricTempered →
        conjugator ∈ arithmeticTempered

namespace SourceIUTIProposition24PartI

variable
  {Ambient : Type u}
  [Group Ambient] [TopologicalSpace Ambient]
  (data : SourceIUTIProposition24PartI Ambient)

attribute [local instance] SourceIUTIProposition24PartI.geometric_normal

theorem geometricTempered_le_arithmeticTempered :
    data.geometricTempered ≤ data.arithmeticTempered := by
  rw [data.geometricTempered_eq]
  exact inf_le_left

theorem geometricTempered_le_geometric :
    data.geometricTempered ≤ data.geometric := by
  rw [data.geometricTempered_eq]
  exact inf_le_right

/-- A cusp inertia subgroup to which Proposition 2.4(i) applies. -/
structure CuspidalInertia where
  inertia : Subgroup Ambient
  inertia_le : inertia ≤ data.geometricTempered
  inertia_ne_bot : inertia ≠ ⊥
  inertia_isCompact : IsCompact (inertia : Set Ambient)

namespace CuspidalInertia

variable (cusp : data.CuspidalInertia)

/-- An ambient conjugate of cusp inertia lies in the arithmetic tempered group
exactly when its conjugator is tempered. -/
theorem conjugate_le_arithmeticTempered_iff
    (conjugator : Ambient) :
    MulAut.conj conjugator • cusp.inertia ≤
        data.arithmeticTempered ↔
      conjugator ∈ data.arithmeticTempered := by
  constructor
  · intro hconjugate
    apply data.compactConjugateRigidity cusp.inertia
      cusp.inertia_le cusp.inertia_ne_bot cusp.inertia_isCompact
      conjugator
    rw [data.geometricTempered_eq]
    refine le_inf hconjugate ?_
    calc
      MulAut.conj conjugator • cusp.inertia ≤
          MulAut.conj conjugator • data.geometric :=
        smul_le_smul_left (MulAut.conj conjugator)
          (cusp.inertia_le.trans
            data.geometricTempered_le_geometric)
      _ = data.geometric :=
        data.geometric_normal.conj_smul_eq_self conjugator
  · intro hconjugator
    exact Subgroup.conj_smul_le_of_le
      (cusp.inertia_le.trans
        data.geometricTempered_le_arithmeticTempered)
      ⟨conjugator, hconjugator⟩

/-- Thus every ambient conjugate contained in the tempered group is already a
conjugate by an element of the tempered group. -/
theorem conjugate_classification
    (conjugator : Ambient) :
    MulAut.conj conjugator • cusp.inertia ≤
        data.arithmeticTempered ↔
      ∃ temperedConjugator : data.arithmeticTempered,
        MulAut.conj conjugator • cusp.inertia =
          MulAut.conj temperedConjugator.1 • cusp.inertia := by
  constructor
  · intro h
    exact
      ⟨⟨conjugator,
          (conjugate_le_arithmeticTempered_iff
            data cusp conjugator).mp h⟩,
        rfl⟩
  · rintro ⟨temperedConjugator, heq⟩
    rw [heq]
    exact
      (conjugate_le_arithmeticTempered_iff
        data cusp temperedConjugator.1).mpr temperedConjugator.2

/-- A conjugate of the arithmetic tempered group contains cusp inertia if and
only if it is the original tempered group.  This is the second cuspidal claim
of IUT I, Corollary 2.5. -/
theorem inertia_le_conjugate_arithmeticTempered_iff
    (conjugator : Ambient) :
    cusp.inertia ≤
        MulAut.conj conjugator • data.arithmeticTempered ↔
      MulAut.conj conjugator • data.arithmeticTempered =
        data.arithmeticTempered := by
  constructor
  · intro hinertia
    have hinverse :
        MulAut.conj conjugator⁻¹ • cusp.inertia ≤
          data.arithmeticTempered :=
      by
        simpa using
          (Subgroup.subset_pointwise_smul_iff.mp hinertia)
    have hinverse_mem :
        conjugator⁻¹ ∈ data.arithmeticTempered :=
      (conjugate_le_arithmeticTempered_iff
        data cusp conjugator⁻¹).mp hinverse
    exact Subgroup.conj_smul_eq_self_of_mem
      (by
        simpa using
          data.arithmeticTempered.inv_mem hinverse_mem)
  · intro heq
    rw [heq]
    exact
      cusp.inertia_le.trans
        data.geometricTempered_le_arithmeticTempered

end CuspidalInertia

end SourceIUTIProposition24PartI

end Iut
