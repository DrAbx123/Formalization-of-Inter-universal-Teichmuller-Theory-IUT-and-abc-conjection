/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceAnabelioid
import Iut.Foundations.SourceSemiGraphOfSubgroups

/-!
# Pointed semi-graphs of connected anabelioids

This module formalizes the categorical data in *Semi-graphs of Anabelioids*,
Definition 2.1, together with the basepoint choices used immediately after that
definition.  Constituent categories are actual Galois categories, branch maps
are exact pullback functors, and every displayed fundamental-group map is
derived from those functors.

The comparison between the direct edge-to-total morphism and the composite
edge-to-vertex-to-total morphism is a genuine 2-isomorphism.  Its basepoint
discrepancy derives the Bass--Serre transport element.  Consequently the
subgroup diagram used by the universal-covering construction is constructed
from anabelioid data rather than supplied independently.
-/

namespace Iut

universe u

/-- The literal constituent and branch data of *Semi-graphs of Anabelioids*,
Definition 2.1.  In particular, this structure does not contain the glued
category `B(G)`: that category is to be constructed from these fields. -/
structure SourceSemiGraphOfAnabelioids where
  base : SourceSemiGraph.{u}
  connected : base.IsConnected
  vertexAnabelioid : base.Vertex → EtaleFundamentalGroup.{u}
  edgeAnabelioid : base.Edge → EtaleFundamentalGroup.{u}
  branchMorphism :
    ∀ {edge} (branch : base.Branch edge) {vertex},
      base.coincidence edge branch = some vertex →
        SourcePointedAnabelioidHom
          (edgeAnabelioid edge) (vertexAnabelioid vertex)
  branchPiOneMonomorphism :
    ∀ {edge} (branch : base.Branch edge) {vertex}
      (abuts : base.coincidence edge branch = some vertex),
      (branchMorphism branch abuts).IsPiOneMonomorphism

/-- A pointed realization of a semi-graph of anabelioids inside a chosen
total anabelioid.  This is useful after `B(G)` has been constructed, but is
deliberately separate from the source data in `SourceSemiGraphOfAnabelioids`.

The `branchComparison` is the 2-commutative triangle of Definition 2.1 after
passing to the total anabelioid.  No subgroup of the total fundamental group
is stored in this structure. -/
structure SourcePointedSemiGraphOfAnabelioids extends
    SourceSemiGraphOfAnabelioids.{u} where
  totalAnabelioid : EtaleFundamentalGroup.{u}
  vertexMorphism :
    ∀ vertex,
      SourcePointedAnabelioidHom
        (vertexAnabelioid vertex) totalAnabelioid
  edgeMorphism :
    ∀ edge,
      SourcePointedAnabelioidHom
        (edgeAnabelioid edge) totalAnabelioid
  vertexPiOneMonomorphism :
    ∀ vertex, (vertexMorphism vertex).IsPiOneMonomorphism
  edgePiOneMonomorphism :
    ∀ edge, (edgeMorphism edge).IsPiOneMonomorphism
  branchComparison :
    ∀ {edge} (branch : base.Branch edge) {vertex}
      (abuts : base.coincidence edge branch = some vertex),
      SourcePointedAnabelioidHom.TwoIso
        ((branchMorphism branch abuts).comp
          (vertexMorphism vertex))
        (edgeMorphism edge)

namespace SourcePointedSemiGraphOfAnabelioids

variable (diagram : SourcePointedSemiGraphOfAnabelioids.{u})

/-- A constituent vertex fundamental group is homeomorphic to its closed
image in the total fundamental group. -/
noncomputable def vertexFundamentalGroupImageEquiv
    (vertex : diagram.base.Vertex) :
    (diagram.vertexAnabelioid vertex).group ≃ₜ*
      (diagram.vertexMorphism vertex).fundamentalGroupClosedImage :=
  SourcePointedAnabelioidHom.fundamentalGroupImageContinuousMulEquiv
    (diagram.vertexMorphism vertex)
    (diagram.vertexPiOneMonomorphism vertex)

/-- A constituent edge fundamental group is homeomorphic to its closed image
in the total fundamental group. -/
noncomputable def edgeFundamentalGroupImageEquiv
    (edge : diagram.base.Edge) :
    (diagram.edgeAnabelioid edge).group ≃ₜ*
      (diagram.edgeMorphism edge).fundamentalGroupClosedImage :=
  SourcePointedAnabelioidHom.fundamentalGroupImageContinuousMulEquiv
    (diagram.edgeMorphism edge)
    (diagram.edgePiOneMonomorphism edge)

/-- The branch transport in the total fundamental group, derived from the
2-isomorphism and the two basepoint identifications. -/
noncomputable def branchTransport
    {edge : diagram.base.Edge}
    (branch : diagram.base.Branch edge)
    {vertex : diagram.base.Vertex}
    (abuts : diagram.base.coincidence edge branch = some vertex) :
    diagram.totalAnabelioid.group :=
  (diagram.branchComparison branch abuts).fundamentalGroupTransport

/--
The semi-graph of closed subgroups of the total fundamental group constructed
from the pointed semi-graph of anabelioids.

The conjugation compatibility is a theorem from the 2-isomorphism:
`tau^-1 * Pi_e * tau <= Pi_v`.
-/
noncomputable def subgroupDiagram :
    SourceSemiGraphSubgroupDiagram diagram.totalAnabelioid.group where
  base := diagram.base
  vertexGroup := fun vertex =>
    (diagram.vertexMorphism vertex).fundamentalGroupImage
  edgeGroup := fun edge =>
    (diagram.edgeMorphism edge).fundamentalGroupImage
  branchTransport := fun {edge} branch {vertex} abuts =>
    diagram.branchTransport branch abuts
  transport_compatible := by
    intro edge branch vertex abuts value value_mem
    change value ∈
      (diagram.edgeMorphism edge).fundamentalGroupImage at value_mem
    rcases value_mem with ⟨edgeElement, rfl⟩
    refine
      ⟨(diagram.branchMorphism branch abuts).fundamentalGroupHom
          edgeElement, ?_⟩
    have conjugacy :=
      SourcePointedAnabelioidHom.TwoIso.fundamentalGroupHom_eq_conjugate
        (diagram.branchComparison branch abuts) edgeElement
    symm
    calc
      (diagram.branchTransport branch abuts)⁻¹ *
            (diagram.edgeMorphism edge).fundamentalGroupHom edgeElement *
          diagram.branchTransport branch abuts =
        (diagram.branchTransport branch abuts)⁻¹ *
            (diagram.branchTransport branch abuts *
                ((diagram.branchMorphism branch abuts).comp
                  (diagram.vertexMorphism vertex)).fundamentalGroupHom
                    edgeElement *
              (diagram.branchTransport branch abuts)⁻¹) *
          diagram.branchTransport branch abuts := by
            rw [conjugacy]
            simp only [branchTransport]
      _ = ((diagram.branchMorphism branch abuts).comp
            (diagram.vertexMorphism vertex)).fundamentalGroupHom
              edgeElement := by group
      _ = (diagram.vertexMorphism vertex).fundamentalGroupHom
            ((diagram.branchMorphism branch abuts).fundamentalGroupHom
              edgeElement) :=
        SourcePointedAnabelioidHom.fundamentalGroupHom_comp
          (diagram.branchMorphism branch abuts)
          (diagram.vertexMorphism vertex) edgeElement

/-- The vertex subgroup of the derived subgroup diagram is exactly the image
of the categorical constituent fundamental-group morphism. -/
theorem subgroupDiagram_vertexGroup
    (vertex : diagram.base.Vertex) :
    diagram.subgroupDiagram.vertexGroup vertex =
      (diagram.vertexMorphism vertex).fundamentalGroupImage :=
  rfl

/-- The edge subgroup of the derived subgroup diagram is exactly the image of
the categorical constituent fundamental-group morphism. -/
theorem subgroupDiagram_edgeGroup
    (edge : diagram.base.Edge) :
    diagram.subgroupDiagram.edgeGroup edge =
      (diagram.edgeMorphism edge).fundamentalGroupImage :=
  rfl

/-- The transport element of the derived subgroup diagram is the element
reconstructed from the categorical 2-isomorphism. -/
theorem subgroupDiagram_branchTransport
    {edge : diagram.base.Edge}
    (branch : diagram.base.Branch edge)
    {vertex : diagram.base.Vertex}
    (abuts : diagram.base.coincidence edge branch = some vertex) :
    diagram.subgroupDiagram.branchTransport branch abuts =
      (diagram.branchComparison branch abuts).fundamentalGroupTransport :=
  rfl

/-- Every derived vertex subgroup is closed in the total profinite
fundamental group. -/
theorem subgroupDiagram_vertexGroup_isClosed
    (vertex : diagram.base.Vertex) :
    IsClosed
      (diagram.subgroupDiagram.vertexGroup vertex :
        Set diagram.totalAnabelioid.group) :=
  (diagram.vertexMorphism vertex).fundamentalGroupImage_isClosed

/-- Every derived edge subgroup is closed in the total profinite fundamental
group. -/
theorem subgroupDiagram_edgeGroup_isClosed
    (edge : diagram.base.Edge) :
    IsClosed
      (diagram.subgroupDiagram.edgeGroup edge :
        Set diagram.totalAnabelioid.group) :=
  (diagram.edgeMorphism edge).fundamentalGroupImage_isClosed

end SourcePointedSemiGraphOfAnabelioids

end Iut
