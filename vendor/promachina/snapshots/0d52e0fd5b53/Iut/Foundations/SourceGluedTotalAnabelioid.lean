/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceGluedGalois

/-!
# The total anabelioid of a connected semi-graph of anabelioids

Definition 2.1 has exactly two cases.  If the connected base semigraph has a
vertex, `B(G)` is the glued category already constructed from its vertex
objects and edge identifications.  If it has no vertices, connectedness forces
a unique isolated edge and `B(G)` is that edge anabelioid itself.  The carrier,
category, Galois proof, and basepoint are dispatched together so no transported
typeclass instances enter the public construction.
-/

namespace Iut

universe u

open CategoryTheory

/-- A connected anabelioid together with a chosen fiber functor, but without
choosing a particular small presentation of its fundamental group. -/
structure SourceBasedConnectedAnabelioid where
  Cover : Type (u + 1)
  coverCategory : Category.{u} Cover
  galoisCategory : @GaloisCategory Cover coverCategory
  fiber : letI := coverCategory; Cover ⥤ FintypeCat.{u}
  fiberFunctor :
    letI := coverCategory
    letI := galoisCategory
    PreGaloisCategory.FiberFunctor fiber

namespace SourceBasedConnectedAnabelioid

instance (data : SourceBasedConnectedAnabelioid.{u}) :
    Category.{u} data.Cover := data.coverCategory

instance (data : SourceBasedConnectedAnabelioid.{u}) :
    GaloisCategory data.Cover := data.galoisCategory

instance (data : SourceBasedConnectedAnabelioid.{u}) :
    PreGaloisCategory.FiberFunctor data.fiber := data.fiberFunctor

end SourceBasedConnectedAnabelioid

namespace SourceSemiGraphOfAnabelioids

variable (diagram : Iut.SourceSemiGraphOfAnabelioids.{u})

/-- The complete category `B(G)` from Definition 2.1, including its
isolated-edge case. -/
noncomputable def totalAnabelioid : SourceBasedConnectedAnabelioid.{u} := by
  classical
  by_cases hasVertex : Nonempty diagram.base.Vertex
  · let root := Classical.choice hasVertex
    exact
      { Cover := diagram.GluedObject
        coverCategory := GluedObject.category
        galoisCategory := GluedObject.galoisCategory diagram root
        fiber := GluedObject.rootFiber diagram root
        fiberFunctor := GluedObject.rootFiberFunctor diagram root }
  · letI : IsEmpty diagram.base.Vertex := not_nonempty_iff.mp hasVertex
    let edge := diagram.connected.uniqueEdge
    exact
      { Cover := (diagram.edgeAnabelioid edge).Cover
        coverCategory := (diagram.edgeAnabelioid edge).coverCategory
        galoisCategory := (diagram.edgeAnabelioid edge).galoisCategory
        fiber := (diagram.edgeAnabelioid edge).fiber
        fiberFunctor := (diagram.edgeAnabelioid edge).fiberFunctor }

/-- The object type of the source-defined total anabelioid. -/
abbrev TotalCover : Type (u + 1) := diagram.totalAnabelioid.Cover

/-- The chosen fiber functor of the source-defined total anabelioid. -/
noncomputable abbrev totalFiber : diagram.TotalCover ⥤ FintypeCat.{u} :=
  diagram.totalAnabelioid.fiber

/-- In the verticial case, the total anabelioid reduces to the glued
category, with root evaluation as its chosen fiber functor. -/
theorem totalAnabelioid_eq_glued
    (hasVertex : Nonempty diagram.base.Vertex) :
    diagram.totalAnabelioid =
      { Cover := diagram.GluedObject
        coverCategory := GluedObject.category
        galoisCategory := GluedObject.galoisCategory diagram
          (Classical.choice hasVertex)
        fiber := GluedObject.rootFiber diagram (Classical.choice hasVertex)
        fiberFunctor := GluedObject.rootFiberFunctor diagram
          (Classical.choice hasVertex) } := by
  classical
  unfold totalAnabelioid
  simp only [hasVertex, dite_true]

/-- In the vertex-free case, the total anabelioid is the anabelioid of the
unique isolated edge. -/
theorem totalAnabelioid_eq_uniqueEdge
    (noVertex : ¬Nonempty diagram.base.Vertex) :
    letI : IsEmpty diagram.base.Vertex := not_nonempty_iff.mp noVertex
    let edge := diagram.connected.uniqueEdge
    diagram.totalAnabelioid =
      { Cover := (diagram.edgeAnabelioid edge).Cover
        coverCategory := (diagram.edgeAnabelioid edge).coverCategory
        galoisCategory := (diagram.edgeAnabelioid edge).galoisCategory
        fiber := (diagram.edgeAnabelioid edge).fiber
        fiberFunctor := (diagram.edgeAnabelioid edge).fiberFunctor } := by
  classical
  unfold totalAnabelioid
  simp only [noVertex, dite_false]

end SourceSemiGraphOfAnabelioids

end Iut
