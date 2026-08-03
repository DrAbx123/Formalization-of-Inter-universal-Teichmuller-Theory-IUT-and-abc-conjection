/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceSemiGraphResidualSeparation
import Iut.Foundations.SourceTemperedFiniteGraphCoverRealization
import Iut.Foundations.SourceTemperedDeckGroup
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup

/-!
# The tempered-to-profinite comparison

For the pointed cofinal system used to construct the tempered deck group, every
finite-level composite deck transformation retains an automorphism of its
Galois object.  These retained automorphisms are compatible under refinement.
Mathlib's Galois pro-representability theorem identifies their inverse limit
with the automorphism group of the root fiber functor.  This file constructs
the resulting pointed representative of the comparison in Proposition 3.6(iii)
of *Semi-graphs of Anabelioids*.

The comparison is constructed from the existing deck coordinates; it is not an
input field.  Its injectivity, which uses residual finiteness of the free
combinatorial deck kernels, is proved below after the finite-refinement
separation theorem.
-/

namespace Iut

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

noncomputable section

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)

private abbrev RootFiber :=
  SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root

/-- The repository's Galois-level type is the literal pointed-Galois-object
indexing type used by Mathlib's pro-representability theorem. -/
private def galoisLevelOfPointedObject
    [GaloisCategory diagram.GluedObject]
    (object : PointedGaloisObject (RootFiber diagram root)) :
    SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root where
  object := object.obj
  point := object.pt
  isGalois := object.isGalois

/-- Point-preserving arrows are unchanged by the preceding identification. -/
private def galoisLevelHomOfPointedHom
    [GaloisCategory diagram.GluedObject]
    {source target : PointedGaloisObject (RootFiber diagram root)}
    (map : source ⟶ target) :
    galoisLevelOfPointedObject diagram root source ⟶
      galoisLevelOfPointedObject diagram root target where
  val := map.val
  comp := map.comp

/-- The retained finite Galois symmetries of a compatible raw deck-limit
point form a section of Mathlib's complete pointed-Galois automorphism system. -/
private noncomputable def retainedSymmetrySection
    [GaloisCategory diagram.GluedObject]
    [FiberFunctor (RootFiber diagram root)]
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (value : (countableDeckSystem diagram root).RawLimit) :
    AutGalois (RootFiber diagram root) := by
  refine ⟨fun object ↦
    UniversalVertex.CompositeDeckTransformation.baseSymmetry
      ((countableDeckSystem diagram root).rawProjection
        (galoisLevelOfPointedObject diagram root object) value).down, ?_⟩
  intro source target map
  let sourceLevel := galoisLevelOfPointedObject diagram root source
  let targetLevel := galoisLevelOfPointedObject diagram root target
  let levelMap := galoisLevelHomOfPointedHom diagram root map
  have compatibility := ConcreteCategory.congr_hom
    (limit.w (deckDiagram diagram root) levelMap) value
  have compatibilityDown := congrArg ULift.down compatibility
  change deckTransition diagram root levelMap
      ((countableDeckSystem diagram root).rawProjection sourceLevel value).down =
    ((countableDeckSystem diagram root).rawProjection targetLevel value).down
      at compatibilityDown
  change
    PreGaloisCategory.autMap map.val
        (UniversalVertex.CompositeDeckTransformation.baseSymmetry
          ((countableDeckSystem diagram root).rawProjection sourceLevel value).down) =
      UniversalVertex.CompositeDeckTransformation.baseSymmetry
        ((countableDeckSystem diagram root).rawProjection targetLevel value).down
  change UniversalVertex.CompositeDeckTransformation.baseSymmetry
      (deckTransition diagram root levelMap
        ((countableDeckSystem diagram root).rawProjection sourceLevel value).down) = _
  exact congrArg UniversalVertex.CompositeDeckTransformation.baseSymmetry
    compatibilityDown

/-- Taking retained finite symmetries in every coordinate is a homomorphism
into the Galois automorphism limit. -/
private noncomputable def retainedSymmetryHom
    [GaloisCategory diagram.GluedObject]
    [FiberFunctor (RootFiber diagram root)]
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    (countableDeckSystem diagram root).RawLimit →*
      AutGalois (RootFiber diagram root) where
  toFun := retainedSymmetrySection diagram root
  map_one' := by
    apply AutGalois.ext (RootFiber diagram root)
    intro object
    change UniversalVertex.CompositeDeckTransformation.baseSymmetry
        (((countableDeckSystem diagram root).rawProjection
          (galoisLevelOfPointedObject diagram root object)) 1).down = 1
    rw [map_one]
    rfl
  map_mul' first second := by
    apply AutGalois.ext (RootFiber diagram root)
    intro object
    change UniversalVertex.CompositeDeckTransformation.baseSymmetry
        (((countableDeckSystem diagram root).rawProjection
          (galoisLevelOfPointedObject diagram root object)) (first * second)).down =
      UniversalVertex.CompositeDeckTransformation.baseSymmetry
          (((countableDeckSystem diagram root).rawProjection
            (galoisLevelOfPointedObject diagram root object)) first).down *
        UniversalVertex.CompositeDeckTransformation.baseSymmetry
          (((countableDeckSystem diagram root).rawProjection
            (galoisLevelOfPointedObject diagram root object)) second).down
    rw [map_mul]
    rfl

/-- Galois reconstruction is contravariant in automorphisms of Galois
objects.  Inversion followed by multiplicative-opposite transport converts
the retained-symmetry homomorphism into the variance expected by `Aut(F)`. -/
private noncomputable def retainedSymmetryOpHom
    [GaloisCategory diagram.GluedObject]
    [FiberFunctor (RootFiber diagram root)]
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    (countableDeckSystem diagram root).RawLimit →*
      (AutGalois (RootFiber diagram root))ᵐᵒᵖ where
  toFun value := MulOpposite.op ((retainedSymmetryHom diagram root value)⁻¹)
  map_one' := by simp
  map_mul' first second := by simp

/-- The pointed representative on the literal inverse limit of the complete
finite-level deck groups. -/
noncomputable def rawTemperedToProfiniteHom
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    (countableDeckSystem diagram root).RawLimit →*
      Aut (RootFiber diagram root) := by
  letI : GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : FiberFunctor (RootFiber diagram root) :=
    SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram root
  exact (autMulEquivAutGalois (RootFiber diagram root)).symm.toMonoidHom.comp
    (retainedSymmetryOpHom diagram root)

/-- If the raw comparison is trivial, every finite Galois symmetry retained by
its deck coordinates is trivial.  This isolates the formal Galois-limit part
of injectivity from the subsequent finite graph-cover separation argument. -/
theorem coordinate_baseSymmetry_eq_one_of_raw_comparison_eq_one
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (value : (countableDeckSystem diagram root).RawLimit)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (comparisonEqualsOne : rawTemperedToProfiniteHom diagram root value = 1) :
    UniversalVertex.CompositeDeckTransformation.baseSymmetry
        (((countableDeckSystem diagram root).rawProjection level value).down) =
      1 := by
  letI : GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : FiberFunctor (RootFiber diagram root) :=
    SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram root
  let pointedLevel : PointedGaloisObject (RootFiber diagram root) :=
    { obj := level.object
      pt := level.point
      isGalois := level.isGalois }
  change (autMulEquivAutGalois (RootFiber diagram root)).symm
      (MulOpposite.op ((retainedSymmetryHom diagram root value)⁻¹)) = 1
    at comparisonEqualsOne
  have mappedComparison := congrArg
    (autMulEquivAutGalois (RootFiber diagram root)) comparisonEqualsOne
  have oppositeInverseEqualsOne :
      MulOpposite.op ((retainedSymmetryHom diagram root value)⁻¹) = 1 := by
    simpa only [MulEquiv.apply_symm_apply, map_one] using mappedComparison
  have inverseEqualsOne :
      (retainedSymmetryHom diagram root value)⁻¹ = 1 := by
    exact MulOpposite.op_injective <| by
      simpa only [MulOpposite.op_one] using oppositeInverseEqualsOne
  have retainedEqualsOne : retainedSymmetryHom diagram root value = 1 :=
    inv_eq_one.mp inverseEqualsOne
  have coordinateEqualsOne := congrArg
    (fun retained : AutGalois (RootFiber diagram root) =>
      retained.val pointedLevel) retainedEqualsOne
  change (retainedSymmetryHom diagram root value).val pointedLevel = 1
  exact coordinateEqualsOne

/-- A nontrivial point of the literal inverse limit is nontrivial in at least
one finite Galois coordinate. -/
theorem exists_rawProjection_ne_one_of_ne_one
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (value : (countableDeckSystem diagram root).RawLimit)
    (valueNontrivial : value ≠ 1) :
    ∃ level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root,
      ((countableDeckSystem diagram root).rawProjection level value).down ≠ 1 := by
  by_contra noNontrivialCoordinate
  apply valueNontrivial
  apply Concrete.limit_ext (deckDiagram diagram root)
  intro level
  change (countableDeckSystem diagram root).rawProjection level value =
    (countableDeckSystem diagram root).rawProjection level 1
  rw [map_one]
  apply ULift.ext
  exact not_ne_iff.mp (not_exists.mp noNontrivialCoordinate level)

/-- Raw inverse-limit coordinates satisfy the concrete deck-transition law. -/
theorem rawProjection_refinement
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (value : (countableDeckSystem diagram root).RawLimit)
    {finer coarser :
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root}
    (refinement : finer ⟶ coarser) :
    deckTransition diagram root refinement
        (((countableDeckSystem diagram root).rawProjection finer value).down) =
      ((countableDeckSystem diagram root).rawProjection coarser value).down := by
  have compatibility := ConcreteCategory.congr_hom
    (limit.w (deckDiagram diagram root) refinement) value
  exact congrArg ULift.down compatibility

/-- A nontrivial coordinate in the kernel of the raw comparison is represented
by a nontrivial reduced loop at that finite level's selected incidence root. -/
theorem exists_nontrivial_coordinate_loop_with_identification_of_raw_comparison_eq_one
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (value : (countableDeckSystem diagram root).RawLimit)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (comparisonEqualsOne : rawTemperedToProfiniteHom diagram root value = 1)
    (coordinateNontrivial :
      ((countableDeckSystem diagram root).rawProjection level value).down ≠ 1) :
    ∃ previous,
      ∃ loop : ReducedWalk (IncidenceGraph diagram root level)
          (IncidenceRoot diagram root level) previous
          (IncidenceRoot diagram root level),
        loop.length ≠ 0 ∧
          UniversalVertex.CompositeDeckTransformation.treePerm
              (((countableDeckSystem diagram root).rawProjection level value).down)
              (UniversalVertex.base (IncidenceGraph diagram root level)
                (IncidenceRoot diagram root level)) =
            ⟨previous, IncidenceRoot diagram root level, loop⟩ := by
  let transformation :=
    ((countableDeckSystem diagram root).rawProjection level value).down
  have symmetryEqualsOne :
      UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation =
        1 :=
    coordinate_baseSymmetry_eq_one_of_raw_comparison_eq_one
      diagram root value level comparisonEqualsOne
  let transformed :=
    UniversalVertex.CompositeDeckTransformation.treePerm transformation
      (UniversalVertex.base (IncidenceGraph diagram root level)
        (IncidenceRoot diagram root level))
  have transformedEquality :
      UniversalVertex.CompositeDeckTransformation.treePerm
          (((countableDeckSystem diagram root).rawProjection level value).down)
          (UniversalVertex.base (IncidenceGraph diagram root level)
            (IncidenceRoot diagram root level)) = transformed :=
    rfl
  have endpointEqualsRoot :
      transformed.endpoint = IncidenceRoot diagram root level := by
    dsimp only [transformed]
    rw [UniversalVertex.CompositeDeckTransformation.endpoint_apply]
    rw [symmetryEqualsOne]
    rw [map_one]
    change IncidenceRoot diagram root level = IncidenceRoot diagram root level
    rfl
  have depthNonzero : transformed.depth ≠ 0 :=
    UniversalVertex.CompositeDeckTransformation.treePerm_base_depth_ne_zero_of_ne_one
      transformation symmetryEqualsOne coordinateNontrivial
  rcases transformed with ⟨previous, current, loop⟩
  change current = IncidenceRoot diagram root level at endpointEqualsRoot
  subst current
  exact ⟨previous, loop, depthNonzero, transformedEquality⟩

/-- A nontrivial coordinate in the kernel of the raw comparison therefore
produces a nontrivial reduced loop at that finite level's selected incidence
root.  This is the exact combinatorial input consumed by finite residual
separation. -/
theorem exists_nontrivial_coordinate_loop_of_raw_comparison_eq_one
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (value : (countableDeckSystem diagram root).RawLimit)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (comparisonEqualsOne : rawTemperedToProfiniteHom diagram root value = 1)
    (coordinateNontrivial :
      ((countableDeckSystem diagram root).rawProjection level value).down ≠ 1) :
    ∃ previous,
      ∃ loop : ReducedWalk (IncidenceGraph diagram root level)
          (IncidenceRoot diagram root level) previous
          (IncidenceRoot diagram root level),
        loop.length ≠ 0 := by
  obtain ⟨previous, loop, nontrivial, _⟩ :=
    exists_nontrivial_coordinate_loop_with_identification_of_raw_comparison_eq_one
      diagram root value level comparisonEqualsOne coordinateNontrivial
  exact ⟨previous, loop, nontrivial⟩

/-- The initial-sheet vertex of the finite separator lies over the selected
root vertex of the finite Galois level. -/
noncomputable def kernelLoopSeparatorRootVertex
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level)) :
    SourceFiniteGraphCoverRealization.VertexIndex diagram root level.object
      (SourceSemiGraphResidualSeparation.separationCover
        (LevelSemiGraph diagram root level) loop)
      (SourceSemiGraphResidualSeparation.separationProjection
        (LevelSemiGraph diagram root level) loop) root :=
  ⟨(level.rootVertex,
      SourceSemiGraphResidualSeparation.initialSheet
        (LevelSemiGraph diagram root level) loop), rfl⟩

/-- The original Galois basepoint represents the orbit component selected by
the initial-sheet separator vertex. -/
noncomputable def kernelLoopSeparatorRootPoint
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level)) :
    SourceActionComponentFiber
      (diagram.vertexAnabelioid root).group
      ((diagram.vertexAnabelioid root).finiteAction
        (level.object.vertexObject root))
      (SourceFiniteGraphCoverRealization.selectedVertexComponent
        diagram root level.object
        (SourceSemiGraphResidualSeparation.separationCover
          (LevelSemiGraph diagram root level) loop)
        (SourceSemiGraphResidualSeparation.separationProjection
          (LevelSemiGraph diagram root level) loop) root
        (kernelLoopSeparatorRootVertex diagram root level loop)) :=
  ⟨level.point, rfl⟩

/-- The finite object of `B(G)` geometrically realizing the selected loop
separator. -/
noncomputable abbrev kernelLoopSeparatorFiniteObject
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level)) : diagram.GluedObject :=
  SourceFiniteGraphCoverRealization.finiteObject diagram root level.object
    (SourceSemiGraphResidualSeparation.separationCover
      (LevelSemiGraph diagram root level) loop)
    (SourceSemiGraphResidualSeparation.separationProjection
      (LevelSemiGraph diagram root level) loop)
    (SourceSemiGraphResidualSeparation.separationProjection_isGraphCovering
      (LevelSemiGraph diagram root level) loop)

/-- Projection of the realized separator object to the original Galois level. -/
noncomputable abbrev kernelLoopSeparatorObjectProjection
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level)) :
    kernelLoopSeparatorFiniteObject diagram root level loop ⟶ level.object :=
  SourceFiniteGraphCoverRealization.finiteObjectProjection diagram root
    level.object
    (SourceSemiGraphResidualSeparation.separationCover
      (LevelSemiGraph diagram root level) loop)
    (SourceSemiGraphResidualSeparation.separationProjection
      (LevelSemiGraph diagram root level) loop)
    (SourceSemiGraphResidualSeparation.separationProjection_isGraphCovering
      (LevelSemiGraph diagram root level) loop)

/-- The point of the realized separator lying over the original Galois
basepoint on the initial sheet. -/
noncomputable abbrev kernelLoopSeparatorFinitePoint
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level)) :
    (RootFiber diagram root).obj
      (kernelLoopSeparatorFiniteObject diagram root level loop) :=
  SourceFiniteGraphCoverRealization.finiteObjectPoint diagram root level.object
    (SourceSemiGraphResidualSeparation.separationCover
      (LevelSemiGraph diagram root level) loop)
    (SourceSemiGraphResidualSeparation.separationProjection
      (LevelSemiGraph diagram root level) loop)
    (SourceSemiGraphResidualSeparation.separationProjection_isGraphCovering
      (LevelSemiGraph diagram root level) loop)
    (kernelLoopSeparatorRootVertex diagram root level loop)
    (kernelLoopSeparatorRootPoint diagram root level loop)

/-- The finite separator is dominated by a pointed Galois level whose
composite projection is a genuine refinement of the original level. -/
theorem exists_kernelLoopSeparator_galois_refinement
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level)) :
    ∃ (finer : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
      (toSeparator : finer.object ⟶
        kernelLoopSeparatorFiniteObject diagram root level loop)
      (refinement : finer ⟶ level),
      refinement.val =
          toSeparator ≫ kernelLoopSeparatorObjectProjection
            diagram root level loop ∧
        (RootFiber diagram root).map toSeparator finer.point =
          kernelLoopSeparatorFinitePoint diagram root level loop := by
  obtain ⟨finer, toSeparator, pointToSeparator, pointToLevel⟩ :=
    SourceFiniteGraphCoverRealization.exists_galoisLevel_refinement_of_point
      diagram root level.object
      (SourceSemiGraphResidualSeparation.separationCover
        (LevelSemiGraph diagram root level) loop)
      (SourceSemiGraphResidualSeparation.separationProjection
        (LevelSemiGraph diagram root level) loop)
      (SourceSemiGraphResidualSeparation.separationProjection_isGraphCovering
        (LevelSemiGraph diagram root level) loop)
      (kernelLoopSeparatorRootVertex diagram root level loop)
      (kernelLoopSeparatorRootPoint diagram root level loop)
  let refinement : finer ⟶ level :=
    ⟨toSeparator ≫ kernelLoopSeparatorObjectProjection
      diagram root level loop, pointToLevel⟩
  exact ⟨finer, toSeparator, refinement, rfl, pointToSeparator⟩

/-- A Galois level dominating the recovered separator maps canonically to
the finite separator semi-graph. -/
noncomputable def kernelLoopSeparatorSemiGraphMap
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level))
    (finer : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (toSeparator : finer.object ⟶
      kernelLoopSeparatorFiniteObject diagram root level loop) :
    (LevelSemiGraph diagram root finer).Hom
      (SourceSemiGraphResidualSeparation.separationCover
        (LevelSemiGraph diagram root level) loop) :=
  (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
    diagram root toSeparator).comp
      (SourceFiniteGraphCoverRealization.finiteObjectCoverComparison
        diagram root level.object
        (SourceSemiGraphResidualSeparation.separationCover
          (LevelSemiGraph diagram root level) loop)
        (SourceSemiGraphResidualSeparation.separationProjection
          (LevelSemiGraph diagram root level) loop)
        (SourceSemiGraphResidualSeparation.separationProjection_isGraphCovering
          (LevelSemiGraph diagram root level) loop))

/-- The Galois-to-separator semi-graph map is proper. -/
theorem kernelLoopSeparatorSemiGraphMap_isProper
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level))
    (finer : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (toSeparator : finer.object ⟶
      kernelLoopSeparatorFiniteObject diagram root level loop) :
    (kernelLoopSeparatorSemiGraphMap
      diagram root level loop finer toSeparator).IsProper :=
  (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition_isProper
    diagram root toSeparator).comp
      (SourceFiniteGraphCoverRealization.finiteObjectCoverComparison_isProper
        diagram root level.object
        (SourceSemiGraphResidualSeparation.separationCover
          (LevelSemiGraph diagram root level) loop)
        (SourceSemiGraphResidualSeparation.separationProjection
          (LevelSemiGraph diagram root level) loop)
        (SourceSemiGraphResidualSeparation.separationProjection_isGraphCovering
          (LevelSemiGraph diagram root level) loop))

/-- The selected finer Galois point maps to the initial-sheet root of the
finite separator. -/
theorem kernelLoopSeparatorSemiGraphMap_rootVertex
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level))
    (finer : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (toSeparator : finer.object ⟶
      kernelLoopSeparatorFiniteObject diagram root level loop)
    (pointToSeparator :
      (RootFiber diagram root).map toSeparator finer.point =
        kernelLoopSeparatorFinitePoint diagram root level loop) :
    (kernelLoopSeparatorSemiGraphMap
      diagram root level loop finer toSeparator).vertexMap finer.rootVertex =
      (kernelLoopSeparatorRootVertex diagram root level loop).1 := by
  let separatorCover :=
    SourceSemiGraphResidualSeparation.separationCover
      (LevelSemiGraph diagram root level) loop
  let separatorProjection :=
    SourceSemiGraphResidualSeparation.separationProjection
      (LevelSemiGraph diagram root level) loop
  let separatorCovering :=
    SourceSemiGraphResidualSeparation.separationProjection_isGraphCovering
      (LevelSemiGraph diagram root level) loop
  have transitionVertex :
      (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
        diagram root toSeparator).vertexMap finer.rootVertex =
        SourceFiniteGraphCoverRealization.finiteObjectPointVertex
          diagram root level.object separatorCover separatorProjection
            separatorCovering
          (kernelLoopSeparatorRootVertex diagram root level loop)
          (kernelLoopSeparatorRootPoint diagram root level loop) := by
    refine Sigma.ext rfl ?_
    exact heq_of_eq (congrArg Quotient.mk'' pointToSeparator)
  change (SourceFiniteGraphCoverRealization.finiteObjectCoverComparison
      diagram root level.object separatorCover separatorProjection
        separatorCovering).vertexMap
      ((SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
        diagram root toSeparator).vertexMap finer.rootVertex) = _
  rw [transitionVertex]
  exact
    SourceFiniteGraphCoverRealization.finiteObjectCoverComparison_finiteObjectPointVertex
      diagram root level.object separatorCover separatorProjection
        separatorCovering
      (kernelLoopSeparatorRootVertex diagram root level loop)
      (kernelLoopSeparatorRootPoint diagram root level loop)

/-- The Galois refinement factors through the separator on complete
semi-graph morphisms. -/
theorem kernelLoopSeparatorSemiGraphMap_factors
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level))
    (finer : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (toSeparator : finer.object ⟶
      kernelLoopSeparatorFiniteObject diagram root level loop)
    (refinement : finer ⟶ level)
    (refinementFactors : refinement.val =
      toSeparator ≫ kernelLoopSeparatorObjectProjection
        diagram root level loop) :
    (kernelLoopSeparatorSemiGraphMap
        diagram root level loop finer toSeparator).comp
      (SourceSemiGraphResidualSeparation.separationProjection
        (LevelSemiGraph diagram root level) loop) =
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition
        diagram root refinement := by
  let separatorCover :=
    SourceSemiGraphResidualSeparation.separationCover
      (LevelSemiGraph diagram root level) loop
  let separatorProjection :=
    SourceSemiGraphResidualSeparation.separationProjection
      (LevelSemiGraph diagram root level) loop
  let separatorCovering :=
    SourceSemiGraphResidualSeparation.separationProjection_isGraphCovering
      (LevelSemiGraph diagram root level) loop
  let toRecovered :=
    SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
      diagram root toSeparator
  let comparison :=
    SourceFiniteGraphCoverRealization.finiteObjectCoverComparison
      diagram root level.object separatorCover separatorProjection
        separatorCovering
  calc
    (toRecovered.comp comparison).comp separatorProjection =
        toRecovered.comp (comparison.comp separatorProjection) :=
      SourceSemiGraph.Hom.comp_assoc _ _ _
    _ = toRecovered.comp
        (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
          diagram root
            (kernelLoopSeparatorObjectProjection
              diagram root level loop)) := by
      rw [SourceFiniteGraphCoverRealization.finiteObjectCoverComparison_factors]
    _ = SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition
        diagram root
          (toSeparator ≫ kernelLoopSeparatorObjectProjection
            diagram root level loop) :=
      (SourceSemiGraphOfAnabelioids.GluedObject.finiteEtaleCoverTransition_comp
        diagram root toSeparator
          (kernelLoopSeparatorObjectProjection
            diagram root level loop)).symm
    _ = SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition
        diagram root refinement := by
      unfold SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition
      rw [← refinementFactors]

/-- The proper semi-graph map to the separator induces a faithful-incidence
graph homomorphism. -/
noncomputable def kernelLoopSeparatorIncidenceMap
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level))
    (finer : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (toSeparator : finer.object ⟶
      kernelLoopSeparatorFiniteObject diagram root level loop) :
    IncidenceGraph diagram root finer →g
      IncidenceNode.incidenceGraph
        (SourceSemiGraphResidualSeparation.separationCover
          (LevelSemiGraph diagram root level) loop) :=
  IncidenceNode.properIncidenceGraphHom (LevelSemiGraph diagram root finer)
    (kernelLoopSeparatorSemiGraphMap
      diagram root level loop finer toSeparator)
    (kernelLoopSeparatorSemiGraphMap_isProper
      diagram root level loop finer toSeparator)

/-- The selected incidence root maps to the initial-sheet separator root. -/
theorem kernelLoopSeparatorIncidenceMap_root
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level))
    (finer : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (toSeparator : finer.object ⟶
      kernelLoopSeparatorFiniteObject diagram root level loop)
    (pointToSeparator :
      (RootFiber diagram root).map toSeparator finer.point =
        kernelLoopSeparatorFinitePoint diagram root level loop) :
    kernelLoopSeparatorIncidenceMap
        diagram root level loop finer toSeparator
        (IncidenceRoot diagram root finer) =
      SourceSemiGraphResidualSeparation.liftIncidenceNode
        (LevelSemiGraph diagram root level) loop
        (IncidenceRoot diagram root level)
        (SourceSemiGraphResidualSeparation.initialSheet
          (LevelSemiGraph diagram root level) loop) := by
  unfold kernelLoopSeparatorIncidenceMap
  rw [IncidenceNode.properIncidenceGraphHom_apply,
    IncidenceNode.properMap_vertex_original]
  exact congrArg (fun vertex => IncidenceNode.vertex (Sum.inl vertex))
    (kernelLoopSeparatorSemiGraphMap_rootVertex
      diagram root level loop finer toSeparator pointToSeparator)

/-- Incidence-node projection through the separator agrees with the direct
Galois refinement. -/
theorem kernelLoopSeparatorIncidenceMap_factors
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level))
    (finer : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (toSeparator : finer.object ⟶
      kernelLoopSeparatorFiniteObject diagram root level loop)
    (refinement : finer ⟶ level)
    (refinementFactors : refinement.val =
      toSeparator ≫ kernelLoopSeparatorObjectProjection
        diagram root level loop)
    (point : IncidenceNode (LevelSemiGraph diagram root finer)) :
    IncidenceNode.properMap
        (SourceSemiGraphResidualSeparation.separationCover
          (LevelSemiGraph diagram root level) loop)
        (SourceSemiGraphResidualSeparation.separationProjection
          (LevelSemiGraph diagram root level) loop)
        (SourceSemiGraphResidualSeparation.separationProjection_isGraphCovering
          (LevelSemiGraph diagram root level) loop).1
        (kernelLoopSeparatorIncidenceMap
          diagram root level loop finer toSeparator point) =
      RefinementIncidenceMap diagram root refinement point := by
  let separatorMap := kernelLoopSeparatorSemiGraphMap
    diagram root level loop finer toSeparator
  let separatorMapProper := kernelLoopSeparatorSemiGraphMap_isProper
    diagram root level loop finer toSeparator
  let separatorProjection :=
    SourceSemiGraphResidualSeparation.separationProjection
      (LevelSemiGraph diagram root level) loop
  let separatorProjectionProper :=
    (SourceSemiGraphResidualSeparation.separationProjection_isGraphCovering
      (LevelSemiGraph diagram root level) loop).1
  have mapEquality : separatorMap.comp separatorProjection =
      SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition
        diagram root refinement :=
    kernelLoopSeparatorSemiGraphMap_factors diagram root level loop finer
      toSeparator refinement refinementFactors
  change IncidenceNode.properMap _ separatorProjection
      separatorProjectionProper
      (IncidenceNode.properMap _ separatorMap separatorMapProper point) = _
  rw [← IncidenceNode.properMap_comp]
  rw [IncidenceNode.properMap_eq_map]
  change IncidenceNode.map (LevelSemiGraph diagram root finer)
      (separatorMap.comp separatorProjection) point =
    IncidenceNode.properMap (LevelSemiGraph diagram root finer)
      (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition
        diagram root refinement)
      (SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel.transition_isProper
        diagram root refinement) point
  rw [IncidenceNode.properMap_eq_map]
  exact congrArg
    (fun map => IncidenceNode.map (LevelSemiGraph diagram root finer) map point)
    mapEquality

/-- Lift the finer Galois universal tree into the separator universal tree. -/
noncomputable def kernelLoopSeparatorTreeMap
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level))
    (finer : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (toSeparator : finer.object ⟶
      kernelLoopSeparatorFiniteObject diagram root level loop)
    (pointToSeparator :
      (RootFiber diagram root).map toSeparator finer.point =
        kernelLoopSeparatorFinitePoint diagram root level loop) :
    IncidenceTreeVertex diagram root finer →
      UniversalVertex
        (IncidenceNode.incidenceGraph
          (SourceSemiGraphResidualSeparation.separationCover
            (LevelSemiGraph diagram root level) loop))
        (SourceSemiGraphResidualSeparation.liftIncidenceNode
          (LevelSemiGraph diagram root level) loop
          (IncidenceRoot diagram root level)
          (SourceSemiGraphResidualSeparation.initialSheet
            (LevelSemiGraph diagram root level) loop)) :=
  fun point => UniversalVertex.castRoot
    (IncidenceNode.incidenceGraph
      (SourceSemiGraphResidualSeparation.separationCover
        (LevelSemiGraph diagram root level) loop))
    (kernelLoopSeparatorIncidenceMap_root
      diagram root level loop finer toSeparator pointToSeparator)
    (UniversalVertex.mapHom
      (IncidenceGraph diagram root finer)
      (IncidenceRoot diagram root finer)
      (IncidenceNode.incidenceGraph
        (SourceSemiGraphResidualSeparation.separationCover
          (LevelSemiGraph diagram root level) loop))
      (kernelLoopSeparatorIncidenceMap
        diagram root level loop finer toSeparator) point)

@[simp]
theorem kernelLoopSeparatorTreeMap_endpoint
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level))
    (finer : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (toSeparator : finer.object ⟶
      kernelLoopSeparatorFiniteObject diagram root level loop)
    (pointToSeparator :
      (RootFiber diagram root).map toSeparator finer.point =
        kernelLoopSeparatorFinitePoint diagram root level loop)
    (point : IncidenceTreeVertex diagram root finer) :
    (kernelLoopSeparatorTreeMap diagram root level loop finer toSeparator
      pointToSeparator point).endpoint =
      kernelLoopSeparatorIncidenceMap
        diagram root level loop finer toSeparator point.endpoint := by
  unfold kernelLoopSeparatorTreeMap
  rw [UniversalVertex.castRoot_endpoint,
    UniversalVertex.mapHom_endpoint]

@[simp]
theorem kernelLoopSeparatorTreeMap_base
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level))
    (finer : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (toSeparator : finer.object ⟶
      kernelLoopSeparatorFiniteObject diagram root level loop)
    (pointToSeparator :
      (RootFiber diagram root).map toSeparator finer.point =
        kernelLoopSeparatorFinitePoint diagram root level loop) :
    kernelLoopSeparatorTreeMap diagram root level loop finer toSeparator
        pointToSeparator
        (UniversalVertex.base (IncidenceGraph diagram root finer)
          (IncidenceRoot diagram root finer)) =
      UniversalVertex.base
        (IncidenceNode.incidenceGraph
          (SourceSemiGraphResidualSeparation.separationCover
            (LevelSemiGraph diagram root level) loop))
        (SourceSemiGraphResidualSeparation.liftIncidenceNode
          (LevelSemiGraph diagram root level) loop
          (IncidenceRoot diagram root level)
          (SourceSemiGraphResidualSeparation.initialSheet
            (LevelSemiGraph diagram root level) loop)) := by
  unfold kernelLoopSeparatorTreeMap
  rw [UniversalVertex.mapHom_base, UniversalVertex.castRoot_base]

/-- The lift from the finer universal tree preserves adjacency. -/
theorem kernelLoopSeparatorTreeMap_adj
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level))
    (finer : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (toSeparator : finer.object ⟶
      kernelLoopSeparatorFiniteObject diagram root level loop)
    (pointToSeparator :
      (RootFiber diagram root).map toSeparator finer.point =
        kernelLoopSeparatorFinitePoint diagram root level loop)
    {first second : IncidenceTreeVertex diagram root finer}
    (adjacent : (UniversalVertex.tree (IncidenceGraph diagram root finer)
      (IncidenceRoot diagram root finer)).Adj first second) :
    (UniversalVertex.tree
      (IncidenceNode.incidenceGraph
        (SourceSemiGraphResidualSeparation.separationCover
          (LevelSemiGraph diagram root level) loop))
      (SourceSemiGraphResidualSeparation.liftIncidenceNode
        (LevelSemiGraph diagram root level) loop
        (IncidenceRoot diagram root level)
        (SourceSemiGraphResidualSeparation.initialSheet
          (LevelSemiGraph diagram root level) loop))).Adj
      (kernelLoopSeparatorTreeMap diagram root level loop finer toSeparator
        pointToSeparator first)
      (kernelLoopSeparatorTreeMap diagram root level loop finer toSeparator
        pointToSeparator second) := by
  unfold kernelLoopSeparatorTreeMap
  apply UniversalVertex.castRoot_adj
  exact UniversalVertex.mapHom_adj _ _ _ _ adjacent

/-- Projecting the separator lift of a finer universal-tree point is exactly
the canonical refinement-tree map to the original level. -/
theorem kernelLoopSeparatorTreeMap_factors
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    {previous : Option (IncidenceNode (LevelSemiGraph diagram root level))}
    (loop : ReducedWalk (IncidenceGraph diagram root level)
      (IncidenceRoot diagram root level) previous
      (IncidenceRoot diagram root level))
    (finer : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (toSeparator : finer.object ⟶
      kernelLoopSeparatorFiniteObject diagram root level loop)
    (refinement : finer ⟶ level)
    (refinementFactors : refinement.val =
      toSeparator ≫ kernelLoopSeparatorObjectProjection
        diagram root level loop)
    (pointToSeparator :
      (RootFiber diagram root).map toSeparator finer.point =
        kernelLoopSeparatorFinitePoint diagram root level loop)
    (point : IncidenceTreeVertex diagram root finer) :
    SourceSemiGraphResidualSeparation.separationTreeProjection
        (LevelSemiGraph diagram root level) loop
        (IncidenceRoot diagram root level)
        (SourceSemiGraphResidualSeparation.initialSheet
          (LevelSemiGraph diagram root level) loop)
        (kernelLoopSeparatorTreeMap diagram root level loop finer toSeparator
          pointToSeparator point) =
      RefinementTreeMap diagram root refinement point := by
  let sourceGraph := IncidenceGraph diagram root finer
  let sourceRoot := IncidenceRoot diagram root finer
  let targetGraph := IncidenceGraph diagram root level
  let targetRoot := IncidenceRoot diagram root level
  let first : IncidenceTreeVertex diagram root finer →
      IncidenceTreeVertex diagram root level := fun value =>
    SourceSemiGraphResidualSeparation.separationTreeProjection
      (LevelSemiGraph diagram root level) loop targetRoot
      (SourceSemiGraphResidualSeparation.initialSheet
        (LevelSemiGraph diagram root level) loop)
      (kernelLoopSeparatorTreeMap diagram root level loop finer toSeparator
        pointToSeparator value)
  let second : IncidenceTreeVertex diagram root finer →
      IncidenceTreeVertex diagram root level :=
    RefinementTreeMap diagram root refinement
  have endpointEquality : ∀ value,
      (first value).endpoint = (second value).endpoint := by
    intro value
    change (SourceSemiGraphResidualSeparation.separationTreeProjection
        (LevelSemiGraph diagram root level) loop targetRoot
        (SourceSemiGraphResidualSeparation.initialSheet
          (LevelSemiGraph diagram root level) loop)
        (kernelLoopSeparatorTreeMap diagram root level loop finer toSeparator
          pointToSeparator value)).endpoint =
      (RefinementTreeMap diagram root refinement value).endpoint
    rw [SourceSemiGraphResidualSeparation.separationTreeProjection_endpoint,
      kernelLoopSeparatorTreeMap_endpoint,
      refinementTreeMap_endpoint]
    exact kernelLoopSeparatorIncidenceMap_factors
      diagram root level loop finer toSeparator refinement refinementFactors
        value.endpoint
  have firstAdjacent : ∀ {value neighbor},
      (UniversalVertex.tree sourceGraph sourceRoot).Adj value neighbor →
        (UniversalVertex.tree targetGraph targetRoot).Adj
          (first value) (first neighbor) := by
    intro value neighbor adjacent
    apply SourceSemiGraphResidualSeparation.separationTreeProjection_adj
    exact kernelLoopSeparatorTreeMap_adj diagram root level loop finer
      toSeparator pointToSeparator adjacent
  have secondAdjacent : ∀ {value neighbor},
      (UniversalVertex.tree sourceGraph sourceRoot).Adj value neighbor →
        (UniversalVertex.tree targetGraph targetRoot).Adj
          (second value) (second neighbor) := by
    intro value neighbor adjacent
    exact refinementTreeMap_adj diagram root refinement adjacent
  have atBase : first (UniversalVertex.base sourceGraph sourceRoot) =
      second (UniversalVertex.base sourceGraph sourceRoot) := by
    change SourceSemiGraphResidualSeparation.separationTreeProjection
        (LevelSemiGraph diagram root level) loop targetRoot
        (SourceSemiGraphResidualSeparation.initialSheet
          (LevelSemiGraph diagram root level) loop)
        (kernelLoopSeparatorTreeMap diagram root level loop finer toSeparator
          pointToSeparator
          (UniversalVertex.base sourceGraph sourceRoot)) =
      RefinementTreeMap diagram root refinement
        (UniversalVertex.base sourceGraph sourceRoot)
    rw [kernelLoopSeparatorTreeMap_base,
      SourceSemiGraphResidualSeparation.separationTreeProjection_base,
      refinementTreeMap_base]
  have mapsEqual := UniversalVertex.map_eq_of_endpoint_eq_adj
    sourceGraph sourceRoot targetGraph targetRoot first second
      endpointEquality firstAdjacent secondAdjacent
      (UniversalVertex.base sourceGraph sourceRoot) atBase
  exact congrFun mapsEqual point

/-- The pointed comparison on the literal deck inverse limit is injective.
Residual finiteness separates a nontrivial kernel loop in a finite graph cover;
compatibility of the Galois coordinates then forces its lifted endpoint to be
both the initial and the noninitial separator sheet. -/
theorem injective_rawTemperedToProfiniteHom
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    Function.Injective (rawTemperedToProfiniteHom diagram root) := by
  apply (injective_iff_map_eq_one _).mpr
  intro value comparisonEqualsOne
  by_contra valueNontrivial
  obtain ⟨level, coordinateNontrivial⟩ :=
    exists_rawProjection_ne_one_of_ne_one diagram root value valueNontrivial
  obtain ⟨previous, loop, loopNontrivial, coarseTransformedEquality⟩ :=
    exists_nontrivial_coordinate_loop_with_identification_of_raw_comparison_eq_one
      diagram root value level comparisonEqualsOne coordinateNontrivial
  obtain ⟨finer, toSeparator, refinement, refinementFactors,
      pointToSeparator⟩ :=
    exists_kernelLoopSeparator_galois_refinement diagram root level loop
  let finerCoordinate : DeckGroup diagram root finer :=
    ((countableDeckSystem diagram root).rawProjection finer value).down
  let finerTransformed : IncidenceTreeVertex diagram root finer :=
    UniversalVertex.CompositeDeckTransformation.treePerm finerCoordinate
      (UniversalVertex.base (IncidenceGraph diagram root finer)
        (IncidenceRoot diagram root finer))
  have finerSymmetryEqualsOne :
      UniversalVertex.CompositeDeckTransformation.baseSymmetry finerCoordinate =
        1 :=
    coordinate_baseSymmetry_eq_one_of_raw_comparison_eq_one
      diagram root value finer comparisonEqualsOne
  have finerEndpointEqualsRoot :
      finerTransformed.endpoint = IncidenceRoot diagram root finer := by
    dsimp only [finerTransformed]
    rw [UniversalVertex.CompositeDeckTransformation.endpoint_apply,
      finerSymmetryEqualsOne, map_one]
    rfl
  have coordinateCompatibility :
      deckTransition diagram root refinement finerCoordinate =
        ((countableDeckSystem diagram root).rawProjection level value).down :=
    rawProjection_refinement diagram root value refinement
  have refinementOfFinerTransformed :
      RefinementTreeMap diagram root refinement finerTransformed =
        ⟨previous, IncidenceRoot diagram root level, loop⟩ := by
    have commutes := deckTransitionToFun_commutes diagram root refinement
      finerCoordinate
      (UniversalVertex.base (IncidenceGraph diagram root finer)
        (IncidenceRoot diagram root finer))
    change RefinementTreeMap diagram root refinement finerTransformed =
      UniversalVertex.CompositeDeckTransformation.treePerm
        (deckTransition diagram root refinement finerCoordinate)
        (RefinementTreeMap diagram root refinement
          (UniversalVertex.base (IncidenceGraph diagram root finer)
            (IncidenceRoot diagram root finer))) at commutes
    rw [refinementTreeMap_base, coordinateCompatibility,
      coarseTransformedEquality] at commutes
    exact commutes
  let separatorPoint := kernelLoopSeparatorTreeMap
    diagram root level loop finer toSeparator pointToSeparator finerTransformed
  let canonicalLoopLift :=
    SourceSemiGraphResidualSeparation.liftUniversalVertex
      (LevelSemiGraph diagram root level) loop loop
      (SourceSemiGraphResidualSeparation.initialSheet
        (LevelSemiGraph diagram root level) loop)
  have separatorProjectionEquality :
      SourceSemiGraphResidualSeparation.separationTreeProjection
          (LevelSemiGraph diagram root level) loop
          (IncidenceRoot diagram root level)
          (SourceSemiGraphResidualSeparation.initialSheet
            (LevelSemiGraph diagram root level) loop) separatorPoint =
        ⟨previous, IncidenceRoot diagram root level, loop⟩ := by
    exact (kernelLoopSeparatorTreeMap_factors diagram root level loop finer
      toSeparator refinement refinementFactors pointToSeparator
      finerTransformed).trans refinementOfFinerTransformed
  have canonicalProjectionEquality :
      SourceSemiGraphResidualSeparation.separationTreeProjection
          (LevelSemiGraph diagram root level) loop
          (IncidenceRoot diagram root level)
          (SourceSemiGraphResidualSeparation.initialSheet
            (LevelSemiGraph diagram root level) loop) canonicalLoopLift =
        ⟨previous, IncidenceRoot diagram root level, loop⟩ := by
    exact SourceSemiGraphResidualSeparation.separationTreeProjection_liftUniversalVertex
      (LevelSemiGraph diagram root level) loop loop
        (SourceSemiGraphResidualSeparation.initialSheet
          (LevelSemiGraph diagram root level) loop)
  have separatorPointEqualsCanonical : separatorPoint = canonicalLoopLift :=
    SourceSemiGraphResidualSeparation.separationTreeProjection_injective
      (LevelSemiGraph diagram root level) loop
      (IncidenceRoot diagram root level)
      (SourceSemiGraphResidualSeparation.initialSheet
        (LevelSemiGraph diagram root level) loop)
      (separatorProjectionEquality.trans canonicalProjectionEquality.symm)
  have separatorEndpointEqualsInitial :
      separatorPoint.endpoint =
        SourceSemiGraphResidualSeparation.liftIncidenceNode
          (LevelSemiGraph diagram root level) loop
          (IncidenceRoot diagram root level)
          (SourceSemiGraphResidualSeparation.initialSheet
            (LevelSemiGraph diagram root level) loop) := by
    dsimp only [separatorPoint]
    rw [kernelLoopSeparatorTreeMap_endpoint, finerEndpointEqualsRoot]
    exact kernelLoopSeparatorIncidenceMap_root diagram root level loop finer
      toSeparator pointToSeparator
  have canonicalEndpointIsNotInitial :=
    SourceSemiGraphResidualSeparation.liftUniversalVertex_loop_endpoint_ne_base
      (LevelSemiGraph diagram root level) loop loopNontrivial
  apply canonicalEndpointIsNotInitial
  change canonicalLoopLift.endpoint = _
  exact (congrArg
    (UniversalVertex.endpoint
      (IncidenceNode.incidenceGraph
        (SourceSemiGraphResidualSeparation.separationCover
          (LevelSemiGraph diagram root level) loop))
      (SourceSemiGraphResidualSeparation.liftIncidenceNode
        (LevelSemiGraph diagram root level) loop
        (IncidenceRoot diagram root level)
        (SourceSemiGraphResidualSeparation.initialSheet
          (LevelSemiGraph diagram root level) loop)))
    separatorPointEqualsCanonical).symm.trans separatorEndpointEqualsInitial

/-- On a pointed Galois object, the comparison acts through the inverse of
the finite symmetry retained by the corresponding deck coordinate.  This is
the concrete coordinate formula used for continuity and separation. -/
theorem rawTemperedToProfiniteHom_app_point
    [GaloisCategory diagram.GluedObject]
    [FiberFunctor (RootFiber diagram root)]
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (value : (countableDeckSystem diagram root).RawLimit)
    (object : PointedGaloisObject (RootFiber diagram root)) :
    (rawTemperedToProfiniteHom diagram root value).hom.app object.obj object.pt =
      (RootFiber diagram root).map
        (UniversalVertex.CompositeDeckTransformation.baseSymmetry
          (((countableDeckSystem diagram root).rawProjection
            (galoisLevelOfPointedObject diagram root object) value).down)⁻¹).hom
        object.pt := by
  rw [show rawTemperedToProfiniteHom diagram root value =
      (autMulEquivAutGalois (RootFiber diagram root)).symm
        ⟨(retainedSymmetryHom diagram root value)⁻¹⟩ by rfl]
  rw [autMulEquivAutGalois_symm_app]
  rfl

/-- The pointed representative `π₁ᵗᵉᵐᵖ(G) → π₁(B(G))`, transported
from the literal deck-group limit to the canonical surjective presentation
used for the tempered topology. -/
noncomputable def temperedToProfiniteHom
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    TemperedDeckGroup diagram root →* Aut (RootFiber diagram root) :=
  (rawTemperedToProfiniteHom diagram root).comp
    (rawDeckLimitContinuousMulEquiv diagram root).symm.toMonoidHom

/-- The pointed tempered-to-profinite comparison is injective. -/
theorem injective_temperedToProfiniteHom
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    Function.Injective (temperedToProfiniteHom diagram root) :=
  (injective_rawTemperedToProfiniteHom diagram root).comp
    (rawDeckLimitContinuousMulEquiv diagram root).symm.injective

/-- Transport the target fiber functor of the pointed comparison along a
chosen basepoint identification. -/
noncomputable def transportedTemperedToProfiniteHom
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (fiber : diagram.GluedObject ⥤ FintypeCat)
    (transport : RootFiber diagram root ≅ fiber) :
    TemperedDeckGroup diagram root →* Aut fiber :=
  transport.conjAut.toMonoidHom.comp (temperedToProfiniteHom diagram root)

/-- The discrepancy between two identifications of the same target fiber
functor. -/
noncomputable def temperedBasepointDiscrepancy
    (fiber : diagram.GluedObject ⥤ FintypeCat)
    (first second : RootFiber diagram root ≅ fiber) : Aut fiber :=
  first.symm ≪≫ second

/-- Replacing the chosen basepoint identification changes the pointed
comparison by inner conjugation, and by nothing else. -/
theorem transportedTemperedToProfiniteHom_eq_conjugate
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (fiber : diagram.GluedObject ⥤ FintypeCat)
    (first second : RootFiber diagram root ≅ fiber)
    (value : TemperedDeckGroup diagram root) :
    transportedTemperedToProfiniteHom diagram root fiber second value =
      temperedBasepointDiscrepancy diagram root fiber first second *
          transportedTemperedToProfiniteHom diagram root fiber first value *
        (temperedBasepointDiscrepancy diagram root fiber first second)⁻¹ := by
  let discrepancy := temperedBasepointDiscrepancy
    diagram root fiber first second
  change second.conjAut (temperedToProfiniteHom diagram root value) =
    discrepancy * first.conjAut (temperedToProfiniteHom diagram root value) *
      discrepancy⁻¹
  have secondEquals : second = first ≪≫ discrepancy := by
    dsimp only [discrepancy, temperedBasepointDiscrepancy]
    simp
  rw [secondEquals, Iso.trans_conjAut]
  ext object point
  rfl

/-- The pointed comparison is continuous for the inverse-limit topology. -/
theorem continuous_temperedToProfiniteHom
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    Continuous (temperedToProfiniteHom diagram root) := by
  letI : GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : FiberFunctor (RootFiber diagram root) :=
    SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram root
  apply continuous_of_continuousAt_one
  rw [continuousAt_def, map_one]
  intro neighborhood neighborhoodAtOne
  obtain ⟨object, objectKernel, objectKernelSubset⟩ :=
    ((nhds_one_has_basis_stabilizers (RootFiber diagram root)).mem_iff'
      neighborhood).mp neighborhoodAtOne
  let level := galoisLevelOfPointedObject diagram root object
  let coordinate : TemperedDeckGroup diagram root →
      DeckGroup diagram root level := fun value ↦
    ((countableDeckSystem diagram root).rawProjection level
      ((rawDeckLimitContinuousMulEquiv diagram root).symm value)).down
  let fixedCoordinate : Set (DeckGroup diagram root level) :=
    { transformation |
      (RootFiber diagram root).map
        (UniversalVertex.CompositeDeckTransformation.baseSymmetry
          transformation⁻¹).hom object.pt = object.pt }
  rw [mem_nhds_iff]
  refine ⟨coordinate ⁻¹' fixedCoordinate, ?_, ?_, ?_⟩
  · intro value valueInPreimage
    apply objectKernelSubset
    change (temperedToProfiniteHom diagram root value).hom.app
      object.obj object.pt = object.pt
    change (rawTemperedToProfiniteHom diagram root
      ((rawDeckLimitContinuousMulEquiv diagram root).symm value)).hom.app
        object.obj object.pt = object.pt
    rw [rawTemperedToProfiniteHom_app_point]
    exact valueInPreimage
  · exact (isOpen_discrete fixedCoordinate).preimage
      ((continuous_of_discreteTopology.comp
        ((countableDeckSystem diagram root).continuous_rawProjection level)).comp
          (rawDeckLimitContinuousMulEquiv diagram root).symm.continuous)
  · change coordinate 1 ∈ fixedCoordinate
    rw [show coordinate 1 = 1 by
      dsimp [coordinate]
      rw [map_one, map_one]
      rfl]
    change (RootFiber diagram root).map (𝟙 object.obj) object.pt = object.pt
    simp

end

end SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

end Iut
