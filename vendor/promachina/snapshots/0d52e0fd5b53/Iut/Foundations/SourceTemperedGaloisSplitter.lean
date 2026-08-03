/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedGraphCoverRealization

/-!
# Replacing a finite tempered splitter by one Galois level

Definition 3.5(ii) only supplies an arbitrary finite glued cover whose local
kernels fix the tempered target.  The cofinal levels used before Proposition
3.6 are pointed connected Galois objects.  A Galois representative of the
complete finite splitter represents every point of its fiber by evaluation;
transport between the evaluation fiber functors proves the same statement at
every vertex and edge.  Consequently its local kernels are contained in the
splitter kernels, so the Galois representative still splits the target.
-/

namespace Iut

universe u

open CategoryTheory

namespace SourceSemiGraphOfAnabelioids.CovObject

variable (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)

/-- Kernel-fixing is transitive through an intermediate action. -/
theorem ActionKernelFixes.trans
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {first middle last : SourceTemperoidAction G}
    (firstFixesMiddle : ActionKernelFixes first middle)
    (middleFixesLast : ActionKernelFixes middle last) :
    ActionKernelFixes first last := by
  intro g fixesFirst point
  exact middleFixesLast g (firstFixesMiddle g fixesFirst) point

/-- One pointed connected Galois object represents all points of the selected
finite splitter.  This is the categorical Galois closure required before
forming the combinatorial universal cover. -/
structure GaloisSplitterRefinement (splitter : diagram.GluedObject) where
  level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root
  evaluation_bijective :
    Function.Bijective (fun morphism : level.object ⟶ splitter ↦
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root).map
        morphism level.point)

/-- Existence of the Galois closure is supplied by the Galois-category
decomposition theorem, not assumed as extra semigraph data. -/
noncomputable def galoisSplitterRefinement
    (splitter : diagram.GluedObject) :
    GaloisSplitterRefinement diagram root splitter := by
  letI : GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root) :=
    SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram root
  let existence :=
    PreGaloisCategory.exists_galois_representative
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root)
      splitter
  let object := Classical.choose existence
  let point := Classical.choose (Classical.choose_spec existence)
  let specification :=
    Classical.choose_spec (Classical.choose_spec existence)
  exact ⟨⟨object, point, specification.1⟩, specification.2⟩

namespace GaloisSplitterRefinement

variable {diagram root} {splitter : diagram.GluedObject}
    (refinement : GaloisSplitterRefinement diagram root splitter)

/-- Evaluation from the representative remains surjective at every vertex.
The proof transports the selected point and the requested target point through
the canonical comparison of evaluation fiber functors. -/
theorem evaluation_surjective_at_vertex
    (vertex : diagram.base.Vertex) :
    Function.Surjective (fun morphism : refinement.level.object ⟶ splitter ↦
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram vertex).map
          morphism
        ((SourceSemiGraphOfAnabelioids.GluedObject.connectedRootFiberIso
          diagram root vertex).hom.app refinement.level.object
            refinement.level.point)) := by
  intro targetPoint
  let comparison :=
    SourceSemiGraphOfAnabelioids.GluedObject.connectedRootFiberIso
      diagram root vertex
  let rootTarget := comparison.inv.app splitter targetPoint
  obtain ⟨morphism, mapsRootPoint⟩ :=
    refinement.evaluation_bijective.2 rootTarget
  refine ⟨morphism, ?_⟩
  have naturality := ConcreteCategory.congr_hom
    (comparison.hom.naturality morphism) refinement.level.point
  change comparison.hom.app splitter
      ((SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root).map
        morphism refinement.level.point) =
    (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram vertex).map
        morphism
      (comparison.hom.app refinement.level.object refinement.level.point)
      at naturality
  rw [show
    (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram root).map
        morphism refinement.level.point = rootTarget from mapsRootPoint]
      at naturality
  change comparison.hom.app splitter rootTarget = _ at naturality
  exact naturality.symm.trans (comparison.inv_hom_id_app_apply splitter targetPoint)

/-- The representative level action has kernel contained in the splitter
kernel at every vertex. -/
theorem vertexActionKernelFixes
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    ActionKernelFixes
      ((finiteCovObject diagram root refinement.level.object).vertexObject vertex)
      ((finiteCovObject diagram root splitter).vertexObject vertex) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  intro element fixes point
  let comparison :=
    SourceSemiGraphOfAnabelioids.GluedObject.connectedRootFiberIso
      diagram root vertex
  let levelPoint :
      ((finiteCovObject diagram root refinement.level.object).vertexObject
        vertex).obj.V.obj :=
    comparison.hom.app refinement.level.object refinement.level.point
  obtain ⟨morphism, mapsPoint⟩ :=
    refinement.evaluation_surjective_at_vertex vertex point
  let map := finiteCovMap diagram root morphism
  have equivariance := ConcreteCategory.congr_hom
    ((map.app vertex).hom.comm element) levelPoint
  calc
    element • point = element • (map.app vertex).hom.hom levelPoint :=
      congrArg (element • ·) mapsPoint.symm
    _ = (map.app vertex).hom.hom (element • levelPoint) :=
      equivariance.symm
    _ = (map.app vertex).hom.hom levelPoint :=
      congrArg (map.app vertex).hom.hom (fixes levelPoint)
    _ = point := mapsPoint

/-- The representative level action has kernel contained in the splitter
kernel at every representative edge action. -/
theorem edgeActionKernelFixes
    (edge : diagram.base.Edge) :
    let reference := coverReferenceBranch diagram root edge
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ActionKernelFixes
      (coverEdgeObject diagram root
        (finiteCovObject diagram root refinement.level.object) edge)
      (coverEdgeObject diagram root
        (finiteCovObject diagram root splitter) edge) := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  dsimp only
  intro element fixes point
  let comparison :=
    SourceSemiGraphOfAnabelioids.GluedObject.connectedRootFiberIso
      diagram root reference.vertex
  let levelPoint :
      (coverEdgeObject diagram root
        (finiteCovObject diagram root refinement.level.object) edge).obj.V.obj :=
    comparison.hom.app refinement.level.object refinement.level.point
  let targetPoint :
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber
        diagram reference.vertex).obj splitter :=
    point
  obtain ⟨morphism, mapsPoint⟩ :=
    refinement.evaluation_surjective_at_vertex reference.vertex targetPoint
  let map := finiteCovMap diagram root morphism
  let edgeMap := reference.temperoidPullback.map
    (map.app reference.vertex)
  change edgeMap.hom.hom levelPoint = targetPoint at mapsPoint
  have mapsEdgePoint : edgeMap.hom.hom levelPoint = point := by
    simpa only [targetPoint] using mapsPoint
  have equivariance := ConcreteCategory.congr_hom
    (edgeMap.hom.comm element) levelPoint
  rw [← mapsEdgePoint]
  exact equivariance.symm.trans
    (congrArg edgeMap.hom.hom (fixes levelPoint))

/-- The Galois representative splits every cover split by the original
finite object. -/
theorem isSplitBy
    {target : diagram.CovObject}
    (split : IsSplitBy diagram root splitter target) :
    IsSplitBy diagram root refinement.level.object target := by
  constructor
  · intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact (refinement.vertexActionKernelFixes vertex).trans (split.1 vertex)
  · intro edge
    let reference := coverReferenceBranch diagram root edge
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    exact (refinement.edgeActionKernelFixes edge).trans (split.2 edge)

end GaloisSplitterRefinement

/-- Every globally bounded tempered cover has a pointed connected Galois level
whose local kernels still split it. -/
theorem exists_galoisLevel_splitting
    {target : diagram.CovObject}
    (tempered : IsGloballyTempered diagram root target) :
    ∃ level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root,
      IsSplitBy diagram root level.object target := by
  obtain ⟨splitter, split⟩ := tempered
  let refinement := galoisSplitterRefinement diagram root splitter
  exact ⟨refinement.level, refinement.isSplitBy split⟩

/-- A connected component selected by `basePoint` admits one pointed Galois
level splitting the entire target whenever that component is the whole target. -/
theorem exists_galoisLevel_splitting_of_isPointConnected
    {target : diagram.CovObject}
    (tempered : IsTempered diagram root target)
    (basePoint : AssociatedQuotient.GeometricPoint target)
    (connected : AssociatedQuotient.IsPointConnected target basePoint) :
    ∃ level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root,
      IsSplitBy diagram root level.object target := by
  obtain ⟨splitter, split⟩ :=
    IsTempered.exists_isSplitBy_of_isPointConnected
      diagram root tempered basePoint connected
  let refinement := galoisSplitterRefinement diagram root splitter
  exact ⟨refinement.level, refinement.isSplitBy split⟩

end SourceSemiGraphOfAnabelioids.CovObject

end Iut
