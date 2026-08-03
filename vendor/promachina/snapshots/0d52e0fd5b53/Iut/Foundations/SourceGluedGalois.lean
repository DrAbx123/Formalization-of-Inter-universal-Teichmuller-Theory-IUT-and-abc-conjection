/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.GaloisImage
import Iut.Foundations.SourceGluedAnabelioid

/-!
# The connected Galois structure on a glued anabelioid

This file equips the literal glued category `B(G)` of a connected verticial
semi-graph with the fiber functor obtained by evaluation at a chosen vertex.
The only non-pointwise exactness issue is preservation of epimorphisms.  It is
proved using constituent epi-mono image factorizations whose images glue
canonically across every edge.
-/

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace SourceSemiGraphOfAnabelioids.GluedObject

variable {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}

section Images

variable {source target : diagram.GluedObject}
    (morphism : source ⟶ target)

/-- The canonical epi-mono factorization of one verticial component. -/
noncomputable def imageVertexFactorization
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    PreGaloisCategory.ImageFactorization (morphism.app vertex) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI := (diagram.vertexAnabelioid vertex).galoisCategory
  letI := (diagram.vertexAnabelioid vertex).fiberFunctor
  exact PreGaloisCategory.imageFactorization
    (diagram.vertexAnabelioid vertex).fiber (morphism.app vertex)

/-- The image object at one vertex. -/
noncomputable def imageVertexObject (vertex : diagram.base.Vertex) :
    (diagram.vertexAnabelioid vertex).Cover := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact (imageVertexFactorization morphism vertex).image

/-- The epimorphic projection to a verticial image. -/
noncomputable def imageVertexProjection (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    source.vertexObject vertex ⟶ imageVertexObject morphism vertex := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact (imageVertexFactorization morphism vertex).projection

/-- The monomorphic inclusion of a verticial image. -/
noncomputable def imageVertexInclusion (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    imageVertexObject morphism vertex ⟶ target.vertexObject vertex := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact (imageVertexFactorization morphism vertex).inclusion

noncomputable instance imageVertexProjectionEpi
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    Epi (imageVertexProjection morphism vertex) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact (imageVertexFactorization morphism vertex).projection_epi

noncomputable instance imageVertexInclusionMono
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    Mono (imageVertexInclusion morphism vertex) := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact (imageVertexFactorization morphism vertex).inclusion_mono

theorem imageVertex_fac (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    imageVertexProjection morphism vertex ≫
        imageVertexInclusion morphism vertex = morphism.app vertex := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact (imageVertexFactorization morphism vertex).fac

/-- The two pulled-back constituent image factorizations form the square to
which the canonical image-comparison isomorphism applies. -/
theorem imageEdgeSquare
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    first.pullback.map (imageVertexProjection morphism first.vertex) ≫
          first.pullback.map (imageVertexInclusion morphism first.vertex) ≫
          (target.glue first second).hom =
      (source.glue first second).hom ≫
          second.pullback.map (imageVertexProjection morphism second.vertex) ≫
          second.pullback.map (imageVertexInclusion morphism second.vertex) := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  calc
    first.pullback.map (imageVertexProjection morphism first.vertex) ≫
          first.pullback.map (imageVertexInclusion morphism first.vertex) ≫
          (target.glue first second).hom =
        first.pullback.map (morphism.app first.vertex) ≫
          (target.glue first second).hom := by
            rw [← Category.assoc, ← Functor.map_comp, imageVertex_fac]
    _ = (source.glue first second).hom ≫
          second.pullback.map (morphism.app second.vertex) :=
      (morphism.naturality first second).symm
    _ = (source.glue first second).hom ≫
          second.pullback.map (imageVertexProjection morphism second.vertex) ≫
          second.pullback.map (imageVertexInclusion morphism second.vertex) := by
      rw [← Functor.map_comp, imageVertex_fac]

/-- Canonical gluing of the constituent image objects. -/
noncomputable def imageGlue
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    first.pullback.obj (imageVertexObject morphism first.vertex) ≅
      second.pullback.obj (imageVertexObject morphism second.vertex) := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI := (diagram.edgeAnabelioid edge).fiberFunctor
  letI : first.pullback.PreservesEpimorphisms := by
    change (diagram.branchMorphism first.branch first.abuts).pullback.PreservesEpimorphisms
    infer_instance
  letI : second.pullback.PreservesEpimorphisms := by
    change (diagram.branchMorphism second.branch second.abuts).pullback.PreservesEpimorphisms
    infer_instance
  letI : PreservesFiniteLimits first.pullback :=
    (diagram.branchMorphism first.branch first.abuts).preservesFiniteLimits
  letI : PreservesFiniteLimits second.pullback :=
    (diagram.branchMorphism second.branch second.abuts).preservesFiniteLimits
  exact PreGaloisCategory.imageComparisonIso
    (diagram.edgeAnabelioid edge).fiber
    (first.pullback.map (imageVertexProjection morphism first.vertex))
    (first.pullback.map (imageVertexInclusion morphism first.vertex))
    (second.pullback.map (imageVertexProjection morphism second.vertex))
    (second.pullback.map (imageVertexInclusion morphism second.vertex))
    (source.glue first second) (target.glue first second)
    (imageEdgeSquare morphism first second)

lemma imageGlue_hom_comp_inclusion
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (imageGlue morphism first second).hom ≫
        second.pullback.map (imageVertexInclusion morphism second.vertex) =
      first.pullback.map (imageVertexInclusion morphism first.vertex) ≫
        (target.glue first second).hom := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI := (diagram.edgeAnabelioid edge).fiberFunctor
  letI : first.pullback.PreservesEpimorphisms := by
    change (diagram.branchMorphism first.branch first.abuts).pullback.PreservesEpimorphisms
    infer_instance
  letI : second.pullback.PreservesEpimorphisms := by
    change (diagram.branchMorphism second.branch second.abuts).pullback.PreservesEpimorphisms
    infer_instance
  letI : PreservesFiniteLimits first.pullback :=
    (diagram.branchMorphism first.branch first.abuts).preservesFiniteLimits
  letI : PreservesFiniteLimits second.pullback :=
    (diagram.branchMorphism second.branch second.abuts).preservesFiniteLimits
  exact PreGaloisCategory.imageComparison_inclusion
    (diagram.edgeAnabelioid edge).fiber
    (first.pullback.map (imageVertexProjection morphism first.vertex))
    (first.pullback.map (imageVertexInclusion morphism first.vertex))
    (second.pullback.map (imageVertexProjection morphism second.vertex))
    (second.pullback.map (imageVertexInclusion morphism second.vertex))
    (source.glue first second) (target.glue first second)
    (imageEdgeSquare morphism first second)

lemma imageProjection_comp_imageGlue
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    first.pullback.map (imageVertexProjection morphism first.vertex) ≫
        (imageGlue morphism first second).hom =
      (source.glue first second).hom ≫
        second.pullback.map (imageVertexProjection morphism second.vertex) := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI := (diagram.edgeAnabelioid edge).galoisCategory
  letI := (diagram.edgeAnabelioid edge).fiberFunctor
  letI : first.pullback.PreservesEpimorphisms := by
    change (diagram.branchMorphism first.branch first.abuts).pullback.PreservesEpimorphisms
    infer_instance
  letI : second.pullback.PreservesEpimorphisms := by
    change (diagram.branchMorphism second.branch second.abuts).pullback.PreservesEpimorphisms
    infer_instance
  letI : PreservesFiniteLimits first.pullback :=
    (diagram.branchMorphism first.branch first.abuts).preservesFiniteLimits
  letI : PreservesFiniteLimits second.pullback :=
    (diagram.branchMorphism second.branch second.abuts).preservesFiniteLimits
  exact PreGaloisCategory.imageComparison_projection
    (diagram.edgeAnabelioid edge).fiber
    (first.pullback.map (imageVertexProjection morphism first.vertex))
    (first.pullback.map (imageVertexInclusion morphism first.vertex))
    (second.pullback.map (imageVertexProjection morphism second.vertex))
    (second.pullback.map (imageVertexInclusion morphism second.vertex))
    (source.glue first second) (target.glue first second)
    (imageEdgeSquare morphism first second)

lemma imageGlue_refl
    {edge : diagram.base.Edge}
    (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    imageGlue morphism branch branch = Iso.refl _ := by
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI : PreservesFiniteLimits branch.pullback :=
    (diagram.branchMorphism branch.branch branch.abuts).preservesFiniteLimits
  apply Iso.ext
  apply (cancel_mono
    (branch.pullback.map
      (imageVertexInclusion morphism branch.vertex))).1
  rw [imageGlue_hom_comp_inclusion]
  rw [target.glue_refl branch]
  simp

lemma imageGlue_trans
    {edge : diagram.base.Edge}
    (first second third : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.vertexAnabelioid third.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (imageGlue morphism first second).trans
        (imageGlue morphism second third) =
      imageGlue morphism first third := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.vertexAnabelioid third.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI : PreservesFiniteLimits third.pullback :=
    (diagram.branchMorphism third.branch third.abuts).preservesFiniteLimits
  apply Iso.ext
  apply (cancel_mono
    (third.pullback.map
      (imageVertexInclusion morphism third.vertex))).1
  simp only [Iso.trans_hom, Category.assoc]
  rw [imageGlue_hom_comp_inclusion morphism second third]
  rw [← Category.assoc]
  rw [imageGlue_hom_comp_inclusion morphism first second]
  rw [Category.assoc, ← Iso.trans_hom]
  rw [target.glue_trans first second third]
  exact (imageGlue_hom_comp_inclusion morphism first third).symm

/-- The constituent images with their canonical edge comparisons. -/
noncomputable def imageObject : diagram.GluedObject where
  vertexObject := imageVertexObject morphism
  glue := imageGlue morphism
  glue_refl := imageGlue_refl morphism
  glue_trans := imageGlue_trans morphism

/-- The constituent epi projections assemble to a glued morphism. -/
noncomputable def imageProjection :
    source ⟶ imageObject morphism where
  app := imageVertexProjection morphism
  naturality := by
    intro edge first second
    exact (imageProjection_comp_imageGlue morphism first second).symm

/-- The constituent mono inclusions assemble to a glued morphism. -/
noncomputable def imageInclusion :
    imageObject morphism ⟶ target where
  app := imageVertexInclusion morphism
  naturality := imageGlue_hom_comp_inclusion morphism

theorem image_fac :
    imageProjection morphism ≫ imageInclusion morphism = morphism := by
  apply Hom.ext
  intro vertex
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  change imageVertexProjection morphism vertex ≫
      imageVertexInclusion morphism vertex = morphism.app vertex
  exact imageVertex_fac morphism vertex

/-- A glued morphism whose every component is epi is epi. -/
theorem epi_of_componentwise_epi
    {first second : diagram.GluedObject}
    (f : first ⟶ second)
    [∀ vertex,
      letI := (diagram.vertexAnabelioid vertex).coverCategory
      Epi (f.app vertex)] : Epi f := by
  apply Epi.mk
  intro object left right equality
  apply Hom.ext
  intro vertex
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  apply (cancel_epi (f.app vertex)).1
  exact congrArg (fun arrow => arrow.app vertex) equality

/-- A glued morphism whose every component is mono is mono. -/
theorem mono_of_componentwise_mono
    {first second : diagram.GluedObject}
    (f : first ⟶ second)
    [∀ vertex,
      letI := (diagram.vertexAnabelioid vertex).coverCategory
      Mono (f.app vertex)] : Mono f := by
  apply Mono.mk
  intro object left right equality
  apply Hom.ext
  intro vertex
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  apply (cancel_mono (f.app vertex)).1
  exact congrArg (fun arrow => arrow.app vertex) equality

noncomputable instance imageProjectionEpi :
    Epi (imageProjection morphism) := by
  letI : ∀ vertex,
      letI := (diagram.vertexAnabelioid vertex).coverCategory
      Epi ((imageProjection morphism).app vertex) := fun vertex => by
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    change Epi (imageVertexProjection morphism vertex)
    infer_instance
  apply epi_of_componentwise_epi

noncomputable instance imageInclusionMono :
    Mono (imageInclusion morphism) := by
  letI : ∀ vertex,
      letI := (diagram.vertexAnabelioid vertex).coverCategory
      Mono ((imageInclusion morphism).app vertex) := fun vertex => by
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    change Mono (imageVertexInclusion morphism vertex)
    infer_instance
  apply mono_of_componentwise_mono

end Images

section RootFiber

variable (diagram : Iut.SourceSemiGraphOfAnabelioids.{u})

/-- Evaluation at a chosen vertex followed by that constituent's fiber
functor.  Connectedness makes the choice immaterial up to the usual
basepoint ambiguity, while an explicit root gives an actual fiber functor. -/
noncomputable def rootFiber (root : diagram.base.Vertex) :
    diagram.GluedObject ⥤ FintypeCat.{u} := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  exact evaluation (diagram := diagram) root ⋙
    (diagram.vertexAnabelioid root).fiber

noncomputable instance rootFiberPreservesTerminalObjects
    (root : diagram.base.Vertex) :
    PreservesLimitsOfShape (Discrete PEmpty.{1})
      (rootFiber diagram root) := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  letI := (diagram.vertexAnabelioid root).galoisCategory
  letI := (diagram.vertexAnabelioid root).fiberFunctor
  change PreservesLimitsOfShape (Discrete PEmpty.{1})
    (evaluation (diagram := diagram) root ⋙
      (diagram.vertexAnabelioid root).fiber)
  infer_instance

noncomputable instance rootFiberPreservesPullbacks
    (root : diagram.base.Vertex) :
    PreservesLimitsOfShape WalkingCospan (rootFiber diagram root) := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  letI := (diagram.vertexAnabelioid root).galoisCategory
  letI := (diagram.vertexAnabelioid root).fiberFunctor
  change PreservesLimitsOfShape WalkingCospan
    (evaluation (diagram := diagram) root ⋙
      (diagram.vertexAnabelioid root).fiber)
  infer_instance

noncomputable instance rootFiberPreservesFiniteCoproducts
    (root : diagram.base.Vertex) :
    PreservesFiniteCoproducts (rootFiber diagram root) := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  letI := (diagram.vertexAnabelioid root).galoisCategory
  letI := (diagram.vertexAnabelioid root).fiberFunctor
  change PreservesFiniteCoproducts
    (evaluation (diagram := diagram) root ⋙
      (diagram.vertexAnabelioid root).fiber)
  infer_instance

noncomputable instance rootFiberReflectsIsomorphisms
    (root : diagram.base.Vertex) :
    (rootFiber diagram root).ReflectsIsomorphisms := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  letI := (diagram.vertexAnabelioid root).galoisCategory
  letI := (diagram.vertexAnabelioid root).fiberFunctor
  change (evaluation (diagram := diagram) root ⋙
    (diagram.vertexAnabelioid root).fiber).ReflectsIsomorphisms
  infer_instance

/-- If a monomorphism of glued objects is also epi, the fiber of its chosen
direct-summand complement is empty.  Two maps to `1 ⨿ 1` agree after the epi,
so they agree globally; on the complement this would identify the two
disjoint coproduct injections at every hypothetical fiber point. -/
theorem complementFiberIsEmptyOfEpi
    {source target : diagram.GluedObject}
    (root : diagram.base.Vertex)
    (inclusion : source ⟶ target) [Mono inclusion] [Epi inclusion] :
    IsEmpty ((rootFiber diagram root).obj
      (complementObject (diagram := diagram) inclusion)) := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  letI := (diagram.vertexAnabelioid root).galoisCategory
  letI := (diagram.vertexAnabelioid root).fiberFunctor
  let complement := complementObject (diagram := diagram) inclusion
  let complementInclusion :=
    GluedObject.complementInclusion (diagram := diagram) inclusion
  let decomposition :=
    complementCofanIsColimit (diagram := diagram) inclusion
  let terminalObject := terminal diagram.GluedObject
  let doubledTerminal := terminalObject ⨿ terminalObject
  let sourceMap : source ⟶ doubledTerminal :=
    terminal.from source ≫ coprod.inl
  let complementLeft : complement ⟶ doubledTerminal :=
    terminal.from complement ≫ coprod.inl
  let complementRight : complement ⟶ doubledTerminal :=
    terminal.from complement ≫ coprod.inr
  let leftDesc : target ⟶ doubledTerminal :=
    BinaryCofan.IsColimit.desc decomposition sourceMap complementLeft
  let rightDesc : target ⟶ doubledTerminal :=
    BinaryCofan.IsColimit.desc decomposition sourceMap complementRight
  have descEquality : leftDesc = rightDesc := by
    apply (cancel_epi inclusion).1
    dsimp [leftDesc, rightDesc]
    have leftFac :
        inclusion ≫ BinaryCofan.IsColimit.desc decomposition
          sourceMap complementLeft = sourceMap := by
      simpa only [BinaryCofan.mk_inl] using
        BinaryCofan.IsColimit.inl_desc decomposition
          sourceMap complementLeft
    have rightFac :
        inclusion ≫ BinaryCofan.IsColimit.desc decomposition
          sourceMap complementRight = sourceMap := by
      simpa only [BinaryCofan.mk_inl] using
        BinaryCofan.IsColimit.inl_desc decomposition
          sourceMap complementRight
    exact leftFac.trans rightFac.symm
  have complementMapEquality : complementLeft = complementRight := by
    calc
      complementLeft = complementInclusion ≫ leftDesc :=
        (BinaryCofan.IsColimit.inr_desc decomposition _ _).symm
      _ = complementInclusion ≫ rightDesc :=
        congrArg (fun arrow => complementInclusion ≫ arrow) descEquality
      _ = complementRight :=
        BinaryCofan.IsColimit.inr_desc decomposition _ _
  exact
    { false := fun point => by
        let fiber := rootFiber diagram root
        change terminal.from complement ≫ coprod.inl =
          terminal.from complement ≫ coprod.inr at complementMapEquality
        have mappedEquality := congrArg fiber.map complementMapEquality
        simp only [Functor.map_comp] at mappedEquality
        have pointEquality :=
          ConcreteCategory.congr_hom mappedEquality point
        have separated := congrArg
          (fun value =>
            (inv (coprodComparison fiber terminalObject terminalObject)) value)
          pointEquality
        change
          (inv (coprodComparison fiber terminalObject terminalObject))
              ((fiber.map (coprod.inl : terminalObject ⟶ doubledTerminal))
                (fiber.map (terminal.from complement) point)) =
            (inv (coprodComparison fiber terminalObject terminalObject))
              ((fiber.map (coprod.inr : terminalObject ⟶ doubledTerminal))
                (fiber.map (terminal.from complement) point)) at separated
        change
          ((fiber.map (terminal.from complement) ≫
              (fiber.map (coprod.inl : terminalObject ⟶ doubledTerminal) ≫
                inv (coprodComparison fiber terminalObject terminalObject))) point) =
            ((fiber.map (terminal.from complement) ≫
              (fiber.map (coprod.inr : terminalObject ⟶ doubledTerminal) ≫
                inv (coprodComparison fiber terminalObject terminalObject))) point)
          at separated
        rw [map_inl_inv_coprodComparison] at separated
        rw [map_inr_inv_coprodComparison] at separated
        have sumSeparated := congrArg
          (fun value =>
            (Types.binaryCoproductIso
              (fiber.obj terminalObject) (fiber.obj terminalObject)).hom
              ((inv (coprodComparison FintypeCat.incl
                (fiber.obj terminalObject) (fiber.obj terminalObject))) value))
          separated
        change
          (((FintypeCat.incl.map
                (coprod.inl : fiber.obj terminalObject ⟶
                  fiber.obj terminalObject ⨿ fiber.obj terminalObject)) ≫
              inv (coprodComparison FintypeCat.incl
                (fiber.obj terminalObject) (fiber.obj terminalObject)) ≫
              (Types.binaryCoproductIso
                (fiber.obj terminalObject) (fiber.obj terminalObject)).hom)
            (fiber.map (terminal.from complement) point)) =
          (((FintypeCat.incl.map
                (coprod.inr : fiber.obj terminalObject ⟶
                  fiber.obj terminalObject ⨿ fiber.obj terminalObject)) ≫
              inv (coprodComparison FintypeCat.incl
                (fiber.obj terminalObject) (fiber.obj terminalObject)) ≫
              (Types.binaryCoproductIso
                (fiber.obj terminalObject) (fiber.obj terminalObject)).hom)
            (fiber.map (terminal.from complement) point)) at sumSeparated
        have leftMorphism :
            FintypeCat.incl.map
                (coprod.inl : fiber.obj terminalObject ⟶
                  fiber.obj terminalObject ⨿ fiber.obj terminalObject) ≫
                inv (coprodComparison FintypeCat.incl
                  (fiber.obj terminalObject) (fiber.obj terminalObject)) ≫
                (Types.binaryCoproductIso
                  (fiber.obj terminalObject)
                  (fiber.obj terminalObject)).hom =
              (↾Sum.inl) := by
          rw [← Category.assoc, map_inl_inv_coprodComparison]
          exact Types.binaryCoproductIso_inl_comp_hom _ _
        have rightMorphism :
            FintypeCat.incl.map
                (coprod.inr : fiber.obj terminalObject ⟶
                  fiber.obj terminalObject ⨿ fiber.obj terminalObject) ≫
                inv (coprodComparison FintypeCat.incl
                  (fiber.obj terminalObject) (fiber.obj terminalObject)) ≫
                (Types.binaryCoproductIso
                  (fiber.obj terminalObject)
                  (fiber.obj terminalObject)).hom =
              (↾Sum.inr) := by
          rw [← Category.assoc, map_inr_inv_coprodComparison]
          exact Types.binaryCoproductIso_inr_comp_hom _ _
        let terminalPoint := fiber.map (terminal.from complement) point
        have finalEquality :
            (@Sum.inl (fiber.obj terminalObject)
                (fiber.obj terminalObject) terminalPoint) =
              (@Sum.inr (fiber.obj terminalObject)
                (fiber.obj terminalObject) terminalPoint) :=
          (ConcreteCategory.congr_hom leftMorphism terminalPoint).symm.trans <|
            sumSeparated.trans
              (ConcreteCategory.congr_hom rightMorphism terminalPoint)
        cases finalEquality }

/-- Invertibility of a mono-epi in the glued category is detected at the
chosen root.  Its direct-summand complement has empty root fiber, hence is
initial at the root; the root component of the mono is therefore an
isomorphism, and connectedness propagates that fact through the graph. -/
theorem isIso_of_mono_of_epi_at_root
    {source target : diagram.GluedObject}
    (root : diagram.base.Vertex)
    (morphism : source ⟶ target) [Mono morphism] [Epi morphism] :
    IsIso morphism := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  letI := (diagram.vertexAnabelioid root).galoisCategory
  letI := (diagram.vertexAnabelioid root).fiberFunctor
  let complement := complementObject (diagram := diagram) morphism
  have complementFiberEmpty :
      IsEmpty ((diagram.vertexAnabelioid root).fiber.obj
        (complement.vertexObject root)) := by
    change IsEmpty ((rootFiber diagram root).obj
      (complementObject (diagram := diagram) morphism))
    exact complementFiberIsEmptyOfEpi diagram root morphism
  obtain ⟨complementInitial⟩ :=
    (PreGaloisCategory.initial_iff_fiber_empty
      (diagram.vertexAnabelioid root).fiber
      (complement.vertexObject root)).mpr complementFiberEmpty
  let rootCofan := BinaryCofan.mk (morphism.app root)
    (complementVertexInclusion (diagram := diagram) morphism root)
  have rootCofanIsColimit : Nonempty (IsColimit rootCofan) :=
    ⟨complementVertexIsColimit (diagram := diagram) morphism root⟩
  haveI rootComponentIsIso : IsIso (morphism.app root) := by
    exact (BinaryCofan.isColimit_iff_isIso_inl
      complementInitial rootCofan).mp rootCofanIsColimit
  change IsIso ((evaluation (diagram := diagram) root).map morphism) at rootComponentIsIso
  exact isIso_of_reflects_iso morphism
    (evaluation (diagram := diagram) root)

/-- Evaluation at a root preserves epimorphisms.  A morphism is first
factored through its glued image.  If the original arrow is epi, its image
inclusion is both mono and epi and therefore an isomorphism by the preceding
root-complement argument. -/
noncomputable instance evaluationPreservesEpimorphisms
    (root : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid root).coverCategory
    (evaluation (diagram := diagram) root).PreservesEpimorphisms := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  exact
    { preserves := fun morphism _ => by
        haveI imageInclusionEpi : Epi (imageInclusion morphism) :=
          epi_of_epi_fac (image_fac morphism)
        haveI imageInclusionIsIso : IsIso (imageInclusion morphism) :=
          isIso_of_mono_of_epi_at_root diagram root (imageInclusion morphism)
        haveI : IsIso ((imageInclusion morphism).app root) := by
          change IsIso
            ((evaluation (diagram := diagram) root).map
              (imageInclusion morphism))
          infer_instance
        haveI projectionEpi :
            Epi (imageVertexProjection morphism root) :=
          imageVertexProjectionEpi morphism root
        haveI inclusionEpi :
            Epi (imageVertexInclusion morphism root) := by
          change Epi ((imageInclusion morphism).app root)
          infer_instance
        change Epi (morphism.app root)
        rw [← imageVertex_fac morphism root]
        infer_instance }

noncomputable instance rootFiberPreservesEpimorphisms
    (root : diagram.base.Vertex) :
    (rootFiber diagram root).PreservesEpimorphisms := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  letI := (diagram.vertexAnabelioid root).galoisCategory
  letI := (diagram.vertexAnabelioid root).fiberFunctor
  change (evaluation (diagram := diagram) root ⋙
    (diagram.vertexAnabelioid root).fiber).PreservesEpimorphisms
  infer_instance

noncomputable instance rootFiberPreservesFiniteGroupQuotient
    (root : diagram.base.Vertex)
    (G : Type u) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) (rootFiber diagram root) := by
  letI := (diagram.vertexAnabelioid root).coverCategory
  letI := (diagram.vertexAnabelioid root).galoisCategory
  letI := (diagram.vertexAnabelioid root).fiberFunctor
  letI : PreservesColimitsOfShape (SingleObj G)
      (evaluation (diagram := diagram) root) :=
    evaluationPreservesFiniteGroupQuotient
      (diagram := diagram) root G
  change PreservesColimitsOfShape (SingleObj G)
    (evaluation (diagram := diagram) root ⋙
      (diagram.vertexAnabelioid root).fiber)
  infer_instance

/-- The root evaluation composite satisfies all six fiber-functor axioms. -/
noncomputable instance rootFiberFunctor
    (root : diagram.base.Vertex) :
    PreGaloisCategory.FiberFunctor (rootFiber diagram root) where
  preservesTerminalObjects := inferInstance
  preservesPullbacks := inferInstance
  preservesFiniteCoproducts := inferInstance
  preservesEpis := inferInstance
  preservesQuotientsByFiniteGroups G _ _ :=
    rootFiberPreservesFiniteGroupQuotient diagram root G
  reflectsIsos := inferInstance

/-- A connected verticial gluing is a Galois category after choosing a root
vertex. -/
@[reducible]
noncomputable def galoisCategory (root : diagram.base.Vertex) :
    GaloisCategory diagram.GluedObject :=
  { preGaloisCategory (diagram := diagram) with
    hasFiberFunctor :=
      ⟨rootFiber diagram root, ⟨rootFiberFunctor diagram root⟩⟩ }

end RootFiber

end SourceSemiGraphOfAnabelioids.GluedObject

end Iut
