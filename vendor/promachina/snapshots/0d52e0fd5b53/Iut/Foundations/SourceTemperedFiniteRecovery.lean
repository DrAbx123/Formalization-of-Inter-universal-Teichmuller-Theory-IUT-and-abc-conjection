/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedCoveringCategory

/-!
# Recovery of finite geometric covers

The finite objects of the literal geometric covering category are not merely
the image of a displayed fully faithful functor.  A countable constituent
action with finite carrier canonically determines a finite continuous action,
hence an object of the original anabelioid.  Applying this at every vertex and
lifting the finite edge gluing recovers an object of `B(G)`.

This is the finite-recovery part of Definition 3.5 and Proposition 3.6(ii) of
*Semi-graphs of Anabelioids*.
-/

namespace Iut

universe u

open CategoryTheory
open scoped FintypeCatDiscrete SourceCountableTypeCatDiscrete

namespace SourceTemperoidAction

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A countable continuous action whose carrier is finite, regarded as a
finite continuous action without changing its points or group action. -/
noncomputable def finiteModel (object : SourceTemperoidAction G)
    [Finite object.obj.V.obj] : ContAction FintypeCat.{u} G := by
  letI : Fintype object.obj.V.obj := Fintype.ofFinite object.obj.V.obj
  refine ⟨Action.FintypeCat.ofMulAction G (FintypeCat.of object.obj.V.obj), ?_⟩
  change ContinuousSMul G object.obj.V.obj
  infer_instance

/-- The finite model becomes the original countable action after applying the
finite-carrier inclusion. -/
noncomputable def finiteModelInclusionIso
    (object : SourceTemperoidAction G) [Finite object.obj.V.obj] :
    (finiteInclusion G).obj (finiteModel G object) ≅ object := by
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ (comm := ?_)
  · exact
      { hom := SourceCountableTypeCat.homMk id
        inv := SourceCountableTypeCat.homMk id
        hom_inv_id := rfl
        inv_hom_id := rfl }
  · intro element
    rfl

end SourceTemperoidAction

namespace EtaleFundamentalGroup

/-- Recover a finite cover from a finite-carrier object of its temperification. -/
noncomputable def finiteCoverOfFiniteTemperoid
    (data : EtaleFundamentalGroup.{u})
    (object : SourceTemperoidAction data.group) [Finite object.obj.V.obj] :
    letI := data.coverCategory
    data.Cover := by
  letI := data.coverCategory
  exact (coverActionEquivalence data).inverse.obj
    (SourceTemperoidAction.finiteModel data.group object)

/-- The recovered finite cover returns the original finite-carrier temperoid
object under finite temperification. -/
noncomputable def finiteCoverOfFiniteTemperoidIso
    (data : EtaleFundamentalGroup.{u})
    (object : SourceTemperoidAction data.group) [Finite object.obj.V.obj] :
    letI := data.coverCategory
    data.finiteTemperification.obj
        (data.finiteCoverOfFiniteTemperoid object) ≅ object := by
  letI := data.coverCategory
  exact (SourceTemperoidAction.finiteInclusion data.group).mapIso
      ((coverActionEquivalence data).counitIso.app
        (SourceTemperoidAction.finiteModel data.group object)) ≪≫
    SourceTemperoidAction.finiteModelInclusionIso data.group object

end EtaleFundamentalGroup

namespace SourceSemiGraphOfAnabelioids.CovObject

variable (diagram : SourceSemiGraphOfAnabelioids.{u})

/-- A literal geometric cover is finite when every constituent carrier is
finite.  Edge restrictions are then automatically finite as well. -/
def IsFiniteCover (object : diagram.CovObject) : Prop :=
  ∀ vertex, Finite (object.vertexObject vertex).obj.V.obj

/-- Every object in the displayed finite-cover image has finite constituent
carriers. -/
theorem finiteCovObject_isFiniteCover
    (root : diagram.base.Vertex) (object : diagram.GluedObject) :
    IsFiniteCover diagram (finiteCovObject diagram root object) := by
  intro vertex
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  change Finite
    (((diagram.vertexAnabelioid vertex).fiber.obj
      (object.vertexObject vertex) : Type u))
  infer_instance

/-- Recover the finite cover at one vertex of a finite geometric cover. -/
noncomputable def finiteRecoveryVertexObject
    (object : diagram.CovObject) (finite : IsFiniteCover diagram object)
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    (diagram.vertexAnabelioid vertex).Cover := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI : Finite (object.vertexObject vertex).obj.V.obj := finite vertex
  exact (diagram.vertexAnabelioid vertex).finiteCoverOfFiniteTemperoid
    (object.vertexObject vertex)

/-- Constituentwise comparison between the recovered finite cover and the
original finite geometric action. -/
noncomputable def finiteRecoveryVertexIso
    (object : diagram.CovObject) (finite : IsFiniteCover diagram object)
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    (diagram.vertexAnabelioid vertex).finiteTemperification.obj
        (finiteRecoveryVertexObject diagram object finite vertex) ≅
      object.vertexObject vertex := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI : Finite (object.vertexObject vertex).obj.V.obj := finite vertex
  exact (diagram.vertexAnabelioid vertex).finiteCoverOfFiniteTemperoidIso
    (object.vertexObject vertex)

/-- Compare the edge restriction of a recovered vertex cover with the
original geometric edge restriction. -/
noncomputable def finiteRecoveryEdgeComparison
    (object : diagram.CovObject) (finite : IsFiniteCover diagram object)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (diagram.edgeAnabelioid edge).finiteTemperification.obj
        (branch.pullback.obj
          (finiteRecoveryVertexObject diagram object finite branch.vertex)) ≅
      branch.temperoidPullback.obj (object.vertexObject branch.vertex) := by
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact
    ((SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
      (diagram.branchMorphism branch.branch branch.abuts)).app
        (finiteRecoveryVertexObject diagram object finite branch.vertex)) ≪≫
      branch.temperoidPullback.mapIso
        (finiteRecoveryVertexIso diagram object finite branch.vertex)

/-- Lift the original finite edge gluing through the fully faithful finite
temperification functor. -/
noncomputable def finiteRecoveryGlue
    (object : diagram.CovObject) (finite : IsFiniteCover diagram object)
    {edge : diagram.base.Edge} (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    first.pullback.obj
        (finiteRecoveryVertexObject diagram object finite first.vertex) ≅
      second.pullback.obj
        (finiteRecoveryVertexObject diagram object finite second.vertex) := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact (diagram.edgeAnabelioid edge).finiteTemperification.preimageIso
    ((finiteRecoveryEdgeComparison diagram object finite first).trans
      ((object.glue first second).trans
        (finiteRecoveryEdgeComparison diagram object finite second).symm))

/-- The lifted finite glue maps back to the prescribed geometric glue. -/
theorem finiteRecoveryGlue_image
    (object : diagram.CovObject) (finite : IsFiniteCover diagram object)
    {edge : diagram.base.Edge} (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (diagram.edgeAnabelioid edge).finiteTemperification.map
        (finiteRecoveryGlue diagram object finite first second).hom =
      (finiteRecoveryEdgeComparison diagram object finite first).hom ≫
        (object.glue first second).hom ≫
        (finiteRecoveryEdgeComparison diagram object finite second).inv := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact (diagram.edgeAnabelioid edge).finiteTemperification.map_preimage _

/-- The recovered gluing is reflexive. -/
theorem finiteRecoveryGlue_refl
    (object : diagram.CovObject) (finite : IsFiniteCover diagram object)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    finiteRecoveryGlue diagram object finite branch branch = Iso.refl _ := by
  letI := (diagram.vertexAnabelioid branch.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  ext
  apply (diagram.edgeAnabelioid edge).finiteTemperification.map_injective
  erw [finiteRecoveryGlue_image]
  simp [object.glue_refl]

/-- The recovered gluing obeys the cocycle law. -/
theorem finiteRecoveryGlue_trans
    (object : diagram.CovObject) (finite : IsFiniteCover diagram object)
    {edge : diagram.base.Edge}
    (first second third : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.vertexAnabelioid third.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    (finiteRecoveryGlue diagram object finite first second).trans
        (finiteRecoveryGlue diagram object finite second third) =
      finiteRecoveryGlue diagram object finite first third := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.vertexAnabelioid third.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  ext
  apply (diagram.edgeAnabelioid edge).finiteTemperification.map_injective
  simp only [Iso.trans_hom, Functor.map_comp]
  rw [finiteRecoveryGlue_image, finiteRecoveryGlue_image,
    finiteRecoveryGlue_image]
  have coherence := congrArg Iso.hom (object.glue_trans first second third)
  simp only [Iso.trans_hom] at coherence
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, ← coherence]
  simp only [Category.assoc]

/-- Recover an actual object of `B(G)` from a finite geometric cover. -/
noncomputable def finiteRecoveryObject
    (object : diagram.CovObject) (finite : IsFiniteCover diagram object) :
    diagram.GluedObject where
  vertexObject := finiteRecoveryVertexObject diagram object finite
  glue := finiteRecoveryGlue diagram object finite
  glue_refl := finiteRecoveryGlue_refl diagram object finite
  glue_trans := finiteRecoveryGlue_trans diagram object finite

/-- The finite inclusion of the recovered object has the original gluing,
transported only by the constituent recovery isomorphisms. -/
theorem finiteCovObject_finiteRecovery_glue_hom
    (root : diagram.base.Vertex)
    (object : diagram.CovObject) (finite : IsFiniteCover diagram object)
    {edge : diagram.base.Edge} (first second : diagram.IncidentBranch edge) :
    letI := (diagram.vertexAnabelioid first.vertex).coverCategory
    letI := (diagram.vertexAnabelioid second.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    ((finiteCovObject diagram root
      (finiteRecoveryObject diagram object finite)).glue first second).hom =
      first.temperoidPullback.map
          (finiteRecoveryVertexIso diagram object finite first.vertex).hom ≫
        (object.glue first second).hom ≫
        second.temperoidPullback.map
          (finiteRecoveryVertexIso diagram object finite second.vertex).inv := by
  letI := (diagram.vertexAnabelioid first.vertex).coverCategory
  letI := (diagram.vertexAnabelioid second.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  rw [finiteCovObject_glue_hom]
  dsimp only [finiteRecoveryObject]
  let firstPullbackComparison :=
    (SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
      (diagram.branchMorphism first.branch first.abuts)).app
        (finiteRecoveryVertexObject diagram object finite first.vertex)
  let secondPullbackComparison :=
    (SourcePointedAnabelioidHom.finiteTemperificationPullbackIso
      (diagram.branchMorphism second.branch second.abuts)).app
        (finiteRecoveryVertexObject diagram object finite second.vertex)
  have glueImage := finiteRecoveryGlue_image diagram object finite first second
  calc
    _ = firstPullbackComparison.inv ≫
        ((finiteRecoveryEdgeComparison diagram object finite first).hom ≫
          (object.glue first second).hom ≫
          (finiteRecoveryEdgeComparison diagram object finite second).inv) ≫
        secondPullbackComparison.hom :=
      congrArg (fun middle ↦ firstPullbackComparison.inv ≫ middle ≫
        secondPullbackComparison.hom) glueImage
    _ = _ := by
      simp only [finiteRecoveryEdgeComparison, Iso.trans_hom, Iso.trans_inv,
        Functor.mapIso_hom, Functor.mapIso_inv]
      let firstMap := first.temperoidPullback.map
        (finiteRecoveryVertexIso diagram object finite first.vertex).hom
      let glueMap := (object.glue first second).hom
      let secondMap := second.temperoidPullback.map
        (finiteRecoveryVertexIso diagram object finite second.vertex).inv
      change firstPullbackComparison.inv ≫
          ((firstPullbackComparison.hom ≫ firstMap) ≫ glueMap ≫
            secondMap ≫ secondPullbackComparison.inv ≫
            secondPullbackComparison.hom) =
        firstMap ≫ glueMap ≫ secondMap
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have cancellation := congrArg
        (fun suffix ↦ (firstMap ≫ glueMap ≫ secondMap) ≫ suffix)
        secondPullbackComparison.inv_hom_id
      simpa only [Category.assoc, Category.comp_id] using cancellation

/-- Every finite geometric cover is isomorphic to the finite inclusion of the
recovered object of `B(G)`. -/
noncomputable def finiteRecoveryIso
    (root : diagram.base.Vertex)
    (object : diagram.CovObject) (finite : IsFiniteCover diagram object) :
    finiteCovObject diagram root (finiteRecoveryObject diagram object finite) ≅
      object where
  hom :=
    { app := fun vertex ↦ by
        letI := (diagram.vertexAnabelioid vertex).coverCategory
        exact (finiteRecoveryVertexIso diagram object finite vertex).hom
      naturality := by
        intro edge first second
        letI := (diagram.vertexAnabelioid first.vertex).coverCategory
        letI := (diagram.vertexAnabelioid second.vertex).coverCategory
        letI := (diagram.edgeAnabelioid edge).coverCategory
        rw [finiteCovObject_finiteRecovery_glue_hom]
        let secondIso :=
          finiteRecoveryVertexIso diagram object finite second.vertex
        have mappedCancellation :
            second.temperoidPullback.map secondIso.inv ≫
                second.temperoidPullback.map secondIso.hom = 𝟙 _ := by
          rw [← Functor.map_comp, secondIso.inv_hom_id]
          exact second.temperoidPullback.map_id _
        have transported := congrArg
          (fun suffix ↦
            (first.temperoidPullback.map
                (finiteRecoveryVertexIso diagram object finite first.vertex).hom ≫
              (object.glue first second).hom) ≫ suffix)
          mappedCancellation
        simpa only [secondIso, Category.assoc, Category.comp_id] using
          transported }
  inv :=
    { app := fun vertex ↦ by
        letI := (diagram.vertexAnabelioid vertex).coverCategory
        exact (finiteRecoveryVertexIso diagram object finite vertex).inv
      naturality := by
        intro edge first second
        letI := (diagram.vertexAnabelioid first.vertex).coverCategory
        letI := (diagram.vertexAnabelioid second.vertex).coverCategory
        letI := (diagram.edgeAnabelioid edge).coverCategory
        rw [finiteCovObject_finiteRecovery_glue_hom]
        let firstIso :=
          finiteRecoveryVertexIso diagram object finite first.vertex
        have mappedCancellation :
            first.temperoidPullback.map firstIso.inv ≫
                first.temperoidPullback.map firstIso.hom = 𝟙 _ := by
          rw [← Functor.map_comp, firstIso.inv_hom_id]
          exact first.temperoidPullback.map_id _
        have transported := congrArg
          (fun leading ↦ leading ≫ (object.glue first second).hom ≫
            second.temperoidPullback.map
              (finiteRecoveryVertexIso diagram object finite second.vertex).inv)
          mappedCancellation
        simpa only [firstIso, Category.assoc, Category.id_comp] using
          transported.symm }
  hom_inv_id := by
    apply Hom.ext
    intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact (finiteRecoveryVertexIso diagram object finite vertex).hom_inv_id
  inv_hom_id := by
    apply Hom.ext
    intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact (finiteRecoveryVertexIso diagram object finite vertex).inv_hom_id

@[simp]
theorem finiteRecoveryIso_hom_app
    (root : diagram.base.Vertex)
    (object : diagram.CovObject) (finite : IsFiniteCover diagram object)
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    (finiteRecoveryIso diagram root object finite).hom.app vertex =
      (finiteRecoveryVertexIso diagram object finite vertex).hom :=
  rfl

@[simp]
theorem finiteRecoveryIso_inv_app
    (root : diagram.base.Vertex)
    (object : diagram.CovObject) (finite : IsFiniteCover diagram object)
    (vertex : diagram.base.Vertex) :
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    (finiteRecoveryIso diagram root object finite).inv.app vertex =
      (finiteRecoveryVertexIso diagram object finite vertex).inv :=
  rfl

/-- Essential-surjectivity statement for the finite part: each geometric
finite cover is represented by an object of `B(G)`. -/
theorem exists_finiteInclusion_preimage
    (root : diagram.base.Vertex)
    (object : diagram.CovObject) (finite : IsFiniteCover diagram object) :
    ∃ source : diagram.GluedObject,
      Nonempty ((finiteInclusion diagram root).obj source ≅ object) :=
  ⟨finiteRecoveryObject diagram object finite,
    ⟨finiteRecoveryIso diagram root object finite⟩⟩

end SourceSemiGraphOfAnabelioids.CovObject

end Iut
