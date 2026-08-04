/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedGaloisSplitter

/-!
# Mapping components of a Galois splitter

The restriction of a connected Galois object to a vertex or edge may have
several orbits, but every one of those orbits is regular modulo the kernel of
the complete local action.  Indeed, global Galois automorphisms commute with
the local action and act transitively on the complete evaluation fiber.

Consequently, if the kernel of a finite Galois level fixes a countable target
action, any selected finite orbit maps equivariantly to that target after one
target point is chosen.  This is the local constituent map needed for the
geometric domination step in Proposition 3.6(ii).
-/

namespace Iut

universe u

open CategoryTheory
open scoped FintypeCatDiscrete SourceCountableTypeCatDiscrete

namespace SourceSemiGraphOfAnabelioids.CovObject

/-- Quotienting by a larger subgroup commutes with left multiplication. -/
theorem quotientMapOfLE_smul
    {G : Type u} [Group G] {first second : Subgroup G}
    (inclusion : first ≤ second) (element : G) (coset : G ⧸ first) :
    Subgroup.quotientMapOfLE inclusion (element • coset) =
      element • Subgroup.quotientMapOfLE inclusion coset := by
  induction coset using Quotient.inductionOn'
  rfl

/-- A selected orbit of a finite action maps equivariantly to a target point
whenever the orbit stabilizer fixes that point. -/
noncomputable def sourceActionComponentMapOfStabilizerFixes
    (G : ProfiniteGrp.{u}) (source : ContAction FintypeCat.{u} G)
    (target : SourceTemperoidAction G)
    (component : SourceActionComponent G source)
    (targetPoint : target.obj.V.obj)
    (stabilizerFixes : ∀ element : G,
      element • component.out = component.out →
        element • targetPoint = targetPoint) :
    SourceActionComponentFiber G source component → target.obj.V.obj :=
  fun point ↦
    let stabilizerInclusion :
        MulAction.stabilizer G component.out ≤
          MulAction.stabilizer G targetPoint := by
      intro element fixes
      rw [MulAction.mem_stabilizer_iff] at fixes ⊢
      exact stabilizerFixes element fixes
    MulAction.ofQuotientStabilizer G targetPoint
      (Subgroup.quotientMapOfLE stabilizerInclusion
        (sourceActionComponentCosetEquiv G source component point))

/-- The component map sends the canonical orbit representative to its chosen
target point. -/
theorem sourceActionComponentMapOfStabilizerFixes_base
    (G : ProfiniteGrp.{u}) (source : ContAction FintypeCat.{u} G)
    (target : SourceTemperoidAction G)
    (component : SourceActionComponent G source)
    (targetPoint : target.obj.V.obj)
    (stabilizerFixes : ∀ element : G,
      element • component.out = component.out →
        element • targetPoint = targetPoint) :
    sourceActionComponentMapOfStabilizerFixes G source target component
        targetPoint stabilizerFixes
        ⟨component.out, Quotient.out_eq' component⟩ =
      targetPoint := by
  let basePoint : SourceActionComponentFiber G source component :=
    ⟨component.out, Quotient.out_eq' component⟩
  let stabilizer := MulAction.stabilizer G component.out
  let stabilizerInclusion : stabilizer ≤
      MulAction.stabilizer G targetPoint := by
    intro element fixes
    rw [MulAction.mem_stabilizer_iff] at fixes ⊢
    exact stabilizerFixes element fixes
  have baseCoset :
      sourceActionComponentCosetEquiv G source component basePoint =
        (QuotientGroup.mk 1 : G ⧸ stabilizer) := by
    apply (sourceActionComponentCosetEquiv G source component).symm.injective
    rw [Equiv.symm_apply_apply]
    apply Subtype.ext
    change component.out = (1 : G) • component.out
    exact (one_smul G component.out).symm
  change MulAction.ofQuotientStabilizer G targetPoint
      (Subgroup.quotientMapOfLE stabilizerInclusion
        (sourceActionComponentCosetEquiv G source component basePoint)) =
    targetPoint
  rw [baseCoset]
  rw [Subgroup.quotientMapOfLE_apply_mk]
  exact MulAction.ofQuotientStabilizer_mk G targetPoint 1 |>.trans
    (one_smul G targetPoint)

/-- The component map is equivariant for the ambient profinite group. -/
theorem sourceActionComponentMapOfStabilizerFixes_smul
    (G : ProfiniteGrp.{u}) (source : ContAction FintypeCat.{u} G)
    (target : SourceTemperoidAction G)
    (component : SourceActionComponent G source)
    (targetPoint : target.obj.V.obj)
    (stabilizerFixes : ∀ element : G,
      element • component.out = component.out →
        element • targetPoint = targetPoint)
    (element : G) (point : SourceActionComponentFiber G source component) :
    sourceActionComponentMapOfStabilizerFixes G source target component
        targetPoint stabilizerFixes (element • point) =
      element • sourceActionComponentMapOfStabilizerFixes G source target
        component targetPoint stabilizerFixes point := by
  let stabilizerInclusion :
      MulAction.stabilizer G component.out ≤
        MulAction.stabilizer G targetPoint := by
    intro groupElement fixes
    rw [MulAction.mem_stabilizer_iff] at fixes ⊢
    exact stabilizerFixes groupElement fixes
  let coset := sourceActionComponentCosetEquiv G source component point
  change MulAction.ofQuotientStabilizer G targetPoint
      (Subgroup.quotientMapOfLE stabilizerInclusion
        (sourceActionComponentCosetEquiv G source component
          (element • point))) =
    element • MulAction.ofQuotientStabilizer G targetPoint
      (Subgroup.quotientMapOfLE stabilizerInclusion
        (sourceActionComponentCosetEquiv G source component point))
  rw [sourceActionComponentCosetEquiv_smul]
  change MulAction.ofQuotientStabilizer G targetPoint
      (Subgroup.quotientMapOfLE stabilizerInclusion
        (element • coset)) =
    element • MulAction.ofQuotientStabilizer G targetPoint
      (Subgroup.quotientMapOfLE stabilizerInclusion
        coset)
  exact (congrArg (MulAction.ofQuotientStabilizer G targetPoint)
    (quotientMapOfLE_smul stabilizerInclusion element coset)).trans
      (MulAction.ofQuotientStabilizer_smul G targetPoint element
        (Subgroup.quotientMapOfLE stabilizerInclusion coset))

/-- A family of selected finite components maps to a target action once a
compatible target point is chosen for every copied component. -/
noncomputable def sourceTemperoidComponentFamilyHomOfStabilizerFixes
    (G : ProfiniteGrp.{u}) (source : ContAction FintypeCat.{u} G)
    (target : SourceTemperoidAction G)
    (Index : Type u) [Countable Index]
    (component : Index → SourceActionComponent G source)
    (targetPoint : Index → target.obj.V.obj)
    (stabilizerFixes : ∀ (index : Index) (element : G),
      element • (component index).out = (component index).out →
        element • targetPoint index = targetPoint index) :
    sourceTemperoidComponentFamilyAction G source Index component ⟶ target :=
  ObjectProperty.homMk
    { hom := SourceCountableTypeCat.homMk (fun point ↦
        sourceActionComponentMapOfStabilizerFixes G source target
          (component point.1) (targetPoint point.1)
          (stabilizerFixes point.1) point.2)
      comm := fun element ↦ by
        apply ConcreteCategory.hom_ext
        intro point
        exact sourceActionComponentMapOfStabilizerFixes_smul
          G source target (component point.1) (targetPoint point.1)
            (stabilizerFixes point.1) element point.2 }

/-- The family map sends the canonical representative in each copied orbit
to the chosen target point. -/
theorem sourceTemperoidComponentFamilyHomOfStabilizerFixes_base
    (G : ProfiniteGrp.{u}) (source : ContAction FintypeCat.{u} G)
    (target : SourceTemperoidAction G)
    (Index : Type u) [Countable Index]
    (component : Index → SourceActionComponent G source)
    (targetPoint : Index → target.obj.V.obj)
    (stabilizerFixes : ∀ (index : Index) (element : G),
      element • (component index).out = (component index).out →
        element • targetPoint index = targetPoint index)
    (index : Index) :
    (sourceTemperoidComponentFamilyHomOfStabilizerFixes G source target
      Index component targetPoint stabilizerFixes).hom.hom
        ⟨index, ⟨(component index).out, Quotient.out_eq' (component index)⟩⟩ =
      targetPoint index := by
  exact sourceActionComponentMapOfStabilizerFixes_base
    G source target (component index) (targetPoint index)
      (stabilizerFixes index)

end SourceSemiGraphOfAnabelioids.CovObject

namespace SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel

open SourceSemiGraphOfAnabelioids.CovObject

variable {diagram : SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex}

/-- Fixing one point of a vertex restriction of a connected Galois level
forces a local group element to fix its complete vertex fiber. -/
theorem vertex_fixes_all_of_fixes
    (level : GaloisLevel diagram root) (vertex : diagram.base.Vertex)
    (element : (diagram.vertexAnabelioid vertex).group)
    (point : ((finiteCovObject diagram root level.object).vertexObject
      vertex).obj.V.obj)
    (fixes : element • point = point) :
    ∀ other : ((finiteCovObject diagram root level.object).vertexObject
      vertex).obj.V.obj, element • other = other := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  letI : GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram vertex) :=
    SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram vertex
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  intro other
  obtain ⟨automorphism, mapsPoint⟩ :=
    (PreGaloisCategory.evaluation_aut_surjective_of_isGalois
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram vertex)
      level.object point) other
  let map := finiteCovMap diagram root automorphism.hom
  change (map.app vertex).hom.hom point = other at mapsPoint
  have equivariance := ConcreteCategory.congr_hom
    ((map.app vertex).hom.comm element) point
  calc
    element • other = element • (map.app vertex).hom.hom point :=
      congrArg (element • ·) mapsPoint.symm
    _ = (map.app vertex).hom.hom (element • point) := equivariance.symm
    _ = (map.app vertex).hom.hom point :=
      congrArg (map.app vertex).hom.hom fixes
    _ = other := mapsPoint

/-- The corresponding regularity statement for the representative edge
restriction of a connected Galois level. -/
theorem edge_fixes_all_of_fixes
    (level : GaloisLevel diagram root) (edge : diagram.base.Edge)
    (element : (diagram.edgeAnabelioid edge).group)
    (point : (SourceSemiGraphOfAnabelioids.CovObject.coverEdgeObject
      diagram root
      (finiteCovObject diagram root level.object) edge).obj.V.obj)
    (fixes : element • point = point) :
    ∀ other : (SourceSemiGraphOfAnabelioids.CovObject.coverEdgeObject
      diagram root
      (finiteCovObject diagram root level.object) edge).obj.V.obj,
      element • other = other := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  letI : GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber
        diagram reference.vertex) :=
    SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor
      diagram reference.vertex
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  intro other
  obtain ⟨automorphism, mapsPoint⟩ :=
    (PreGaloisCategory.evaluation_aut_surjective_of_isGalois
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber
        diagram reference.vertex) level.object point) other
  let map := finiteCovMap diagram root automorphism.hom
  let edgeMap := reference.temperoidPullback.map
    (map.app reference.vertex)
  change edgeMap.hom.hom point = other at mapsPoint
  have equivariance := ConcreteCategory.congr_hom
    (edgeMap.hom.comm element) point
  have mapsEdgePoint : edgeMap.hom.hom point = other := mapsPoint
  rw [← mapsEdgePoint]
  exact equivariance.symm.trans (congrArg edgeMap.hom.hom fixes)

end SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel

namespace SourceSemiGraphOfAnabelioids.CovObject

/-- Kernel splitting by a Galois level implies that the stabilizer of any
vertex point fixes every point of the target vertex action. -/
theorem galoisVertexStabilizerFixesTarget
    {diagram : SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex}
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (target : diagram.CovObject)
    (split : IsSplitBy diagram root level.object target)
    (vertex : diagram.base.Vertex)
    (sourcePoint : ((finiteCovObject diagram root level.object).vertexObject
      vertex).obj.V.obj)
    (element : (diagram.vertexAnabelioid vertex).group)
    (fixes : element • sourcePoint = sourcePoint) :
    ∀ targetPoint : (target.vertexObject vertex).obj.V.obj,
      element • targetPoint = targetPoint := by
  letI := (diagram.vertexAnabelioid vertex).coverCategory
  exact split.1 vertex element
    (level.vertex_fixes_all_of_fixes vertex element sourcePoint fixes)

/-- Kernel splitting by a Galois level gives the analogous stabilizer
statement for every representative edge action. -/
theorem galoisEdgeStabilizerFixesTarget
    {diagram : SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex}
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel diagram root)
    (target : diagram.CovObject)
    (split : IsSplitBy diagram root level.object target)
    (edge : diagram.base.Edge)
    (sourcePoint : (coverEdgeObject diagram root
      (finiteCovObject diagram root level.object) edge).obj.V.obj)
    (element : (diagram.edgeAnabelioid edge).group)
    (fixes : element • sourcePoint = sourcePoint) :
    ∀ targetPoint : (coverEdgeObject diagram root target edge).obj.V.obj,
      element • targetPoint = targetPoint := by
  let reference := coverReferenceBranch diagram root edge
  letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
  letI := (diagram.edgeAnabelioid edge).coverCategory
  exact split.2 edge element
    (level.edge_fixes_all_of_fixes edge element sourcePoint fixes)

end SourceSemiGraphOfAnabelioids.CovObject

end Iut
