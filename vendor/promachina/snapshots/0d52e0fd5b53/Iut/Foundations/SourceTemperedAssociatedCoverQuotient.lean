/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperoidAssociatedQuotient
import Iut.Foundations.SourceTemperedGeometricDeckAction

/-!
# Associated geometric quotients of a deck-equivariant cover

This file applies the carrier-level associated quotient to every constituent
of a geometric cover.  The naturality squares of a deck action make the
original branch gluing descend to the quotient, producing a literal object
of `B^cov(G)` rather than defining it through the action category.

The construction is the quotient-cover step in the proof of *Semi-graphs of
Anabelioids*, Proposition 3.6(ii).
-/

namespace Iut

universe u

open CategoryTheory

namespace SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

variable {Deck : Type u} [Group Deck]
variable {diagram : SourceSemiGraphOfAnabelioids.{u}}

/-- Elementary geometric motion is reversible: invert the local group
element, or traverse the branch gluing in the opposite direction. -/
theorem GeometricPointStep.symm {source : diagram.CovObject}
    {first second : GeometricPoint source}
    (step : GeometricPointStep source first second) :
    GeometricPointStep source second first := by
  cases step with
  | localAction vertex element point =>
      have reverse := GeometricPointStep.localAction
        (source := source) vertex element⁻¹ (element • point)
      simpa using reverse
  | @glue edge left right point =>
      have reverse := GeometricPointStep.glue
        (source := source) right left
        ((source.glue left right).hom.hom.hom point)
      have backEquality :
          (source.glue right left).hom.hom.hom
              ((source.glue left right).hom.hom.hom point) = point := by
        have coherence := congrArg Iso.hom
          (source.glue_trans left right left)
        rw [source.glue_refl] at coherence
        exact ConcreteCategory.congr_hom coherence point
      rw [backEquality] at reverse
      exact reverse

/-- A finite geometric path may be traversed backwards. -/
theorem reachable_symm {source : diagram.CovObject}
    {first second : GeometricPoint source}
    (path : Relation.ReflTransGen (GeometricPointStep source) first second) :
    Relation.ReflTransGen (GeometricPointStep source) second first := by
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | tail path step inductionHypothesis =>
      exact (Relation.ReflTransGen.single step.symm).trans inductionHypothesis

/-- Point-connectedness is independent of the chosen point inside the same
connected geometric cover. -/
theorem IsPointConnected.rebase {source : diagram.CovObject}
    {basePoint : GeometricPoint source}
    (connected : IsPointConnected source basePoint)
    (newBase : GeometricPoint source) :
    IsPointConnected source newBase := by
  intro point
  exact (reachable_symm (connected newBase)).trans (connected point)

/-- A geometric-cover morphism acts on geometric points without changing
their base vertex. -/
def geometricPointMap {source target : diagram.CovObject}
    (map : source ⟶ target) : GeometricPoint source → GeometricPoint target
  | ⟨vertex, point⟩ =>
      ⟨vertex, ConcreteCategory.hom (map.app vertex).hom.hom point⟩

/-- Local orbit motion and branch gluing are both preserved by a geometric
cover morphism. -/
theorem geometricPointStep_map {source target : diagram.CovObject}
    (map : source ⟶ target) {first second : GeometricPoint source}
    (step : GeometricPointStep source first second) :
    GeometricPointStep target
      (geometricPointMap map first) (geometricPointMap map second) := by
  cases step with
  | localAction vertex element point =>
      have mappedStep := GeometricPointStep.localAction
        (source := target) vertex element
          (ConcreteCategory.hom (map.app vertex).hom.hom point)
      have equality :
          ConcreteCategory.hom (map.app vertex).hom.hom (element • point) =
            element • ConcreteCategory.hom (map.app vertex).hom.hom point :=
        ConcreteCategory.congr_hom ((map.app vertex).hom.comm element) point
      rw [← equality] at mappedStep
      exact mappedStep
  | @glue edge first second point =>
      have mappedStep := GeometricPointStep.glue
        (source := target) first second
          (ConcreteCategory.hom (map.app first.vertex).hom.hom point)
      have equality :
          ConcreteCategory.hom (map.app second.vertex).hom.hom
              ((source.glue first second).hom.hom.hom point) =
            (target.glue first second).hom.hom.hom
              (ConcreteCategory.hom (map.app first.vertex).hom.hom point) := by
        exact ConcreteCategory.congr_hom (map.naturality first second) point
      rw [← equality] at mappedStep
      exact mappedStep

/-- Reachability of geometric points is functorial under cover morphisms. -/
theorem reachable_map {source target : diagram.CovObject}
    (map : source ⟶ target) {first second : GeometricPoint source}
    (path : Relation.ReflTransGen (GeometricPointStep source) first second) :
    Relation.ReflTransGen (GeometricPointStep target)
      (geometricPointMap map first) (geometricPointMap map second) := by
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | tail path step inductionHypothesis =>
      exact inductionHypothesis.tail (geometricPointStep_map map step)

/-- A constituentwise surjective morphism carries point-connectedness to its
target.  This is the concrete geometric form of the standard fact that a
quotient of a connected cover is connected. -/
theorem isPointConnected_of_surjective_hom
    {source target : diagram.CovObject}
    (map : source ⟶ target)
    (surjective : ∀ vertex, Function.Surjective (map.app vertex).hom.hom)
    (basePoint : GeometricPoint source)
    (connected : IsPointConnected source basePoint) :
    IsPointConnected target (geometricPointMap map basePoint) := by
  rintro ⟨vertex, point⟩
  obtain ⟨sourcePoint, sourcePointEquality⟩ := surjective vertex point
  have path := reachable_map map (connected ⟨vertex, sourcePoint⟩)
  simpa [geometricPointMap, sourcePointEquality] using path

/-- Two geometric-cover morphisms out of a point-connected source are equal
as soon as they agree at the chosen point.  Equivariance propagates equality
inside a constituent and the gluing naturality squares propagate it across
branches. -/
theorem hom_ext_of_isPointConnected
    {source target : diagram.CovObject}
    (basePoint : GeometricPoint source)
    (connected : IsPointConnected source basePoint)
    {first second : source ⟶ target}
    (atBase :
      ConcreteCategory.hom (first.app basePoint.1).hom.hom basePoint.2 =
        ConcreteCategory.hom (second.app basePoint.1).hom.hom basePoint.2) :
    first = second := by
  let Agree : GeometricPoint source → Prop := fun point ↦
    ConcreteCategory.hom (first.app point.1).hom.hom point.2 =
      ConcreteCategory.hom (second.app point.1).hom.hom point.2
  have stepPreserves : ∀ {sourcePoint targetPoint : GeometricPoint source},
      GeometricPointStep source sourcePoint targetPoint →
        Agree sourcePoint → Agree targetPoint := by
    intro sourcePoint targetPoint step inductionHypothesis
    cases step with
    | localAction vertex element point =>
        change ConcreteCategory.hom (first.app vertex).hom.hom point =
          ConcreteCategory.hom (second.app vertex).hom.hom point
          at inductionHypothesis
        calc
          ConcreteCategory.hom (first.app vertex).hom.hom (element • point) =
              element • ConcreteCategory.hom
                (first.app vertex).hom.hom point :=
            ConcreteCategory.congr_hom
              ((first.app vertex).hom.comm element) point
          _ = element • ConcreteCategory.hom
                (second.app vertex).hom.hom point :=
            congrArg (element • ·) inductionHypothesis
          _ = ConcreteCategory.hom
                (second.app vertex).hom.hom (element • point) :=
            (ConcreteCategory.congr_hom
              ((second.app vertex).hom.comm element) point).symm
    | @glue edge left right point =>
        change ConcreteCategory.hom (first.app left.vertex).hom.hom point =
          ConcreteCategory.hom (second.app left.vertex).hom.hom point
          at inductionHypothesis
        have firstNaturality :=
          ConcreteCategory.congr_hom (first.naturality left right) point
        change ConcreteCategory.hom (first.app right.vertex).hom.hom
              (ConcreteCategory.hom (source.glue left right).hom.hom point) =
            ConcreteCategory.hom (target.glue left right).hom.hom
              (ConcreteCategory.hom (first.app left.vertex).hom.hom point)
          at firstNaturality
        have secondNaturality :=
          ConcreteCategory.congr_hom (second.naturality left right) point
        change ConcreteCategory.hom (second.app right.vertex).hom.hom
              (ConcreteCategory.hom (source.glue left right).hom.hom point) =
            ConcreteCategory.hom (target.glue left right).hom.hom
              (ConcreteCategory.hom (second.app left.vertex).hom.hom point)
          at secondNaturality
        exact firstNaturality.trans <|
          (congrArg (ConcreteCategory.hom
            (target.glue left right).hom.hom) inductionHypothesis).trans
              secondNaturality.symm
  apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
  intro vertex
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext
  intro point
  have path := connected ⟨vertex, point⟩
  have agrees : Agree basePoint → Agree ⟨vertex, point⟩ :=
    path.trans_induction_on
      (fun _ hypothesis ↦ hypothesis)
      (fun step ↦ stepPreserves step)
      (fun _ _ firstPreserves secondPreserves hypothesis ↦
        secondPreserves (firstPreserves hypothesis))
  exact agrees atBase

/-- If the target is point-connected from the image of one source point,
then a cover morphism is surjective on every constituent.  Image membership
is preserved by both kinds of geometric motion because the map is locally
equivariant and commutes with branch gluing. -/
theorem hom_surjective_of_target_isPointConnected
    {source target : diagram.CovObject}
    (map : source ⟶ target)
    (basePoint : GeometricPoint source)
    (targetConnected : IsPointConnected target
      (geometricPointMap map basePoint))
    (vertex : diagram.base.Vertex) :
    Function.Surjective (map.app vertex).hom.hom := by
  let InImage : GeometricPoint target → Prop := fun targetPoint ↦
    ∃ sourcePoint, geometricPointMap map sourcePoint = targetPoint
  have stepPreserves : ∀ {first second : GeometricPoint target},
      GeometricPointStep target first second → InImage first → InImage second := by
    intro first second step inImage
    rcases inImage with ⟨⟨sourceVertex, sourcePoint⟩, equality⟩
    cases step with
    | localAction targetVertex element targetPoint =>
        have vertexEquality : sourceVertex = targetVertex :=
          Sigma.mk.inj_iff.mp equality |>.1
        subst sourceVertex
        have pointEquality :
            ConcreteCategory.hom (map.app targetVertex).hom.hom sourcePoint =
              targetPoint :=
          eq_of_heq (Sigma.mk.inj_iff.mp equality |>.2)
        refine ⟨⟨targetVertex, element • sourcePoint⟩, ?_⟩
        change (⟨targetVertex,
          ConcreteCategory.hom (map.app targetVertex).hom.hom
            (element • sourcePoint)⟩ : GeometricPoint target) =
          ⟨targetVertex, element • targetPoint⟩
        apply Sigma.ext
        · rfl
        apply heq_of_eq
        calc
          ConcreteCategory.hom (map.app targetVertex).hom.hom
              (element • sourcePoint) =
            element • ConcreteCategory.hom
              (map.app targetVertex).hom.hom sourcePoint :=
            ConcreteCategory.congr_hom
              ((map.app targetVertex).hom.comm element) sourcePoint
          _ = element • targetPoint := congrArg (element • ·) pointEquality
    | @glue edge left right targetPoint =>
        have vertexEquality : sourceVertex = left.vertex :=
          Sigma.mk.inj_iff.mp equality |>.1
        subst sourceVertex
        have pointEquality :
            ConcreteCategory.hom (map.app left.vertex).hom.hom sourcePoint =
              targetPoint :=
          eq_of_heq (Sigma.mk.inj_iff.mp equality |>.2)
        refine ⟨⟨right.vertex,
          ConcreteCategory.hom (source.glue left right).hom.hom sourcePoint⟩,
          ?_⟩
        change (⟨right.vertex,
          ConcreteCategory.hom (map.app right.vertex).hom.hom
            (ConcreteCategory.hom
              (source.glue left right).hom.hom sourcePoint)⟩ :
              GeometricPoint target) =
          ⟨right.vertex,
            ConcreteCategory.hom (target.glue left right).hom.hom targetPoint⟩
        apply Sigma.ext
        · rfl
        apply heq_of_eq
        have naturality :=
          ConcreteCategory.congr_hom (map.naturality left right) sourcePoint
        change ConcreteCategory.hom (map.app right.vertex).hom.hom
              (ConcreteCategory.hom
                (source.glue left right).hom.hom sourcePoint) =
            ConcreteCategory.hom (target.glue left right).hom.hom
              (ConcreteCategory.hom
                (map.app left.vertex).hom.hom sourcePoint)
          at naturality
        exact naturality.trans <|
          congrArg (ConcreteCategory.hom
            (target.glue left right).hom.hom) pointEquality
  intro point
  have path := targetConnected ⟨vertex, point⟩
  have inImage : InImage (geometricPointMap map basePoint) →
      InImage ⟨vertex, point⟩ :=
    path.trans_induction_on
      (fun _ hypothesis ↦ hypothesis)
      (fun step ↦ stepPreserves step)
      (fun _ _ firstPreserves secondPreserves hypothesis ↦
        secondPreserves (firstPreserves hypothesis))
  rcases inImage ⟨basePoint, rfl⟩ with
    ⟨⟨sourceVertex, sourcePoint⟩, equality⟩
  have vertexEquality : sourceVertex = vertex :=
    Sigma.mk.inj_iff.mp equality |>.1
  subst sourceVertex
  exact ⟨sourcePoint, eq_of_heq (Sigma.mk.inj_iff.mp equality |>.2)⟩

/-! ## Deck action on maps from a connected universal source -/

/-- Evaluate a geometric-cover morphism at a chosen source point. -/
def homEvaluation {source target : diagram.CovObject}
    (basePoint : GeometricPoint source) :
    (source ⟶ target) → (target.vertexObject basePoint.1).obj.V.obj :=
  fun map ↦ ConcreteCategory.hom (map.app basePoint.1).hom.hom basePoint.2

/-- Evaluation at one point is injective when the source is point-connected. -/
theorem homEvaluation_injective {source target : diagram.CovObject}
    (basePoint : GeometricPoint source)
    (connected : IsPointConnected source basePoint) :
    Function.Injective (homEvaluation (target := target) basePoint) := by
  intro first second equality
  exact hom_ext_of_isPointConnected basePoint connected equality

/-- The maps from a point-connected source to a countable geometric cover
form a countable type: one point determines the complete map. -/
@[reducible]
noncomputable def homCountable {source target : diagram.CovObject}
    (basePoint : GeometricPoint source)
    (connected : IsPointConnected source basePoint) :
    Countable (source ⟶ target) :=
  Function.Injective.countable (homEvaluation_injective basePoint connected)

/-- Deck transformations act on maps out of the source by inverse
precomposition.  This is the action for which evaluation of `(source × Hom)`
is invariant under the diagonal deck action. -/
@[reducible]
noncomputable def homDeckMulAction
    (source target : diagram.CovObject) (deckAction : Deck →* Aut source) :
    MulAction Deck (source ⟶ target) where
  smul transformation map := (deckAction transformation).inv ≫ map
  one_smul map := by
    apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
    intro vertex
    change ((deckAction 1).inv ≫ map).app vertex = map.app vertex
    rw [map_one]
    rfl
  mul_smul first second map := by
    apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
    intro vertex
    change ((deckAction (first * second)).inv ≫ map).app vertex =
      ((deckAction first).inv ≫ (deckAction second).inv ≫ map).app vertex
    rw [map_mul]
    rfl

/-- Two points in the same local orbit are joined by one elementary local
motion.  This is the point-level counterpart of equality in the component
quotient. -/
theorem reachable_of_same_component
    (source : diagram.CovObject) (vertex : diagram.base.Vertex)
    (first second : (source.vertexObject vertex).obj.V.obj)
    (sameComponent :
      (Quotient.mk'' first :
          SourceSemiGraphOfAnabelioids.CovObject.ActionComponent
            (source.vertexObject vertex)) =
        Quotient.mk'' second) :
    Relation.ReflTransGen (GeometricPointStep source)
      ⟨vertex, first⟩ ⟨vertex, second⟩ := by
  have inOrbit : second ∈
      MulAction.orbit (diagram.vertexAnabelioid vertex).group first := by
    rw [← MulAction.orbitRel_apply, ← Quotient.eq'']
    exact sameComponent.symm
  obtain ⟨element, equality⟩ := MulAction.mem_orbit_iff.mp inOrbit
  have step := GeometricPointStep.localAction
    (source := source) vertex element first
  rw [equality] at step
  exact Relation.ReflTransGen.single step

/-- Adjacency of the orbit-component semi-graph lifts to point-level
reachability.  The proof chooses one representative of the intervening edge
orbit, transports it to both incident vertex constituents, and uses local
orbit motion before and after the gluing step. -/
theorem reachable_of_coverAdjacent
    (root : diagram.base.Vertex) (source : diagram.CovObject)
    (firstVertex secondVertex : diagram.base.Vertex)
    (firstPoint : (source.vertexObject firstVertex).obj.V.obj)
    (secondPoint : (source.vertexObject secondVertex).obj.V.obj)
    (adjacent :
      (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph
        diagram root source).Adjacent
          ⟨firstVertex, Quotient.mk'' firstPoint⟩
          ⟨secondVertex, Quotient.mk'' secondPoint⟩) :
    Relation.ReflTransGen (GeometricPointStep source)
      ⟨firstVertex, firstPoint⟩ ⟨secondVertex, secondPoint⟩ := by
  rcases adjacent with
    ⟨⟨edge, component⟩, firstBranch, secondBranch, distinct,
      firstAbuts, secondAbuts⟩
  change (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph
      diagram root source).coincidence
        ⟨edge, component⟩ firstBranch =
      some ⟨firstVertex, Quotient.mk'' firstPoint⟩ at firstAbuts
  change (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph
      diagram root source).coincidence
        ⟨edge, component⟩ secondBranch =
      some ⟨secondVertex, Quotient.mk'' secondPoint⟩ at secondAbuts
  unfold SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph at firstAbuts
  unfold SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph at secondAbuts
  change (match firstBaseAbuts :
      diagram.base.coincidence edge firstBranch with
    | none => none
    | some vertex => some (⟨vertex,
        SourceSemiGraphOfAnabelioids.CovObject.coverComponentMap
          diagram root source
            (⟨firstBranch, vertex, firstBaseAbuts⟩ :
              diagram.IncidentBranch edge) component⟩ :
        SourceSemiGraphOfAnabelioids.CovObject.CoverVertex diagram source)) =
      some (⟨firstVertex, Quotient.mk'' firstPoint⟩ :
        SourceSemiGraphOfAnabelioids.CovObject.CoverVertex diagram source)
      at firstAbuts
  change (match secondBaseAbuts :
      diagram.base.coincidence edge secondBranch with
    | none => none
    | some vertex => some (⟨vertex,
        SourceSemiGraphOfAnabelioids.CovObject.coverComponentMap
          diagram root source
            (⟨secondBranch, vertex, secondBaseAbuts⟩ :
              diagram.IncidentBranch edge) component⟩ :
        SourceSemiGraphOfAnabelioids.CovObject.CoverVertex diagram source)) =
      some (⟨secondVertex, Quotient.mk'' secondPoint⟩ :
        SourceSemiGraphOfAnabelioids.CovObject.CoverVertex diagram source)
      at secondAbuts
  split at firstAbuts
  next noFirstVertex => cases firstAbuts
  next actualFirstVertex firstBaseAbuts =>
    split at secondAbuts
    next noSecondVertex => cases secondAbuts
    next actualSecondVertex secondBaseAbuts =>
      have firstVertexEquality : actualFirstVertex = firstVertex :=
        (Sigma.mk.inj_iff.mp (Option.some.inj firstAbuts)).1
      have secondVertexEquality : actualSecondVertex = secondVertex :=
        (Sigma.mk.inj_iff.mp (Option.some.inj secondAbuts)).1
      subst actualFirstVertex
      subst actualSecondVertex
      let first : diagram.IncidentBranch edge :=
        ⟨firstBranch, firstVertex, firstBaseAbuts⟩
      let second : diagram.IncidentBranch edge :=
        ⟨secondBranch, secondVertex, secondBaseAbuts⟩
      let reference :=
        SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
          diagram root edge
      let edgePoint := component.out
      let firstGluePoint : (source.vertexObject firstVertex).obj.V.obj :=
        (source.glue reference first).hom.hom.hom edgePoint
      let secondGluePoint : (source.vertexObject secondVertex).obj.V.obj :=
        (source.glue reference second).hom.hom.hom edgePoint
      have firstComponentEquality :
          (Quotient.mk'' firstPoint :
              SourceSemiGraphOfAnabelioids.CovObject.ActionComponent
                (source.vertexObject firstVertex)) =
            Quotient.mk'' firstGluePoint := by
        have fromIncidence :
            SourceSemiGraphOfAnabelioids.CovObject.coverComponentMap
                diagram root source first component =
              Quotient.mk'' firstPoint :=
          eq_of_heq (Sigma.mk.inj_iff.mp
            (Option.some.inj firstAbuts)).2
        rw [← fromIncidence]
        unfold SourceSemiGraphOfAnabelioids.CovObject.coverComponentMap
        rw [← Quotient.out_eq' component]
        rfl
      have secondComponentEquality :
          (Quotient.mk'' secondGluePoint :
              SourceSemiGraphOfAnabelioids.CovObject.ActionComponent
                (source.vertexObject secondVertex)) =
            Quotient.mk'' secondPoint := by
        have fromIncidence :
            SourceSemiGraphOfAnabelioids.CovObject.coverComponentMap
                diagram root source second component =
              Quotient.mk'' secondPoint :=
          eq_of_heq (Sigma.mk.inj_iff.mp
            (Option.some.inj secondAbuts)).2
        rw [← fromIncidence]
        unfold SourceSemiGraphOfAnabelioids.CovObject.coverComponentMap
        rw [← Quotient.out_eq' component]
        rfl
      have firstReach := reachable_of_same_component source firstVertex
        firstPoint firstGluePoint firstComponentEquality
      have glueStep : GeometricPointStep source
          ⟨firstVertex, firstGluePoint⟩
          ⟨secondVertex, secondGluePoint⟩ := by
        have rawStep := GeometricPointStep.glue
          (source := source) first second firstGluePoint
        have glueEquality :
            (source.glue first second).hom.hom.hom firstGluePoint =
              secondGluePoint := by
          have coherence := congrArg Iso.hom
            (source.glue_trans reference first second)
          exact ConcreteCategory.congr_hom coherence edgePoint
        rw [glueEquality] at rawStep
        exact rawStep
      have secondReach := reachable_of_same_component source secondVertex
        secondGluePoint secondPoint secondComponentEquality
      exact firstReach.trans <|
        (Relation.ReflTransGen.single glueStep).trans secondReach

/-- Connectedness of the orbit-component semi-graph upgrades to literal
point-connectedness of the geometric cover.  No choice made here enters the
statement: representatives are used only to lift a component path, and local
orbit motion connects them to the prescribed endpoints. -/
theorem isPointConnected_of_coverSemiGraph_isConnected
    (root : diagram.base.Vertex) (source : diagram.CovObject)
    (basePoint : GeometricPoint source)
    (connected :
      (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph
        diagram root source).IsConnected) :
    IsPointConnected source basePoint := by
  intro targetPoint
  let baseComponent :
      (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph
        diagram root source).Vertex :=
    ⟨basePoint.1, Quotient.mk'' basePoint.2⟩
  let targetComponent :
      (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph
        diagram root source).Vertex :=
    ⟨targetPoint.1, Quotient.mk'' targetPoint.2⟩
  rcases connected with verticial | isolated
  · let representative :
        (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph
          diagram root source).Vertex → GeometricPoint source :=
      fun component ↦ ⟨component.1, component.2.out⟩
    have componentPath := verticial.2.2 baseComponent targetComponent
    have representativePath :
        Relation.ReflTransGen (GeometricPointStep source)
          (representative baseComponent)
          (representative targetComponent) := by
      apply componentPath.lift' representative
      rintro ⟨firstVertex, firstComponent⟩
        ⟨secondVertex, secondComponent⟩ adjacent
      have firstEquality :
          (⟨firstVertex, Quotient.mk'' firstComponent.out⟩ :
              SourceSemiGraphOfAnabelioids.CovObject.CoverVertex
                diagram source) = ⟨firstVertex, firstComponent⟩ := by
        exact congrArg
          (fun component ↦
            (⟨firstVertex, component⟩ :
              SourceSemiGraphOfAnabelioids.CovObject.CoverVertex
                diagram source))
          (Quotient.out_eq' firstComponent)
      have secondEquality :
          (⟨secondVertex, Quotient.mk'' secondComponent.out⟩ :
              SourceSemiGraphOfAnabelioids.CovObject.CoverVertex
                diagram source) = ⟨secondVertex, secondComponent⟩ := by
        exact congrArg
          (fun component ↦
            (⟨secondVertex, component⟩ :
              SourceSemiGraphOfAnabelioids.CovObject.CoverVertex
                diagram source))
          (Quotient.out_eq' secondComponent)
      apply reachable_of_coverAdjacent root source firstVertex secondVertex
        firstComponent.out secondComponent.out
      rwa [firstEquality, secondEquality]
    have reachRepresentativeBase :=
      reachable_of_same_component source basePoint.1 basePoint.2
        baseComponent.2.out (Quotient.out_eq' baseComponent.2).symm
    have reachTarget :=
      reachable_of_same_component source targetPoint.1
        targetComponent.2.out targetPoint.2
          (Quotient.out_eq' targetComponent.2)
    exact reachRepresentativeBase.trans <|
      representativePath.trans reachTarget
  · letI : IsEmpty
        (SourceSemiGraphOfAnabelioids.CovObject.coverSemiGraph
          diagram root source).Vertex := isolated.1
    exact isEmptyElim baseComponent

/-- The deck action on one vertex constituent, obtained by evaluating the
deck-equivariant geometric cover. -/
noncomputable def vertexDeckAction
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (vertex : diagram.base.Vertex) :
    Deck →* Aut (source.vertexObject vertex) :=
  ((SourceSemiGraphOfAnabelioids.CovObject.evaluation
    (diagram := diagram) vertex).mapAut source).comp deckAction

/-- Restrict the evaluated deck action from a vertex to an incident edge. -/
noncomputable def branchDeckAction
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    Deck →* Aut
      (branch.temperoidPullback.obj
        (source.vertexObject branch.vertex)) :=
  (branch.temperoidPullback.mapAut
    (source.vertexObject branch.vertex)).comp
      (vertexDeckAction source deckAction branch.vertex)

/-- Naturality of a geometric deck transformation is precisely the
equivariance condition needed to descend a branch-gluing isomorphism. -/
theorem glue_hom_commutes
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge)
    (transformation : Deck) :
    (branchDeckAction source deckAction first transformation).hom ≫
        (source.glue first second).hom =
      (source.glue first second).hom ≫
        (branchDeckAction source deckAction second transformation).hom := by
  change first.temperoidPullback.map
        ((deckAction transformation).hom.app first.vertex) ≫
      (source.glue first second).hom =
    (source.glue first second).hom ≫
      second.temperoidPullback.map
        ((deckAction transformation).hom.app second.vertex)
  exact ((deckAction transformation).hom.naturality first second).symm

/-- Associated quotient on one vertex constituent. -/
noncomputable def vertexAction
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] [Countable X]
    (vertex : diagram.base.Vertex) :
    SourceTemperoidAction (diagram.vertexAnabelioid vertex).group :=
  SourceTemperoidAssociatedQuotient.action
    (source.vertexObject vertex)
    (vertexDeckAction source deckAction vertex) X

/-- Restriction to an edge commutes definitionally with forming an
associated quotient. -/
noncomputable def restrictionIso
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] [Countable X]
    {edge : diagram.base.Edge} (branch : diagram.IncidentBranch edge) :
    branch.temperoidPullback.obj
        (vertexAction source deckAction X branch.vertex) ≅
      SourceTemperoidAssociatedQuotient.action
        (branch.temperoidPullback.obj
          (source.vertexObject branch.vertex))
        (branchDeckAction source deckAction branch) X :=
  Iso.refl _

/-- The original branch gluing descends through the diagonal deck quotient. -/
noncomputable def branchIso
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] [Countable X]
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge) :
    first.temperoidPullback.obj
        (vertexAction source deckAction X first.vertex) ≅
      second.temperoidPullback.obj
        (vertexAction source deckAction X second.vertex) :=
  restrictionIso source deckAction X first ≪≫
    SourceTemperoidAssociatedQuotient.sourceIsoOfHomCommutes
      (branchDeckAction source deckAction first)
      (branchDeckAction source deckAction second)
      (source.glue first second)
      (glue_hom_commutes source deckAction first second) ≪≫
    (restrictionIso source deckAction X second).symm

/-- The descended branch gluing transports the source coordinate and leaves
the auxiliary coordinate unchanged. -/
@[simp]
theorem branchIso_hom_mk
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] [Countable X]
    {edge : diagram.base.Edge}
    (first second : diagram.IncidentBranch edge)
    (point : (first.temperoidPullback.obj
      (source.vertexObject first.vertex)).obj.V.obj)
    (auxiliary : X) :
    (branchIso source deckAction X first second).hom.hom.hom
        (SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject first.vertex)
          (vertexDeckAction source deckAction first.vertex)
          (point, auxiliary)) =
      SourceTemperoidAssociatedQuotient.mk
        (source.vertexObject second.vertex)
        (vertexDeckAction source deckAction second.vertex)
        ((source.glue first second).hom.hom.hom point, auxiliary) :=
  rfl

/-- The literal geometric cover obtained by quotienting a deck-equivariant
cover against an auxiliary deck-set. -/
noncomputable def covObject
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] [Countable X] :
    diagram.CovObject where
  vertexObject := vertexAction source deckAction X
  glue := branchIso source deckAction X
  glue_refl := by
    intro edge branch
    apply Iso.ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    letI := SourceTemperoidAssociatedQuotient.diagonalMulAction
      (source.vertexObject branch.vertex)
      (vertexDeckAction source deckAction branch.vertex) X
    induction point using Quotient.inductionOn' with
    | _ point =>
        change SourceTemperoidAssociatedQuotient.mk
            (source.vertexObject branch.vertex)
            (vertexDeckAction source deckAction branch.vertex)
            ((source.glue branch branch).hom.hom.hom point.1, point.2) =
          SourceTemperoidAssociatedQuotient.mk
            (source.vertexObject branch.vertex)
            (vertexDeckAction source deckAction branch.vertex) point
        rw [source.glue_refl]
        rfl
  glue_trans := by
    intro edge first second third
    apply Iso.ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    letI := SourceTemperoidAssociatedQuotient.diagonalMulAction
      (source.vertexObject first.vertex)
      (vertexDeckAction source deckAction first.vertex) X
    induction point using Quotient.inductionOn' with
    | _ point =>
        apply congrArg
          (SourceTemperoidAssociatedQuotient.mk
            (source.vertexObject third.vertex)
            (vertexDeckAction source deckAction third.vertex))
        apply Prod.ext
        · exact congrArg (fun arrow ↦ arrow.hom.hom point.1)
            (source.glue_trans first second third)
        · rfl

/-- Fixing an auxiliary point assembles the constituent insertions into the
geometric morphism from the source cover to its associated quotient. -/
noncomputable def sourceInsertion
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    {X : Type u} [MulAction Deck X] [Countable X]
    (point : X) :
    source ⟶ covObject source deckAction X where
  app vertex := SourceTemperoidAssociatedQuotient.insertion
    (source.vertexObject vertex)
    (vertexDeckAction source deckAction vertex) point
  naturality := by
    intro edge first second
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro sourcePoint
    exact branchIso_hom_mk source deckAction X first second
      sourcePoint point

@[simp]
theorem sourceInsertion_apply
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    {X : Type u} [MulAction Deck X] [Countable X]
    (point : X) (vertex : diagram.base.Vertex)
    (sourcePoint : (source.vertexObject vertex).obj.V.obj) :
    ((sourceInsertion source deckAction point).app vertex).hom.hom
        sourcePoint =
      SourceTemperoidAssociatedQuotient.mk
        (source.vertexObject vertex)
        (vertexDeckAction source deckAction vertex)
        (sourcePoint, point) :=
  rfl

/-- A transitive auxiliary action makes the geometric structural map
constituentwise surjective. -/
theorem sourceInsertion_surjective
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    {X : Type u} [MulAction Deck X] [Countable X]
    (point : X) (transitive : MulAction.IsPretransitive Deck X)
    (vertex : diagram.base.Vertex) :
    Function.Surjective
      ((sourceInsertion source deckAction point).app vertex).hom.hom :=
  SourceTemperoidAssociatedQuotient.insertion_surjective
    (source.vertexObject vertex)
    (vertexDeckAction source deckAction vertex) point transitive

/-- The auxiliary deck-orbit label of a geometric point in an associated
quotient.  Local movement and branch gluing alter only the source coordinate,
so this label is the component invariant used in the connected-case
classification. -/
noncomputable def geometricAuxiliaryComponent
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] [Countable X] :
    GeometricPoint (covObject source deckAction X) →
      MulAction.orbitRel.Quotient Deck X
  | ⟨vertex, point⟩ =>
      SourceTemperoidAssociatedQuotient.auxiliaryComponent
        (source.vertexObject vertex)
        (vertexDeckAction source deckAction vertex) X point

/-- Every elementary geometric motion preserves the auxiliary orbit label. -/
theorem geometricPointStep_auxiliaryComponent
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] [Countable X]
    {first second : GeometricPoint (covObject source deckAction X)}
    (step : GeometricPointStep (covObject source deckAction X) first second) :
    geometricAuxiliaryComponent source deckAction X first =
      geometricAuxiliaryComponent source deckAction X second := by
  cases step with
  | localAction vertex element point =>
      exact (SourceTemperoidAssociatedQuotient.auxiliaryComponent_local_smul
        (source.vertexObject vertex)
        (vertexDeckAction source deckAction vertex) X element point).symm
  | @glue edge first second point =>
      letI := SourceTemperoidAssociatedQuotient.diagonalMulAction
        (source.vertexObject first.vertex)
        (vertexDeckAction source deckAction first.vertex) X
      induction point using Quotient.inductionOn' with
      | _ point => rfl

/-- A geometric path in an associated quotient cannot leave its auxiliary
deck orbit. -/
theorem reachable_auxiliaryComponent
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] [Countable X]
    {first second : GeometricPoint (covObject source deckAction X)}
    (path : Relation.ReflTransGen
      (GeometricPointStep (covObject source deckAction X)) first second) :
    geometricAuxiliaryComponent source deckAction X first =
      geometricAuxiliaryComponent source deckAction X second := by
  induction path with
  | refl => rfl
  | tail path step inductionHypothesis =>
      exact inductionHypothesis.trans
        (geometricPointStep_auxiliaryComponent source deckAction X step)

/-- Every nonempty associated quotient is literally a subcover of its source
cover; the witnessing arrow is the structural insertion at the selected
auxiliary point. -/
theorem covObject_isSubcoverOf
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    {X : Type u} [MulAction Deck X] [Countable X]
    (point : X) :
    SourceSemiGraphOfAnabelioids.CovObject.IsSubcoverOf
      (covObject source deckAction X) source :=
  SourceSemiGraphOfAnabelioids.CovObject.isSubcoverOf_of_hom
    (sourceInsertion source deckAction point)

/-- A transitive auxiliary deck action produces a point-connected associated
quotient from a point-connected geometric source. -/
theorem covObject_isPointConnected_of_pretransitive
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (root : diagram.base.Vertex)
    (basePoint : (source.vertexObject root).obj.V.obj)
    (connected : IsPointConnected source ⟨root, basePoint⟩)
    {X : Type u} [MulAction Deck X] [Countable X]
    (point : X) (transitive : MulAction.IsPretransitive Deck X) :
    IsPointConnected (covObject source deckAction X)
      ⟨root, SourceTemperoidAssociatedQuotient.mk
        (source.vertexObject root)
        (vertexDeckAction source deckAction root)
        (basePoint, point)⟩ := by
  simpa [geometricPointMap] using isPointConnected_of_surjective_hom
    (sourceInsertion source deckAction point)
    (sourceInsertion_surjective source deckAction point transitive)
    ⟨root, basePoint⟩ connected

/-- Point-connectedness of an associated geometric quotient forces the
auxiliary deck action to be transitive.  Together with
`covObject_isPointConnected_of_pretransitive`, this is the connected-cover /
transitive-action correspondence at a fixed geometric universal-cover level. -/
theorem pretransitive_of_covObject_isPointConnected
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (root : diagram.base.Vertex)
    (basePoint : (source.vertexObject root).obj.V.obj)
    {X : Type u} [MulAction Deck X] [Countable X]
    (point : X)
    (connected : IsPointConnected (covObject source deckAction X)
      ⟨root, SourceTemperoidAssociatedQuotient.mk
        (source.vertexObject root)
        (vertexDeckAction source deckAction root)
        (basePoint, point)⟩) :
    MulAction.IsPretransitive Deck X := by
  constructor
  intro first second
  have pathFirst := connected
    ⟨root, SourceTemperoidAssociatedQuotient.mk
      (source.vertexObject root)
      (vertexDeckAction source deckAction root)
      (basePoint, first)⟩
  have pathSecond := connected
    ⟨root, SourceTemperoidAssociatedQuotient.mk
      (source.vertexObject root)
      (vertexDeckAction source deckAction root)
      (basePoint, second)⟩
  have firstComponentEquality := reachable_auxiliaryComponent
    source deckAction X pathFirst
  have secondComponentEquality := reachable_auxiliaryComponent
    source deckAction X pathSecond
  change (Quotient.mk'' point : MulAction.orbitRel.Quotient Deck X) =
    Quotient.mk'' first at firstComponentEquality
  change (Quotient.mk'' point : MulAction.orbitRel.Quotient Deck X) =
    Quotient.mk'' second at secondComponentEquality
  have componentEquality :
      (Quotient.mk'' first : MulAction.orbitRel.Quotient Deck X) =
        Quotient.mk'' second :=
    firstComponentEquality.symm.trans secondComponentEquality
  have inOrbit : second ∈ MulAction.orbit Deck first := by
    rw [← MulAction.orbitRel_apply, ← Quotient.eq'']
    exact componentEquality.symm
  exact MulAction.mem_orbit_iff.mp inOrbit

/-- At a point-connected source, the associated geometric quotient is
point-connected at the displayed point exactly when the auxiliary deck
action is transitive. -/
theorem covObject_isPointConnected_iff_pretransitive
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (root : diagram.base.Vertex)
    (basePoint : (source.vertexObject root).obj.V.obj)
    (sourceConnected : IsPointConnected source ⟨root, basePoint⟩)
    {X : Type u} [MulAction Deck X] [Countable X]
    (point : X) :
    IsPointConnected (covObject source deckAction X)
        ⟨root, SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject root)
          (vertexDeckAction source deckAction root)
          (basePoint, point)⟩ ↔
      MulAction.IsPretransitive Deck X := by
  constructor
  · exact pretransitive_of_covObject_isPointConnected
      source deckAction root basePoint point
  · exact covObject_isPointConnected_of_pretransitive
      source deckAction root basePoint sourceConnected point

/-- Any kernel that fixes the source action also fixes its associated deck
quotient. -/
theorem actionKernelFixes
    {Local : Type u} [Group Local] [TopologicalSpace Local]
    [IsTopologicalGroup Local]
    (splitter source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] [Countable X]
    (fixes : SourceSemiGraphOfAnabelioids.CovObject.ActionKernelFixes
      splitter source) :
    SourceSemiGraphOfAnabelioids.CovObject.ActionKernelFixes splitter
      (SourceTemperoidAssociatedQuotient.action source deckAction X) := by
  intro element fixesSplitter point
  letI := SourceTemperoidAssociatedQuotient.diagonalMulAction
    source deckAction X
  induction point using Quotient.inductionOn' with
  | _ point =>
      change ConcreteCategory.hom
          ((SourceTemperoidAssociatedQuotient.action
            source deckAction X).obj.ρ element)
          (SourceTemperoidAssociatedQuotient.mk source deckAction point) =
        SourceTemperoidAssociatedQuotient.mk source deckAction point
      rw [SourceTemperoidAssociatedQuotient.action_smul_mk]
      apply congrArg (SourceTemperoidAssociatedQuotient.mk source deckAction)
      exact Prod.ext (fixes element fixesSplitter point.1) rfl

/-- Associated quotients preserve geometric temperedness, with the same
finite étale splitting cover. -/
theorem covObject_isTempered
    (root : diagram.base.Vertex)
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] [Countable X]
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsGloballyTempered
      diagram root source) :
    SourceSemiGraphOfAnabelioids.CovObject.IsTempered diagram root
      (covObject source deckAction X) := by
  obtain ⟨splitter, vertexFixes, edgeFixes⟩ := tempered
  apply SourceSemiGraphOfAnabelioids.CovObject.isTempered_of_isSplitBy
    diagram root (splitter := splitter)
  constructor
  · intro vertex
    letI := (diagram.vertexAnabelioid vertex).coverCategory
    exact actionKernelFixes
      ((SourceSemiGraphOfAnabelioids.CovObject.finiteCovObject
        diagram root splitter).vertexObject vertex)
      (source.vertexObject vertex)
      (vertexDeckAction source deckAction vertex) X
      (vertexFixes vertex)
  · intro edge
    let reference :=
      SourceSemiGraphOfAnabelioids.CovObject.coverReferenceBranch
        diagram root edge
    letI := (diagram.vertexAnabelioid reference.vertex).coverCategory
    letI := (diagram.edgeAnabelioid edge).coverCategory
    exact actionKernelFixes
      (SourceSemiGraphOfAnabelioids.CovObject.coverEdgeObject diagram root
        (SourceSemiGraphOfAnabelioids.CovObject.finiteCovObject
          diagram root splitter) edge)
      (SourceSemiGraphOfAnabelioids.CovObject.coverEdgeObject
        diagram root source edge)
      (branchDeckAction source deckAction reference) X
      (edgeFixes edge)

section Functoriality

variable [TopologicalSpace Deck] [IsTopologicalGroup Deck]

/-- A morphism of auxiliary deck-actions induces a morphism of the associated
geometric quotient covers. -/
noncomputable def map
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    {X Y : SourceTemperoidAction Deck} (arrow : X ⟶ Y) :
    covObject source deckAction X.obj.V.obj ⟶
      covObject source deckAction Y.obj.V.obj where
  app vertex := SourceTemperoidAssociatedQuotient.map
    (source.vertexObject vertex)
    (vertexDeckAction source deckAction vertex) arrow
  naturality := by
    intro edge first second
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    letI := SourceTemperoidAssociatedQuotient.diagonalMulAction
      (source.vertexObject first.vertex)
      (vertexDeckAction source deckAction first.vertex) X.obj.V.obj
    induction point using Quotient.inductionOn' with
    | _ point => rfl

section DeckTransitionFunctoriality

variable {FinerDeck : Type u} [Group FinerDeck]

/-- An equivariant map between geometric source covers along a deck-group
transition descends to their associated quotient covers. -/
noncomputable def sourceMapOfTransition
    (source : diagram.CovObject) (sourceDeckAction : FinerDeck →* Aut source)
    (target : diagram.CovObject) (targetDeckAction : Deck →* Aut target)
    (transition : FinerDeck →* Deck)
    (sourceMap : source ⟶ target)
    (commutes : ∀ transformation,
      (sourceDeckAction transformation).hom ≫ sourceMap =
        sourceMap ≫ (targetDeckAction (transition transformation)).hom)
    (X : SourceTemperoidAction Deck) :
    @covObject FinerDeck _ diagram source sourceDeckAction X.obj.V.obj
        (MulAction.compHom X.obj.V.obj transition) _ ⟶
      covObject target targetDeckAction X.obj.V.obj where
  app vertex := SourceTemperoidAssociatedQuotient.sourceMapOfTransition
    (vertexDeckAction source sourceDeckAction vertex)
    (vertexDeckAction target targetDeckAction vertex)
    transition (sourceMap.app vertex)
    (fun transformation ↦ congrArg (fun arrow ↦ arrow.app vertex)
      (commutes transformation))
  naturality := by
    intro edge first second
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    letI : MulAction FinerDeck X.obj.V.obj :=
      MulAction.compHom X.obj.V.obj transition
    letI := SourceTemperoidAssociatedQuotient.diagonalMulAction
      (source.vertexObject first.vertex)
      (vertexDeckAction source sourceDeckAction first.vertex) X.obj.V.obj
    induction point using Quotient.inductionOn' with
    | _ point =>
        change SourceTemperoidAssociatedQuotient.mk
            (target.vertexObject second.vertex)
            (vertexDeckAction target targetDeckAction second.vertex)
            ((sourceMap.app second.vertex).hom.hom
              ((source.glue first second).hom.hom.hom point.1), point.2) =
          SourceTemperoidAssociatedQuotient.mk
            (target.vertexObject second.vertex)
            (vertexDeckAction target targetDeckAction second.vertex)
            ((target.glue first second).hom.hom.hom
              ((sourceMap.app first.vertex).hom.hom point.1), point.2)
        apply congrArg
          (SourceTemperoidAssociatedQuotient.mk
            (target.vertexObject second.vertex)
            (vertexDeckAction target targetDeckAction second.vertex))
        exact Prod.ext
          (ConcreteCategory.congr_hom
            (sourceMap.naturality first second) point.1) rfl

end DeckTransitionFunctoriality

/-- A morphism between associated geometric quotients preserves one fixed
auxiliary value at every source point once this is known at a point-connected
base. -/
theorem map_mk_of_isPointConnected
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (root : diagram.base.Vertex)
    (basePoint : (source.vertexObject root).obj.V.obj)
    (connected : IsPointConnected source ⟨root, basePoint⟩)
    {X Y : SourceTemperoidAction Deck}
    (arrow : covObject source deckAction X.obj.V.obj ⟶
      covObject source deckAction Y.obj.V.obj)
    (auxiliaryMap : X.obj.V.obj → Y.obj.V.obj)
    (atBase : ∀ point,
      (arrow.app root).hom.hom
          (SourceTemperoidAssociatedQuotient.mk
            (source.vertexObject root)
            (vertexDeckAction source deckAction root)
            (basePoint, point)) =
        SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject root)
          (vertexDeckAction source deckAction root)
          (basePoint, auxiliaryMap point))
    (vertex : diagram.base.Vertex)
    (sourcePoint : (source.vertexObject vertex).obj.V.obj)
    (point : X.obj.V.obj) :
    (arrow.app vertex).hom.hom
        (SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject vertex)
          (vertexDeckAction source deckAction vertex)
          (sourcePoint, point)) =
      SourceTemperoidAssociatedQuotient.mk
        (source.vertexObject vertex)
        (vertexDeckAction source deckAction vertex)
        (sourcePoint, auxiliaryMap point) := by
  let Preserved : GeometricPoint source → Prop := fun geometricPoint ↦
    (arrow.app geometricPoint.1).hom.hom
        (SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject geometricPoint.1)
          (vertexDeckAction source deckAction geometricPoint.1)
          (geometricPoint.2, point)) =
      SourceTemperoidAssociatedQuotient.mk
        (source.vertexObject geometricPoint.1)
        (vertexDeckAction source deckAction geometricPoint.1)
        (geometricPoint.2, auxiliaryMap point)
  change Preserved ⟨vertex, sourcePoint⟩
  have stepPreserves : ∀ {first second : GeometricPoint source},
      GeometricPointStep source first second →
        Preserved first → Preserved second := by
    intro first second step inductionHypothesis
    cases step with
      | localAction stepVertex element stepPoint =>
          letI := SourceTemperoidAssociatedQuotient.localMulAction
            (source.vertexObject stepVertex)
            (vertexDeckAction source deckAction stepVertex) X.obj.V.obj
          letI := SourceTemperoidAssociatedQuotient.localMulAction
            (source.vertexObject stepVertex)
            (vertexDeckAction source deckAction stepVertex) Y.obj.V.obj
          change (arrow.app stepVertex).hom.hom
              (SourceTemperoidAssociatedQuotient.mk
                (source.vertexObject stepVertex)
                (vertexDeckAction source deckAction stepVertex)
                (stepPoint, point)) =
            SourceTemperoidAssociatedQuotient.mk
              (source.vertexObject stepVertex)
              (vertexDeckAction source deckAction stepVertex)
              (stepPoint, auxiliaryMap point) at inductionHypothesis
          calc
            (arrow.app stepVertex).hom.hom
                (SourceTemperoidAssociatedQuotient.mk
                  (source.vertexObject stepVertex)
                  (vertexDeckAction source deckAction stepVertex)
                  (element • stepPoint, point)) =
              (arrow.app stepVertex).hom.hom
                (element • SourceTemperoidAssociatedQuotient.mk
                  (source.vertexObject stepVertex)
                  (vertexDeckAction source deckAction stepVertex)
                  (stepPoint, point)) := by
                    rw [SourceTemperoidAssociatedQuotient.local_smul_mk]
            _ = element • (arrow.app stepVertex).hom.hom
                (SourceTemperoidAssociatedQuotient.mk
                  (source.vertexObject stepVertex)
                  (vertexDeckAction source deckAction stepVertex)
                  (stepPoint, point)) :=
              ConcreteCategory.congr_hom
                ((arrow.app stepVertex).hom.comm element) _
            _ = element • SourceTemperoidAssociatedQuotient.mk
                (source.vertexObject stepVertex)
                (vertexDeckAction source deckAction stepVertex)
                (stepPoint, auxiliaryMap point) :=
              congrArg (element • ·) inductionHypothesis
            _ = SourceTemperoidAssociatedQuotient.mk
                (source.vertexObject stepVertex)
                (vertexDeckAction source deckAction stepVertex)
                (element • stepPoint, auxiliaryMap point) := by
                  rw [SourceTemperoidAssociatedQuotient.local_smul_mk]
      | @glue edge first second stepPoint =>
          have naturalityAtPoint := ConcreteCategory.congr_hom
            (arrow.naturality first second)
            (SourceTemperoidAssociatedQuotient.mk
              (source.vertexObject first.vertex)
              (vertexDeckAction source deckAction first.vertex)
              (stepPoint, point))
          change (arrow.app second.vertex).hom.hom
              ((branchIso source deckAction X.obj.V.obj
                first second).hom.hom.hom
                (SourceTemperoidAssociatedQuotient.mk
                  (source.vertexObject first.vertex)
                  (vertexDeckAction source deckAction first.vertex)
                  (stepPoint, point))) =
            (branchIso source deckAction Y.obj.V.obj
              first second).hom.hom.hom
              ((arrow.app first.vertex).hom.hom
                (SourceTemperoidAssociatedQuotient.mk
                  (source.vertexObject first.vertex)
                  (vertexDeckAction source deckAction first.vertex)
                  (stepPoint, point))) at naturalityAtPoint
          change (arrow.app first.vertex).hom.hom
              (SourceTemperoidAssociatedQuotient.mk
                (source.vertexObject first.vertex)
                (vertexDeckAction source deckAction first.vertex)
                (stepPoint, point)) =
            SourceTemperoidAssociatedQuotient.mk
              (source.vertexObject first.vertex)
              (vertexDeckAction source deckAction first.vertex)
              (stepPoint, auxiliaryMap point) at inductionHypothesis
          refine Eq.trans ?_ (branchIso_hom_mk source deckAction
            Y.obj.V.obj first second stepPoint (auxiliaryMap point))
          calc
            (arrow.app second.vertex).hom.hom
                (SourceTemperoidAssociatedQuotient.mk
                  (source.vertexObject second.vertex)
                  (vertexDeckAction source deckAction second.vertex)
                  ((source.glue first second).hom.hom.hom stepPoint, point)) =
              (arrow.app second.vertex).hom.hom
                ((branchIso source deckAction X.obj.V.obj
                  first second).hom.hom.hom
                  (SourceTemperoidAssociatedQuotient.mk
                    (source.vertexObject first.vertex)
                    (vertexDeckAction source deckAction first.vertex)
                    (stepPoint, point))) := by
                      apply congrArg (arrow.app second.vertex).hom.hom
                      exact (branchIso_hom_mk source deckAction
                        X.obj.V.obj first second stepPoint point).symm
            _ = (branchIso source deckAction Y.obj.V.obj
                  first second).hom.hom.hom
                ((arrow.app first.vertex).hom.hom
                  (SourceTemperoidAssociatedQuotient.mk
                    (source.vertexObject first.vertex)
                    (vertexDeckAction source deckAction first.vertex)
                    (stepPoint, point))) := naturalityAtPoint
            _ = (branchIso source deckAction Y.obj.V.obj
                  first second).hom.hom.hom
                (SourceTemperoidAssociatedQuotient.mk
                  (source.vertexObject first.vertex)
                  (vertexDeckAction source deckAction first.vertex)
                  (stepPoint, auxiliaryMap point)) := by
                    rw [inductionHypothesis]
  have path := connected ⟨vertex, sourcePoint⟩
  have pathPreserves :
      Preserved ⟨root, basePoint⟩ → Preserved ⟨vertex, sourcePoint⟩ :=
    path.trans_induction_on
      (fun _ hypothesis ↦ hypothesis)
      (fun step ↦ stepPreserves step)
      (fun _ _ firstPreserves secondPreserves hypothesis ↦
        secondPreserves (firstPreserves hypothesis))
  exact pathPreserves (atBase point)

/-- On a point-connected source whose deck action is free, base-normalized
geometric quotient morphisms recover deck-equivariant auxiliary maps. -/
theorem auxiliaryMap_smul_of_isPointConnected
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (root : diagram.base.Vertex)
    (basePoint : (source.vertexObject root).obj.V.obj)
    (connected : IsPointConnected source ⟨root, basePoint⟩)
    (free : letI := (SourceTemperoidAssociatedQuotient.sourceDeckMulAction
        (source.vertexObject root)
        (vertexDeckAction source deckAction root));
      IsCancelSMul Deck (source.vertexObject root).obj.V.obj)
    {X Y : SourceTemperoidAction Deck}
    (arrow : covObject source deckAction X.obj.V.obj ⟶
      covObject source deckAction Y.obj.V.obj)
    (auxiliaryMap : X.obj.V.obj → Y.obj.V.obj)
    (atBase : ∀ point,
      (arrow.app root).hom.hom
          (SourceTemperoidAssociatedQuotient.mk
            (source.vertexObject root)
            (vertexDeckAction source deckAction root)
            (basePoint, point)) =
        SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject root)
          (vertexDeckAction source deckAction root)
          (basePoint, auxiliaryMap point))
    (transformation : Deck) (point : X.obj.V.obj) :
    auxiliaryMap (transformation • point) =
      transformation • auxiliaryMap point := by
  let rootDeckAction := vertexDeckAction source deckAction root
  letI := SourceTemperoidAssociatedQuotient.sourceDeckMulAction
    (source.vertexObject root) rootDeckAction
  letI : IsCancelSMul Deck (source.vertexObject root).obj.V.obj := free
  let inversePoint : (source.vertexObject root).obj.V.obj :=
    transformation⁻¹ • basePoint
  have forwardInverse : transformation • inversePoint = basePoint := by
    dsimp only [inversePoint]
    rw [← mul_smul]
    simp
  have sourceClass :
      SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject root) rootDeckAction
          (basePoint, transformation • point) =
        SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject root) rootDeckAction
          (inversePoint, point) := by
    rw [← forwardInverse]
    exact SourceTemperoidAssociatedQuotient.mk_smul
      (source.vertexObject root) rootDeckAction transformation
        (inversePoint, point)
  have targetClass :
      SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject root) rootDeckAction
          (basePoint, transformation • auxiliaryMap point) =
        SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject root) rootDeckAction
          (inversePoint, auxiliaryMap point) := by
    rw [← forwardInverse]
    exact SourceTemperoidAssociatedQuotient.mk_smul
      (source.vertexObject root) rootDeckAction transformation
        (inversePoint, auxiliaryMap point)
  have mappedInverse := map_mk_of_isPointConnected
    source deckAction root basePoint connected arrow auxiliaryMap atBase
      root inversePoint point
  change (arrow.app root).hom.hom
      (SourceTemperoidAssociatedQuotient.mk
        (source.vertexObject root) rootDeckAction
        (inversePoint, point)) =
    SourceTemperoidAssociatedQuotient.mk
      (source.vertexObject root) rootDeckAction
      (inversePoint, auxiliaryMap point) at mappedInverse
  apply SourceTemperoidAssociatedQuotient.baseInsertion_injective
    (source.vertexObject root) rootDeckAction basePoint free
  change SourceTemperoidAssociatedQuotient.mk
      (source.vertexObject root) rootDeckAction
        (basePoint, auxiliaryMap (transformation • point)) =
    SourceTemperoidAssociatedQuotient.mk
      (source.vertexObject root) rootDeckAction
        (basePoint, transformation • auxiliaryMap point)
  refine Eq.trans ?_ targetClass.symm
  refine Eq.trans ?_ mappedInverse
  calc
    _ = (arrow.app root).hom.hom
          (SourceTemperoidAssociatedQuotient.mk
            (source.vertexObject root) rootDeckAction
            (basePoint, transformation • point)) :=
      (atBase (transformation • point)).symm
    _ = (arrow.app root).hom.hom
          (SourceTemperoidAssociatedQuotient.mk
            (source.vertexObject root) rootDeckAction
            (inversePoint, point)) := congrArg (arrow.app root).hom.hom sourceClass

/-- Associated geometric quotient as a functor from continuous deck-actions
to literal geometric covers. -/
noncomputable def functor
    (source : diagram.CovObject) (deckAction : Deck →* Aut source) :
    SourceTemperoidAction Deck ⥤ diagram.CovObject where
  obj X := covObject source deckAction X.obj.V.obj
  map := map source deckAction
  map_id X := by
    apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
    intro vertex
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    letI := SourceTemperoidAssociatedQuotient.diagonalMulAction
      (source.vertexObject vertex)
      (vertexDeckAction source deckAction vertex) X.obj.V.obj
    induction point using Quotient.inductionOn' with
    | _ point => rfl
  map_comp {X Y Z} first second := by
    apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
    intro vertex
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    letI := SourceTemperoidAssociatedQuotient.diagonalMulAction
      (source.vertexObject vertex)
      (vertexDeckAction source deckAction vertex) X.obj.V.obj
    induction point using Quotient.inductionOn' with
    | _ point => rfl

/-- The associated quotient functor with its geometric temperedness proof. -/
noncomputable def temperedFunctor
    (root : diagram.base.Vertex)
    (source : diagram.CovObject) (deckAction : Deck →* Aut source)
    (tempered : SourceSemiGraphOfAnabelioids.CovObject.IsGloballyTempered
      diagram root source) :
    SourceTemperoidAction Deck ⥤
      SourceSemiGraphOfAnabelioids.CovObject.TemperedCover diagram root :=
  (SourceSemiGraphOfAnabelioids.CovObject.temperedObjectProperty diagram root).lift
    (functor source deckAction)
    (fun X ↦ covObject_isTempered root source deckAction X.obj.V.obj tempered)

end Functoriality

end SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

namespace SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

open SourceSemiGraphOfAnabelioids.GluedObject
open SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
open SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient

/-- At a pointed connected Galois level, the geometric universal cover and
its literal deck action send every continuous level action to a geometric
tempered quotient cover. -/
noncomputable def associatedTemperedFunctor
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    SourceTemperoidAction (DeckGroup diagram root level) ⥤
      SourceSemiGraphOfAnabelioids.CovObject.TemperedCover diagram root := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  exact
    SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.temperedFunctor
      root
      (SourceFiniteLevelUniversalCover.covObject
        diagram root level.object level.rootVertex)
      (deckCovActionHom diagram root level)
      ⟨level.object,
        SourceFiniteLevelUniversalCover.covObject_isSplitBy
          diagram root level.object level.rootVertex⟩

/-- The distinguished pointed Galois element gives an actual point in the
root constituent of the geometric universal cover. -/
noncomputable def rootVertexPoint
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    letI : Countable diagram.base.Vertex := Finite.to_countable
    letI : Countable diagram.base.Edge := Finite.to_countable
    (SourceFiniteLevelUniversalCover.covObject
      diagram root level.object level.rootVertex).vertexObject root |>.obj.V.obj := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  let lifted : SourceSemiGraphUniversalCover.LiftedVertex
      (LevelSemiGraph diagram root level) level.rootVertex :=
    { path := UniversalVertex.base
        (IncidenceGraph diagram root level) (IncidenceRoot diagram root level)
      vertex := level.rootVertex
      endpoint_eq := rfl }
  let index : GeometricVertexIndex diagram root level root :=
    ⟨lifted, rfl⟩
  exact ⟨index, ⟨level.point, rfl⟩⟩

/-- The distinguished root point reaches every geometric point of the
finite-level universal cover.  This is the literal geometric connectedness
input required by Proposition 3.6(ii), not merely connectedness of the orbit
component set. -/
theorem covObject_isPointConnected
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    letI : Countable diagram.base.Vertex := Finite.to_countable
    letI : Countable diagram.base.Edge := Finite.to_countable
    SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.IsPointConnected
      (SourceFiniteLevelUniversalCover.covObject
        diagram root level.object level.rootVertex)
      ⟨root, rootVertexPoint diagram root level⟩ := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  exact isPointConnected_of_coverSemiGraph_isConnected
      root
      (SourceFiniteLevelUniversalCover.covObject
        diagram root level.object level.rootVertex)
      ⟨root, rootVertexPoint diagram root level⟩
      (SourceFiniteLevelUniversalCover.coverSemiGraph_isConnected
        diagram root level.object level.rootVertex)

/-- The complete deck action on every constituent of the literal geometric
universal cover is free.  A transformation fixing a geometric point fixes
its finite Galois-fiber coordinate, hence has trivial retained symmetry;
fixing the accompanying universal-tree vertex then makes the whole composite
deck transformation trivial. -/
theorem vertexDeckAction_isCancel
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    (vertex : diagram.base.Vertex)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    letI : Countable diagram.base.Vertex := Finite.to_countable
    letI : Countable diagram.base.Edge := Finite.to_countable
    let source := SourceFiniteLevelUniversalCover.covObject
      diagram root level.object level.rootVertex
    letI := SourceTemperoidAssociatedQuotient.sourceDeckMulAction
      (source.vertexObject vertex)
      (SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.vertexDeckAction
        source (deckCovActionHom diagram root level) vertex)
    IsCancelSMul (DeckGroup diagram root level)
      (source.vertexObject vertex).obj.V.obj := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  let deckAction :=
    SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.vertexDeckAction
      source (deckCovActionHom diagram root level) vertex
  letI := SourceTemperoidAssociatedQuotient.sourceDeckMulAction
    (source.vertexObject vertex) deckAction
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro transformation point fixed
  change ((deckVertexActionIso diagram root level transformation vertex).hom.hom.hom
    point) = point at fixed
  have fiberFixed := congrArg (fun value ↦ value.2.1) fixed
  have symmetryEquality :
      UniversalVertex.CompositeDeckTransformation.baseSymmetry transformation =
        1 := by
    letI : GaloisCategory diagram.GluedObject :=
      SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
    letI : PreGaloisCategory.FiberFunctor
        (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram vertex) :=
      SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram vertex
    letI : PreGaloisCategory.IsGalois level.object := level.isGalois
    apply PreGaloisCategory.evaluation_aut_injective_of_isConnected
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram vertex)
      level.object point.2.1
    change (deckVertexFiniteActionIso
        diagram root level transformation vertex).hom.hom.hom point.2.1 =
      point.2.1 at fiberFixed
    change (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber
        diagram vertex).map
          (UniversalVertex.CompositeDeckTransformation.baseSymmetry
            transformation).hom point.2.1 = point.2.1 at fiberFixed
    exact fiberFixed.trans
      (ConcreteCategory.congr_hom
        ((SourceSemiGraphOfAnabelioids.GluedObject.rootFiber
          diagram vertex).map_id level.object) point.2.1).symm
  apply UniversalVertex.CompositeDeckTransformation.encoding_injective
    point.1.1.path
  apply Prod.ext symmetryEquality
  have indexFixed := congrArg (fun value ↦ value.1) fixed
  exact congrArg (fun index ↦ index.1.path) indexFixed

/-- The distinguished root constituent is the root specialization of
vertexwise freeness. -/
theorem rootVertexDeckAction_isCancel
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    letI : Countable diagram.base.Vertex := Finite.to_countable
    letI : Countable diagram.base.Edge := Finite.to_countable
    let source := SourceFiniteLevelUniversalCover.covObject
      diagram root level.object level.rootVertex
    letI := SourceTemperoidAssociatedQuotient.sourceDeckMulAction
      (source.vertexObject root)
      (SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.vertexDeckAction
        source (deckCovActionHom diagram root level) root)
    IsCancelSMul (DeckGroup diagram root level)
      (source.vertexObject root).obj.V.obj :=
  vertexDeckAction_isCancel diagram root level root

/-- The complete deck action is transitive on every vertex constituent of
the geometric universal cover. -/
theorem vertexDeckAction_isPretransitive
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    (vertex : diagram.base.Vertex)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    letI : Countable diagram.base.Vertex := Finite.to_countable
    letI : Countable diagram.base.Edge := Finite.to_countable
    let source := SourceFiniteLevelUniversalCover.covObject
      diagram root level.object level.rootVertex
    letI := SourceTemperoidAssociatedQuotient.sourceDeckMulAction
      (source.vertexObject vertex)
      (SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.vertexDeckAction
        source (deckCovActionHom diagram root level) vertex)
    MulAction.IsPretransitive (DeckGroup diagram root level)
      (source.vertexObject vertex).obj.V.obj := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  let deckAction :=
    SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.vertexDeckAction
      source (deckCovActionHom diagram root level) vertex
  letI := SourceTemperoidAssociatedQuotient.sourceDeckMulAction
    (source.vertexObject vertex) deckAction
  constructor
  intro first second
  rcases first with
    ⟨⟨⟨firstPath, ⟨firstBase, firstComponent⟩, firstEndpoint⟩,
      firstOverVertex⟩, firstPoint⟩
  rcases second with
    ⟨⟨⟨secondPath, ⟨secondBase, secondComponent⟩, secondEndpoint⟩,
      secondOverVertex⟩, secondPoint⟩
  change firstBase = vertex at firstOverVertex
  change secondBase = vertex at secondOverVertex
  subst firstBase
  subst secondBase
  letI : GaloisCategory diagram.GluedObject :=
    SourceSemiGraphOfAnabelioids.GluedObject.galoisCategory diagram root
  letI : PreGaloisCategory.FiberFunctor
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber diagram vertex) :=
    SourceSemiGraphOfAnabelioids.GluedObject.rootFiberFunctor diagram vertex
  letI : PreGaloisCategory.IsGalois level.object := level.isGalois
  let firstValue :
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber
        diagram vertex).obj level.object := firstPoint.1
  let secondValue :
      (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber
        diagram vertex).obj level.object := secondPoint.1
  obtain ⟨automorphism, pointEquality⟩ :=
    MulAction.exists_smul_eq (Aut level.object)
      firstValue secondValue
  change (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber
      diagram vertex).map automorphism.hom firstValue =
    secondValue at pointEquality
  have firstFiberComponent :
      firstComponent = Quotient.mk'' firstPoint.1 := by
    apply (SourceSemiGraphOfAnabelioids.CovObject.finiteVertexComponentEquiv
      diagram root level.object vertex).injective
    exact firstPoint.2.symm
  have secondFiberComponent :
      secondComponent = Quotient.mk'' secondPoint.1 := by
    apply (SourceSemiGraphOfAnabelioids.CovObject.finiteVertexComponentEquiv
      diagram root level.object vertex).injective
    exact secondPoint.2.symm
  have finiteVertexEquality :
      level.automorphismAction.vertexAction automorphism
          ⟨vertex, firstComponent⟩ =
        ⟨vertex, secondComponent⟩ := by
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    change EtaleFundamentalGroup.fiberComponentHomMap
        (diagram.vertexAnabelioid vertex)
        (automorphism.hom.app vertex) firstComponent = secondComponent
    rw [firstFiberComponent, secondFiberComponent]
    exact congrArg Quotient.mk'' pointEquality
  have endpointEquality :
      (IncidenceActionHom diagram root level automorphism).val
          firstPath.endpoint = secondPath.endpoint := by
    change IncidenceNode.incidencePerm
        (SourceFiniteLevelUniversalCover.LevelSemiGraph
          diagram root level.object)
        level.automorphismAction automorphism firstPath.endpoint =
      secondPath.endpoint
    rw [firstEndpoint, secondEndpoint,
      IncidenceNode.incidencePerm_vertex]
    exact congrArg (fun vertex ↦ IncidenceNode.vertex (Sum.inl vertex))
      finiteVertexEquality
  let transformation : DeckGroup diagram root level :=
    UniversalVertex.CompositeDeckTransformation.between
      automorphism firstPath secondPath endpointEquality
  refine ⟨transformation, ?_⟩
  let firstGeometricPoint : (source.vertexObject vertex).obj.V.obj :=
    ⟨⟨⟨firstPath, ⟨vertex, firstComponent⟩, firstEndpoint⟩, rfl⟩,
      firstPoint⟩
  let secondGeometricPoint : (source.vertexObject vertex).obj.V.obj :=
    ⟨⟨⟨secondPath, ⟨vertex, secondComponent⟩, secondEndpoint⟩, rfl⟩,
      secondPoint⟩
  change (deckVertexActionIso
      diagram root level transformation vertex).hom.hom.hom firstGeometricPoint =
    secondGeometricPoint
  have indexEquality :
      ((deckVertexActionIso diagram root level transformation vertex).hom.hom.hom
        firstGeometricPoint).1 = secondGeometricPoint.1 := by
    change deckVertexIndexEquiv diagram root level transformation vertex
        ⟨⟨firstPath, ⟨vertex, firstComponent⟩, firstEndpoint⟩, rfl⟩ =
      ⟨⟨secondPath, ⟨vertex, secondComponent⟩, secondEndpoint⟩, rfl⟩
    apply Subtype.ext
    apply SourceSemiGraphUniversalCover.LiftedVertex.path_injective
    exact UniversalVertex.CompositeDeckTransformation.between_apply_first
      automorphism firstPath secondPath endpointEquality
  apply Sigma.ext indexEquality
  rw [Subtype.heq_iff_coe_heq rfl (by
    apply heq_of_eq
    funext value
    apply propext
    rw [indexEquality])]
  apply heq_of_eq
  change (SourceSemiGraphOfAnabelioids.GluedObject.rootFiber
      diagram vertex).map automorphism.hom firstValue = secondValue
  exact pointEquality

/-- The root instance used for normalization is the distinguished case of
vertexwise deck transitivity. -/
theorem rootVertexDeckAction_isPretransitive
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    letI : Countable diagram.base.Vertex := Finite.to_countable
    letI : Countable diagram.base.Edge := Finite.to_countable
    let source := SourceFiniteLevelUniversalCover.covObject
      diagram root level.object level.rootVertex
    letI := SourceTemperoidAssociatedQuotient.sourceDeckMulAction
      (source.vertexObject root)
      (SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.vertexDeckAction
        source (deckCovActionHom diagram root level) root)
    MulAction.IsPretransitive (DeckGroup diagram root level)
      (source.vertexObject root).obj.V.obj :=
  vertexDeckAction_isPretransitive diagram root level root

/-- Normalization at the distinguished root point identifies the root
constituent of a finite-level associated geometric quotient with its
auxiliary deck-action carrier. -/
noncomputable def rootAssociatedCarrierEquiv
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (X : SourceTemperoidAction (DeckGroup diagram root level)) :
    X.obj.V.obj ≃
      (((associatedTemperedFunctor diagram root level).obj X).obj.vertexObject
        root).obj.V.obj := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  let deckAction :=
    SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.vertexDeckAction
      source (deckCovActionHom diagram root level) root
  exact SourceTemperoidAssociatedQuotient.baseInsertionEquiv
    (source.vertexObject root) deckAction
    (rootVertexPoint diagram root level)
    (rootVertexDeckAction_isCancel diagram root level)
    (rootVertexDeckAction_isPretransitive diagram root level)

@[simp]
theorem rootAssociatedCarrierEquiv_apply
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    (X : SourceTemperoidAction (DeckGroup diagram root level))
    (point : X.obj.V.obj) :
    rootAssociatedCarrierEquiv diagram root level X point =
      SourceTemperoidAssociatedQuotient.mk
        ((SourceFiniteLevelUniversalCover.covObject
          diagram root level.object level.rootVertex).vertexObject root)
        (vertexDeckAction
          (SourceFiniteLevelUniversalCover.covObject
            diagram root level.object level.rootVertex)
          (deckCovActionHom diagram root level) root)
        (rootVertexPoint diagram root level, point) := by
  rfl

/-- Normalize a geometric quotient morphism at the distinguished root to
recover its underlying map of auxiliary carriers.  Deck equivariance is the
remaining global gluing obligation. -/
noncomputable def recoverAuxiliaryFunction
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    {X Y : SourceTemperoidAction (DeckGroup diagram root level)}
    (arrow : (associatedTemperedFunctor diagram root level).obj X ⟶
      (associatedTemperedFunctor diagram root level).obj Y) :
    X.obj.V.obj → Y.obj.V.obj :=
  fun point ↦
    (rootAssociatedCarrierEquiv diagram root level Y).symm
      (arrow.hom.app root |>.hom.hom
        (rootAssociatedCarrierEquiv diagram root level X point))

/-- Re-encoding the recovered auxiliary value gives exactly the original
geometric morphism evaluated on the normalized root class. -/
theorem rootAssociatedCarrierEquiv_recoverAuxiliaryFunction
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    {X Y : SourceTemperoidAction (DeckGroup diagram root level)}
    (arrow : (associatedTemperedFunctor diagram root level).obj X ⟶
      (associatedTemperedFunctor diagram root level).obj Y)
    (point : X.obj.V.obj) :
    rootAssociatedCarrierEquiv diagram root level Y
        (recoverAuxiliaryFunction diagram root level arrow point) =
      (arrow.hom.app root).hom.hom
        (rootAssociatedCarrierEquiv diagram root level X point) := by
  exact (rootAssociatedCarrierEquiv diagram root level Y).apply_symm_apply _

/-- At the distinguished root, the recovered auxiliary function is exactly
the value encoded by the geometric quotient morphism. -/
theorem recoverAuxiliaryFunction_atBase
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    {X Y : SourceTemperoidAction (DeckGroup diagram root level)}
    (arrow : (associatedTemperedFunctor diagram root level).obj X ⟶
      (associatedTemperedFunctor diagram root level).obj Y)
    (point : X.obj.V.obj) :
    let source := SourceFiniteLevelUniversalCover.covObject
      diagram root level.object level.rootVertex
    (arrow.hom.app root).hom.hom
        (SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject root)
          (vertexDeckAction source (deckCovActionHom diagram root level) root)
          (rootVertexPoint diagram root level, point)) =
      SourceTemperoidAssociatedQuotient.mk
        (source.vertexObject root)
        (vertexDeckAction source (deckCovActionHom diagram root level) root)
        (rootVertexPoint diagram root level,
          recoverAuxiliaryFunction diagram root level arrow point) := by
  exact (rootAssociatedCarrierEquiv_recoverAuxiliaryFunction
    diagram root level arrow point).symm

/-- Recover the actual equivariant morphism of auxiliary deck-actions from a
geometric morphism between finite-level associated quotients. -/
noncomputable def recoverAuxiliaryMap
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    {X Y : SourceTemperoidAction (DeckGroup diagram root level)}
    (arrow : (associatedTemperedFunctor diagram root level).obj X ⟶
      (associatedTemperedFunctor diagram root level).obj Y) :
    X ⟶ Y := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  let deckAction := deckCovActionHom diagram root level
  let auxiliaryMap := recoverAuxiliaryFunction diagram root level arrow
  have atBase : ∀ point,
      (arrow.hom.app root).hom.hom
          (SourceTemperoidAssociatedQuotient.mk
            (source.vertexObject root)
            (vertexDeckAction source deckAction root)
            (rootVertexPoint diagram root level, point)) =
        SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject root)
          (vertexDeckAction source deckAction root)
          (rootVertexPoint diagram root level, auxiliaryMap point) := by
    intro point
    exact recoverAuxiliaryFunction_atBase diagram root level arrow point
  have equivariant : ∀ transformation point,
      auxiliaryMap (transformation • point) =
        transformation • auxiliaryMap point :=
    auxiliaryMap_smul_of_isPointConnected
      source deckAction root (rootVertexPoint diagram root level)
      (covObject_isPointConnected diagram root level)
      (rootVertexDeckAction_isCancel diagram root level)
      arrow.hom auxiliaryMap atBase
  exact ObjectProperty.homMk
    ({ hom := SourceCountableTypeCat.homMk auxiliaryMap
       comm := fun transformation ↦ by
         apply ConcreteCategory.hom_ext
         intro point
         exact equivariant transformation point } :
      X.obj ⟶ Y.obj)

/-- Reapplying the associated-quotient functor to the recovered equivariant
map returns the original geometric morphism. -/
theorem associatedTemperedFunctor_map_recoverAuxiliaryMap
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    {X Y : SourceTemperoidAction (DeckGroup diagram root level)}
    (arrow : (associatedTemperedFunctor diagram root level).obj X ⟶
      (associatedTemperedFunctor diagram root level).obj Y) :
    (associatedTemperedFunctor diagram root level).map
        (recoverAuxiliaryMap diagram root level arrow) = arrow := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  let deckAction := deckCovActionHom diagram root level
  let auxiliaryMap := recoverAuxiliaryFunction diagram root level arrow
  have atBase : ∀ point,
      (arrow.hom.app root).hom.hom
          (SourceTemperoidAssociatedQuotient.mk
            (source.vertexObject root)
            (vertexDeckAction source deckAction root)
            (rootVertexPoint diagram root level, point)) =
        SourceTemperoidAssociatedQuotient.mk
          (source.vertexObject root)
          (vertexDeckAction source deckAction root)
          (rootVertexPoint diagram root level, auxiliaryMap point) := by
    intro point
    exact recoverAuxiliaryFunction_atBase diagram root level arrow point
  apply ObjectProperty.hom_ext
  apply SourceSemiGraphOfAnabelioids.CovObject.Hom.ext
  intro vertex
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ConcreteCategory.hom_ext
  intro quotientPoint
  letI := SourceTemperoidAssociatedQuotient.diagonalMulAction
    (source.vertexObject vertex)
    (vertexDeckAction source deckAction vertex) X.obj.V.obj
  induction quotientPoint using Quotient.inductionOn' with
  | _ point =>
      exact (map_mk_of_isPointConnected
        source deckAction root (rootVertexPoint diagram root level)
        (covObject_isPointConnected diagram root level)
        arrow.hom auxiliaryMap atBase vertex point.1 point.2).symm

/-- The finite-level geometric associated-quotient functor is full: every
geometric morphism is induced by its uniquely recovered deck-equivariant
auxiliary map. -/
@[reducible]
noncomputable def associatedTemperedFunctorFull
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    (associatedTemperedFunctor diagram root level).Full where
  map_surjective arrow :=
    ⟨recoverAuxiliaryMap diagram root level arrow,
      associatedTemperedFunctor_map_recoverAuxiliaryMap
        diagram root level arrow⟩

/-- Root normalization recovers the original point map from every morphism
that was produced by the associated-quotient functor. -/
theorem recoverAuxiliaryFunction_map
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge]
    {X Y : SourceTemperoidAction (DeckGroup diagram root level)}
    (map : X ⟶ Y) (point : X.obj.V.obj) :
    recoverAuxiliaryFunction diagram root level
        ((associatedTemperedFunctor diagram root level).map map) point =
      map.hom.hom point := by
  apply (rootAssociatedCarrierEquiv diagram root level Y).injective
  rw [rootAssociatedCarrierEquiv_recoverAuxiliaryFunction]
  rfl

/-- Consequently the finite-level geometric associated-quotient functor is
faithful: its root constituent already recovers every equivariant map of
auxiliary deck-actions. -/
@[reducible]
noncomputable def associatedTemperedFunctorFaithful
    (diagram : SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex)
    (level : SourceSemiGraphOfAnabelioids.GluedObject.GaloisLevel
      diagram root)
    [Finite diagram.base.Vertex] [Finite diagram.base.Edge] :
    (associatedTemperedFunctor diagram root level).Faithful := by
  letI : Countable diagram.base.Vertex := Finite.to_countable
  letI : Countable diagram.base.Edge := Finite.to_countable
  let source := SourceFiniteLevelUniversalCover.covObject
    diagram root level.object level.rootVertex
  let deckAction :=
    SourceSemiGraphOfAnabelioids.CovObject.AssociatedQuotient.vertexDeckAction
      source (deckCovActionHom diagram root level) root
  let free := rootVertexDeckAction_isCancel diagram root level
  let faithful := SourceTemperoidAssociatedQuotient.functorFaithful
    (source.vertexObject root) deckAction
    (rootVertexPoint diagram root level) free
  constructor
  intro X Y first second equality
  apply faithful.map_injective
  exact congrArg
    (fun arrow : (associatedTemperedFunctor diagram root level).obj X ⟶
        (associatedTemperedFunctor diagram root level).obj Y ↦
      arrow.hom.app root) equality

end SourceCombinatorialUniversalCover.SourceGaloisCombinatorialUniversalCover

end Iut
