/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedDeckGroup
import Iut.Foundations.SourceTemperoid

/-!
# Factoring connected tempered actions through one inverse-limit level

The final sentence of the proof of *Semi-graphs of Anabelioids*, Proposition
3.6(ii), passes from the discrete deck groups at finite levels to their inverse
limit.  This file makes that passage explicit on the action side.

A connected continuous action of a cofiltered inverse limit has an open point
stabilizer.  One sufficiently fine normal coordinate kernel lies in that
stabilizer, hence fixes the complete transitive action.  If the coordinate is
surjective, the action therefore descends to that discrete level and pulling
it back along the coordinate projection recovers the original action.
-/

namespace Iut

universe u v w

open CategoryTheory
open scoped SourceCountableTypeCatDiscrete

namespace SourceTemperedGroupPresentation

variable {Index : Type u} [Category.{v} Index]
    (system : SourceTemperedGroupPresentation Index)

/-- Equality of one coordinate implies equality of the induced action when
that coordinate kernel acts trivially. -/
theorem smul_eq_of_projection_eq
    {X : Type w} [MulAction system.Limit X]
    (level : Index)
    (kernelFixes : ∀ (element : system.Limit),
      system.projection level element = 1 →
        ∀ point : X, element • point = point)
    {first second : system.Limit}
    (projection_eq : system.projection level first =
      system.projection level second)
    (point : X) : first • point = second • point := by
  have quotientTrivial :
      system.projection level (second⁻¹ * first) = 1 := by
    rw [map_mul, map_inv, projection_eq]
    simp
  have fixes := kernelFixes (second⁻¹ * first) quotientTrivial point
  calc
    first • point = (second * (second⁻¹ * first)) • point := by
      rw [mul_inv_cancel_left]
    _ = second • ((second⁻¹ * first) • point) :=
      mul_smul _ _ _
    _ = second • point := congrArg (second • ·) fixes

/-- A surjective coordinate projection transports a kernel-trivial action to
the corresponding discrete level. -/
@[reducible] noncomputable def descendedSMul
    {X : Type w} [MulAction system.Limit X]
    (level : Index)
    (projectionSurjective : Function.Surjective (system.projection level)) :
    SMul (system.DiscreteLevel level) X where
  smul coordinate point :=
    Classical.choose (projectionSurjective coordinate) • point

/-- The chosen lift used by the descended scalar action projects to the
requested coordinate. -/
theorem projection_choose_preimage
    (level : Index)
    (projectionSurjective : Function.Surjective (system.projection level))
    (coordinate : system.DiscreteLevel level) :
    system.projection level
        (Classical.choose (projectionSurjective coordinate)) = coordinate :=
  Classical.choose_spec (projectionSurjective coordinate)

/-- Kernel triviality makes the descended scalar action lawful. -/
@[reducible] noncomputable def descendedMulAction
    {X : Type w} [MulAction system.Limit X]
    (level : Index)
    (projectionSurjective : Function.Surjective (system.projection level))
    (kernelFixes : ∀ (element : system.Limit),
      system.projection level element = 1 →
        ∀ point : X, element • point = point) :
    MulAction (system.DiscreteLevel level) X where
  smul coordinate point :=
    Classical.choose (projectionSurjective coordinate) • point
  one_smul point := by
    change (Classical.choose (projectionSurjective 1) : system.Limit) •
      point = point
    exact kernelFixes _
      (system.projection_choose_preimage level projectionSurjective 1) point
  mul_smul first second point := by
    let firstLift : system.Limit :=
      Classical.choose (projectionSurjective first)
    let secondLift : system.Limit :=
      Classical.choose (projectionSurjective second)
    change Classical.choose (projectionSurjective (first * second)) • point =
      firstLift • (secondLift • point)
    rw [← mul_smul firstLift secondLift point]
    apply system.smul_eq_of_projection_eq level kernelFixes
    calc
      system.projection level
          (Classical.choose (projectionSurjective (first * second))) =
          first * second :=
        system.projection_choose_preimage
          level projectionSurjective (first * second)
      _ = system.projection level firstLift *
          system.projection level secondLift :=
        congrArg₂ (fun left right ↦ left * right)
          (system.projection_choose_preimage
            level projectionSurjective first).symm
          (system.projection_choose_preimage
            level projectionSurjective second).symm
      _ = system.projection level (firstLift * secondLift) :=
        (map_mul (system.projection level) firstLift secondLift).symm

/-- The countable continuous action at a discrete level obtained by descent. -/
noncomputable def descendedAction
    (object : SourceTemperoidAction.{w, max u v} system.Limit)
    (level : Index)
    (projectionSurjective : Function.Surjective (system.projection level))
    (kernelFixes : ∀ (element : system.Limit),
      system.projection level element = 1 →
        ∀ point : object.obj.V.obj, element • point = point) :
    SourceTemperoidAction.{w, max u v} (system.DiscreteLevel level) := by
  letI : MulAction (system.DiscreteLevel level) object.obj.V.obj :=
    system.descendedMulAction level projectionSurjective kernelFixes
  let action : Action SourceCountableTypeCat.{w}
      (system.DiscreteLevel level) :=
    SourceCountableTypeCat.ofMulAction (system.DiscreteLevel level)
      object.obj.V
  refine ⟨action, ?_⟩
  change ContinuousSMul (system.DiscreteLevel level)
    ((forget₂ (Action SourceCountableTypeCat.{w}
      (system.DiscreteLevel level)) TopCat).obj action)
  letI : DiscreteTopology
      ((forget₂ (Action SourceCountableTypeCat.{w}
        (system.DiscreteLevel level)) TopCat).obj action) := ⟨rfl⟩
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro point
  exact isOpen_discrete _

/-- Evaluation of the descended level action uses the selected preimage of
the level coordinate. -/
@[simp]
theorem descendedAction_apply
    (object : SourceTemperoidAction.{w, max u v} system.Limit)
    (level : Index)
    (projectionSurjective : Function.Surjective (system.projection level))
    (kernelFixes : ∀ (element : system.Limit),
      system.projection level element = 1 →
        ∀ point : object.obj.V.obj, element • point = point)
    (coordinate : system.DiscreteLevel level)
    (point : object.obj.V.obj) :
    ConcreteCategory.hom
        ((system.descendedAction object level projectionSurjective
          kernelFixes).obj.ρ coordinate) point =
      Classical.choose (projectionSurjective coordinate) • point :=
  rfl

/-- Descent preserves transitivity: a limit-group element carrying one point
to another projects to a level-group element with the same action. -/
theorem descendedAction_pretransitive
    (object : SourceConnectedTemperoid.{w, max u v} system.Limit)
    (level : Index)
    (projectionSurjective : Function.Surjective (system.projection level))
    (kernelFixes : ∀ (element : system.Limit),
      system.projection level element = 1 →
        ∀ point : object.obj.obj.V.obj, element • point = point) :
    MulAction.IsPretransitive (system.DiscreteLevel level)
      (system.descendedAction object.obj level projectionSurjective
        kernelFixes).obj.V.obj := by
  constructor
  intro first second
  change object.obj.obj.V.obj at first second
  obtain ⟨element, maps⟩ := object.property.2.exists_smul_eq first second
  refine ⟨system.projection level element, ?_⟩
  change (Classical.choose
      (projectionSurjective (system.projection level element)) :
        system.Limit) • first = second
  exact (system.smul_eq_of_projection_eq level kernelFixes
    (system.projection_choose_preimage level projectionSurjective
      (system.projection level element)) first).trans maps

/-- Pulling the descended action back along its coordinate projection gives
the original inverse-limit action on the same carrier. -/
noncomputable def descendedActionRestrictionIso
    (object : SourceTemperoidAction.{w, max u v} system.Limit)
    (level : Index)
    (projectionSurjective : Function.Surjective (system.projection level))
    (kernelFixes : ∀ (element : system.Limit),
      system.projection level element = 1 →
        ∀ point : object.obj.V.obj, element • point = point) :
    (ContAction.res SourceCountableTypeCat
      (system.continuousProjection level)).obj
        (system.descendedAction object level projectionSurjective kernelFixes) ≅
      object := by
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ (comm := ?_)
  · exact
      { hom := SourceCountableTypeCat.homMk id
        inv := SourceCountableTypeCat.homMk id
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          intro point
          rfl
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro point
          rfl }
  · intro element
    apply ConcreteCategory.hom_ext
    intro point
    simp only [SourceCountableTypeCat.comp_apply,
      SourceCountableTypeCat.homMk_apply, id_eq]
    change ConcreteCategory.hom
        ((system.descendedAction object level projectionSurjective
          kernelFixes).obj.ρ (system.projection level element)) point =
      ConcreteCategory.hom (object.obj.ρ element) point
    rw [system.descendedAction_apply]
    exact system.smul_eq_of_projection_eq level kernelFixes
      (system.projection_choose_preimage level projectionSurjective _) point

/-- A complete witness that a connected inverse-limit action comes from one
discrete coordinate. -/
structure ConnectedActionLevelFactorization
    (object : SourceConnectedTemperoid.{w, max u v} system.Limit) where
  level : Index
  levelAction : SourceTemperoidAction.{w, max u v}
    (system.DiscreteLevel level)
  levelConnected :
    sourceConnectedTemperoidAction.{w, max u v}
      (system.DiscreteLevel level) levelAction
  comparison :
    (ContAction.res SourceCountableTypeCat
      (system.continuousProjection level)).obj levelAction ≅ object.obj

/-- A coordinate kernel contained in one point stabilizer fixes every point
of a transitive action, since coordinate kernels are normal. -/
theorem projectionKernel_fixes_connectedAction
    [IsCofiltered Index]
    (object : SourceConnectedTemperoid.{w, max u v} system.Limit)
    (point : object.obj.obj.V.obj)
    (level : Index)
    (kernel_le_stabilizer :
      (system.projectionKernel level : Set system.Limit) ⊆
        MulAction.stabilizer system.Limit point) :
    ∀ (element : system.Limit),
      system.projection level element = 1 →
        ∀ target : object.obj.obj.V.obj, element • target = target := by
  intro element projectionTrivial target
  obtain ⟨transport, rfl⟩ :=
    object.property.2.exists_smul_eq point target
  have conjugateTrivial :
      system.projection level (transport⁻¹ * element * transport) = 1 := by
    rw [map_mul, map_mul, map_inv, projectionTrivial]
    simp
  have fixesPoint := kernel_le_stabilizer conjugateTrivial
  change (transport⁻¹ * element * transport) • point = point at fixesPoint
  calc
    element • transport • point = (element * transport) • point :=
      smul_smul _ _ _
    _ = (transport * (transport⁻¹ * element * transport)) • point :=
      congrArg (fun value : system.Limit ↦ value • point) (by group)
    _ = transport • ((transport⁻¹ * element * transport) • point) :=
      mul_smul _ _ _
    _ = transport • point := congrArg (transport • ·) fixesPoint

/-- Every connected action of a cofiltered inverse limit with surjective
coordinates descends to one discrete level. -/
noncomputable def connectedActionLevelFactorization
    [IsCofiltered Index]
    (projectionSurjective : ∀ level,
      Function.Surjective (system.projection level))
    (object : SourceConnectedTemperoid.{w, max u v} system.Limit) :
    system.ConnectedActionLevelFactorization object := by
  let point : object.obj.obj.V.obj := Classical.choice object.property.1
  have openStabilizer :
      IsOpen (MulAction.stabilizer system.Limit point : Set system.Limit) :=
    stabilizer_isOpen system.Limit point
  let existence :=
    system.exists_projectionKernel_le_of_mem_nhds_one
      (openStabilizer.mem_nhds (Subgroup.one_mem _))
  let level : Index := Classical.choose existence
  let kernel_le := Classical.choose_spec existence
  let kernelFixes := system.projectionKernel_fixes_connectedAction
    object point level kernel_le
  let levelAction := system.descendedAction object.obj level
    (projectionSurjective level) kernelFixes
  exact
    { level := level
      levelAction := levelAction
      levelConnected :=
        ⟨object.property.1,
          system.descendedAction_pretransitive object level
            (projectionSurjective level) kernelFixes⟩
      comparison := system.descendedActionRestrictionIso object.obj level
        (projectionSurjective level) kernelFixes }

end SourceTemperedGroupPresentation

namespace SourceCountableGroupDiagram

variable {Index : Type u} [Category.{v} Index]
    (system : SourceCountableGroupDiagram Index)

/-- For the canonical image presentation, coordinate surjectivity is derived
from the raw limit, so every connected action factors through one level with
no additional surjectivity input. -/
noncomputable def connectedActionLevelFactorization
    [IsCofiltered Index]
    (object : SourceConnectedTemperoid.{w, max u v}
      system.imagePresentation.Limit) :
    system.imagePresentation.ConnectedActionLevelFactorization object :=
  system.imagePresentation.connectedActionLevelFactorization
    system.imagePresentation_projection_surjective object

end SourceCountableGroupDiagram

end Iut
