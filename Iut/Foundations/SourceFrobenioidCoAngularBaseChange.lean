/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidIsotropicBase

open CategoryTheory

/-!
# Co-angular base change between isotropic Frobenioid objects

This file constructs the common co-angular pre-steps used in the proof of
Frobenioids I, Proposition 2.2(ii).  It also records the identity and
composition coherence forced by the uniqueness clause for unit transport.
-/

namespace Iut.FrobenioidCoAngularBaseChange

universe u

noncomputable section

variable (F : FrobenioidPresentation.{u})

/-- Every isomorphism in the carrier of a Frobenioid is linear. -/
theorem isLinear_of_isIso
    {source target : F.carrier} (arrow : source ⟶ target)
    [IsIso arrow] :
    F.preFrobenioid.IsLinear arrow := by
  change F.preFrobenioid.frobeniusDegree arrow = 1
  have identity := congrArg F.preFrobenioid.frobeniusDegree
    (IsIso.hom_inv_id arrow)
  rw [F.preFrobenioid.frobeniusDegree_comp,
    F.preFrobenioid.frobeniusDegree_id] at identity
  apply PNat.eq
  have valueIdentity := congrArg PNat.val identity
  exact Nat.eq_one_of_dvd_one
    ⟨(F.preFrobenioid.frobeniusDegree (inv arrow)).val,
      valueIdentity.symm⟩

/-- Every carrier isomorphism is a pre-step. -/
theorem isPreStep_of_isIso
    {source target : F.carrier} (arrow : source ⟶ target)
    [IsIso arrow] :
    F.preFrobenioid.IsPreStep arrow := by
  refine ⟨isLinear_of_isIso F arrow, ?_⟩
  change IsIso (F.preFrobenioid.base.map arrow)
  infer_instance

/-- Pre-steps are closed under composition. -/
theorem isPreStep_comp
    {source middle target : F.carrier}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (firstPreStep : F.preFrobenioid.IsPreStep first)
    (secondPreStep : F.preFrobenioid.IsPreStep second) :
    F.preFrobenioid.IsPreStep (first ≫ second) := by
  constructor
  · rw [PreFrobenioid.IsLinear,
      F.preFrobenioid.frobeniusDegree_comp,
      firstPreStep.1, secondPreStep.1]
    rfl
  · change IsIso (F.preFrobenioid.base.map (first ≫ second))
    rw [F.preFrobenioid.base.map_comp]
    haveI : IsIso (F.preFrobenioid.base.map first) := firstPreStep.2
    haveI : IsIso (F.preFrobenioid.base.map second) := secondPreStep.2
    infer_instance

/-- The literal identity transport used to identify the transport selected by
the Frobenioid axioms. -/
def identityUnitTransport (object : F.carrier) :
    F.preFrobenioid.CoAngularUnitTransport (𝟙 object) where
  transport := MulEquiv.refl _
  conjugates value := by
    change value.hom ≫ 𝟙 object = 𝟙 object ≫ value.hom
    simp

/-- On an isotropic object, the uniquely selected unit transport along the
identity is the literal identity equivalence. -/
theorem unitTransport_id
    (object : F.carrier)
    (isotropic : F.preFrobenioid.IsIsotropic object) :
    F.axioms.unitTransport (𝟙 object)
        (isPreStep_of_isIso F (𝟙 object))
        (FrobenioidRationalMonoidTransport.isCoAngular_of_isotropicSource
          F (𝟙 object) isotropic) =
      identityUnitTransport F object := by
  exact F.axioms.unitTransport_unique (𝟙 object)
    (isPreStep_of_isIso F (𝟙 object))
    (FrobenioidRationalMonoidTransport.isCoAngular_of_isotropicSource
      F (𝟙 object) isotropic)
    (F.axioms.unitTransport (𝟙 object)
      (isPreStep_of_isIso F (𝟙 object))
      (FrobenioidRationalMonoidTransport.isCoAngular_of_isotropicSource
        F (𝟙 object) isotropic))
    (identityUnitTransport F object)

/-- Compose two chosen unit transports. -/
def compUnitTransport
    {source middle target : F.carrier}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (firstPreStep : F.preFrobenioid.IsPreStep first)
    (firstCoAngular : F.preFrobenioid.IsCoAngular first)
    (secondPreStep : F.preFrobenioid.IsPreStep second)
    (secondCoAngular : F.preFrobenioid.IsCoAngular second) :
    F.preFrobenioid.CoAngularUnitTransport (first ≫ second) where
  transport :=
    (F.axioms.unitTransport first firstPreStep firstCoAngular).transport.trans
      (F.axioms.unitTransport second secondPreStep secondCoAngular).transport
  conjugates value := by
    rw [← Category.assoc,
      (F.axioms.unitTransport first firstPreStep firstCoAngular).conjugates,
      Category.assoc,
      (F.axioms.unitTransport second secondPreStep secondCoAngular).conjugates]
    simp only [MulEquiv.trans_apply]
    rw [Category.assoc]

/-- Uniqueness of unit transport forces compatibility with composition. -/
theorem unitTransport_comp
    {source middle target : F.carrier}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (firstPreStep : F.preFrobenioid.IsPreStep first)
    (firstCoAngular : F.preFrobenioid.IsCoAngular first)
    (secondPreStep : F.preFrobenioid.IsPreStep second)
    (secondCoAngular : F.preFrobenioid.IsCoAngular second) :
    F.axioms.unitTransport (first ≫ second)
        (isPreStep_comp F first second firstPreStep secondPreStep)
        (F.axioms.coAngular_comp first second
          firstCoAngular secondCoAngular) =
      compUnitTransport F first second firstPreStep firstCoAngular
        secondPreStep secondCoAngular := by
  exact F.axioms.unitTransport_unique (first ≫ second)
    (isPreStep_comp F first second firstPreStep secondPreStep)
    (F.axioms.coAngular_comp first second
      firstCoAngular secondCoAngular)
    (F.axioms.unitTransport (first ≫ second)
      (isPreStep_comp F first second firstPreStep secondPreStep)
      (F.axioms.coAngular_comp first second
        firstCoAngular secondCoAngular))
    (compUnitTransport F first second firstPreStep firstCoAngular
      secondPreStep secondCoAngular)

/-- A common pair of co-angular pre-steps over a prescribed base isomorphism,
with an isotropic common source. -/
structure CommonCoAngularPreStepWitness
    (left right : FrobenioidIsotropicBase.DStar F)
    (baseIso :
      F.preFrobenioid.base.obj left.object ≅
        F.preFrobenioid.base.obj right.object) where
  midpoint : F.carrier
  midpoint_isotropic : F.preFrobenioid.IsIsotropic midpoint
  toLeft : midpoint ⟶ left.object
  toRight : midpoint ⟶ right.object
  toLeft_preStep : F.preFrobenioid.IsPreStep toLeft
  toRight_preStep : F.preFrobenioid.IsPreStep toRight
  toLeft_coAngular : F.preFrobenioid.IsCoAngular toLeft
  toRight_coAngular : F.preFrobenioid.IsCoAngular toRight
  leftBaseInverse :
    F.preFrobenioid.base.obj left.object ⟶
      F.preFrobenioid.base.obj midpoint
  leftBaseInverse_hom :
    leftBaseInverse ≫ F.preFrobenioid.base.map toLeft =
      𝟙 (F.preFrobenioid.base.obj left.object)
  hom_leftBaseInverse :
    F.preFrobenioid.base.map toLeft ≫ leftBaseInverse =
      𝟙 (F.preFrobenioid.base.obj midpoint)
  comparison :
    leftBaseInverse ≫
        F.preFrobenioid.base.map toRight =
      baseIso.hom

/-- Definition 1.3(i)(b), followed by an isotropic hull, supplies the common
co-angular pre-steps used in Proposition 2.2(ii). -/
def commonCoAngularPreSteps
    (left right : FrobenioidIsotropicBase.DStar F)
    (baseIso :
      F.preFrobenioid.base.obj left.object ≅
        F.preFrobenioid.base.obj right.object) :
    CommonCoAngularPreStepWitness F left right baseIso := by
  let common := Classical.choice
    (F.axioms.commonPreSteps left.object right.object baseIso)
  let hull := Classical.choice (F.axioms.isotropicHull common.midpoint)
  let toLeft := Classical.choose
    (hull.lift common.toLeft left.isotropic)
  have toLeftRelation := (Classical.choose_spec
    (hull.lift common.toLeft left.isotropic)).1
  let toRight := Classical.choose
    (hull.lift common.toRight right.isotropic)
  have toRightRelation := (Classical.choose_spec
    (hull.lift common.toRight right.isotropic)).1
  have toLeftLinear : F.preFrobenioid.IsLinear toLeft := by
    change F.preFrobenioid.frobeniusDegree toLeft = 1
    have degrees := congrArg F.preFrobenioid.frobeniusDegree
      toLeftRelation
    rw [F.preFrobenioid.frobeniusDegree_comp,
      hull.preStep.1, common.toLeft_preStep.1] at degrees
    simpa using degrees
  have toRightLinear : F.preFrobenioid.IsLinear toRight := by
    change F.preFrobenioid.frobeniusDegree toRight = 1
    have degrees := congrArg F.preFrobenioid.frobeniusDegree
      toRightRelation
    rw [F.preFrobenioid.frobeniusDegree_comp,
      hull.preStep.1, common.toRight_preStep.1] at degrees
    simpa using degrees
  have toLeftBaseIso : F.preFrobenioid.IsBaseIso toLeft := by
    change IsIso (F.preFrobenioid.base.map toLeft)
    have compositeIsIso :
        IsIso (F.preFrobenioid.base.map hull.hom ≫
          F.preFrobenioid.base.map toLeft) := by
      rw [← F.preFrobenioid.base.map_comp, toLeftRelation]
      exact common.toLeft_preStep.2
    haveI : IsIso (F.preFrobenioid.base.map hull.hom ≫
        F.preFrobenioid.base.map toLeft) := compositeIsIso
    haveI : IsIso (F.preFrobenioid.base.map hull.hom) := hull.preStep.2
    exact IsIso.of_isIso_comp_left
      (F.preFrobenioid.base.map hull.hom)
      (F.preFrobenioid.base.map toLeft)
  have toRightBaseIso : F.preFrobenioid.IsBaseIso toRight := by
    change IsIso (F.preFrobenioid.base.map toRight)
    have compositeIsIso :
        IsIso (F.preFrobenioid.base.map hull.hom ≫
          F.preFrobenioid.base.map toRight) := by
      rw [← F.preFrobenioid.base.map_comp, toRightRelation]
      exact common.toRight_preStep.2
    haveI : IsIso (F.preFrobenioid.base.map hull.hom ≫
        F.preFrobenioid.base.map toRight) := compositeIsIso
    haveI : IsIso (F.preFrobenioid.base.map hull.hom) := hull.preStep.2
    exact IsIso.of_isIso_comp_left
      (F.preFrobenioid.base.map hull.hom)
      (F.preFrobenioid.base.map toRight)
  have toLeftPreStep : F.preFrobenioid.IsPreStep toLeft :=
    ⟨toLeftLinear, toLeftBaseIso⟩
  have toRightPreStep : F.preFrobenioid.IsPreStep toRight :=
    ⟨toRightLinear, toRightBaseIso⟩
  have toLeftCoAngular : F.preFrobenioid.IsCoAngular toLeft :=
    FrobenioidRationalMonoidTransport.isCoAngular_of_isotropicSource
      F toLeft hull.isotropic
  have toRightCoAngular : F.preFrobenioid.IsCoAngular toRight :=
    FrobenioidRationalMonoidTransport.isCoAngular_of_isotropicSource
      F toRight hull.isotropic
  letI : IsIso (F.preFrobenioid.base.map toLeft) := toLeftBaseIso
  letI : IsIso (F.preFrobenioid.base.map toRight) := toRightBaseIso
  refine
    { midpoint := hull.hull
      midpoint_isotropic := hull.isotropic
      toLeft := toLeft
      toRight := toRight
      toLeft_preStep := toLeftPreStep
      toRight_preStep := toRightPreStep
      toLeft_coAngular := toLeftCoAngular
      toRight_coAngular := toRightCoAngular
      leftBaseInverse := inv (F.preFrobenioid.base.map toLeft)
      leftBaseInverse_hom := by simp
      hom_leftBaseInverse := by simp
      comparison := ?_ }
  have hullBaseIsIso : IsIso (F.preFrobenioid.base.map hull.hom) :=
    hull.preStep.2
  letI : IsIso (F.preFrobenioid.base.map hull.hom) := hullBaseIsIso
  have commonLeftBaseIsIso :
      IsIso (F.preFrobenioid.base.map common.toLeft) :=
    common.toLeft_preStep.2
  letI : IsIso (F.preFrobenioid.base.map common.toLeft) :=
    commonLeftBaseIsIso
  have leftBaseRelation := congrArg F.preFrobenioid.base.map
    toLeftRelation
  have rightBaseRelation := congrArg F.preFrobenioid.base.map
    toRightRelation
  rw [F.preFrobenioid.base.map_comp] at leftBaseRelation
  rw [F.preFrobenioid.base.map_comp] at rightBaseRelation
  have inverseToLeft :
      inv (F.preFrobenioid.base.map toLeft) =
        common.leftBaseInverse ≫
          F.preFrobenioid.base.map hull.hom := by
    apply (cancel_mono (F.preFrobenioid.base.map toLeft)).1
    rw [IsIso.inv_hom_id]
    symm
    calc
      (common.leftBaseInverse ≫
            F.preFrobenioid.base.map hull.hom) ≫
          F.preFrobenioid.base.map toLeft =
        common.leftBaseInverse ≫
          (F.preFrobenioid.base.map hull.hom ≫
            F.preFrobenioid.base.map toLeft) :=
        Category.assoc _ _ _
      _ = common.leftBaseInverse ≫
          F.preFrobenioid.base.map common.toLeft := by
        rw [leftBaseRelation]
      _ = 𝟙 _ := common.leftBaseInverse_hom
  calc
    inv (F.preFrobenioid.base.map toLeft) ≫
          F.preFrobenioid.base.map toRight =
        (common.leftBaseInverse ≫
            F.preFrobenioid.base.map hull.hom) ≫
          F.preFrobenioid.base.map toRight := by
      rw [inverseToLeft]
    _ = common.leftBaseInverse ≫
          (F.preFrobenioid.base.map hull.hom ≫
            F.preFrobenioid.base.map toRight) :=
      Category.assoc _ _ _
    _ = common.leftBaseInverse ≫
          F.preFrobenioid.base.map common.toRight := by
      rw [rightBaseRelation]
    _ = baseIso.hom := common.comparison

namespace CommonCoAngularPreStepWitness

variable {F}
variable {left right : FrobenioidIsotropicBase.DStar F}
variable {baseIso :
  F.preFrobenioid.base.obj left.object ≅
    F.preFrobenioid.base.obj right.object}

/-- The right base map is the left base map followed by the prescribed base
isomorphism. -/
theorem rightBase_eq_leftBase_comp
    (witness : CommonCoAngularPreStepWitness F left right baseIso) :
    F.preFrobenioid.base.map witness.toRight =
      F.preFrobenioid.base.map witness.toLeft ≫ baseIso.hom := by
  calc
    F.preFrobenioid.base.map witness.toRight =
        𝟙 _ ≫ F.preFrobenioid.base.map witness.toRight := by simp
    _ = (F.preFrobenioid.base.map witness.toLeft ≫
          witness.leftBaseInverse) ≫
        F.preFrobenioid.base.map witness.toRight := by
      rw [witness.hom_leftBaseInverse]
    _ = F.preFrobenioid.base.map witness.toLeft ≫
        (witness.leftBaseInverse ≫
          F.preFrobenioid.base.map witness.toRight) :=
      Category.assoc _ _ _
    _ = F.preFrobenioid.base.map witness.toLeft ≫ baseIso.hom := by
      rw [witness.comparison]

/-- The multiplicative equivalence attached to one common co-angular witness. -/
def rationalMonoidEquiv
    (witness : CommonCoAngularPreStepWitness F left right baseIso) :
    F.preFrobenioid.LinearBaseIdentityEndomorphism left.object ≃*
      F.preFrobenioid.LinearBaseIdentityEndomorphism right.object :=
  (F.axioms.unitTransport witness.toLeft witness.toLeft_preStep
      witness.toLeft_coAngular).transport.symm.trans
    (F.axioms.unitTransport witness.toRight witness.toRight_preStep
      witness.toRight_coAngular).transport

/-- The equivalence obtained from common co-angular pre-steps is independent
of the chosen common witness. -/
theorem rationalMonoidEquiv_eq
    (first second : CommonCoAngularPreStepWitness F left right baseIso) :
    first.rationalMonoidEquiv = second.rationalMonoidEquiv := by
  let firstMidpoint : FrobenioidIsotropicBase.DStar F :=
    { object := first.midpoint
      isotropic := first.midpoint_isotropic }
  let secondMidpoint : FrobenioidIsotropicBase.DStar F :=
    { object := second.midpoint
      isotropic := second.midpoint_isotropic }
  letI : IsIso (F.preFrobenioid.base.map first.toLeft) :=
    first.toLeft_preStep.2
  letI : IsIso (F.preFrobenioid.base.map second.toLeft) :=
    second.toLeft_preStep.2
  let midpointIso :
      F.preFrobenioid.base.obj first.midpoint ≅
        F.preFrobenioid.base.obj second.midpoint :=
    asIso (F.preFrobenioid.base.map first.toLeft) ≪≫
      (asIso (F.preFrobenioid.base.map second.toLeft)).symm
  let refinement := commonCoAngularPreSteps F
    firstMidpoint secondMidpoint midpointIso
  have refinementRightBase :
      F.preFrobenioid.base.map refinement.toRight =
        F.preFrobenioid.base.map refinement.toLeft ≫
          midpointIso.hom :=
    refinement.rightBase_eq_leftBase_comp
  have leftCompositeBase :
      F.preFrobenioid.base.map
          (refinement.toLeft ≫ first.toLeft) =
        F.preFrobenioid.base.map
          (refinement.toRight ≫ second.toLeft) := by
    rw [F.preFrobenioid.base.map_comp,
      F.preFrobenioid.base.map_comp, refinementRightBase]
    simp [midpointIso, Category.assoc]
  have rightCompositeBase :
      F.preFrobenioid.base.map
          (refinement.toLeft ≫ first.toRight) =
        F.preFrobenioid.base.map
          (refinement.toRight ≫ second.toRight) := by
    rw [F.preFrobenioid.base.map_comp,
      F.preFrobenioid.base.map_comp,
      first.rightBase_eq_leftBase_comp,
      second.rightBase_eq_leftBase_comp,
      refinementRightBase]
    simp [midpointIso, Category.assoc]
  have firstLeftPreStep := isPreStep_comp F
    refinement.toLeft first.toLeft
    refinement.toLeft_preStep first.toLeft_preStep
  have secondLeftPreStep := isPreStep_comp F
    refinement.toRight second.toLeft
    refinement.toRight_preStep second.toLeft_preStep
  have firstRightPreStep := isPreStep_comp F
    refinement.toLeft first.toRight
    refinement.toLeft_preStep first.toRight_preStep
  have secondRightPreStep := isPreStep_comp F
    refinement.toRight second.toRight
    refinement.toRight_preStep second.toRight_preStep
  have firstLeftCoAngular : F.preFrobenioid.IsCoAngular
      (refinement.toLeft ≫ first.toLeft) :=
    F.axioms.coAngular_comp refinement.toLeft first.toLeft
      refinement.toLeft_coAngular first.toLeft_coAngular
  have secondLeftCoAngular : F.preFrobenioid.IsCoAngular
      (refinement.toRight ≫ second.toLeft) :=
    F.axioms.coAngular_comp refinement.toRight second.toLeft
      refinement.toRight_coAngular second.toLeft_coAngular
  have firstRightCoAngular : F.preFrobenioid.IsCoAngular
      (refinement.toLeft ≫ first.toRight) :=
    F.axioms.coAngular_comp refinement.toLeft first.toRight
      refinement.toLeft_coAngular first.toRight_coAngular
  have secondRightCoAngular : F.preFrobenioid.IsCoAngular
      (refinement.toRight ≫ second.toRight) :=
    F.axioms.coAngular_comp refinement.toRight second.toRight
      refinement.toRight_coAngular second.toRight_coAngular
  have selectedLeftEquality :=
    F.axioms.unitTransport_dependsOnlyOnBase
      (refinement.toLeft ≫ first.toLeft)
      (refinement.toRight ≫ second.toLeft)
      firstLeftPreStep firstLeftCoAngular
      secondLeftPreStep secondLeftCoAngular leftCompositeBase
  have selectedRightEquality :=
    F.axioms.unitTransport_dependsOnlyOnBase
      (refinement.toLeft ≫ first.toRight)
      (refinement.toRight ≫ second.toRight)
      firstRightPreStep firstRightCoAngular
      secondRightPreStep secondRightCoAngular rightCompositeBase
  have firstLeftComposition := congrArg
    PreFrobenioid.CoAngularUnitTransport.transport
    (unitTransport_comp F refinement.toLeft first.toLeft
      refinement.toLeft_preStep refinement.toLeft_coAngular
      first.toLeft_preStep first.toLeft_coAngular)
  have secondLeftComposition := congrArg
    PreFrobenioid.CoAngularUnitTransport.transport
    (unitTransport_comp F refinement.toRight second.toLeft
      refinement.toRight_preStep refinement.toRight_coAngular
      second.toLeft_preStep second.toLeft_coAngular)
  have firstRightComposition := congrArg
    PreFrobenioid.CoAngularUnitTransport.transport
    (unitTransport_comp F refinement.toLeft first.toRight
      refinement.toLeft_preStep refinement.toLeft_coAngular
      first.toRight_preStep first.toRight_coAngular)
  have secondRightComposition := congrArg
    PreFrobenioid.CoAngularUnitTransport.transport
    (unitTransport_comp F refinement.toRight second.toRight
      refinement.toRight_preStep refinement.toRight_coAngular
      second.toRight_preStep second.toRight_coAngular)
  let refineFirst :=
    (F.axioms.unitTransport refinement.toLeft
      refinement.toLeft_preStep refinement.toLeft_coAngular).transport
  let refineSecond :=
    (F.axioms.unitTransport refinement.toRight
      refinement.toRight_preStep refinement.toRight_coAngular).transport
  let firstLeft :=
    (F.axioms.unitTransport first.toLeft
      first.toLeft_preStep first.toLeft_coAngular).transport
  let secondLeft :=
    (F.axioms.unitTransport second.toLeft
      second.toLeft_preStep second.toLeft_coAngular).transport
  let firstRight :=
    (F.axioms.unitTransport first.toRight
      first.toRight_preStep first.toRight_coAngular).transport
  let secondRight :=
    (F.axioms.unitTransport second.toRight
      second.toRight_preStep second.toRight_coAngular).transport
  have leftTransportEquality :
      refineFirst.trans firstLeft = refineSecond.trans secondLeft := by
    calc
      refineFirst.trans firstLeft =
          (F.axioms.unitTransport
            (refinement.toLeft ≫ first.toLeft)
            firstLeftPreStep firstLeftCoAngular).transport := by
        exact firstLeftComposition.symm
      _ = (F.axioms.unitTransport
            (refinement.toRight ≫ second.toLeft)
            secondLeftPreStep secondLeftCoAngular).transport :=
        selectedLeftEquality
      _ = refineSecond.trans secondLeft := secondLeftComposition
  have rightTransportEquality :
      refineFirst.trans firstRight = refineSecond.trans secondRight := by
    calc
      refineFirst.trans firstRight =
          (F.axioms.unitTransport
            (refinement.toLeft ≫ first.toRight)
            firstRightPreStep firstRightCoAngular).transport := by
        exact firstRightComposition.symm
      _ = (F.axioms.unitTransport
            (refinement.toRight ≫ second.toRight)
            secondRightPreStep secondRightCoAngular).transport :=
        selectedRightEquality
      _ = refineSecond.trans secondRight := secondRightComposition
  apply MulEquiv.ext
  intro value
  let commonValue := refineFirst.symm (firstLeft.symm value)
  have leftAtCommon := DFunLike.congr_fun leftTransportEquality commonValue
  have secondMidpointValue :
      refineSecond commonValue = secondLeft.symm value := by
    apply secondLeft.injective
    simpa [commonValue] using leftAtCommon.symm
  have rightAtCommon := DFunLike.congr_fun rightTransportEquality commonValue
  change firstRight (firstLeft.symm value) =
    secondRight (secondLeft.symm value)
  simpa [commonValue, secondMidpointValue] using rightAtCommon

end CommonCoAngularPreStepWitness

/-- The canonical base-isomorphism transport, defined using one selected
common co-angular witness. -/
def baseIsoRationalMonoidEquiv
    (left right : FrobenioidIsotropicBase.DStar F)
    (baseIso :
      F.preFrobenioid.base.obj left.object ≅
        F.preFrobenioid.base.obj right.object) :
    F.preFrobenioid.LinearBaseIdentityEndomorphism left.object ≃*
      F.preFrobenioid.LinearBaseIdentityEndomorphism right.object :=
  (commonCoAngularPreSteps F left right baseIso).rationalMonoidEquiv

/-- Every common witness computes the canonical base-isomorphism transport. -/
theorem rationalMonoidEquiv_eq_baseIsoRationalMonoidEquiv
    {left right : FrobenioidIsotropicBase.DStar F}
    {baseIso :
      F.preFrobenioid.base.obj left.object ≅
        F.preFrobenioid.base.obj right.object}
    (witness : CommonCoAngularPreStepWitness F left right baseIso) :
    witness.rationalMonoidEquiv =
      baseIsoRationalMonoidEquiv F left right baseIso :=
  witness.rationalMonoidEquiv_eq
    (commonCoAngularPreSteps F left right baseIso)

/-- The common witness consisting of two identity arrows. -/
def identityCommonCoAngularPreStepWitness
    (object : FrobenioidIsotropicBase.DStar F) :
    CommonCoAngularPreStepWitness F object object
      (Iso.refl (F.preFrobenioid.base.obj object.object)) where
  midpoint := object.object
  midpoint_isotropic := object.isotropic
  toLeft := 𝟙 object.object
  toRight := 𝟙 object.object
  toLeft_preStep := isPreStep_of_isIso F (𝟙 object.object)
  toRight_preStep := isPreStep_of_isIso F (𝟙 object.object)
  toLeft_coAngular :=
    FrobenioidRationalMonoidTransport.isCoAngular_of_isotropicSource
      F (𝟙 object.object) object.isotropic
  toRight_coAngular :=
    FrobenioidRationalMonoidTransport.isCoAngular_of_isotropicSource
      F (𝟙 object.object) object.isotropic
  leftBaseInverse := 𝟙 _
  leftBaseInverse_hom := by simp
  hom_leftBaseInverse := by simp
  comparison := by simp

/-- Canonical transport along the identity base isomorphism is the identity. -/
theorem baseIsoRationalMonoidEquiv_refl
    (object : FrobenioidIsotropicBase.DStar F) :
    baseIsoRationalMonoidEquiv F object object
        (Iso.refl (F.preFrobenioid.base.obj object.object)) =
      MulEquiv.refl
        (F.preFrobenioid.LinearBaseIdentityEndomorphism object.object) := by
  rw [← rationalMonoidEquiv_eq_baseIsoRationalMonoidEquiv F
    (identityCommonCoAngularPreStepWitness F object)]
  apply MulEquiv.ext
  intro value
  simp [CommonCoAngularPreStepWitness.rationalMonoidEquiv,
    identityCommonCoAngularPreStepWitness]

namespace CommonCoAngularPreStepWitness

variable {F}
variable {left right : FrobenioidIsotropicBase.DStar F}
variable {baseIso :
  F.preFrobenioid.base.obj left.object ≅
    F.preFrobenioid.base.obj right.object}

/-- Reverse a common witness. -/
def symm
    (witness : CommonCoAngularPreStepWitness F left right baseIso) :
    CommonCoAngularPreStepWitness F right left baseIso.symm where
  midpoint := witness.midpoint
  midpoint_isotropic := witness.midpoint_isotropic
  toLeft := witness.toRight
  toRight := witness.toLeft
  toLeft_preStep := witness.toRight_preStep
  toRight_preStep := witness.toLeft_preStep
  toLeft_coAngular := witness.toRight_coAngular
  toRight_coAngular := witness.toLeft_coAngular
  leftBaseInverse := baseIso.inv ≫ witness.leftBaseInverse
  leftBaseInverse_hom := by
    rw [Category.assoc, witness.comparison]
    simp
  hom_leftBaseInverse := by
    rw [witness.rightBase_eq_leftBase_comp]
    simp [Category.assoc, witness.hom_leftBaseInverse]
  comparison := by
    simp [Category.assoc, witness.leftBaseInverse_hom]

/-- Reversing the common witness reverses its rational-monoid equivalence. -/
theorem symm_rationalMonoidEquiv
    (witness : CommonCoAngularPreStepWitness F left right baseIso) :
    witness.symm.rationalMonoidEquiv =
      witness.rationalMonoidEquiv.symm := by
  rfl

variable {middle : FrobenioidIsotropicBase.DStar F}
variable {secondBaseIso :
  F.preFrobenioid.base.obj right.object ≅
    F.preFrobenioid.base.obj middle.object}

/-- The base isomorphism aligning the middle objects of two composable common
witnesses. -/
def compositionMidpointIso
    (first : CommonCoAngularPreStepWitness F left right baseIso)
    (second : CommonCoAngularPreStepWitness F right middle secondBaseIso) :
    F.preFrobenioid.base.obj first.midpoint ≅
      F.preFrobenioid.base.obj second.midpoint := by
  letI : IsIso (F.preFrobenioid.base.map first.toRight) :=
    first.toRight_preStep.2
  letI : IsIso (F.preFrobenioid.base.map second.toLeft) :=
    second.toLeft_preStep.2
  exact asIso (F.preFrobenioid.base.map first.toRight) ≪≫
    (asIso (F.preFrobenioid.base.map second.toLeft)).symm

/-- A common refinement aligning the middle legs of two composable common
witnesses. -/
def compositionRefinement
    (first : CommonCoAngularPreStepWitness F left right baseIso)
    (second : CommonCoAngularPreStepWitness F right middle secondBaseIso) :
    CommonCoAngularPreStepWitness F
      { object := first.midpoint
        isotropic := first.midpoint_isotropic }
      { object := second.midpoint
        isotropic := second.midpoint_isotropic }
      (compositionMidpointIso first second) :=
  commonCoAngularPreSteps F
    { object := first.midpoint
      isotropic := first.midpoint_isotropic }
    { object := second.midpoint
      isotropic := second.midpoint_isotropic }
    (compositionMidpointIso first second)

/-- Compose two common witnesses after refining their middle legs. -/
def comp
    (first : CommonCoAngularPreStepWitness F left right baseIso)
    (second : CommonCoAngularPreStepWitness F right middle secondBaseIso) :
    CommonCoAngularPreStepWitness F left middle
      (baseIso ≪≫ secondBaseIso) := by
  let refinement := compositionRefinement first second
  let toLeft := refinement.toLeft ≫ first.toLeft
  let toRight := refinement.toRight ≫ second.toRight
  have toLeftPreStep := isPreStep_comp F
    refinement.toLeft first.toLeft
    refinement.toLeft_preStep first.toLeft_preStep
  have toRightPreStep := isPreStep_comp F
    refinement.toRight second.toRight
    refinement.toRight_preStep second.toRight_preStep
  have toLeftCoAngular : F.preFrobenioid.IsCoAngular toLeft :=
    F.axioms.coAngular_comp refinement.toLeft first.toLeft
      refinement.toLeft_coAngular first.toLeft_coAngular
  have toRightCoAngular : F.preFrobenioid.IsCoAngular toRight :=
    F.axioms.coAngular_comp refinement.toRight second.toRight
      refinement.toRight_coAngular second.toRight_coAngular
  refine
    { midpoint := refinement.midpoint
      midpoint_isotropic := refinement.midpoint_isotropic
      toLeft := toLeft
      toRight := toRight
      toLeft_preStep := toLeftPreStep
      toRight_preStep := toRightPreStep
      toLeft_coAngular := toLeftCoAngular
      toRight_coAngular := toRightCoAngular
      leftBaseInverse :=
        first.leftBaseInverse ≫ refinement.leftBaseInverse
      leftBaseInverse_hom := ?_
      hom_leftBaseInverse := ?_
      comparison := ?_ }
  · rw [show F.preFrobenioid.base.map toLeft =
        F.preFrobenioid.base.map refinement.toLeft ≫
          F.preFrobenioid.base.map first.toLeft by
        simp [toLeft, F.preFrobenioid.base.map_comp]]
    calc
      (first.leftBaseInverse ≫ refinement.leftBaseInverse) ≫
            (F.preFrobenioid.base.map refinement.toLeft ≫
              F.preFrobenioid.base.map first.toLeft) =
          first.leftBaseInverse ≫
            (refinement.leftBaseInverse ≫
              F.preFrobenioid.base.map refinement.toLeft) ≫
                F.preFrobenioid.base.map first.toLeft := by
        simp only [Category.assoc]
      _ = first.leftBaseInverse ≫
            F.preFrobenioid.base.map first.toLeft := by
        rw [refinement.leftBaseInverse_hom]
        simp
      _ = 𝟙 _ := first.leftBaseInverse_hom
  · rw [show F.preFrobenioid.base.map toLeft =
        F.preFrobenioid.base.map refinement.toLeft ≫
          F.preFrobenioid.base.map first.toLeft by
        simp [toLeft, F.preFrobenioid.base.map_comp]]
    calc
      (F.preFrobenioid.base.map refinement.toLeft ≫
            F.preFrobenioid.base.map first.toLeft) ≫
          (first.leftBaseInverse ≫ refinement.leftBaseInverse) =
        F.preFrobenioid.base.map refinement.toLeft ≫
          (F.preFrobenioid.base.map first.toLeft ≫
            first.leftBaseInverse) ≫ refinement.leftBaseInverse := by
        simp only [Category.assoc]
      _ = F.preFrobenioid.base.map refinement.toLeft ≫
            refinement.leftBaseInverse := by
        rw [first.hom_leftBaseInverse]
        simp
      _ = 𝟙 _ := refinement.hom_leftBaseInverse
  · rw [show F.preFrobenioid.base.map toRight =
        F.preFrobenioid.base.map refinement.toRight ≫
          F.preFrobenioid.base.map second.toRight by
        simp [toRight, F.preFrobenioid.base.map_comp]]
    calc
      (first.leftBaseInverse ≫ refinement.leftBaseInverse) ≫
            (F.preFrobenioid.base.map refinement.toRight ≫
              F.preFrobenioid.base.map second.toRight) =
          first.leftBaseInverse ≫
            ((refinement.leftBaseInverse ≫
                F.preFrobenioid.base.map refinement.toRight) ≫
              F.preFrobenioid.base.map second.toRight) := by
        simp only [Category.assoc]
      _ = first.leftBaseInverse ≫
            (compositionMidpointIso first second).hom ≫
              F.preFrobenioid.base.map second.toRight := by
        rw [refinement.comparison]
      _ = (baseIso ≪≫ secondBaseIso).hom := by
        letI : IsIso (F.preFrobenioid.base.map first.toRight) :=
          first.toRight_preStep.2
        letI : IsIso (F.preFrobenioid.base.map second.toLeft) :=
          second.toLeft_preStep.2
        have midpointIsoHom :
            (compositionMidpointIso first second).hom =
              F.preFrobenioid.base.map first.toRight ≫
                inv (F.preFrobenioid.base.map second.toLeft) := by
          rfl
        rw [second.rightBase_eq_leftBase_comp]
        rw [midpointIsoHom]
        simp only [Category.assoc, IsIso.inv_hom_id_assoc]
        rw [← Category.assoc, first.comparison]
        rfl

/-- Rational-monoid transport computed from common witnesses respects
composition. -/
theorem comp_rationalMonoidEquiv
    (first : CommonCoAngularPreStepWitness F left right baseIso)
    (second : CommonCoAngularPreStepWitness F right middle secondBaseIso) :
    (first.comp second).rationalMonoidEquiv =
      first.rationalMonoidEquiv.trans second.rationalMonoidEquiv := by
  let refinement := first.compositionRefinement second
  have middleLeftPreStep := isPreStep_comp F
    refinement.toLeft first.toRight
    refinement.toLeft_preStep first.toRight_preStep
  have middleRightPreStep := isPreStep_comp F
    refinement.toRight second.toLeft
    refinement.toRight_preStep second.toLeft_preStep
  have middleLeftCoAngular : F.preFrobenioid.IsCoAngular
      (refinement.toLeft ≫ first.toRight) :=
    F.axioms.coAngular_comp refinement.toLeft first.toRight
      refinement.toLeft_coAngular first.toRight_coAngular
  have middleRightCoAngular : F.preFrobenioid.IsCoAngular
      (refinement.toRight ≫ second.toLeft) :=
    F.axioms.coAngular_comp refinement.toRight second.toLeft
      refinement.toRight_coAngular second.toLeft_coAngular
  have middleBaseEquality :
      F.preFrobenioid.base.map
          (refinement.toLeft ≫ first.toRight) =
        F.preFrobenioid.base.map
          (refinement.toRight ≫ second.toLeft) := by
    letI : IsIso (F.preFrobenioid.base.map first.toRight) :=
      first.toRight_preStep.2
    letI : IsIso (F.preFrobenioid.base.map second.toLeft) :=
      second.toLeft_preStep.2
    rw [F.preFrobenioid.base.map_comp,
      F.preFrobenioid.base.map_comp,
      refinement.rightBase_eq_leftBase_comp]
    simp [compositionMidpointIso, refinement, Category.assoc]
  have selectedMiddleEquality :=
    F.axioms.unitTransport_dependsOnlyOnBase
      (refinement.toLeft ≫ first.toRight)
      (refinement.toRight ≫ second.toLeft)
      middleLeftPreStep middleLeftCoAngular
      middleRightPreStep middleRightCoAngular middleBaseEquality
  have middleLeftComposition := congrArg
    PreFrobenioid.CoAngularUnitTransport.transport
    (unitTransport_comp F refinement.toLeft first.toRight
      refinement.toLeft_preStep refinement.toLeft_coAngular
      first.toRight_preStep first.toRight_coAngular)
  have middleRightComposition := congrArg
    PreFrobenioid.CoAngularUnitTransport.transport
    (unitTransport_comp F refinement.toRight second.toLeft
      refinement.toRight_preStep refinement.toRight_coAngular
      second.toLeft_preStep second.toLeft_coAngular)
  have compositeLeftComposition := congrArg
    PreFrobenioid.CoAngularUnitTransport.transport
    (unitTransport_comp F refinement.toLeft first.toLeft
      refinement.toLeft_preStep refinement.toLeft_coAngular
      first.toLeft_preStep first.toLeft_coAngular)
  have compositeRightComposition := congrArg
    PreFrobenioid.CoAngularUnitTransport.transport
    (unitTransport_comp F refinement.toRight second.toRight
      refinement.toRight_preStep refinement.toRight_coAngular
      second.toRight_preStep second.toRight_coAngular)
  let refineLeft :=
    (F.axioms.unitTransport refinement.toLeft
      refinement.toLeft_preStep refinement.toLeft_coAngular).transport
  let refineRight :=
    (F.axioms.unitTransport refinement.toRight
      refinement.toRight_preStep refinement.toRight_coAngular).transport
  let firstLeft :=
    (F.axioms.unitTransport first.toLeft
      first.toLeft_preStep first.toLeft_coAngular).transport
  let firstRight :=
    (F.axioms.unitTransport first.toRight
      first.toRight_preStep first.toRight_coAngular).transport
  let secondLeft :=
    (F.axioms.unitTransport second.toLeft
      second.toLeft_preStep second.toLeft_coAngular).transport
  let secondRight :=
    (F.axioms.unitTransport second.toRight
      second.toRight_preStep second.toRight_coAngular).transport
  have middleTransportEquality :
      refineLeft.trans firstRight = refineRight.trans secondLeft := by
    calc
      refineLeft.trans firstRight =
          (F.axioms.unitTransport
            (refinement.toLeft ≫ first.toRight)
            middleLeftPreStep middleLeftCoAngular).transport := by
        exact middleLeftComposition.symm
      _ = (F.axioms.unitTransport
            (refinement.toRight ≫ second.toLeft)
            middleRightPreStep middleRightCoAngular).transport :=
        selectedMiddleEquality
      _ = refineRight.trans secondLeft := middleRightComposition
  apply MulEquiv.ext
  intro value
  let commonValue := refineLeft.symm (firstLeft.symm value)
  have middleAtCommon :=
    DFunLike.congr_fun middleTransportEquality commonValue
  have secondMidpointValue :
      refineRight commonValue =
        secondLeft.symm (firstRight (firstLeft.symm value)) := by
    apply secondLeft.injective
    simpa [commonValue] using middleAtCommon.symm
  change
    (F.axioms.unitTransport
      (refinement.toRight ≫ second.toRight) _ _).transport
        ((F.axioms.unitTransport
          (refinement.toLeft ≫ first.toLeft) _ _).transport.symm value) =
      secondRight (secondLeft.symm (firstRight (firstLeft.symm value)))
  rw [compositeLeftComposition, compositeRightComposition]
  simp only [compUnitTransport, MulEquiv.trans_apply]
  change secondRight (refineRight commonValue) =
    secondRight (secondLeft.symm (firstRight (firstLeft.symm value)))
  rw [secondMidpointValue]

end CommonCoAngularPreStepWitness

/-- Canonical base-isomorphism transport respects inverses. -/
theorem baseIsoRationalMonoidEquiv_symm
    (left right : FrobenioidIsotropicBase.DStar F)
    (baseIso :
      F.preFrobenioid.base.obj left.object ≅
        F.preFrobenioid.base.obj right.object) :
    baseIsoRationalMonoidEquiv F right left baseIso.symm =
      (baseIsoRationalMonoidEquiv F left right baseIso).symm := by
  let witness := commonCoAngularPreSteps F left right baseIso
  calc
    baseIsoRationalMonoidEquiv F right left baseIso.symm =
        witness.symm.rationalMonoidEquiv :=
      (rationalMonoidEquiv_eq_baseIsoRationalMonoidEquiv F
        witness.symm).symm
    _ = witness.rationalMonoidEquiv.symm :=
      witness.symm_rationalMonoidEquiv
    _ = (baseIsoRationalMonoidEquiv F left right baseIso).symm := by
      rw [rationalMonoidEquiv_eq_baseIsoRationalMonoidEquiv F witness]

/-- Canonical base-isomorphism transport respects composition. -/
theorem baseIsoRationalMonoidEquiv_trans
    (left right middle : FrobenioidIsotropicBase.DStar F)
    (firstBaseIso :
      F.preFrobenioid.base.obj left.object ≅
        F.preFrobenioid.base.obj right.object)
    (secondBaseIso :
      F.preFrobenioid.base.obj right.object ≅
        F.preFrobenioid.base.obj middle.object) :
    baseIsoRationalMonoidEquiv F left middle
        (firstBaseIso ≪≫ secondBaseIso) =
      (baseIsoRationalMonoidEquiv F left right firstBaseIso).trans
        (baseIsoRationalMonoidEquiv F right middle secondBaseIso) := by
  let first := commonCoAngularPreSteps F left right firstBaseIso
  let second := commonCoAngularPreSteps F right middle secondBaseIso
  calc
    baseIsoRationalMonoidEquiv F left middle
          (firstBaseIso ≪≫ secondBaseIso) =
        (first.comp second).rationalMonoidEquiv :=
      (rationalMonoidEquiv_eq_baseIsoRationalMonoidEquiv F
        (first.comp second)).symm
    _ = first.rationalMonoidEquiv.trans second.rationalMonoidEquiv :=
      first.comp_rationalMonoidEquiv second
    _ = (baseIsoRationalMonoidEquiv F left right firstBaseIso).trans
          (baseIsoRationalMonoidEquiv F right middle secondBaseIso) := by
      rw [rationalMonoidEquiv_eq_baseIsoRationalMonoidEquiv F first,
        rationalMonoidEquiv_eq_baseIsoRationalMonoidEquiv F second]

end

end Iut.FrobenioidCoAngularBaseChange
