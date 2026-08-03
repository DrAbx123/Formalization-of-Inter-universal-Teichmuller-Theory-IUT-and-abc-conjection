/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidFactorization

/-!
# Essential uniqueness of source model Frobenioid factorizations

This file completes Frobenioids I, Definition 1.3(iv)(a), for the model
category.  The pullback-stage isomorphism is constructed from the two
representable universal properties, the Frobenius-stage isomorphism comes from
the equal-degree witness, and the middle square is derived from pullback full
faithfulness.  Total epimorphicity forces both comparison isomorphisms to be
unique.
-/

open CategoryTheory
namespace Iut.SourceModelFrobenioid.Carrier
universe u
noncomputable section
variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

theorem factorization_frobeniusDegree
    {source target : Carrier Phi data} {arrow : source ⟶ target}
    (factor : (preFrobenioid Phi data).FrobenioidFactorization arrow) :
    factor.frobenius.frobeniusDegree = arrow.frobeniusDegree := by
  have preStepLinear := factor.preStep_type.1
  change factor.preStep.frobeniusDegree = 1 at preStepLinear
  have pullbackLinear :=
    (pullback_linear_lbInvertible factor.pullback factor.pullback_type).1
  change factor.pullback.frobeniusDegree = 1 at pullbackLinear
  have projected := congrArg Hom.frobeniusDegree factor.composite
  change factor.frobenius.frobeniusDegree *
      (factor.preStep.frobeniusDegree * factor.pullback.frobeniusDegree) =
    arrow.frobeniusDegree at projected
  rw [preStepLinear, pullbackLinear] at projected
  simpa using projected

/-- The pullback-stage comparison, including its defining slice equations. -/
structure FactorizationPullbackComparison
    {source target : Carrier Phi data} {arrow : source ⟶ target}
    (left right : (preFrobenioid Phi data).FrobenioidFactorization arrow) where
  iso : left.preStepCodomain ≅ right.preStepCodomain
  hom_comp : iso.hom ≫ right.pullback = left.pullback
  inv_comp : iso.inv ≫ left.pullback = right.pullback
  prefix_hom :
    (left.frobenius.base ≫ left.preStep.base) ≫ iso.hom.base =
      right.frobenius.base ≫ right.preStep.base
  prefix_inv :
    (right.frobenius.base ≫ right.preStep.base) ≫ iso.inv.base =
      left.frobenius.base ≫ left.preStep.base

/-- The isomorphism between the pullback-stage objects of two factorizations. -/
def factorizationPullbackComparison
    {source target : Carrier Phi data} {arrow : source ⟶ target}
    (left right : (preFrobenioid Phi data).FrobenioidFactorization arrow) :
    FactorizationPullbackComparison left right := by
  have leftFrobeniusBaseIsIso := left.frobenius_type.2
  change IsIso left.frobenius.base at leftFrobeniusBaseIsIso
  letI : IsIso left.frobenius.base := leftFrobeniusBaseIsIso
  have leftPreStepBaseIsIso := left.preStep_type.2
  change IsIso left.preStep.base at leftPreStepBaseIsIso
  letI : IsIso left.preStep.base := leftPreStepBaseIsIso
  have rightFrobeniusBaseIsIso := right.frobenius_type.2
  change IsIso right.frobenius.base at rightFrobeniusBaseIsIso
  letI : IsIso right.frobenius.base := rightFrobeniusBaseIsIso
  have rightPreStepBaseIsIso := right.preStep_type.2
  change IsIso right.preStep.base at rightPreStepBaseIsIso
  letI : IsIso right.preStep.base := rightPreStepBaseIsIso
  let leftPrefix := left.frobenius.base ≫ left.preStep.base
  let rightPrefix := right.frobenius.base ≫ right.preStep.base
  let forwardBase := inv leftPrefix ≫ rightPrefix
  have forwardBaseComp :
      forwardBase ≫ right.pullback.base = left.pullback.base := by
    have leftCompositeBase := congrArg Hom.base left.composite
    rw [comp_base, comp_base, ← Category.assoc] at leftCompositeBase
    change leftPrefix ≫ left.pullback.base = arrow.base at leftCompositeBase
    have rightCompositeBase := congrArg Hom.base right.composite
    rw [comp_base, comp_base, ← Category.assoc] at rightCompositeBase
    change rightPrefix ≫ right.pullback.base = arrow.base at rightCompositeBase
    dsimp only [forwardBase]
    rw [Category.assoc, rightCompositeBase, ← leftCompositeBase]
    simp
  let forwardComparison :
      (preFrobenioid Phi data).PullbackComparisonTarget
        right.pullback left.preStepCodomain :=
    { toCodomain := left.pullback
      toBaseDomain := forwardBase
      commutes := forwardBaseComp.symm }
  have forwardExists :=
    (right.pullback_type left.preStepCodomain).2 forwardComparison
  let forward := Classical.choose forwardExists
  have forwardComparisonEq := Classical.choose_spec forwardExists
  have forwardComp : forward ≫ right.pullback = left.pullback :=
    congrArg PreFrobenioid.PullbackComparisonTarget.toCodomain
      forwardComparisonEq
  have forwardBaseEq : forward.base = forwardBase :=
    congrArg PreFrobenioid.PullbackComparisonTarget.toBaseDomain
      forwardComparisonEq
  let backwardBase := inv rightPrefix ≫ leftPrefix
  have backwardBaseComp :
      backwardBase ≫ left.pullback.base = right.pullback.base := by
    have leftCompositeBase := congrArg Hom.base left.composite
    rw [comp_base, comp_base, ← Category.assoc] at leftCompositeBase
    change leftPrefix ≫ left.pullback.base = arrow.base at leftCompositeBase
    have rightCompositeBase := congrArg Hom.base right.composite
    rw [comp_base, comp_base, ← Category.assoc] at rightCompositeBase
    change rightPrefix ≫ right.pullback.base = arrow.base at rightCompositeBase
    dsimp only [backwardBase]
    rw [Category.assoc, leftCompositeBase, ← rightCompositeBase]
    simp
  let backwardComparison :
      (preFrobenioid Phi data).PullbackComparisonTarget
        left.pullback right.preStepCodomain :=
    { toCodomain := right.pullback
      toBaseDomain := backwardBase
      commutes := backwardBaseComp.symm }
  have backwardExists :=
    (left.pullback_type right.preStepCodomain).2 backwardComparison
  let backward := Classical.choose backwardExists
  have backwardComparisonEq := Classical.choose_spec backwardExists
  have backwardComp : backward ≫ left.pullback = right.pullback :=
    congrArg PreFrobenioid.PullbackComparisonTarget.toCodomain
      backwardComparisonEq
  have backwardBaseEq : backward.base = backwardBase :=
    congrArg PreFrobenioid.PullbackComparisonTarget.toBaseDomain
      backwardComparisonEq
  have forwardBackward : forward ≫ backward = 𝟙 left.preStepCodomain := by
    apply (left.pullback_type left.preStepCodomain).1
    apply pullbackComparisonTarget_ext Phi data
    · change (forward ≫ backward) ≫ left.pullback =
        𝟙 left.preStepCodomain ≫ left.pullback
      rw [Category.assoc, backwardComp, forwardComp]
      simp
    · change (forward ≫ backward).base =
        𝟙 (Object.base left.preStepCodomain)
      rw [comp_base, forwardBaseEq, backwardBaseEq]
      dsimp only [forwardBase, backwardBase]
      simp
  have backwardForward : backward ≫ forward = 𝟙 right.preStepCodomain := by
    apply (right.pullback_type right.preStepCodomain).1
    apply pullbackComparisonTarget_ext Phi data
    · change (backward ≫ forward) ≫ right.pullback =
        𝟙 right.preStepCodomain ≫ right.pullback
      rw [Category.assoc, forwardComp, backwardComp]
      simp
    · change (backward ≫ forward).base =
        𝟙 (Object.base right.preStepCodomain)
      rw [comp_base, backwardBaseEq, forwardBaseEq]
      dsimp only [forwardBase, backwardBase]
      simp
  exact
    { iso :=
        { hom := forward
          inv := backward
          hom_inv_id := forwardBackward
          inv_hom_id := backwardForward }
      hom_comp := forwardComp
      inv_comp := backwardComp
      prefix_hom := by
        rw [forwardBaseEq]
        dsimp only [forwardBase]
        change leftPrefix ≫ inv leftPrefix ≫ rightPrefix = rightPrefix
        exact IsIso.hom_inv_id_assoc leftPrefix rightPrefix
      prefix_inv := by
        rw [backwardBaseEq]
        dsimp only [backwardBase]
        change rightPrefix ≫ inv rightPrefix ≫ leftPrefix = leftPrefix
        exact IsIso.hom_inv_id_assoc rightPrefix leftPrefix }

structure FactorizationFrobeniusComparison
    {source target : Carrier Phi data} {arrow : source ⟶ target}
    (left right : (preFrobenioid Phi data).FrobenioidFactorization arrow) where
  iso : left.frobeniusCodomain ≅ right.frobeniusCodomain
  square : left.frobenius ≫ iso.hom = right.frobenius

/-- Essential uniqueness of the equal-degree Frobenius stages. -/
def factorizationFrobeniusComparison
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    {source target : Carrier Phi data} {arrow : source ⟶ target}
    (left right : (preFrobenioid Phi data).FrobenioidFactorization arrow) :
    FactorizationFrobeniusComparison left right := by
  let witness := frobeniusDegreeWitness Phi data baseTotallyEpimorphic
    source arrow.frobeniusDegree
  have leftExists := witness.essentiallyUnique left.frobenius
    left.frobenius_type (factorization_frobeniusDegree left)
  let leftIso := Classical.choose leftExists
  have leftSquare : witness.hom ≫ leftIso.hom = left.frobenius :=
    (Classical.choose_spec leftExists).1
  have rightExists := witness.essentiallyUnique right.frobenius
    right.frobenius_type (factorization_frobeniusDegree right)
  let rightIso := Classical.choose rightExists
  have rightSquare : witness.hom ≫ rightIso.hom = right.frobenius :=
    (Classical.choose_spec rightExists).1
  let comparison := leftIso.symm ≪≫ rightIso
  refine ⟨comparison, ?_⟩
  dsimp only [comparison]
  rw [Iso.trans_hom, Iso.symm_hom]
  rw [← leftSquare, Category.assoc, Iso.hom_inv_id_assoc, rightSquare]

/-- Definition 1.3(iv)(a)'s comparison of arbitrary factorizations. -/
def factorizationIso
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    {source target : Carrier Phi data} {arrow : source ⟶ target}
    (left right : (preFrobenioid Phi data).FrobenioidFactorization arrow) :
    (preFrobenioid Phi data).FrobenioidFactorizationIso left right := by
  let frobeniusComparison := factorizationFrobeniusComparison
    baseTotallyEpimorphic left right
  let pullbackComparison := factorizationPullbackComparison left right
  let candidate := frobeniusComparison.iso.inv ≫ left.preStep ≫
    pullbackComparison.iso.hom
  have frobeniusInvSquare :
      right.frobenius ≫ frobeniusComparison.iso.inv = left.frobenius := by
    rw [← frobeniusComparison.square, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have toCodomainEquality :
      candidate ≫ right.pullback = right.preStep ≫ right.pullback := by
    letI : Epi right.frobenius :=
      epi Phi data baseTotallyEpimorphic right.frobenius
    apply (cancel_epi right.frobenius).mp
    dsimp only [candidate]
    have frobeniusWhiskered :
        right.frobenius ≫ frobeniusComparison.iso.inv ≫ left.preStep ≫
              pullbackComparison.iso.hom ≫ right.pullback =
          left.frobenius ≫ left.preStep ≫
              pullbackComparison.iso.hom ≫ right.pullback := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ left.preStep ≫ pullbackComparison.iso.hom ≫
          right.pullback) frobeniusInvSquare
    calc
      right.frobenius ≫
            (frobeniusComparison.iso.inv ≫ left.preStep ≫
              pullbackComparison.iso.hom) ≫ right.pullback =
          left.frobenius ≫ left.preStep ≫
              pullbackComparison.iso.hom ≫ right.pullback := by
        simpa only [Category.assoc] using frobeniusWhiskered
      _ = left.frobenius ≫ left.preStep ≫ left.pullback := by
        rw [pullbackComparison.hom_comp]
      _ = arrow := left.composite
      _ = right.frobenius ≫ right.preStep ≫ right.pullback :=
        right.composite.symm
  have toBaseEquality : candidate.base = right.preStep.base := by
    letI : Epi right.frobenius.base :=
      baseTotallyEpimorphic right.frobenius.base
    apply (cancel_epi right.frobenius.base).mp
    have frobeniusInvBase := congrArg Hom.base frobeniusInvSquare
    rw [comp_base] at frobeniusInvBase
    change right.frobenius.base ≫
        (frobeniusComparison.iso.inv.base ≫ left.preStep.base ≫
          pullbackComparison.iso.hom.base) =
      right.frobenius.base ≫ right.preStep.base
    have baseWhiskered :
        right.frobenius.base ≫ frobeniusComparison.iso.inv.base ≫
              left.preStep.base ≫ pullbackComparison.iso.hom.base =
          left.frobenius.base ≫ left.preStep.base ≫
            pullbackComparison.iso.hom.base := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ left.preStep.base ≫
          pullbackComparison.iso.hom.base) frobeniusInvBase
    calc
      right.frobenius.base ≫
            (frobeniusComparison.iso.inv.base ≫ left.preStep.base ≫
              pullbackComparison.iso.hom.base) =
          left.frobenius.base ≫ left.preStep.base ≫
            pullbackComparison.iso.hom.base := by
        simpa only [Category.assoc] using baseWhiskered
      _ = right.frobenius.base ≫ right.preStep.base := by
        simpa only [Category.assoc] using pullbackComparison.prefix_hom
  have preStepSquare : candidate = right.preStep := by
    apply (right.pullback_type right.frobeniusCodomain).1
    apply pullbackComparisonTarget_ext Phi data
    · exact toCodomainEquality
    · exact toBaseEquality
  exact
    { frobeniusCodomainIso := frobeniusComparison.iso
      preStepCodomainIso := pullbackComparison.iso
      frobenius_square := frobeniusComparison.square
      preStep_square := preStepSquare
      pullback_square := pullbackComparison.inv_comp }

theorem frobenioidFactorizationIso_ext
    {source target : Carrier Phi data} {arrow : source ⟶ target}
    {left right : (preFrobenioid Phi data).FrobenioidFactorization arrow}
    {first second :
      (preFrobenioid Phi data).FrobenioidFactorizationIso left right}
    (frobeniusCodomainIso :
      first.frobeniusCodomainIso = second.frobeniusCodomainIso)
    (preStepCodomainIso :
      first.preStepCodomainIso = second.preStepCodomainIso) :
    first = second := by
  cases first
  cases second
  cases frobeniusCodomainIso
  cases preStepCodomainIso
  rfl

/-- The two comparison isomorphisms are uniquely forced by cancellation. -/
theorem factorizationIso_unique
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f)
    {source target : Carrier Phi data} {arrow : source ⟶ target}
    (left right : (preFrobenioid Phi data).FrobenioidFactorization arrow)
    (first second :
      (preFrobenioid Phi data).FrobenioidFactorizationIso left right) :
    first = second := by
  have frobeniusHomEquality :
      first.frobeniusCodomainIso.hom =
        second.frobeniusCodomainIso.hom := by
    letI : Epi left.frobenius :=
      epi Phi data baseTotallyEpimorphic left.frobenius
    apply (cancel_epi left.frobenius).mp
    exact first.frobenius_square.trans second.frobenius_square.symm
  have frobeniusIsoEquality :
      first.frobeniusCodomainIso = second.frobeniusCodomainIso := by
    apply Iso.ext
    exact frobeniusHomEquality
  have secondPreStepSquare := second.preStep_square
  rw [← frobeniusIsoEquality] at secondPreStepSquare
  have preStepHomEquality :
      first.preStepCodomainIso.hom = second.preStepCodomainIso.hom := by
    let middlePrefix := first.frobeniusCodomainIso.inv ≫ left.preStep
    letI : Epi middlePrefix :=
      epi Phi data baseTotallyEpimorphic middlePrefix
    apply (cancel_epi middlePrefix).mp
    simpa only [middlePrefix, Category.assoc] using
      first.preStep_square.trans secondPreStepSquare.symm
  have preStepIsoEquality :
      first.preStepCodomainIso = second.preStepCodomainIso := by
    apply Iso.ext
    exact preStepHomEquality
  exact frobenioidFactorizationIso_ext frobeniusIsoEquality
    preStepIsoEquality

end
end Iut.SourceModelFrobenioid.Carrier
