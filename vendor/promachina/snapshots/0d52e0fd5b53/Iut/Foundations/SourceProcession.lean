/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.Procession
import Iut.Foundations.SourceThetaHodgeTheater

/-!
# Source label processions

This module connects the generic procession of IUT I, Definition 4.10 to the
`l* = (l - 1) / 2` sign-label set used in Propositions 4.7 and 4.11.
-/

open CategoryTheory

namespace Iut

universe u

namespace PrimeGeFive

/-- The positive integer `l* = (l - 1) / 2` from IUT I, Section 0. -/
def lStar (l : PrimeGeFive) : ℕ :=
  (l.value - 1) / 2

theorem lStar_pos (l : PrimeGeFive) :
    0 < l.lStar := by
  unfold lStar
  have := l.ge_five
  omega

/-- `l*` packaged as the positive length of the procession. -/
def lStarPositive (l : PrimeGeFive) : ℕ+ :=
  ⟨l.lStar, l.lStar_pos⟩

@[simp]
theorem lStarPositive_val (l : PrimeGeFive) :
    l.lStarPositive.1 = l.lStar :=
  rfl

end PrimeGeFive

/-- The ordered positive representatives `1, ..., l*`, universe-lifted. -/
abbrev IUTIPositiveLabel (l : PrimeGeFive) : Type u :=
  CategoryCapsule.FiniteIndex l.lStar

namespace IUTIPositiveLabel

variable {l : PrimeGeFive}

/-- The integer representative in `{1, ..., l*}`. -/
def representative (j : IUTIPositiveLabel.{u} l) : ℕ :=
  j.down.1 + 1

theorem representative_pos (j : IUTIPositiveLabel.{u} l) :
    0 < representative j := by
  simp [representative]

theorem representative_lt_l (j : IUTIPositiveLabel.{u} l) :
    representative j < l.value := by
  have hj := j.down.2
  unfold representative PrimeGeFive.lStar at *
  omega

/-- The positive representative as a nonzero element of `Z/lZ`. -/
def coordinate (j : IUTIPositiveLabel.{u} l) :
    ZMod l.value :=
  representative j

theorem coordinate_ne_zero (j : IUTIPositiveLabel.{u} l) :
    coordinate j ≠ 0 := by
  intro h
  have hdvd : l.value ∣ representative j :=
    (ZMod.natCast_eq_zero_iff
      (representative j) l.value).mp h
  exact
    (Nat.not_dvd_of_pos_of_lt
      j.representative_pos j.representative_lt_l) hdvd

/-- The corresponding nonzero Tate label. -/
def nonzeroTateLabel (j : IUTIPositiveLabel.{u} l) :
    EtaleTheta.NonzeroLabel
      (EtaleTheta.LTorsionLabel l.value) :=
  ⟨Multiplicative.ofAdd (coordinate j), by
    intro h
    apply coordinate_ne_zero j
    exact congrArg Multiplicative.toAdd h⟩

/-- The sign class represented by `j + 1`. -/
def signLabel (j : IUTIPositiveLabel.{u} l) :
    EtaleTheta.SignLabel
      (EtaleTheta.LTorsionLabel l.value) :=
  EtaleTheta.toSignLabel (nonzeroTateLabel j)

theorem signLabel_injective :
    Function.Injective
      (signLabel :
        IUTIPositiveLabel.{u} l ->
          EtaleTheta.SignLabel
            (EtaleTheta.LTorsionLabel l.value)) := by
  intro a b hab
  have hrel := Quotient.exact hab
  rcases hrel with hsame | hopposite
  · have hcoordinate :
        coordinate a = coordinate b := by
      simpa [nonzeroTateLabel] using
        congrArg
          (fun x :
            EtaleTheta.NonzeroLabel
              (EtaleTheta.LTorsionLabel l.value) =>
              Multiplicative.toAdd x.1)
          hsame
    have hrepresentative :
        representative a = representative b := by
      have hval := congrArg ZMod.val hcoordinate
      simpa [coordinate,
        ZMod.val_natCast_of_lt a.representative_lt_l,
        ZMod.val_natCast_of_lt b.representative_lt_l] using hval
    apply ULift.ext
    apply Fin.ext
    unfold representative at hrepresentative
    omega
  · have hcoordinate :
        coordinate a = -coordinate b := by
      simpa [nonzeroTateLabel] using
        congrArg
          (fun x :
            EtaleTheta.NonzeroLabel
              (EtaleTheta.LTorsionLabel l.value) =>
              Multiplicative.toAdd x.1)
          hopposite
    have hzero :
        ((representative a + representative b : ℕ) :
          ZMod l.value) = 0 := by
      rw [Nat.cast_add]
      change coordinate a + coordinate b = 0
      rw [hcoordinate]
      exact neg_add_cancel (coordinate b)
    have hdvd :
        l.value ∣ representative a + representative b :=
      (ZMod.natCast_eq_zero_iff
        (representative a + representative b)
        l.value).mp hzero
    have hsum_pos :
        0 < representative a + representative b :=
      Nat.add_pos_left a.representative_pos _
    have hsum_lt :
        representative a + representative b < l.value := by
      obtain ⟨k, hk⟩ :=
        l.prime.odd_of_ne_two l.ne_two
      have ha := a.down.2
      have hb := b.down.2
      unfold representative PrimeGeFive.lStar at *
      omega
    exact
      (Nat.not_dvd_of_pos_of_lt hsum_pos hsum_lt hdvd).elim

theorem signLabel_surjective :
    Function.Surjective
      (signLabel :
        IUTIPositiveLabel.{u} l ->
          EtaleTheta.SignLabel
            (EtaleTheta.LTorsionLabel l.value)) := by
  intro label
  refine Quotient.inductionOn label ?_
  intro x
  let z : ZMod l.value :=
    Multiplicative.toAdd x.1
  have hz_ne_zero : z ≠ 0 := by
    intro hz
    apply x.2
    apply Multiplicative.toAdd.injective
    change z = 0
    exact hz
  have hz_val_ne_zero : z.val ≠ 0 :=
    (ZMod.val_eq_zero z).not.mpr hz_ne_zero
  have hz_val_pos : 0 < z.val :=
    Nat.pos_of_ne_zero hz_val_ne_zero
  have hz_val_lt : z.val < l.value :=
    z.val_lt
  by_cases hz_low : z.val ≤ l.lStar
  · let j : IUTIPositiveLabel.{u} l :=
      ULift.up
        ⟨z.val - 1, by
          omega⟩
    refine ⟨j, Quotient.sound (Or.inl ?_)⟩
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    change coordinate j = z
    rw [coordinate, representative]
    change (((z.val - 1) + 1 : ℕ) : ZMod l.value) = z
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hz_val_ne_zero)]
    exact ZMod.natCast_zmod_val z
  · obtain ⟨k, hk⟩ :=
      l.prime.odd_of_ne_two l.ne_two
    have hz_high :
        (l.value - 1) / 2 < z.val := by
      change
        ¬ z.val ≤ (l.value - 1) / 2 at hz_low
      omega
    have hcomplement_pos :
        0 < l.value - z.val := by
      omega
    have hcomplement_le :
        l.value - z.val ≤ l.lStar := by
      change
        l.value - z.val ≤ (l.value - 1) / 2
      omega
    let j : IUTIPositiveLabel.{u} l :=
      ULift.up
        ⟨l.value - z.val - 1, by
          omega⟩
    refine ⟨j, Quotient.sound (Or.inr ?_)⟩
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    change coordinate j = -z
    rw [coordinate, representative]
    change
      (((l.value - z.val - 1) + 1 : ℕ) :
        ZMod l.value) = -z
    rw [Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hcomplement_pos))]
    rw [← ZMod.natCast_zmod_val (-z)]
    congr 1
    rw [ZMod.neg_val, if_neg hz_ne_zero]

/-- The ordered representatives are exactly the nonzero sign-label set. -/
noncomputable def signLabelEquiv :
    IUTIPositiveLabel.{u} l ≃
      EtaleTheta.SignLabel
        (EtaleTheta.LTorsionLabel l.value) :=
  Equiv.ofBijective signLabel
    ⟨signLabel_injective, signLabel_surjective⟩

end IUTIPositiveLabel

section DThetaBridge

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : SourceInitialThetaCore Fmod F K}
variable (models : IUTIThetaHodgeTheaterModels theta)

/-- A positive procession label together with its typed source history. -/
@[ext]
structure SourceHistoryPositiveLabel where
  history : SourceThetaArithmeticHistory theta
  positiveLabel : IUTIPositiveLabel.{u} theta.l

/--
The part of a D-theta bridge needed by IUT I, Proposition 4.11.

The poly-arrow is a genuine collection of placewise D-prime-strip morphisms.
The evaluation-label map records the output of Proposition 4.7(i); proving it
from the bad-place evaluation sections remains a separate source obligation.
-/
structure SourceDThetaBridgeCore where
  capsule :
    CategoryCapsule
      (CategoryTheory.Cat.of (SourceDPrimeStrip models))
  target : SourceDPrimeStrip models
  capsule_history :
    ∀ j, (capsule.object j).history = target.history
  polyMorphism :
    ∀ j, Set (capsule.object j ⟶ target)
  polyMorphism_nonempty :
    ∀ j, (polyMorphism j).Nonempty
  evaluationLabel :
    capsule.index ->
      EtaleTheta.SignLabel
        (EtaleTheta.LTorsionLabel theta.l.value)
  evaluationLabel_injective :
    Function.Injective evaluationLabel
  evaluationLabel_surjective :
    Function.Surjective evaluationLabel

namespace SourceDThetaBridgeCore

variable {models}

/-- The bridge history is derived from its target prime strip. -/
def history (bridge : SourceDThetaBridgeCore models) :
    SourceThetaArithmeticHistory theta :=
  bridge.target.history

/--
A compatible isomorphism member between D-theta bridge cores.

It is one member of the full poly-isomorphisms of Definition 4.6(ii), with
the conjugation and label-transport conditions made explicit.
-/
structure IsomorphismMember
    (source target : SourceDThetaBridgeCore models) where
  history_compatible : source.history = target.history
  indexEquiv :
    source.capsule.index ≃ target.capsule.index
  componentIso :
    ∀ j,
      source.capsule.object j ≅
        target.capsule.object (indexEquiv j)
  targetIso : source.target ≅ target.target
  evaluationLabel_compatible :
    ∀ j,
      target.evaluationLabel (indexEquiv j) =
        source.evaluationLabel j
  polyMorphism_compatible :
    ∀ j f,
      f ∈ source.polyMorphism j ↔
        (componentIso j).inv ≫ f ≫ targetIso.hom ∈
          target.polyMorphism (indexEquiv j)

namespace IsomorphismMember

variable {source middle target : SourceDThetaBridgeCore models}

/-- Identity member of the bridge full poly-isomorphisms. -/
def id (source : SourceDThetaBridgeCore models) :
    IsomorphismMember source source where
  history_compatible := rfl
  indexEquiv := Equiv.refl source.capsule.index
  componentIso j := Iso.refl (source.capsule.object j)
  targetIso := Iso.refl source.target
  evaluationLabel_compatible j := rfl
  polyMorphism_compatible j f := by
    have hcomp :
        f ≫ 𝟙 source.target = f :=
      Category.comp_id f
    change
      f ∈ source.polyMorphism j ↔
        𝟙 (source.capsule.object j) ≫ f ≫
          𝟙 source.target ∈ source.polyMorphism j
    rw [Category.id_comp, hcomp]

/-- Inverse of a compatible bridge-isomorphism member. -/
def symm
    (iso : IsomorphismMember source target) :
    IsomorphismMember target source where
  history_compatible := iso.history_compatible.symm
  indexEquiv := iso.indexEquiv.symm
  componentIso j :=
    (eqToIso
      (congrArg target.capsule.object
        (iso.indexEquiv.apply_symm_apply j).symm)).trans
      (iso.componentIso (iso.indexEquiv.symm j)).symm
  targetIso := iso.targetIso.symm
  evaluationLabel_compatible j := by
    exact
      (iso.evaluationLabel_compatible
        (iso.indexEquiv.symm j)).symm |>.trans <|
          congrArg target.evaluationLabel
            (iso.indexEquiv.apply_symm_apply j)
  polyMorphism_compatible j f := by
    have transport_mem
        (sourceIndex : source.capsule.index)
        (targetIndex : target.capsule.index)
        (indexEquality : iso.indexEquiv sourceIndex = targetIndex)
        (arrow : target.capsule.object targetIndex ⟶ target.target) :
        eqToHom
              (congrArg target.capsule.object indexEquality) ≫ arrow ∈
            target.polyMorphism (iso.indexEquiv sourceIndex) ↔
          arrow ∈ target.polyMorphism targetIndex := by
      cases indexEquality
      rw [eqToHom_refl, Category.id_comp]
    let k := iso.indexEquiv.symm j
    let indexEquality : iso.indexEquiv k = j :=
      iso.indexEquiv.apply_symm_apply j
    let adjusted :
        target.capsule.object (iso.indexEquiv k) ⟶ target.target :=
      eqToHom (congrArg target.capsule.object indexEquality) ≫ f
    let transported :=
      (iso.componentIso k).hom ≫
        adjusted ≫ iso.targetIso.inv
    have htransport :=
      iso.polyMorphism_compatible
        k transported
    have hright :
        ((eqToIso
            (congrArg target.capsule.object indexEquality.symm)).trans
              (iso.componentIso k).symm).inv ≫
            f ≫ iso.targetIso.inv =
          transported := by
      dsimp [adjusted, transported]
      let indexHom :=
        eqToHom (congrArg target.capsule.object indexEquality)
      change
        ((iso.componentIso k).hom ≫ indexHom) ≫
              f ≫ iso.targetIso.inv =
          (iso.componentIso k).hom ≫
              (indexHom ≫ f) ≫ iso.targetIso.inv
      simp only [Category.assoc]
    have hsimplify :
        (iso.componentIso k).inv ≫
              transported ≫ iso.targetIso.hom =
            adjusted := by
      simp only [transported, Category.assoc,
        Iso.inv_hom_id_assoc]
      exact
        (congrArg (fun arrow => adjusted ≫ arrow)
          iso.targetIso.inv_hom_id).trans
            (Category.comp_id adjusted)
    change
      f ∈ target.polyMorphism j ↔
        ((eqToIso
            (congrArg target.capsule.object indexEquality.symm)).trans
              (iso.componentIso k).symm).inv ≫
            f ≫ iso.targetIso.inv ∈
          source.polyMorphism k
    rw [hright]
    rw [hsimplify] at htransport
    exact
      (transport_mem k j indexEquality f).symm.trans
        htransport.symm

/-- Composition of compatible bridge-isomorphism members. -/
def comp
    (first : IsomorphismMember source middle)
    (second : IsomorphismMember middle target) :
    IsomorphismMember source target where
  history_compatible :=
    first.history_compatible.trans second.history_compatible
  indexEquiv := first.indexEquiv.trans second.indexEquiv
  componentIso j :=
    (first.componentIso j).trans
      (second.componentIso (first.indexEquiv j))
  targetIso := first.targetIso.trans second.targetIso
  evaluationLabel_compatible j :=
    (second.evaluationLabel_compatible
      (first.indexEquiv j)).trans
        (first.evaluationLabel_compatible j)
  polyMorphism_compatible j f := by
    rw [first.polyMorphism_compatible]
    rw [second.polyMorphism_compatible]
    simp only [Iso.trans_hom, Iso.trans_inv]
    rfl

end IsomorphismMember

/-- Proposition 4.7(i)'s label map as an actual equivalence. -/
noncomputable def evaluationLabelEquiv
    (bridge : SourceDThetaBridgeCore models) :
    bridge.capsule.index ≃
      EtaleTheta.SignLabel
        (EtaleTheta.LTorsionLabel theta.l.value) :=
  Equiv.ofBijective bridge.evaluationLabel
    ⟨bridge.evaluationLabel_injective,
      bridge.evaluationLabel_surjective⟩

/--
The ordering of the capsule indices obtained by transporting the paper's
positive representatives through the evaluation-label bijection.
-/
noncomputable def orderedIndexEquiv
    (bridge : SourceDThetaBridgeCore models) :
    bridge.capsule.index ≃
      IUTIPositiveLabel.{u} theta.l :=
  bridge.evaluationLabelEquiv.trans
    IUTIPositiveLabel.signLabelEquiv.symm

/-- Each ordered capsule index remembers the arithmetic history which owns it. -/
noncomputable def historyIndex
    (bridge : SourceDThetaBridgeCore models)
    (j : bridge.capsule.index) :
    SourceHistoryPositiveLabel (theta := theta) where
  history := bridge.history
  positiveLabel := bridge.orderedIndexEquiv j

theorem IsomorphismMember.orderedIndex_compatible
    {source target : SourceDThetaBridgeCore models}
    (iso : IsomorphismMember source target)
    (j : source.capsule.index) :
    target.orderedIndexEquiv (iso.indexEquiv j) =
      source.orderedIndexEquiv j := by
  simp only [orderedIndexEquiv, evaluationLabelEquiv,
    Equiv.trans_apply, Equiv.ofBijective_apply]
  rw [iso.evaluationLabel_compatible]

theorem IsomorphismMember.historyIndex_compatible
    {source target : SourceDThetaBridgeCore models}
    (iso : IsomorphismMember source target)
    (j : source.capsule.index) :
    target.historyIndex (iso.indexEquiv j) =
      source.historyIndex j := by
  apply SourceHistoryPositiveLabel.ext
  · exact iso.history_compatible.symm
  · exact iso.orderedIndex_compatible j

/-- The holomorphic `l*`-procession of D-prime-strips from Proposition 4.11(i). -/
noncomputable def procession
    (bridge : SourceDThetaBridgeCore models) :
    CategoryProcession
      (CategoryTheory.Cat.of (SourceDPrimeStrip models))
      theta.l.lStarPositive :=
  bridge.capsule.nestedProcession bridge.orderedIndexEquiv

theorem procession_capsule_card
    (bridge : SourceDThetaBridgeCore models)
    (j : Fin theta.l.lStarPositive.1) :
    Fintype.card (bridge.procession.capsule j).index =
      j.1 + 1 :=
  bridge.procession.capsule_card j

/-- Every adjacent arrow contains its canonical identity-isomorphism member. -/
noncomputable def processionTransitionMember
    (bridge : SourceDThetaBridgeCore models)
    (j : Fin (theta.l.lStarPositive.1 - 1)) :
    (bridge.capsule.nestedTransition
      bridge.orderedIndexEquiv j).Members :=
  bridge.capsule.nestedTransitionMember
    bridge.orderedIndexEquiv j

/-- Proposition 4.11(i)'s reduced label indeterminacy is exactly `l*!`. -/
theorem procession_label_indeterminacy
    (bridge : SourceDThetaBridgeCore models) :
    (∏ j : Fin theta.l.lStarPositive.1,
      Fintype.card (bridge.procession.capsule j).index) =
        Nat.factorial theta.l.lStar := by
  simpa using
    bridge.capsule.nested_label_indeterminacy
      bridge.orderedIndexEquiv

/-- The componentwise isomorphisms at one retained procession position. -/
private noncomputable def IsomorphismMember.processionComponentMember
    {source target : SourceDThetaBridgeCore models}
    (iso : IsomorphismMember source target)
    (j : Fin theta.l.lStarPositive.1) :
    (CategoryCapsule.FullPolyMorphism.mk
      (source := source.procession.capsule j)
      (target := target.procession.capsule j)
      (Function.Embedding.refl
        (source.procession.capsule j).index)).Members := by
  intro i
  let label : IUTIPositiveLabel.{u} theta.l :=
    ULift.up
      ⟨i.down.1,
        lt_of_lt_of_le i.down.2
          (Nat.succ_le_iff.mpr j.2)⟩
  let sourceIndex :=
    source.orderedIndexEquiv.symm label
  have hindex :
      iso.indexEquiv sourceIndex =
        target.orderedIndexEquiv.symm label := by
    apply target.orderedIndexEquiv.injective
    rw [iso.orderedIndex_compatible]
    dsimp [sourceIndex]
    exact
      (Equiv.apply_symm_apply
        source.orderedIndexEquiv label).trans
        (Equiv.apply_symm_apply
          target.orderedIndexEquiv label).symm
  change
    source.capsule.object sourceIndex ≅
      target.capsule.object
        (target.orderedIndexEquiv.symm label)
  exact
    (iso.componentIso sourceIndex).trans
      (eqToIso
        (congrArg target.capsule.object hindex))

/-- A bridge-isomorphism member induces a morphism of holomorphic processions. -/
noncomputable def IsomorphismMember.processionHom
    {source target : SourceDThetaBridgeCore models}
    (iso : IsomorphismMember source target) :
    CategoryProcession.Hom source.procession target.procession where
  positionEmbedding :=
    Function.Embedding.refl
      (Fin theta.l.lStarPositive.1)
  positionStrictMono := strictMono_id
  component j :=
    { indexEmbedding :=
        Function.Embedding.refl
          (source.procession.capsule j).index
      members_nonempty :=
        ⟨iso.processionComponentMember j⟩ }

/-- The induced procession morphism has actual componentwise isomorphism members. -/
noncomputable def IsomorphismMember.processionHomMember
    {source target : SourceDThetaBridgeCore models}
    (iso : IsomorphismMember source target) :
    ∀ j, (iso.processionHom.component j).Members :=
  iso.processionComponentMember

/--
The mono-analytic procession obtained by applying the natural
mono-analyticization functor, as in Proposition 4.11(ii).
-/
noncomputable def monoAnalyticProcession
    (mono : SourceDMonoAnalyticization models)
    (bridge : SourceDThetaBridgeCore models) :
    CategoryProcession
      (CategoryTheory.Cat.of
        (SourceDMonoAnalyticPrimeStrip models))
      theta.l.lStarPositive :=
  bridge.procession.map mono.functor

theorem monoAnalyticProcession_capsule_card
    (mono : SourceDMonoAnalyticization models)
    (bridge : SourceDThetaBridgeCore models)
    (j : Fin theta.l.lStarPositive.1) :
    Fintype.card
        ((bridge.monoAnalyticProcession mono).capsule j).index =
      j.1 + 1 :=
  (bridge.monoAnalyticProcession mono).capsule_card j

/-- The canonical adjacent member survives mono-analyticization. -/
noncomputable def monoAnalyticTransitionMember
    (mono : SourceDMonoAnalyticization models)
    (bridge : SourceDThetaBridgeCore models)
    (j : Fin (theta.l.lStarPositive.1 - 1)) :
    ((bridge.capsule.nestedTransition
      bridge.orderedIndexEquiv j).map mono.functor).Members :=
  (bridge.processionTransitionMember j).map mono.functor

theorem monoAnalyticProcession_label_indeterminacy
    (mono : SourceDMonoAnalyticization models)
    (bridge : SourceDThetaBridgeCore models) :
    (∏ j : Fin theta.l.lStarPositive.1,
      Fintype.card
        ((bridge.monoAnalyticProcession mono).capsule j).index) =
      Nat.factorial theta.l.lStar := by
  simpa [monoAnalyticProcession] using
    bridge.procession_label_indeterminacy

/-- Naturality of the mono-analytic procession on a bridge-isomorphism member. -/
noncomputable def IsomorphismMember.monoAnalyticProcessionHom
    {source target : SourceDThetaBridgeCore models}
    (mono : SourceDMonoAnalyticization models)
    (iso : IsomorphismMember source target) :
    CategoryProcession.Hom
      (source.monoAnalyticProcession mono)
      (target.monoAnalyticProcession mono) :=
  iso.processionHom.map mono.functor

noncomputable def IsomorphismMember.monoAnalyticProcessionHomMember
    {source target : SourceDThetaBridgeCore models}
    (mono : SourceDMonoAnalyticization models)
    (iso : IsomorphismMember source target) :
    ∀ j,
      ((iso.processionHom.component j).map
        mono.functor).Members :=
  fun j => (iso.processionHomMember j).map mono.functor

end SourceDThetaBridgeCore

end DThetaBridge

end Iut
