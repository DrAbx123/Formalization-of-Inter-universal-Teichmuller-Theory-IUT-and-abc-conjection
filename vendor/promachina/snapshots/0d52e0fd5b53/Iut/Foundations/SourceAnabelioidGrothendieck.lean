/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiberFunctorComparison
import Iut.Foundations.SourceContinuousAnabelioid
import Iut.Foundations.SourceAnabelioidEquivalence
import Iut.Foundations.SourceConnectedFiniteEtaleConverse

/-!
# Grothendieck's correspondence for connected anabelioids

This file formalizes Definitions 1.1.1--1.1.2 and Proposition 1.1.4 of
Mochizuki's *The Geometry of Anabelioids* (printed/PDF pages 9--13).

An unpointed morphism is only an exact contravariant pullback functor.  The
comparison between its pulled-back fiber functor and the chosen target fiber
functor is derived from exactness and connected Galois-category theory.  Thus
the resulting homomorphism of fundamental groups is well-defined only up to
inner conjugacy, exactly as in the source.
-/

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

/-! ## Unpointed exact morphisms -/

/-- A morphism of connected anabelioids in the sense of Definition 1.1.2:
an exact functor in the contravariant direction.  No basepoint comparison is
part of the data. -/
structure SourceAnabelioidHom
    (source target : EtaleFundamentalGroup.{u}) where
  pullback :
    letI := target.coverCategory
    letI := source.coverCategory
    target.Cover ⥤ source.Cover
  preservesFiniteLimits :
    letI := target.coverCategory
    letI := source.coverCategory
    PreservesFiniteLimits pullback
  preservesFiniteColimits :
    letI := target.coverCategory
    letI := source.coverCategory
    PreservesFiniteColimits pullback

namespace SourceAnabelioidHom

variable {source middle target : EtaleFundamentalGroup.{u}}

/-- The identity exact morphism. -/
def identity (data : EtaleFundamentalGroup.{u}) :
    SourceAnabelioidHom data data := by
  letI := data.coverCategory
  exact
    { pullback := 𝟭 data.Cover
      preservesFiniteLimits := inferInstance
      preservesFiniteColimits := inferInstance }

/-- Composition of exact morphisms, with the source's contravariant order. -/
def comp
    (first : SourceAnabelioidHom source middle)
    (second : SourceAnabelioidHom middle target) :
    SourceAnabelioidHom source target := by
  letI := source.coverCategory
  letI := middle.coverCategory
  letI := target.coverCategory
  letI : PreservesFiniteLimits first.pullback :=
    first.preservesFiniteLimits
  letI : PreservesFiniteColimits first.pullback :=
    first.preservesFiniteColimits
  letI : PreservesFiniteLimits second.pullback :=
    second.preservesFiniteLimits
  letI : PreservesFiniteColimits second.pullback :=
    second.preservesFiniteColimits
  exact
    { pullback := second.pullback ⋙ first.pullback
      preservesFiniteLimits := inferInstance
      preservesFiniteColimits := inferInstance }

/-- Exactness makes the pulled-back source fiber functor a fiber functor. -/
@[implicit_reducible] noncomputable def pulledBackFiberFunctor
    (morphism : SourceAnabelioidHom source target) :
    letI := source.coverCategory
    letI := target.coverCategory
    letI := source.galoisCategory
    letI := target.galoisCategory
    letI := source.fiberFunctor
    FiberFunctor (morphism.pullback ⋙ source.fiber) := by
  letI := source.coverCategory
  letI := target.coverCategory
  letI := source.galoisCategory
  letI := target.galoisCategory
  letI := source.fiberFunctor
  letI : PreservesFiniteLimits morphism.pullback :=
    morphism.preservesFiniteLimits
  letI : PreservesFiniteColimits morphism.pullback :=
    morphism.preservesFiniteColimits
  exact SourceFiberFunctorComparison.compFiberFunctor
    morphism.pullback source.fiber

/-- The arbitrary comparison with the chosen target basepoint.  Its existence
is proved; it is not supplied as morphism data. -/
noncomputable def fiberIso
    (morphism : SourceAnabelioidHom source target) :
    letI := source.coverCategory
    letI := target.coverCategory
    letI := source.galoisCategory
    letI := target.galoisCategory
    letI := source.fiberFunctor
    letI := target.fiberFunctor
    morphism.pullback ⋙ source.fiber ≅ target.fiber := by
  letI := source.coverCategory
  letI := target.coverCategory
  letI := source.galoisCategory
  letI := target.galoisCategory
  letI := source.fiberFunctor
  letI := target.fiberFunctor
  letI : FiberFunctor (morphism.pullback ⋙ source.fiber) :=
    morphism.pulledBackFiberFunctor
  exact SourceFiberFunctorComparison.fiberFunctorIso
    (morphism.pullback ⋙ source.fiber) target.fiber

/-- Choose a basepoint comparison only after the unpointed exact morphism has
been given. -/
noncomputable def toPointedHom
    (morphism : SourceAnabelioidHom source target) :
    SourcePointedAnabelioidHom source target := by
  letI := source.coverCategory
  letI := target.coverCategory
  exact
    { pullback := morphism.pullback
      preservesFiniteLimits := morphism.preservesFiniteLimits
      preservesFiniteColimits := morphism.preservesFiniteColimits
      fiberIso := morphism.fiberIso }

/-- A 2-isomorphism between unpointed morphisms is a natural isomorphism of
their exact pullback functors. -/
structure TwoIso (first second : SourceAnabelioidHom source target) where
  pullbackIso :
    letI := source.coverCategory
    letI := target.coverCategory
    first.pullback ≅ second.pullback

namespace TwoIso

variable {first second : SourceAnabelioidHom source target}

@[ext]
theorem ext
    {firstSecond secondFirst : TwoIso first second}
    (equality : firstSecond.pullbackIso.hom =
      secondFirst.pullbackIso.hom) :
    firstSecond = secondFirst := by
  cases firstSecond
  cases secondFirst
  simp only [mk.injEq]
  exact Iso.ext equality

end TwoIso

/-- Forgetting the derived basepoint comparisons turns an unpointed
2-isomorphism into the pointed comparison used by the conjugacy theorem. -/
noncomputable def TwoIso.toPointed
    {first second : SourceAnabelioidHom source target}
    (comparison : TwoIso first second) :
    SourcePointedAnabelioidHom.TwoIso
      first.toPointedHom second.toPointedHom := by
  letI := source.coverCategory
  letI := target.coverCategory
  exact { pullbackIso := comparison.pullbackIso }

/-- Natural isomorphism of exact pullbacks is the equivalence relation on
categorical anabelioid morphisms. -/
def CategoricalEquivalent
    (first second : SourceAnabelioidHom source target) : Prop :=
  Nonempty (TwoIso first second)

instance categoricalEquivalentSetoid :
    Setoid (SourceAnabelioidHom source target) where
  r := CategoricalEquivalent
  iseqv := by
    constructor
    · intro morphism
      letI := source.coverCategory
      letI := target.coverCategory
      exact ⟨{ pullbackIso := Iso.refl morphism.pullback }⟩
    · intro first second comparison
      letI := source.coverCategory
      letI := target.coverCategory
      obtain ⟨comparison⟩ := comparison
      exact ⟨{ pullbackIso := comparison.pullbackIso.symm }⟩
    · intro first second third firstSecond secondThird
      letI := source.coverCategory
      letI := target.coverCategory
      obtain ⟨firstSecond⟩ := firstSecond
      obtain ⟨secondThird⟩ := secondThird
      exact
        ⟨{ pullbackIso :=
            firstSecond.pullbackIso ≪≫ secondThird.pullbackIso }⟩

/-- Isomorphism classes of exact contravariant functors: the set
`Mor(X,Y)` in Proposition 1.1.4(i). -/
abbrev MorphismClass
    (source target : EtaleFundamentalGroup.{u}) :=
  Quotient (categoricalEquivalentSetoid (source := source) (target := target))

end SourceAnabelioidHom

/-! ## Basepoint-compatible two-isomorphisms -/

namespace SourcePointedAnabelioidHom

variable {source target : EtaleFundamentalGroup.{u}}

/-- A two-isomorphism of pointed morphisms.  In addition to identifying the
pullback functors, it commutes with the chosen fiber-functor identifications.
This is the pointed notion of isomorphism used in Proposition 1.1.4(ii). -/
structure BasepointTwoIso
    (first second : SourcePointedAnabelioidHom source target) where
  pullbackIso :
    letI := source.coverCategory
    letI := target.coverCategory
    first.pullback ≅ second.pullback
  fiberIso_compatibility :
    letI := source.coverCategory
    letI := target.coverCategory
    first.fiberIso =
      Functor.isoWhiskerRight pullbackIso source.fiber ≪≫ second.fiberIso

namespace BasepointTwoIso

variable
    {first second third : SourcePointedAnabelioidHom source target}

/-- Forgetting basepoint compatibility leaves an ordinary two-isomorphism. -/
def toTwoIso (comparison : BasepointTwoIso first second) :
    TwoIso first second :=
  { pullbackIso := comparison.pullbackIso }

/-- The identity pointed two-isomorphism. -/
def refl (morphism : SourcePointedAnabelioidHom source target) :
    BasepointTwoIso morphism morphism := by
  letI := source.coverCategory
  letI := target.coverCategory
  exact
    { pullbackIso := Iso.refl _
      fiberIso_compatibility := by simp }

/-- Reverse a pointed two-isomorphism. -/
def symm (comparison : BasepointTwoIso first second) :
    BasepointTwoIso second first := by
  letI := source.coverCategory
  letI := target.coverCategory
  refine
    { pullbackIso := comparison.pullbackIso.symm
      fiberIso_compatibility := ?_ }
  rw [comparison.fiberIso_compatibility]
  have cancel :
      Functor.isoWhiskerRight comparison.pullbackIso.symm source.fiber ≪≫
          Functor.isoWhiskerRight comparison.pullbackIso source.fiber =
        Iso.refl _ := by
    apply Iso.ext
    ext action point
    simp
  rw [← Iso.trans_assoc, cancel]
  simp

/-- Compose pointed two-isomorphisms. -/
def trans
    (firstSecond : BasepointTwoIso first second)
    (secondThird : BasepointTwoIso second third) :
    BasepointTwoIso first third := by
  letI := source.coverCategory
  letI := target.coverCategory
  refine
    { pullbackIso := firstSecond.pullbackIso ≪≫ secondThird.pullbackIso
      fiberIso_compatibility := ?_ }
  rw [firstSecond.fiberIso_compatibility]
  rw [secondThird.fiberIso_compatibility]
  simp

/-- A basepoint-compatible two-isomorphism induces equality, rather than
merely inner conjugacy, of the recovered fundamental-group maps. -/
theorem fundamentalGroupHom_eq
    (comparison : BasepointTwoIso first second) :
    first.fundamentalGroupHom = second.fundamentalGroupHom := by
  letI := source.coverCategory
  letI := target.coverCategory
  ext element
  apply (certifiedFundamentalGroupEquiv target).injective
  rw [first.certifiedFundamentalGroupEquiv_fundamentalGroupHom]
  rw [second.certifiedFundamentalGroupEquiv_fundamentalGroupHom]
  have discrepancyIdentity :
      comparison.toTwoIso.fiberDiscrepancy = Iso.refl target.fiber := by
    dsimp [TwoIso.fiberDiscrepancy, toTwoIso]
    rw [← comparison.fiberIso_compatibility]
    simp
  rw [comparison.toTwoIso.fiberAutHom_eq_conjugate]
  rw [discrepancyIdentity]
  apply Aut.ext
  ext action point
  rfl

end BasepointTwoIso

/-- Basepoint-compatible natural isomorphism is the equivalence relation on
pointed exact morphisms in Proposition 1.1.4(ii). -/
def BasepointEquivalent
    (first second : SourcePointedAnabelioidHom source target) : Prop :=
  Nonempty (BasepointTwoIso first second)

instance basepointEquivalentSetoid :
    Setoid (SourcePointedAnabelioidHom source target) where
  r := BasepointEquivalent
  iseqv := by
    constructor
    · intro morphism
      exact ⟨BasepointTwoIso.refl morphism⟩
    · intro first second comparison
      obtain ⟨comparison⟩ := comparison
      exact ⟨comparison.symm⟩
    · intro first second third firstSecond secondThird
      obtain ⟨firstSecond⟩ := firstSecond
      obtain ⟨secondThird⟩ := secondThird
      exact ⟨firstSecond.trans secondThird⟩

/-- Isomorphism classes of basepoint-compatible exact morphisms, the target
of the bijection in Proposition 1.1.4(ii). -/
abbrev PointedMorphismClass
    (source target : EtaleFundamentalGroup.{u}) :=
  Quotient
    (basepointEquivalentSetoid (source := source) (target := target))

end SourcePointedAnabelioidHom

/-- Objects of the source paper's category `Mor(X,Y)`: exact pullback
functors between two fixed connected anabelioids. -/
structure SourceExactPullbackCategory
    (source target : EtaleFundamentalGroup.{u}) where
  toAnabelioidHom : SourceAnabelioidHom source target

namespace SourceExactPullbackCategory

variable {source target : EtaleFundamentalGroup.{u}}

instance : Category (SourceExactPullbackCategory source target) where
  Hom first second :=
    SourceAnabelioidHom.TwoIso
      first.toAnabelioidHom second.toAnabelioidHom
  id morphism := by
    letI := source.coverCategory
    letI := target.coverCategory
    exact { pullbackIso := Iso.refl morphism.toAnabelioidHom.pullback }
  comp firstSecond secondThird := by
    letI := source.coverCategory
    letI := target.coverCategory
    exact
      { pullbackIso :=
          firstSecond.pullbackIso ≪≫ secondThird.pullbackIso }
  id_comp morphism := by
    apply SourceAnabelioidHom.TwoIso.ext
    simp
  comp_id morphism := by
    apply SourceAnabelioidHom.TwoIso.ext
    simp
  assoc firstSecond secondThird thirdFourth := by
    apply SourceAnabelioidHom.TwoIso.ext
    simp

/-- A natural isomorphism of exact pullback functors is an isomorphism in
`Mor(X,Y)`. -/
def isoOfTwoIso
    {first second : SourceExactPullbackCategory source target}
    (comparison : SourceAnabelioidHom.TwoIso
      first.toAnabelioidHom second.toAnabelioidHom) :
    first ≅ second := by
  letI := source.coverCategory
  letI := target.coverCategory
  exact
    { hom := comparison
      inv := { pullbackIso := comparison.pullbackIso.symm }
      hom_inv_id := by
        apply SourceAnabelioidHom.TwoIso.ext
        change (comparison.pullbackIso ≪≫ comparison.pullbackIso.symm).hom =
          (Iso.refl _).hom
        simp
      inv_hom_id := by
        apply SourceAnabelioidHom.TwoIso.ext
        change (comparison.pullbackIso.symm ≪≫ comparison.pullbackIso).hom =
          (Iso.refl _).hom
        simp }

end SourceExactPullbackCategory

/-! ## Continuous homomorphisms modulo inner conjugacy -/

/-- Two continuous homomorphisms are equivalent when they differ by an inner
automorphism of the target, as in `HomOut(G,H)` on page 11. -/
def SourceInnerConjugate {G H : ProfiniteGrp.{u}}
    (first second : G ⟶ H) : Prop :=
  ∃ transport : H, ∀ element : G,
    second element = transport * first element * transport⁻¹

theorem sourceInnerConjugate_refl {G H : ProfiniteGrp.{u}}
    (morphism : G ⟶ H) : SourceInnerConjugate morphism morphism := by
  exact ⟨1, by simp⟩

theorem sourceInnerConjugate_symm {G H : ProfiniteGrp.{u}}
    {first second : G ⟶ H}
    (comparison : SourceInnerConjugate first second) :
    SourceInnerConjugate second first := by
  obtain ⟨transport, equality⟩ := comparison
  refine ⟨transport⁻¹, ?_⟩
  intro element
  rw [equality]
  simp [mul_assoc]

theorem sourceInnerConjugate_trans {G H : ProfiniteGrp.{u}}
    {first second third : G ⟶ H}
    (firstSecond : SourceInnerConjugate first second)
    (secondThird : SourceInnerConjugate second third) :
    SourceInnerConjugate first third := by
  obtain ⟨firstTransport, firstEquality⟩ := firstSecond
  obtain ⟨secondTransport, secondEquality⟩ := secondThird
  refine ⟨secondTransport * firstTransport, ?_⟩
  intro element
  rw [secondEquality, firstEquality]
  simp [mul_assoc]

/-- An arrow in the source paper's category `HomOut(G,H)`: a target-group
element realizing the displayed conjugacy equation. -/
structure SourceConjugator {G H : ProfiniteGrp.{u}}
    (first second : G ⟶ H) where
  element : H
  conjugates : ∀ value : G,
    second value = element * first value * element⁻¹

namespace SourceConjugator

variable {G H : ProfiniteGrp.{u}}
variable {first second third fourth : G ⟶ H}

@[ext]
theorem ext {firstSecond secondFirst : SourceConjugator first second}
    (equality : firstSecond.element = secondFirst.element) :
    firstSecond = secondFirst := by
  cases firstSecond
  cases secondFirst
  simp_all

/-- Identity conjugator. -/
def identity (morphism : G ⟶ H) : SourceConjugator morphism morphism where
  element := 1
  conjugates := by simp

/-- Conjugators compose in the order dictated by categorical composition. -/
def comp
    (firstSecond : SourceConjugator first second)
    (secondThird : SourceConjugator second third) :
    SourceConjugator first third where
  element := secondThird.element * firstSecond.element
  conjugates := by
    intro value
    rw [secondThird.conjugates, firstSecond.conjugates]
    simp [mul_assoc]

end SourceConjugator

/-- The source paper's category `HomOut(G,H)`, before passage to isomorphism
classes. -/
structure SourceConjugatorCategory (G H : ProfiniteGrp.{u}) where
  toContinuousHom : G ⟶ H

namespace SourceConjugatorCategory

variable {G H : ProfiniteGrp.{u}}

instance : Category (SourceConjugatorCategory G H) where
  Hom first second :=
    SourceConjugator first.toContinuousHom second.toContinuousHom
  id morphism := SourceConjugator.identity morphism.toContinuousHom
  comp := SourceConjugator.comp
  id_comp morphism := by
    ext
    simp [SourceConjugator.comp, SourceConjugator.identity]
  comp_id morphism := by
    ext
    simp [SourceConjugator.comp, SourceConjugator.identity]
  assoc firstSecond secondThird thirdFourth := by
    ext
    simp [SourceConjugator.comp, mul_assoc]

end SourceConjugatorCategory

instance sourceInnerConjugateSetoid (G H : ProfiniteGrp.{u}) :
    Setoid (G ⟶ H) where
  r := SourceInnerConjugate
  iseqv :=
    ⟨sourceInnerConjugate_refl,
      sourceInnerConjugate_symm,
      sourceInnerConjugate_trans⟩

/-- Continuous homomorphisms modulo target inner automorphisms. -/
abbrev SourceOuterHom (G H : ProfiniteGrp.{u}) :=
  Quotient (sourceInnerConjugateSetoid G H)

namespace SourceOuterHom

/-- The identity outer homomorphism. -/
def identity (G : ProfiniteGrp.{u}) : SourceOuterHom G G :=
  Quotient.mk _ (𝟙 G)

/-- Composition of outer homomorphisms.  If both representatives are
conjugated, the composite is conjugated by the product of the second
conjugator and the image of the first conjugator. -/
noncomputable def comp {G H K : ProfiniteGrp.{u}}
    (first : SourceOuterHom G H) (second : SourceOuterHom H K) :
    SourceOuterHom G K :=
  Quotient.map₂ (fun first second => first ≫ second) (by
    intro first first' firstComparison second second' secondComparison
    obtain ⟨firstTransport, firstEquality⟩ := firstComparison
    obtain ⟨secondTransport, secondEquality⟩ := secondComparison
    refine
      ⟨secondTransport * second firstTransport, ?_⟩
    intro element
    change second' (first' element) =
      (secondTransport * second firstTransport) *
          second (first element) *
        (secondTransport * second firstTransport)⁻¹
    rw [secondEquality, firstEquality]
    simp [map_mul, map_inv, mul_assoc]) first second

end SourceOuterHom

namespace SourceAnabelioidHom

/-- The identity categorical morphism class. -/
def MorphismClass.identity (data : EtaleFundamentalGroup.{u}) :
    MorphismClass data data :=
  Quotient.mk _ (SourceAnabelioidHom.identity data)

/-- Composition of categorical morphism classes. -/
noncomputable def MorphismClass.comp
    {source middle target : EtaleFundamentalGroup.{u}}
    (first : MorphismClass source middle)
    (second : MorphismClass middle target) :
    MorphismClass source target :=
  Quotient.map₂ SourceAnabelioidHom.comp (by
    intro first first' firstComparison second second' secondComparison
    obtain ⟨firstComparison⟩ := firstComparison
    obtain ⟨secondComparison⟩ := secondComparison
    letI := source.coverCategory
    letI := middle.coverCategory
    letI := target.coverCategory
    exact
      ⟨{ pullbackIso :=
          Functor.isoWhiskerLeft second.pullback
              firstComparison.pullbackIso ≪≫
            Functor.isoWhiskerRight secondComparison.pullbackIso
              first'.pullback }⟩) first second

/-- An exact categorical morphism determines an outer continuous
homomorphism. -/
noncomputable def outerHom
    {source target : EtaleFundamentalGroup.{u}}
    (morphism : SourceAnabelioidHom source target) :
    SourceOuterHom source.group target.group :=
  Quotient.mk _ morphism.toPointedHom.fundamentalGroupHom

/-- Naturally isomorphic exact pullbacks induce the same outer
homomorphism. -/
theorem outerHom_eq_of_twoIso
    {source target : EtaleFundamentalGroup.{u}}
    {first second : SourceAnabelioidHom source target}
    (comparison : TwoIso first second) :
    first.outerHom = second.outerHom := by
  apply Quotient.sound
  let pointedComparison := comparison.toPointed
  exact
    ⟨pointedComparison.fundamentalGroupTransport,
      pointedComparison.fundamentalGroupHom_eq_conjugate⟩

/-- The map from categorical morphism classes to outer homomorphisms. -/
noncomputable def morphismClassToOuterHom
    (source target : EtaleFundamentalGroup.{u}) :
    MorphismClass source target →
      SourceOuterHom source.group target.group :=
  Quotient.lift outerHom <| by
    intro first second comparison
    obtain ⟨comparison⟩ := comparison
    exact outerHom_eq_of_twoIso comparison

/-- The class-to-outer-hom map preserves identities. -/
theorem morphismClassToOuterHom_identity
    (data : EtaleFundamentalGroup.{u}) :
    morphismClassToOuterHom data data (MorphismClass.identity data) =
      SourceOuterHom.identity data.group := by
  letI := data.coverCategory
  let first := (identity data).toPointedHom
  let second := SourcePointedAnabelioidHom.identity data
  let comparison : SourcePointedAnabelioidHom.TwoIso first second :=
    { pullbackIso := Iso.refl _ }
  apply Quotient.sound
  refine ⟨comparison.fundamentalGroupTransport, ?_⟩
  intro element
  calc
    element = second.fundamentalGroupHom element :=
      (SourcePointedAnabelioidHom.fundamentalGroupHom_identity
        data element).symm
    _ = comparison.fundamentalGroupTransport *
          first.fundamentalGroupHom element *
        comparison.fundamentalGroupTransport⁻¹ :=
      comparison.fundamentalGroupHom_eq_conjugate element

/-- The class-to-outer-hom map preserves composition. -/
theorem morphismClassToOuterHom_comp
    {source middle target : EtaleFundamentalGroup.{u}}
    (first : MorphismClass source middle)
    (second : MorphismClass middle target) :
    morphismClassToOuterHom source target (first.comp second) =
      SourceOuterHom.comp
        (morphismClassToOuterHom source middle first)
        (morphismClassToOuterHom middle target second) := by
  refine Quotient.inductionOn first ?_
  intro firstRepresentative
  refine Quotient.inductionOn second ?_
  intro secondRepresentative
  letI := source.coverCategory
  letI := middle.coverCategory
  letI := target.coverCategory
  let compositePointed :=
    (firstRepresentative.comp secondRepresentative).toPointedHom
  let composedPointed :=
    firstRepresentative.toPointedHom.comp secondRepresentative.toPointedHom
  let comparison : SourcePointedAnabelioidHom.TwoIso
      compositePointed composedPointed :=
    { pullbackIso := Iso.refl _ }
  apply Quotient.sound
  refine ⟨comparison.fundamentalGroupTransport, ?_⟩
  intro element
  calc
    secondRepresentative.toPointedHom.fundamentalGroupHom
        (firstRepresentative.toPointedHom.fundamentalGroupHom element) =
      composedPointed.fundamentalGroupHom element :=
        (SourcePointedAnabelioidHom.fundamentalGroupHom_comp
          firstRepresentative.toPointedHom
          secondRepresentative.toPointedHom element).symm
    _ = comparison.fundamentalGroupTransport *
          compositePointed.fundamentalGroupHom element *
        comparison.fundamentalGroupTransport⁻¹ :=
      comparison.fundamentalGroupHom_eq_conjugate element

/-! ## The standard `B(G)` models -/

/-- Forget the chosen basepoint comparison of a pointed morphism. -/
def ofPointed
    {source target : EtaleFundamentalGroup.{u}}
    (morphism : SourcePointedAnabelioidHom source target) :
    SourceAnabelioidHom source target :=
  { pullback := morphism.pullback
    preservesFiniteLimits := morphism.preservesFiniteLimits
    preservesFiniteColimits := morphism.preservesFiniteColimits }

/-- Equip an unpointed exact morphism with any chosen comparison of fiber
functors.  This auxiliary construction is used only to state independence of
the choice. -/
def pointedHomOfFiberIso
    {source target : EtaleFundamentalGroup.{u}}
    (morphism : SourceAnabelioidHom source target)
    (comparison :
      letI := source.coverCategory
      letI := target.coverCategory
      morphism.pullback ⋙ source.fiber ≅ target.fiber) :
    SourcePointedAnabelioidHom source target := by
  letI := source.coverCategory
  letI := target.coverCategory
  exact
    { pullback := morphism.pullback
      preservesFiniteLimits := morphism.preservesFiniteLimits
      preservesFiniteColimits := morphism.preservesFiniteColimits
      fiberIso := comparison }

/-- Any two basepoint comparisons for the same exact pullback give inner
conjugate fundamental-group homomorphisms. -/
theorem fundamentalGroupHom_innerConjugate_of_fiberIso
    {source target : EtaleFundamentalGroup.{u}}
    (morphism : SourceAnabelioidHom source target)
    (firstComparison secondComparison :
      letI := source.coverCategory
      letI := target.coverCategory
      morphism.pullback ⋙ source.fiber ≅ target.fiber) :
    SourceInnerConjugate
      (pointedHomOfFiberIso morphism firstComparison).fundamentalGroupHom
      (pointedHomOfFiberIso morphism secondComparison).fundamentalGroupHom := by
  letI := source.coverCategory
  letI := target.coverCategory
  let comparison : SourcePointedAnabelioidHom.TwoIso
      (pointedHomOfFiberIso morphism firstComparison)
      (pointedHomOfFiberIso morphism secondComparison) :=
    { pullbackIso := Iso.refl _ }
  exact
    ⟨comparison.fundamentalGroupTransport,
      comparison.fundamentalGroupHom_eq_conjugate⟩

/-- Forgetting a pointed morphism and then deriving a basepoint comparison
does not change its outer homomorphism. -/
theorem outerHom_ofPointed
    {source target : EtaleFundamentalGroup.{u}}
    (morphism : SourcePointedAnabelioidHom source target) :
    (ofPointed morphism).outerHom =
      Quotient.mk _ morphism.fundamentalGroupHom := by
  letI := source.coverCategory
  letI := target.coverCategory
  let comparison : SourcePointedAnabelioidHom.TwoIso
      (ofPointed morphism).toPointedHom morphism :=
    { pullbackIso := Iso.refl _ }
  apply Quotient.sound
  exact
    ⟨comparison.fundamentalGroupTransport,
      comparison.fundamentalGroupHom_eq_conjugate⟩

/-- Restriction of continuous actions is the exact pullback constructed from
a continuous homomorphism; neither the functor nor exactness is supplied. -/
noncomputable def ofContinuousHom {G H : ProfiniteGrp.{u}} (morphism : G ⟶ H) :
    SourceAnabelioidHom
      (continuousActionEtaleFundamentalGroup G)
      (continuousActionEtaleFundamentalGroup H) :=
  ofPointed (continuousActionPointedHom morphism)

/-- Conjugate continuous homomorphisms induce naturally isomorphic
restriction functors, with the natural isomorphism determined by the given
conjugating element. -/
noncomputable def restrictionTwoIsoOfConjugator
    {G H : ProfiniteGrp.{u}} {first second : G ⟶ H}
    (comparison : SourceConjugator first second) :
    TwoIso (ofContinuousHom first) (ofContinuousHom second) := by
  letI := (continuousActionEtaleFundamentalGroup G).coverCategory
  letI := (continuousActionEtaleFundamentalGroup H).coverCategory
  refine { pullbackIso := ?_ }
  change ContAction.res FintypeCat.{u} first.hom ≅
    ContAction.res FintypeCat.{u} second.hom
  refine NatIso.ofComponents (fun action => ?_) ?_
  · apply ObjectProperty.isoMk _
    change
      (Action.res FintypeCat.{u} first.hom.toMonoidHom).obj action.obj ≅
        (Action.res FintypeCat.{u} second.hom.toMonoidHom).obj action.obj
    let underlyingIso :
        ((Action.res FintypeCat.{u} first.hom.toMonoidHom).obj
            action.obj).V ≅
          ((Action.res FintypeCat.{u} second.hom.toMonoidHom).obj
            action.obj).V := by
      change action.obj.V ≅ action.obj.V
      exact action.obj.ρAut comparison.element
    exact Action.mkIso underlyingIso (comm := by
      intro element
      dsimp [underlyingIso, Action.res]
      change action.obj.ρ (first element) ≫
          action.obj.ρ comparison.element =
        action.obj.ρ comparison.element ≫
          action.obj.ρ (second element)
      calc
        _ = action.obj.ρ (comparison.element * first element) :=
          (action.obj.ρ.map_mul comparison.element (first element)).symm
        _ = action.obj.ρ (second element * comparison.element) := by
          rw [comparison.conjugates]
          simp [mul_assoc]
        _ = _ := action.obj.ρ.map_mul (second element) comparison.element)
  · intro firstAction secondAction actionMap
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    dsimp [Action.res]
    exact (actionMap.hom.comm comparison.element).symm

/-- Conjugate continuous homomorphisms induce naturally isomorphic
restriction functors. -/
theorem restrictionCategoricalEquivalentOfInnerConjugate
    {G H : ProfiniteGrp.{u}} {first second : G ⟶ H}
    (comparison : SourceInnerConjugate first second) :
    CategoricalEquivalent
      (ofContinuousHom first) (ofContinuousHom second) := by
  obtain ⟨transport, equality⟩ := comparison
  exact ⟨restrictionTwoIsoOfConjugator
    { element := transport, conjugates := equality }⟩

/-- The functor in Proposition 1.1.4(i), from continuous homomorphisms and
conjugating elements to exact restriction functors and natural isomorphisms. -/
noncomputable def grothendieckFunctor (G H : ProfiniteGrp.{u}) :
    SourceConjugatorCategory G H ⥤
      SourceExactPullbackCategory
        (continuousActionEtaleFundamentalGroup G)
        (continuousActionEtaleFundamentalGroup H) where
  obj morphism :=
    ⟨ofContinuousHom morphism.toContinuousHom⟩
  map comparison := restrictionTwoIsoOfConjugator comparison
  map_id morphism := by
    apply TwoIso.ext
    apply NatTrans.ext
    apply funext
    intro action
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply FintypeCat.hom_ext
    intro point
    change (action.obj.ρ (1 : H)).hom point = point
    simp
  map_comp firstSecond secondThird := by
    apply TwoIso.ext
    apply NatTrans.ext
    apply funext
    intro action
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply FintypeCat.hom_ext
    intro point
    change
      (action.obj.ρ
        (secondThird.element * firstSecond.element)).hom point =
        (action.obj.ρ secondThird.element).hom
          ((action.obj.ρ firstSecond.element).hom point)
    exact ConcreteCategory.congr_hom
      (action.obj.ρ.map_mul secondThird.element firstSecond.element) point

/-- Regard a natural isomorphism of standard restriction functors as a
2-isomorphism of their canonical pointed lifts. -/
noncomputable def restrictionPointedTwoIso
    {G H : ProfiniteGrp.{u}} {first second : G ⟶ H}
    (comparison : TwoIso (ofContinuousHom first) (ofContinuousHom second)) :
    SourcePointedAnabelioidHom.TwoIso
      (continuousActionPointedHom first)
      (continuousActionPointedHom second) := by
  letI := (continuousActionEtaleFundamentalGroup G).coverCategory
  letI := (continuousActionEtaleFundamentalGroup H).coverCategory
  exact { pullbackIso := comparison.pullbackIso }

/-- Recover the unique conjugating element from a natural isomorphism of
restriction functors.  This is the reverse direction of Lemma 1.1.5. -/
noncomputable def conjugatorOfRestrictionTwoIso
    {G H : ProfiniteGrp.{u}} {first second : G ⟶ H}
    (comparison : TwoIso (ofContinuousHom first) (ofContinuousHom second)) :
    SourceConjugator first second := by
  let pointedComparison := restrictionPointedTwoIso comparison
  let transport : H := pointedComparison.fundamentalGroupTransport
  exact
    { element := transport
      conjugates := by
        intro value
        simpa only [transport,
          continuousActionPointedHom_fundamentalGroupHom]
          using pointedComparison.fundamentalGroupHom_eq_conjugate value }

/-- Extracting the conjugator from the natural isomorphism constructed from
it returns the original element. -/
theorem conjugatorOfRestrictionTwoIso_ofConjugator
    {G H : ProfiniteGrp.{u}} {first second : G ⟶ H}
    (comparison : SourceConjugator first second) :
    conjugatorOfRestrictionTwoIso
        (restrictionTwoIsoOfConjugator comparison) = comparison := by
  apply SourceConjugator.ext
  let source := continuousActionEtaleFundamentalGroup G
  let target := continuousActionEtaleFundamentalGroup H
  let pointedComparison := restrictionPointedTwoIso
    (restrictionTwoIsoOfConjugator comparison)
  letI := source.coverCategory
  letI := target.coverCategory
  change pointedComparison.fundamentalGroupTransport = comparison.element
  apply (SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv
    target).injective
  rw [pointedComparison.certifiedFundamentalGroupEquiv_transport]
  apply Aut.ext
  ext action point
  rw [SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv_hom_app]
  rfl

/-- Every natural isomorphism of restriction functors is the one induced by
its recovered conjugating element.  This is the uniqueness direction of
Lemma 1.1.5. -/
theorem restrictionTwoIsoOfConjugator_conjugator
    {G H : ProfiniteGrp.{u}} {first second : G ⟶ H}
    (comparison : TwoIso (ofContinuousHom first) (ofContinuousHom second)) :
    restrictionTwoIsoOfConjugator
        (conjugatorOfRestrictionTwoIso comparison) = comparison := by
  let source := continuousActionEtaleFundamentalGroup G
  let target := continuousActionEtaleFundamentalGroup H
  let pointedComparison := restrictionPointedTwoIso comparison
  let transport : H := pointedComparison.fundamentalGroupTransport
  letI := source.coverCategory
  letI := target.coverCategory
  apply TwoIso.ext
  apply NatTrans.ext
  apply funext
  intro action
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply FintypeCat.hom_ext
  intro point
  change (action.obj.ρ transport).hom point =
    ((comparison.pullbackIso.hom.app action).hom.hom) point
  have actionEquality :=
    SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv_hom_app
      target transport action point
  change
    ((SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv
      target transport).hom.app action) point =
      (action.obj.ρ transport).hom point at actionEquality
  rw [← actionEquality]
  rw [show transport = pointedComparison.fundamentalGroupTransport by rfl]
  rw [pointedComparison.certifiedFundamentalGroupEquiv_transport]
  rfl

/-- Lemma 1.1.5 as an equivalence: conjugating elements are exactly natural
isomorphisms between the associated restriction functors. -/
noncomputable def restrictionConjugatorEquiv
    {G H : ProfiniteGrp.{u}} (first second : G ⟶ H) :
    SourceConjugator first second ≃
      TwoIso (ofContinuousHom first) (ofContinuousHom second) where
  toFun := restrictionTwoIsoOfConjugator
  invFun := conjugatorOfRestrictionTwoIso
  left_inv := conjugatorOfRestrictionTwoIso_ofConjugator
  right_inv := restrictionTwoIsoOfConjugator_conjugator

/-- Full faithfulness of the functor in Proposition 1.1.4(i), supplied by
the exact arrow calculation of Lemma 1.1.5. -/
noncomputable def grothendieckFunctorFullyFaithful
    (G H : ProfiniteGrp.{u}) :
    (grothendieckFunctor G H).FullyFaithful where
  preimage comparison := conjugatorOfRestrictionTwoIso comparison
  map_preimage comparison :=
    restrictionTwoIsoOfConjugator_conjugator comparison
  preimage_map comparison :=
    conjugatorOfRestrictionTwoIso_ofConjugator comparison

/-- Restriction descends from actual continuous homomorphisms to outer
homomorphism classes. -/
noncomputable def outerHomToMorphismClass (G H : ProfiniteGrp.{u}) :
    SourceOuterHom G H →
      MorphismClass
        (continuousActionEtaleFundamentalGroup G)
        (continuousActionEtaleFundamentalGroup H) :=
  Quotient.map ofContinuousHom <| by
    intro first second comparison
    exact restrictionCategoricalEquivalentOfInnerConjugate comparison

/-- Every pointed exact pullback between the standard action anabelioids is
basepoint-compatibly isomorphic to restriction along its derived
fundamental-group homomorphism.  This is Proposition 1.1.4(ii)'s
essential-surjectivity construction before passing to isomorphism classes. -/
noncomputable def basepointTwoIso_restriction_fundamentalGroupHom
    {G H : ProfiniteGrp.{u}}
    (pointed : SourcePointedAnabelioidHom
      (continuousActionEtaleFundamentalGroup G)
      (continuousActionEtaleFundamentalGroup H)) :
    SourcePointedAnabelioidHom.BasepointTwoIso pointed
      (continuousActionPointedHom pointed.fundamentalGroupHom) := by
  let source := continuousActionEtaleFundamentalGroup G
  let target := continuousActionEtaleFundamentalGroup H
  let induced := pointed.fundamentalGroupHom
  letI := source.coverCategory
  letI := target.coverCategory
  letI := source.galoisCategory
  letI := target.galoisCategory
  letI := source.fiberFunctor
  letI := target.fiberFunctor
  letI (X : source.Cover) : MulAction source.group (source.fiber.obj X) :=
    source.action X
  letI (X : target.Cover) : MulAction target.group (target.fiber.obj X) :=
    target.action X
  let pullbackIso :
      pointed.pullback ≅ ContAction.res FintypeCat.{u} induced.hom := by
    refine NatIso.ofComponents (fun action => ?_) ?_
    · apply ObjectProperty.isoMk _
      change
        (pointed.pullback.obj action).obj ≅
          ((ContAction.res FintypeCat.{u} induced.hom).obj action).obj
      let underlyingIso :
          (pointed.pullback.obj action).obj.V ≅
            ((ContAction.res FintypeCat.{u} induced.hom).obj action).obj.V := by
        change (pointed.pullback ⋙ source.fiber).obj action ≅
          target.fiber.obj action
        exact pointed.fiberIso.app action
      exact Action.mkIso underlyingIso (comm := by
        intro element
        apply FintypeCat.hom_ext
        intro point
        dsimp [underlyingIso, ContAction.res, Action.res]
        change pointed.fiberIso.hom.app action
            (element • point) =
          induced element • pointed.fiberIso.hom.app action point
        have equivariance := pointed.fiberIso_equivariant
          (SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv
            source element) action point
        rw [← pointed.certifiedFundamentalGroupEquiv_fundamentalGroupHom]
          at equivariance
        change
          ((SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv
              target (induced element)).hom.app action)
              (pointed.fiberIso.hom.app action point) =
            pointed.fiberIso.hom.app action
              ((SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv
                source element).hom.app
                  (pointed.pullback.obj action) point)
          at equivariance
        rw [SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv_hom_app]
          at equivariance
        rw [SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv_hom_app]
          at equivariance
        exact equivariance.symm)
    · intro firstAction secondAction actionMap
      apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      dsimp [ContAction.res, Action.res]
      exact pointed.fiberIso.hom.naturality actionMap
  refine
    { pullbackIso := pullbackIso
      fiberIso_compatibility := ?_ }
  apply Iso.ext
  ext action point
  rfl

/-- Every exact pullback between the standard action anabelioids is naturally
isomorphic to restriction along its derived fundamental-group homomorphism.
This is the essential-surjectivity direction of Proposition 1.1.4(i). -/
theorem categoricallyEquivalent_restriction_fundamentalGroupHom
    {G H : ProfiniteGrp.{u}}
    (morphism : SourceAnabelioidHom
      (continuousActionEtaleFundamentalGroup G)
      (continuousActionEtaleFundamentalGroup H)) :
    CategoricalEquivalent morphism
      (ofContinuousHom morphism.toPointedHom.fundamentalGroupHom) := by
  let comparison :=
    basepointTwoIso_restriction_fundamentalGroupHom morphism.toPointedHom
  exact ⟨{ pullbackIso := comparison.pullbackIso }⟩

/-- Essential surjectivity of the functor in Proposition 1.1.4(i): every
exact pullback is naturally isomorphic to restriction along its derived
fundamental-group homomorphism. -/
noncomputable instance grothendieckFunctorEssSurj (G H : ProfiniteGrp.{u}) :
    (grothendieckFunctor G H).EssSurj where
  mem_essImage morphism := by
    let induced :=
      morphism.toAnabelioidHom.toPointedHom.fundamentalGroupHom
    refine ⟨⟨induced⟩, ?_⟩
    obtain ⟨comparison⟩ :=
      categoricallyEquivalent_restriction_fundamentalGroupHom
        morphism.toAnabelioidHom
    let reverseComparison :
        TwoIso (ofContinuousHom induced) morphism.toAnabelioidHom :=
      { pullbackIso := comparison.pullbackIso.symm }
    exact ⟨SourceExactPullbackCategory.isoOfTwoIso reverseComparison⟩

noncomputable instance grothendieckFunctorIsEquivalence
    (G H : ProfiniteGrp.{u}) :
    (grothendieckFunctor G H).IsEquivalence where
  faithful := (grothendieckFunctorFullyFaithful G H).faithful
  full := (grothendieckFunctorFullyFaithful G H).full
  essSurj := inferInstance

/-- Proposition 1.1.4(i) at its stated categorical level. -/
noncomputable def grothendieckCategoricalEquivalence
    (G H : ProfiniteGrp.{u}) :
    SourceConjugatorCategory G H ≌
      SourceExactPullbackCategory
        (continuousActionEtaleFundamentalGroup G)
        (continuousActionEtaleFundamentalGroup H) :=
  (grothendieckFunctor G H).asEquivalence

/-- Restriction sends an actual continuous homomorphism to the isomorphism
class of its basepoint-compatible exact pullback. -/
noncomputable def continuousHomToPointedMorphismClass
    (G H : ProfiniteGrp.{u}) :
    (G ⟶ H) →
      SourcePointedAnabelioidHom.PointedMorphismClass
        (continuousActionEtaleFundamentalGroup G)
        (continuousActionEtaleFundamentalGroup H) :=
  fun morphism ↦ Quotient.mk _ (continuousActionPointedHom morphism)

/-- Recover the actual continuous homomorphism from a pointed morphism
class.  Basepoint compatibility makes this independent of the representative
without quotienting by inner conjugacy. -/
noncomputable def pointedMorphismClassToContinuousHom
    (G H : ProfiniteGrp.{u}) :
    SourcePointedAnabelioidHom.PointedMorphismClass
        (continuousActionEtaleFundamentalGroup G)
        (continuousActionEtaleFundamentalGroup H) →
      (G ⟶ H) :=
  Quotient.lift
    (fun morphism ↦ morphism.fundamentalGroupHom) <| by
      intro first second comparison
      obtain ⟨comparison⟩ := comparison
      exact comparison.fundamentalGroupHom_eq

/-- Proposition 1.1.4(ii): actual continuous homomorphisms correspond
bijectively to isomorphism classes of basepoint-compatible exact pullbacks. -/
noncomputable def pointedGrothendieckCorrespondence
    (G H : ProfiniteGrp.{u}) :
    (G ⟶ H) ≃
      SourcePointedAnabelioidHom.PointedMorphismClass
        (continuousActionEtaleFundamentalGroup G)
        (continuousActionEtaleFundamentalGroup H) where
  toFun := continuousHomToPointedMorphismClass G H
  invFun := pointedMorphismClassToContinuousHom G H
  left_inv := by
    intro morphism
    ext element
    exact continuousActionPointedHom_fundamentalGroupHom morphism element
  right_inv := by
    intro quotientValue
    refine Quotient.inductionOn quotientValue ?_
    intro pointed
    apply Quotient.sound
    exact ⟨(basepointTwoIso_restriction_fundamentalGroupHom pointed).symm⟩

/-- Applying the outer-hom construction to a restriction functor recovers
the original continuous homomorphism modulo inner conjugacy.  The possible
conjugator comes solely from the derived, arbitrary fiber comparison. -/
theorem outerHom_ofContinuousHom {G H : ProfiniteGrp.{u}}
    (morphism : G ⟶ H) :
    (ofContinuousHom morphism).outerHom = Quotient.mk _ morphism := by
  let source := continuousActionEtaleFundamentalGroup G
  let target := continuousActionEtaleFundamentalGroup H
  let first := (ofContinuousHom morphism).toPointedHom
  let second := continuousActionPointedHom morphism
  letI := source.coverCategory
  letI := target.coverCategory
  let comparison : SourcePointedAnabelioidHom.TwoIso first second :=
    { pullbackIso := Iso.refl _ }
  apply Quotient.sound
  refine ⟨comparison.fundamentalGroupTransport, ?_⟩
  intro element
  calc
    morphism element = second.fundamentalGroupHom element :=
      (continuousActionPointedHom_fundamentalGroupHom
        morphism element).symm
    _ = comparison.fundamentalGroupTransport *
          first.fundamentalGroupHom element *
        comparison.fundamentalGroupTransport⁻¹ :=
      comparison.fundamentalGroupHom_eq_conjugate element

/-- Decategorifying `grothendieckCategoricalEquivalence` gives the two inverse
constructions in Proposition 1.1.4(i) on isomorphism/conjugacy classes. -/
noncomputable def grothendieckCorrespondence (G H : ProfiniteGrp.{u}) :
    MorphismClass
        (continuousActionEtaleFundamentalGroup G)
        (continuousActionEtaleFundamentalGroup H) ≃
      SourceOuterHom G H where
  toFun := morphismClassToOuterHom _ _
  invFun := outerHomToMorphismClass G H
  left_inv := by
    intro quotientValue
    refine Quotient.inductionOn quotientValue ?_
    intro morphism
    change Quotient.mk _
        (ofContinuousHom morphism.toPointedHom.fundamentalGroupHom) =
      Quotient.mk _ morphism
    exact (Quotient.sound
      (categoricallyEquivalent_restriction_fundamentalGroupHom
        morphism)).symm
  right_inv := by
    intro quotientValue
    refine Quotient.inductionOn quotientValue ?_
    intro morphism
    exact outerHom_ofContinuousHom morphism

/-- On representatives, the inverse of the quotient correspondence is
exactly the object map of the categorical equivalence in Proposition
1.1.4(i).  Thus the established quotient result is its decategorification. -/
theorem grothendieckCorrespondence_symm_mk
    {G H : ProfiniteGrp.{u}} (morphism : G ⟶ H) :
    (grothendieckCorrespondence G H).symm (Quotient.mk _ morphism) =
      Quotient.mk _
        ((grothendieckCategoricalEquivalence G H).functor.obj
          ⟨morphism⟩).toAnabelioidHom :=
  rfl

end SourceAnabelioidHom

/-! ## Existing pointed and finite-etale endpoints -/

namespace SourcePointedAnabelioidEquivalence

/-- The unpointed exact morphism underlying the existing pointed
categorical-equivalence endpoint. -/
def toUnpointedHom
    {source target : EtaleFundamentalGroup.{u}}
    (equivalence : SourcePointedAnabelioidEquivalence source target) :
    SourceAnabelioidHom source target :=
  SourceAnabelioidHom.ofPointed
    equivalence.toSourcePointedAnabelioidHom

/-- The general outer-hom construction agrees with the profinite
isomorphism already derived from a pointed categorical equivalence. -/
theorem toUnpointedHom_outerHom
    {source target : EtaleFundamentalGroup.{u}}
    (equivalence : SourcePointedAnabelioidEquivalence source target) :
    equivalence.toUnpointedHom.outerHom =
      Quotient.mk _
        equivalence.toSourcePointedAnabelioidHom.fundamentalGroupHom :=
  SourceAnabelioidHom.outerHom_ofPointed _

end SourcePointedAnabelioidEquivalence

namespace SourceConnectedFiniteEtaleHom

/-- The unpointed exact morphism underlying a connected finite-etale
morphism. -/
def toUnpointedHom
    {source target : EtaleFundamentalGroup.{u}}
    (morphism : SourceConnectedFiniteEtaleHom source target) :
    SourceAnabelioidHom source target :=
  SourceAnabelioidHom.ofPointed morphism.toPointedHom

/-- The general outer-hom construction agrees with the existing open-image
fundamental-group endpoint. -/
theorem toUnpointedHom_outerHom
    {source target : EtaleFundamentalGroup.{u}}
    (morphism : SourceConnectedFiniteEtaleHom source target) :
    morphism.toUnpointedHom.outerHom =
      Quotient.mk _ morphism.toPointedHom.fundamentalGroupHom :=
  SourceAnabelioidHom.outerHom_ofPointed _

end SourceConnectedFiniteEtaleHom

end Iut
