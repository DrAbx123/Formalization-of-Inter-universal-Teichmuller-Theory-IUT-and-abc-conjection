/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.InitialThetaData

/-!
Examples for the first formal slice of initial theta data.

These examples are intentionally small.  They verify the constructor and the
basic projections without pretending that a complete arithmetic example of IUT
initial data has already been supplied.
-/

namespace Iut

namespace InitialThetaDataExample

/-- The first admissible prime allowed by IUT I, Definition 3.1(c). -/
def primeFive : PrimeGeFive where
  value := 5
  prime := by norm_num
  ge_five := by norm_num

example : Nat.Prime primeFive.value :=
  primeFive.prime

example : 5 ≤ primeFive.value :=
  primeFive.ge_five

example (x : ZMod primeFive.value) :
    zmodLabelTranslate primeFive 0 x = x :=
  zmodLabelTranslate_zero primeFive x

example (g h x : ZMod primeFive.value) :
    zmodLabelTranslate primeFive (g + h) x =
      zmodLabelTranslate primeFive g (zmodLabelTranslate primeFive h x) :=
  zmodLabelTranslate_add primeFive g h x

example (x y : ZMod primeFive.value) :
    ∃! t : ZMod primeFive.value, zmodLabelTranslate primeFive t x = y :=
  zmodLabelTranslate_existsUnique primeFive x y

example (x : ZMod primeFive.value) :
    zmodLabelTranslate primeFive (zmodLabelCoordinateFromZero primeFive x) 0 = x :=
  zmodLabelCoordinateFromZero_spec primeFive x

example (x t : ZMod primeFive.value)
    (ht : zmodLabelTranslate primeFive t 0 = x) :
    t = zmodLabelCoordinateFromZero primeFive x :=
  zmodLabelCoordinateFromZero_unique primeFive x t ht

section ReductionPresentationRegression

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonminimal presentation has the same curve-level good classification. -/
example (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) :
    HasGoodReductionOnMinimalModel R (C • W) ↔
      HasGoodReductionOnMinimalModel R W :=
  hasGoodReductionOnMinimalModel_smul_iff R C W

/-- A nonminimal presentation has the same curve-level multiplicative classification. -/
example (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) :
    HasMultiplicativeReductionOnMinimalModel R (C • W) ↔
      HasMultiplicativeReductionOnMinimalModel R W :=
  hasMultiplicativeReductionOnMinimalModel_smul_iff R C W

/-- Mathlib's chosen minimal transform has the same good classification. -/
example (W : WeierstrassCurve K) :
    HasGoodReductionOnMinimalModel R (W.minimal R) ↔
      HasGoodReductionOnMinimalModel R W :=
  hasGoodReductionOnMinimalModel_minimal_iff R W

/-- Mathlib's chosen minimal transform has the same multiplicative classification. -/
example (W : WeierstrassCurve K) :
    HasMultiplicativeReductionOnMinimalModel R (W.minimal R) ↔
      HasMultiplicativeReductionOnMinimalModel R W :=
  hasMultiplicativeReductionOnMinimalModel_minimal_iff R W

end ReductionPresentationRegression

section AbstractConstructor

universe u

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable [DecidableEq F]

/-- A constructor smoke test for EtTh orbicurve type assertions. -/
def abstractOrbicurveTypeData
    (C : HyperbolicOrbicurveModel F) (kind : OrbicurveTypeKind)
    (hasType : Prop) (hType : hasType) :
    OrbicurveTypeData primeFive C kind where
  hasType := hasType
  hasType_holds := hType

example (C : HyperbolicOrbicurveModel F) (kind : OrbicurveTypeKind)
    (hasType : Prop) (hType : hasType) :
    (abstractOrbicurveTypeData C kind hasType hType).hasType :=
  (abstractOrbicurveTypeData C kind hasType hType).holds

/-- A constructor smoke test for a typed orbicurve morphism placeholder. -/
def abstractHyperbolicOrbicurveMorphismData
    (source target : HyperbolicOrbicurveModel F)
    (label : String) (morphismExists : Prop) (hMorphism : morphismExists) :
    HyperbolicOrbicurveMorphismData source target where
  label := label
  morphismExists := morphismExists
  morphismExists_holds := hMorphism

example (source target : HyperbolicOrbicurveModel F)
    (label : String) (morphismExists : Prop) (hMorphism : morphismExists) :
    (abstractHyperbolicOrbicurveMorphismData source target
      label morphismExists hMorphism).morphismExists :=
  (abstractHyperbolicOrbicurveMorphismData source target
    label morphismExists hMorphism).exists_holds

/-- A constructor smoke test for a source automorphism over a cover morphism. -/
def abstractHyperbolicOrbicurveAutomorphismOverData
    {source target : HyperbolicOrbicurveModel F}
    (coverMorphism : HyperbolicOrbicurveMorphismData source target)
    (label : String)
    (automorphismExists inverseExists overTarget : Prop)
    (hAutomorphism : automorphismExists)
    (hInverse : inverseExists)
    (hOverTarget : overTarget) :
    HyperbolicOrbicurveAutomorphismOverData coverMorphism where
  label := label
  automorphismExists := automorphismExists
  automorphismExists_holds := hAutomorphism
  inverseExists := inverseExists
  inverseExists_holds := hInverse
  overTarget := overTarget
  overTarget_holds := hOverTarget

example {source target : HyperbolicOrbicurveModel F}
    (coverMorphism : HyperbolicOrbicurveMorphismData source target)
    (label : String)
    (automorphismExists inverseExists overTarget : Prop)
    (hAutomorphism : automorphismExists)
    (hInverse : inverseExists)
    (hOverTarget : overTarget) :
    (abstractHyperbolicOrbicurveAutomorphismOverData
      coverMorphism label automorphismExists inverseExists overTarget
      hAutomorphism hInverse hOverTarget).overTarget :=
  (abstractHyperbolicOrbicurveAutomorphismOverData
    coverMorphism label automorphismExists inverseExists overTarget
    hAutomorphism hInverse hOverTarget).overTarget_holds

/--
A constructor smoke test for supplied composition operations on over-target
orbicurve automorphisms.
-/
def abstractHyperbolicOrbicurveAutomorphismCompositionData
    {source target : HyperbolicOrbicurveModel F}
    (coverMorphism : HyperbolicOrbicurveMorphismData source target)
    (identityAutomorphism :
      HyperbolicOrbicurveAutomorphismOverData coverMorphism)
    (composeAutomorphism :
      HyperbolicOrbicurveAutomorphismOverData coverMorphism →
        HyperbolicOrbicurveAutomorphismOverData coverMorphism →
        HyperbolicOrbicurveAutomorphismOverData coverMorphism)
    (inverseAutomorphism :
      HyperbolicOrbicurveAutomorphismOverData coverMorphism →
        HyperbolicOrbicurveAutomorphismOverData coverMorphism) :
    HyperbolicOrbicurveAutomorphismCompositionData coverMorphism where
  identityAutomorphism := identityAutomorphism
  composeAutomorphism := composeAutomorphism
  inverseAutomorphism := inverseAutomorphism

example {source target : HyperbolicOrbicurveModel F}
    (coverMorphism : HyperbolicOrbicurveMorphismData source target)
    (identityAutomorphism :
      HyperbolicOrbicurveAutomorphismOverData coverMorphism)
    (composeAutomorphism :
      HyperbolicOrbicurveAutomorphismOverData coverMorphism →
        HyperbolicOrbicurveAutomorphismOverData coverMorphism →
        HyperbolicOrbicurveAutomorphismOverData coverMorphism)
    (inverseAutomorphism :
      HyperbolicOrbicurveAutomorphismOverData coverMorphism →
        HyperbolicOrbicurveAutomorphismOverData coverMorphism) :
    (abstractHyperbolicOrbicurveAutomorphismCompositionData
      coverMorphism identityAutomorphism composeAutomorphism
      inverseAutomorphism).identityAutomorphism.overTarget :=
  (abstractHyperbolicOrbicurveAutomorphismCompositionData
    coverMorphism identityAutomorphism composeAutomorphism
    inverseAutomorphism).identity_overTarget

/-- A constructor smoke test for finite-etale/Galois properties of a fixed morphism. -/
def abstractFiniteEtaleGaloisOrbicurveMorphismData
    {source target : HyperbolicOrbicurveModel F}
    (morphism : HyperbolicOrbicurveMorphismData source target)
    (finiteEtale galois : Prop)
    (hFiniteEtale : finiteEtale) (hGalois : galois) :
    FiniteEtaleGaloisOrbicurveMorphismData morphism where
  finiteEtale := finiteEtale
  finiteEtale_holds := hFiniteEtale
  galois := galois
  galois_holds := hGalois

example {source target : HyperbolicOrbicurveModel F}
    (morphism : HyperbolicOrbicurveMorphismData source target)
    (finiteEtale galois : Prop)
    (hFiniteEtale : finiteEtale) (hGalois : galois) :
    (abstractFiniteEtaleGaloisOrbicurveMorphismData
      morphism finiteEtale galois hFiniteEtale hGalois).finiteEtale ∧
      (abstractFiniteEtaleGaloisOrbicurveMorphismData
        morphism finiteEtale galois hFiniteEtale hGalois).galois :=
  (abstractFiniteEtaleGaloisOrbicurveMorphismData
    morphism finiteEtale galois hFiniteEtale hGalois).finiteEtaleAndGalois

/-- A constructor smoke test for the deck group of a finite-etale Galois cover. -/
def abstractOrbicurveCoverDeckTransformationData
    {source target : HyperbolicOrbicurveModel F}
    {morphism : HyperbolicOrbicurveMorphismData source target}
    (coverProperties : FiniteEtaleGaloisOrbicurveMorphismData morphism)
    (deckGroup : Type u) [Group deckGroup]
    (deckTransformationsOfCover : Prop)
    (hDeckTransformations : deckTransformationsOfCover) :
    OrbicurveCoverDeckTransformationData coverProperties where
  deckGroup := deckGroup
  deckGroupGroup := inferInstance
  deckTransformationsOfCover := deckTransformationsOfCover
  deckTransformationsOfCover_holds := hDeckTransformations

example {source target : HyperbolicOrbicurveModel F}
    {morphism : HyperbolicOrbicurveMorphismData source target}
    (coverProperties : FiniteEtaleGaloisOrbicurveMorphismData morphism)
    (deckGroup : Type u) [Group deckGroup]
    (deckTransformationsOfCover : Prop)
    (hDeckTransformations : deckTransformationsOfCover) :
    (abstractOrbicurveCoverDeckTransformationData
      coverProperties deckGroup deckTransformationsOfCover
      hDeckTransformations).deckTransformationsOfCover :=
  (abstractOrbicurveCoverDeckTransformationData
    coverProperties deckGroup deckTransformationsOfCover
    hDeckTransformations).deckTransformationsOfCover_proof

/--
A constructor smoke test for realizing a cover deck group by source
automorphisms over the cover morphism.
-/
def abstractOrbicurveCoverDeckAutomorphismRealizationData
    {source target : HyperbolicOrbicurveModel F}
    {morphism : HyperbolicOrbicurveMorphismData source target}
    {coverProperties : FiniteEtaleGaloisOrbicurveMorphismData morphism}
    (deckData : OrbicurveCoverDeckTransformationData coverProperties)
    (deckAutomorphism :
      deckData.deckGroup → HyperbolicOrbicurveAutomorphismOverData morphism)
    (realizesDeckTransformations : Prop)
    (hRealizes : realizesDeckTransformations) :
    OrbicurveCoverDeckAutomorphismRealizationData deckData where
  deckAutomorphism := deckAutomorphism
  realizesDeckTransformations := realizesDeckTransformations
  realizesDeckTransformations_holds := hRealizes

example {source target : HyperbolicOrbicurveModel F}
    {morphism : HyperbolicOrbicurveMorphismData source target}
    {coverProperties : FiniteEtaleGaloisOrbicurveMorphismData morphism}
    (deckData : OrbicurveCoverDeckTransformationData coverProperties)
    (deckAutomorphism :
      deckData.deckGroup → HyperbolicOrbicurveAutomorphismOverData morphism)
    (realizesDeckTransformations : Prop)
    (hRealizes : realizesDeckTransformations)
    (g : deckData.deckGroup) :
    let realization :=
      abstractOrbicurveCoverDeckAutomorphismRealizationData
        deckData deckAutomorphism realizesDeckTransformations hRealizes
    (realization.deckAutomorphism g).overTarget := by
  dsimp
  exact
    OrbicurveCoverDeckAutomorphismRealizationData.deckAutomorphism_overTarget
      (abstractOrbicurveCoverDeckAutomorphismRealizationData
        deckData deckAutomorphism realizesDeckTransformations hRealizes) g

/--
A constructor smoke test for group-law compatibility of a deck automorphism
realization.
-/
def abstractOrbicurveCoverDeckAutomorphismGroupLawData
    {source target : HyperbolicOrbicurveModel F}
    {morphism : HyperbolicOrbicurveMorphismData source target}
    {coverProperties : FiniteEtaleGaloisOrbicurveMorphismData morphism}
    {deckData : OrbicurveCoverDeckTransformationData coverProperties}
    (realization : OrbicurveCoverDeckAutomorphismRealizationData deckData)
    (identityCompatible multiplicationCompatible : Prop)
    (hIdentity : identityCompatible)
    (hMultiplication : multiplicationCompatible) :
    OrbicurveCoverDeckAutomorphismGroupLawData realization where
  identityCompatible := identityCompatible
  identityCompatible_holds := hIdentity
  multiplicationCompatible := multiplicationCompatible
  multiplicationCompatible_holds := hMultiplication

example {source target : HyperbolicOrbicurveModel F}
    {morphism : HyperbolicOrbicurveMorphismData source target}
    {coverProperties : FiniteEtaleGaloisOrbicurveMorphismData morphism}
    {deckData : OrbicurveCoverDeckTransformationData coverProperties}
    (realization : OrbicurveCoverDeckAutomorphismRealizationData deckData)
    (identityCompatible multiplicationCompatible : Prop)
    (hIdentity : identityCompatible)
    (hMultiplication : multiplicationCompatible) :
    (abstractOrbicurveCoverDeckAutomorphismGroupLawData
      realization identityCompatible multiplicationCompatible
      hIdentity hMultiplication).identityCompatible ∧
      (abstractOrbicurveCoverDeckAutomorphismGroupLawData
        realization identityCompatible multiplicationCompatible
        hIdentity hMultiplication).multiplicationCompatible :=
  (abstractOrbicurveCoverDeckAutomorphismGroupLawData
    realization identityCompatible multiplicationCompatible
    hIdentity hMultiplication).compatible

/--
A constructor smoke test for actual equation-level compatibility between deck
group multiplication and supplied over-target automorphism composition.
-/
def abstractOrbicurveCoverDeckAutomorphismCompositionCompatibilityData
    {source target : HyperbolicOrbicurveModel F}
    {morphism : HyperbolicOrbicurveMorphismData source target}
    {coverProperties : FiniteEtaleGaloisOrbicurveMorphismData morphism}
    {deckData : OrbicurveCoverDeckTransformationData coverProperties}
    (realization : OrbicurveCoverDeckAutomorphismRealizationData deckData)
    (composition : HyperbolicOrbicurveAutomorphismCompositionData morphism)
    (deckIdentityCompatible :
      realization.deckAutomorphism (1 : deckData.deckGroup) =
        composition.identityAutomorphism)
    (deckMultiplicationCompatible :
      ∀ g h : deckData.deckGroup,
        realization.deckAutomorphism (g * h) =
          composition.composeAutomorphism
            (realization.deckAutomorphism g)
            (realization.deckAutomorphism h)) :
    OrbicurveCoverDeckAutomorphismCompositionCompatibilityData
      realization composition where
  deckIdentityCompatible := deckIdentityCompatible
  deckMultiplicationCompatible := deckMultiplicationCompatible

example {source target : HyperbolicOrbicurveModel F}
    {morphism : HyperbolicOrbicurveMorphismData source target}
    {coverProperties : FiniteEtaleGaloisOrbicurveMorphismData morphism}
    {deckData : OrbicurveCoverDeckTransformationData coverProperties}
    (realization : OrbicurveCoverDeckAutomorphismRealizationData deckData)
    (composition : HyperbolicOrbicurveAutomorphismCompositionData morphism)
    (deckIdentityCompatible :
      realization.deckAutomorphism (1 : deckData.deckGroup) =
        composition.identityAutomorphism)
    (deckMultiplicationCompatible :
      ∀ g h : deckData.deckGroup,
        realization.deckAutomorphism (g * h) =
          composition.composeAutomorphism
            (realization.deckAutomorphism g)
            (realization.deckAutomorphism h))
    (g h : deckData.deckGroup) :
    realization.deckAutomorphism (g * h) =
      composition.composeAutomorphism
        (realization.deckAutomorphism g)
        (realization.deckAutomorphism h) :=
  (abstractOrbicurveCoverDeckAutomorphismCompositionCompatibilityData
    realization composition deckIdentityCompatible
    deckMultiplicationCompatible).deckMultiplication g h

/--
A constructor smoke test for a function-field extension attached to a fixed
orbicurve cover morphism.
-/
def abstractFunctionFieldExtensionOfOrbicurveCoverData
    {source target : HyperbolicOrbicurveModel F}
    (morphism : HyperbolicOrbicurveMorphismData source target)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (extensionOfCover : Prop) (hExtension : extensionOfCover) :
    FunctionFieldExtensionOfOrbicurveCoverData morphism B L where
  extensionOfCover := extensionOfCover
  extensionOfCover_holds := hExtension

example {source target : HyperbolicOrbicurveModel F}
    (morphism : HyperbolicOrbicurveMorphismData source target)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (extensionOfCover : Prop) (hExtension : extensionOfCover) :
    (abstractFunctionFieldExtensionOfOrbicurveCoverData
      (B := B) (L := L) morphism extensionOfCover hExtension).extensionOfCover :=
  (abstractFunctionFieldExtensionOfOrbicurveCoverData
    (B := B) (L := L) morphism extensionOfCover hExtension).extensionOfCover_proof

/-- A constructor smoke test for comparing a cover deck group with the theta quotient. -/
noncomputable def abstractOrbicurveCoverDeckQuotientData
    (thetaApproach : ThetaApproachQuotientData)
    {source target : HyperbolicOrbicurveModel F}
    {morphism : HyperbolicOrbicurveMorphismData source target}
    {coverProperties : FiniteEtaleGaloisOrbicurveMorphismData morphism}
    (deckData : OrbicurveCoverDeckTransformationData coverProperties)
    (deckGroupEquivQuotient :
      letI : Group deckData.deckGroup := deckData.deckGroupGroup
      deckData.deckGroup ≃* ThetaApproachQuotientData.deckQuotient thetaApproach)
    (deckGroupIdentifiesThetaQuotient : Prop)
    (hIdentifies : deckGroupIdentifiesThetaQuotient) :
    OrbicurveCoverDeckQuotientData thetaApproach deckData where
  deckGroupEquivQuotient := deckGroupEquivQuotient
  deckGroupIdentifiesThetaQuotient := deckGroupIdentifiesThetaQuotient
  deckGroupIdentifiesThetaQuotient_holds := hIdentifies

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {source target : HyperbolicOrbicurveModel F}
    {morphism : HyperbolicOrbicurveMorphismData source target}
    {coverProperties : FiniteEtaleGaloisOrbicurveMorphismData morphism}
    (deckData : OrbicurveCoverDeckTransformationData coverProperties)
    (deckGroupEquivQuotient :
      letI : Group deckData.deckGroup := deckData.deckGroupGroup
      deckData.deckGroup ≃* ThetaApproachQuotientData.deckQuotient thetaApproach)
    (deckGroupIdentifiesThetaQuotient : Prop)
    (hIdentifies : deckGroupIdentifiesThetaQuotient) :
    (abstractOrbicurveCoverDeckQuotientData
      thetaApproach deckData deckGroupEquivQuotient
      deckGroupIdentifiesThetaQuotient hIdentifies).deckGroupIdentifiesThetaQuotient :=
  (abstractOrbicurveCoverDeckQuotientData
    thetaApproach deckData deckGroupEquivQuotient
    deckGroupIdentifiesThetaQuotient hIdentifies).identifiesThetaQuotient

/--
A constructor smoke test for the quotient action on an indexed function-field
extension.
-/
noncomputable def abstractDeckQuotientFunctionFieldActionData
    (thetaApproach : ThetaApproachQuotientData)
    {source target : HyperbolicOrbicurveModel F}
    {morphism : HyperbolicOrbicurveMorphismData source target}
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (functionFieldExtension :
      FunctionFieldExtensionOfOrbicurveCoverData morphism B L)
    (quotientEquivAlgAut :
      ThetaApproachQuotientData.deckQuotient thetaApproach ≃* (L ≃ₐ[B] L)) :
    DeckQuotientFunctionFieldActionData thetaApproach functionFieldExtension where
  quotientEquivAlgAut := quotientEquivAlgAut

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {source target : HyperbolicOrbicurveModel F}
    {morphism : HyperbolicOrbicurveMorphismData source target}
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (functionFieldExtension :
      FunctionFieldExtensionOfOrbicurveCoverData morphism B L)
    (quotientEquivAlgAut :
      ThetaApproachQuotientData.deckQuotient thetaApproach ≃* (L ≃ₐ[B] L)) :
    (abstractDeckQuotientFunctionFieldActionData
      thetaApproach functionFieldExtension quotientEquivAlgAut).toAlgAutEquiv =
      quotientEquivAlgAut :=
  rfl

/--
A constructor smoke test for reconstruction/action compatibility attached to a
fixed quotient action.
-/
def abstractThetaFunctionFieldActionCompatibilityData
    (thetaApproach : ThetaApproachQuotientData)
    {source target : HyperbolicOrbicurveModel F}
    {morphism : HyperbolicOrbicurveMorphismData source target}
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    {functionFieldExtension :
      FunctionFieldExtensionOfOrbicurveCoverData morphism B L}
    (quotientAction :
      DeckQuotientFunctionFieldActionData thetaApproach functionFieldExtension)
    (reconstructedFunctionFieldOfXK deckActionMatchesGalQuotient : Prop)
    (hReconstructed : reconstructedFunctionFieldOfXK)
    (hDeck : deckActionMatchesGalQuotient) :
    ThetaFunctionFieldActionCompatibilityData quotientAction where
  reconstructedFunctionFieldOfXK := reconstructedFunctionFieldOfXK
  reconstructedFunctionFieldOfXK_holds := hReconstructed
  deckActionMatchesGalQuotient := deckActionMatchesGalQuotient
  deckActionMatchesGalQuotient_holds := hDeck

example
    (thetaApproach : ThetaApproachQuotientData)
    {source target : HyperbolicOrbicurveModel F}
    {morphism : HyperbolicOrbicurveMorphismData source target}
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    {functionFieldExtension :
      FunctionFieldExtensionOfOrbicurveCoverData morphism B L}
    (quotientAction :
      DeckQuotientFunctionFieldActionData thetaApproach functionFieldExtension)
    (reconstructedFunctionFieldOfXK deckActionMatchesGalQuotient : Prop)
    (hReconstructed : reconstructedFunctionFieldOfXK)
    (hDeck : deckActionMatchesGalQuotient) :
    let compatibility :=
      abstractThetaFunctionFieldActionCompatibilityData
        thetaApproach quotientAction reconstructedFunctionFieldOfXK
        deckActionMatchesGalQuotient hReconstructed hDeck
    compatibility.reconstructedFunctionFieldOfXK ∧
      compatibility.deckActionMatchesGalQuotient :=
  ⟨hReconstructed, hDeck⟩

/-- A constructor smoke test for a pointed EtTh quotient. -/
def abstractPointedEtaleQuotient (Q : Type u) (zero : Q) :
    PointedEtaleQuotient where
  carrier := Q
  zero := zero

/-- A constructor smoke test for the unit action on a quotient. -/
def abstractQuotientUnitActionData
    (Q : PointedEtaleQuotient)
    (units : Type u) (smul : units -> Q.carrier -> Q.carrier)
    (hNonzero : ∀ a x, x ≠ Q.zero -> smul a x ≠ Q.zero) :
    QuotientUnitActionData Q where
  units := units
  smul := smul
  smul_nonzero := hNonzero

/-- A constructor smoke test for a nonzero quotient element. -/
def abstractNonzeroQuotientElement
    (Q : PointedEtaleQuotient)
    (unitAction : QuotientUnitActionData Q)
    (element : Q.carrier) (hNe : element ≠ Q.zero) :
    NonzeroQuotientElement where
  quotient := Q
  unitAction := unitAction
  element := element
  element_ne_zero := hNe

/-- A constructor smoke test for a cusp arising from a nonzero quotient element. -/
def abstractCuspData
    (C : HyperbolicOrbicurveModel F) (origin : NonzeroQuotientElement) :
    CuspData C where
  label := "abstract-cusp"
  quotientOrigin := origin

example (C : HyperbolicOrbicurveModel F) (origin : NonzeroQuotientElement) :
    (abstractCuspData C origin).arisesFromNonzeroQuotientElement :=
  (abstractCuspData C origin).arisesFromNonzeroQuotientElement_holds

/-- A constructor smoke test for a sign action on a quotient. -/
def abstractQuotientSignAction
    (Q : PointedEtaleQuotient)
    (neg : Q.carrier -> Q.carrier)
    (hZero : neg Q.zero = Q.zero)
    (hInvolutive : ∀ x, neg (neg x) = x) :
    QuotientSignAction Q where
  neg := neg
  neg_zero := hZero
  neg_involutive := hInvolutive

example (Q : PointedEtaleQuotient)
    (signAction : QuotientSignAction Q) (generator : Q.carrier) :
    signAction.InSignOrbit generator generator :=
  signAction.generator_mem_signOrbit generator

example (Q : PointedEtaleQuotient)
    (signAction : QuotientSignAction Q) (generator : Q.carrier) :
    signAction.InSignOrbit (signAction.neg generator) generator :=
  signAction.neg_generator_mem_signOrbit generator

example (Q : PointedEtaleQuotient)
    (signAction : QuotientSignAction Q) (x : Q.NonzeroCarrier) :
    signAction.toSignLabelQuotient (signAction.negNonzero x) =
      signAction.toSignLabelQuotient x :=
  signAction.toSignLabelQuotient_neg_eq x

/-- A constructor smoke test for compatibility between sign and unit actions. -/
def abstractQuotientSignUnitCompatibility
    (Q : PointedEtaleQuotient)
    (unitAction : QuotientUnitActionData Q)
    (signAction : QuotientSignAction Q)
    (signUnit : unitAction.units)
    (hSign : ∀ x, unitAction.smul signUnit x = signAction.neg x) :
    QuotientSignUnitCompatibility Q unitAction signAction where
  signUnit := signUnit
  signUnit_smul_eq_neg := hSign

example (Q : PointedEtaleQuotient)
    (unitAction : QuotientUnitActionData Q)
    (signAction : QuotientSignAction Q)
    (signUnit : unitAction.units)
    (hSign : ∀ x, unitAction.smul signUnit x = signAction.neg x)
    (x : Q.carrier) :
    unitAction.smul
        (abstractQuotientSignUnitCompatibility Q unitAction signAction
          signUnit hSign).signUnit x =
      signAction.neg x :=
  (abstractQuotientSignUnitCompatibility Q unitAction signAction
    signUnit hSign).signUnit_smul_eq_neg x

/-- A constructor smoke test for a canonical-generator-up-to-sign witness. -/
def abstractCanonicalGeneratorUpToSignElement
    (Z : PointedEtaleQuotient)
    (signAction : QuotientSignAction Z)
    (canonicalGenerator element : Z.carrier)
    (hOrbit : signAction.InSignOrbit element canonicalGenerator) :
    CanonicalGeneratorUpToSignElement where
  quotient := Z
  signAction := signAction
  canonicalGenerator := canonicalGenerator
  element := element
  element_in_signOrbit := hOrbit

example (Z : PointedEtaleQuotient)
    (signAction : QuotientSignAction Z)
    (canonicalGenerator element : Z.carrier)
    (hOrbit : signAction.InSignOrbit element canonicalGenerator) :
    (abstractCanonicalGeneratorUpToSignElement Z signAction
      canonicalGenerator element hOrbit).canonicalGeneratorUpToSign :=
  (abstractCanonicalGeneratorUpToSignElement Z signAction
    canonicalGenerator element hOrbit).canonicalGeneratorUpToSign_holds

example (G : Type u) [Group G]
    (functionField : ReconstructedFunctionFieldData G)
    (x : functionField.carrier) :
    (1 : G) • x = x :=
  functionField.one_smul_element x

example (G : Type u) [Group G]
    (functionField : ReconstructedFunctionFieldData G)
    (g h : G) (x : functionField.carrier) :
    (g * h) • x = g • h • x :=
  functionField.mul_smul_element g h x

example (G : Type u) [Group G]
    (functionField : ReconstructedFunctionFieldData G)
    (g : G) :
    g • (1 : functionField.carrier) = 1 :=
  functionField.smul_one_element g

example (G : Type u) [Group G]
    (functionField : ReconstructedFunctionFieldData G)
    (g : G) (x y : functionField.carrier) :
    g • (x + y) = g • x + g • y :=
  functionField.smul_add_element g x y

example (G : Type u) [Group G]
    (functionField : ReconstructedFunctionFieldData G)
    (g : G) (x y : functionField.carrier) :
    g • (x * y) = g • x * g • y :=
  functionField.smul_mul_element g x y

example (G : Type u) [Group G]
    (functionField : ReconstructedFunctionFieldData G) :
    Function.Injective functionField.baseToFunctionField :=
  functionField.baseToFunctionField_injective_holds

example (G : Type u) [Group G]
    (functionField : ReconstructedFunctionFieldData G)
    (g : G) (b : functionField.baseCarrier) :
    g • functionField.baseToFunctionField b = functionField.baseToFunctionField b :=
  functionField.deck_smul_base g b

example (G : Type u) [Group G]
    (functionField : ReconstructedFunctionFieldData G)
    (g : G) (b : functionField.baseCarrier) :
    functionField.deckRingAut g (functionField.baseToFunctionField b) =
      functionField.baseToFunctionField b :=
  functionField.deckRingAut_fixesBase g b

example (G : Type u) [Group G]
    (functionField : ReconstructedFunctionFieldData G)
    (x : functionField.carrier) :
    (∀ g : G, g • x = x) ↔
      ∃ b : functionField.baseCarrier, functionField.baseToFunctionField b = x :=
  functionField.deck_fixed_iff_in_base x

example (G : Type u) [Group G]
    (data : AlgebraicDeckFunctionFieldData G F K) :
    data.toReconstructedFunctionFieldData.baseToFunctionField =
      algebraMap F K :=
  data.toReconstructed_baseToFunctionField

example (G : Type u) [Group G]
    (data : AlgebraicDeckFunctionFieldData G F K) :
    Function.Injective data.toReconstructedFunctionFieldData.deckRingAutHom :=
  data.toReconstructed_deckRingAutHom_injective

example (G : Type u) [Group G]
    (data : AlgebraicDeckFunctionFieldData G F K)
    (g : G) (x : K) :
    data.toReconstructedFunctionFieldData.deckRingAut g x =
      data.deckEquivAlgAut g x :=
  data.toReconstructed_deckRingAut_apply g x

example (G : Type u) [Group G]
    (data : AlgebraicDeckFunctionFieldData G F K)
    (x : K) :
    (∀ g : G, data.toReconstructedFunctionFieldData.deckRingAut g x = x) ↔
      ∃ b : F, algebraMap F K b = x :=
  data.toReconstructed_fixed_iff_in_base x

noncomputable example :
    AlgebraicDeckFunctionFieldData (F ≃ₐ[F] F) F F :=
  AlgebraicDeckFunctionFieldData.identity F

noncomputable example :
    AlgebraicDeckFunctionFieldData (K ≃ₐ[F] K) F K :=
  AlgebraicDeckFunctionFieldData.finiteGalois F K

example (x : K) :
    (∀ σ : K ≃ₐ[F] K, σ x = x) ↔
      ∃ b : F, algebraMap F K b = x :=
  AlgebraicDeckFunctionFieldData.finiteGalois_fixed_iff_in_base x

noncomputable example :
    let data := AlgebraicDeckFunctionFieldData.finiteGalois F K
    Function.Injective data.toReconstructedFunctionFieldData.deckRingAutHom := by
  let data := AlgebraicDeckFunctionFieldData.finiteGalois F K
  exact data.toReconstructed_deckRingAutHom_injective

noncomputable example (x : K) :
    let data := AlgebraicDeckFunctionFieldData.finiteGalois F K
    (∀ σ : K ≃ₐ[F] K, data.toReconstructedFunctionFieldData.deckRingAut σ x = x) ↔
      ∃ b : F, algebraMap F K b = x :=
  by
    let data := AlgebraicDeckFunctionFieldData.finiteGalois F K
    exact data.toReconstructed_fixed_iff_in_base x

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    (data :
      AlgebraicDeckFunctionFieldData
        (ThetaApproachQuotientData.deckQuotient thetaApproach) B L)
    (reconstructedFunctionFieldOfXK deckActionMatchesGalQuotient : Prop)
    (hReconstructed : reconstructedFunctionFieldOfXK)
    (hDeck : deckActionMatchesGalQuotient) :
    ThetaApproachFunctionFieldData thetaApproach :=
  ThetaApproachFunctionFieldData.ofAlgebraicDeckFunctionField
    data reconstructedFunctionFieldOfXK hReconstructed
    deckActionMatchesGalQuotient hDeck

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    (data :
      AlgebraicDeckFunctionFieldData
        (ThetaApproachQuotientData.deckQuotient thetaApproach) B L)
    (reconstructedFunctionFieldOfXK deckActionMatchesGalQuotient : Prop)
    (hReconstructed : reconstructedFunctionFieldOfXK)
    (hDeck : deckActionMatchesGalQuotient) :
    Function.Injective
      (ThetaApproachFunctionFieldData.deckRingAutHom
        (ThetaApproachFunctionFieldData.ofAlgebraicDeckFunctionField
          data reconstructedFunctionFieldOfXK hReconstructed
          deckActionMatchesGalQuotient hDeck)) :=
  (ThetaApproachFunctionFieldData.ofAlgebraicDeckFunctionField
    data reconstructedFunctionFieldOfXK hReconstructed
    deckActionMatchesGalQuotient hDeck).deckRingAutHom_injective

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (quotientEquivAlgAut :
      ThetaApproachQuotientData.deckQuotient thetaApproach ≃* (L ≃ₐ[B] L))
    (reconstructedFunctionFieldOfXK deckActionMatchesGalQuotient : Prop)
    (hReconstructed : reconstructedFunctionFieldOfXK)
    (hDeck : deckActionMatchesGalQuotient) :
    ThetaApproachFunctionFieldData thetaApproach :=
  ThetaApproachFunctionFieldData.ofFiniteGaloisAlgAutEquiv
    quotientEquivAlgAut reconstructedFunctionFieldOfXK hReconstructed
    deckActionMatchesGalQuotient hDeck

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (quotientEquivAlgAut :
      ThetaApproachQuotientData.deckQuotient thetaApproach ≃* (L ≃ₐ[B] L))
    (reconstructedFunctionFieldOfXK deckActionMatchesGalQuotient : Prop)
    (hReconstructed : reconstructedFunctionFieldOfXK)
    (hDeck : deckActionMatchesGalQuotient)
    (q : ThetaApproachQuotientData.deckQuotient thetaApproach) (x : L) :
    (ThetaApproachFunctionFieldData.ofFiniteGaloisAlgAutEquiv
      quotientEquivAlgAut reconstructedFunctionFieldOfXK hReconstructed
      deckActionMatchesGalQuotient hDeck).reconstructedFunctionField.deckRingAut q x =
      quotientEquivAlgAut q x :=
  ThetaApproachFunctionFieldData.ofFiniteGaloisAlgAutEquiv_deckRingAut_apply
    quotientEquivAlgAut reconstructedFunctionFieldOfXK hReconstructed
    deckActionMatchesGalQuotient hDeck q x

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (quotientEquivAlgAut :
      ThetaApproachQuotientData.deckQuotient thetaApproach ≃* (L ≃ₐ[B] L))
    (reconstructedFunctionFieldOfXK deckActionMatchesGalQuotient : Prop)
    (hReconstructed : reconstructedFunctionFieldOfXK)
    (hDeck : deckActionMatchesGalQuotient)
    (x : L) :
    (∀ q : ThetaApproachQuotientData.deckQuotient thetaApproach,
        (ThetaApproachFunctionFieldData.ofFiniteGaloisAlgAutEquiv
          quotientEquivAlgAut reconstructedFunctionFieldOfXK hReconstructed
          deckActionMatchesGalQuotient hDeck).reconstructedFunctionField.deckRingAut q x = x) ↔
      ∃ b : B, algebraMap B L b = x :=
  ThetaApproachFunctionFieldData.ofFiniteGaloisAlgAutEquiv_fixed_iff_in_base
    quotientEquivAlgAut reconstructedFunctionFieldOfXK hReconstructed
    deckActionMatchesGalQuotient hDeck x

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (quotientEquivAlgAut :
      ThetaApproachQuotientData.deckQuotient thetaApproach ≃* (L ≃ₐ[B] L))
    (reconstructedFunctionFieldOfXK deckActionMatchesGalQuotient : Prop)
    (hReconstructed : reconstructedFunctionFieldOfXK)
    (hDeck : deckActionMatchesGalQuotient) :
    let functionFieldData :=
      ThetaApproachFunctionFieldData.ofFiniteGaloisAlgAutEquiv
        quotientEquivAlgAut reconstructedFunctionFieldOfXK hReconstructed
        deckActionMatchesGalQuotient hDeck
    (functionFieldData.piCKRingAutHom).ker =
      thetaApproach.piXK_to_piCK.openEmbedding.imageSubgroup := by
  let functionFieldData :=
    ThetaApproachFunctionFieldData.ofFiniteGaloisAlgAutEquiv
      quotientEquivAlgAut reconstructedFunctionFieldOfXK hReconstructed
      deckActionMatchesGalQuotient hDeck
  exact functionFieldData.piCKRingAutHom_ker

/-- A constructor smoke test for a typed finite etale Galois cover certificate. -/
noncomputable def abstractThetaFiniteEtaleGaloisCoverCertificate
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (baseField : Type) [Field baseField]
    (sourceOrbicurve targetOrbicurve : HyperbolicOrbicurveModel baseField)
    (coverMorphism :
      HyperbolicOrbicurveMorphismData sourceOrbicurve targetOrbicurve)
    (coverProperties :
      FiniteEtaleGaloisOrbicurveMorphismData coverMorphism)
    (coverDeckTransformations :
      OrbicurveCoverDeckTransformationData coverProperties)
    (coverDeckAutomorphisms :
      OrbicurveCoverDeckAutomorphismRealizationData coverDeckTransformations)
    (coverDeckAutomorphismGroupLaw :
      OrbicurveCoverDeckAutomorphismGroupLawData coverDeckAutomorphisms)
    (coverAutomorphismComposition :
      HyperbolicOrbicurveAutomorphismCompositionData coverMorphism)
    (coverDeckAutomorphismCompositionCompatibility :
      OrbicurveCoverDeckAutomorphismCompositionCompatibilityData
        coverDeckAutomorphisms coverAutomorphismComposition)
    (coverDeckQuotient :
      OrbicurveCoverDeckQuotientData thetaApproach coverDeckTransformations)
    (functionFieldExtension :
      FunctionFieldExtensionOfOrbicurveCoverData coverMorphism B L)
    (quotientAction :
      DeckQuotientFunctionFieldActionData thetaApproach functionFieldExtension) :
    ThetaFiniteEtaleGaloisCoverCertificate thetaApproach B L where
  baseField := baseField
  baseFieldField := inferInstance
  sourceOrbicurve := sourceOrbicurve
  targetOrbicurve := targetOrbicurve
  coverMorphism := coverMorphism
  coverProperties := coverProperties
  coverDeckTransformations := coverDeckTransformations
  coverDeckAutomorphisms := coverDeckAutomorphisms
  coverDeckAutomorphismGroupLaw := coverDeckAutomorphismGroupLaw
  coverAutomorphismComposition := coverAutomorphismComposition
  coverDeckAutomorphismCompositionCompatibility :=
    coverDeckAutomorphismCompositionCompatibility
  coverDeckQuotient := coverDeckQuotient
  functionFieldExtension := functionFieldExtension
  quotientAction := quotientAction

/-- A constructor smoke test for a typed finite Galois theta function-field cover. -/
noncomputable def abstractThetaFiniteGaloisFunctionFieldCoverData
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (coverCertificate : ThetaFiniteEtaleGaloisCoverCertificate thetaApproach B L)
    (actionCompatibility :
      ThetaFunctionFieldActionCompatibilityData coverCertificate.quotientAction) :
    ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L where
  coverCertificate := coverCertificate
  actionCompatibility := actionCompatibility

example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (certificate : ThetaFiniteEtaleGaloisCoverCertificate thetaApproach B L) :
    certificate.finiteEtaleCover ∧ certificate.galoisCover :=
  certificate.finiteEtaleAndGalois

example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (certificate : ThetaFiniteEtaleGaloisCoverCertificate thetaApproach B L) :
    certificate.functionFieldExtensionOfCover :=
  certificate.functionFieldExtensionOfCover_proof

example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (certificate : ThetaFiniteEtaleGaloisCoverCertificate thetaApproach B L) :
    certificate.coverMorphism.morphismExists :=
  certificate.coverMorphismExists

example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (certificate : ThetaFiniteEtaleGaloisCoverCertificate thetaApproach B L) :
    certificate.coverDeckTransformations.deckTransformationsOfCover :=
  certificate.deckTransformationsOfCover

example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (certificate : ThetaFiniteEtaleGaloisCoverCertificate thetaApproach B L) :
    certificate.coverDeckQuotient.deckGroupIdentifiesThetaQuotient :=
  certificate.coverDeckIdentifiesThetaQuotient

example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (certificate : ThetaFiniteEtaleGaloisCoverCertificate thetaApproach B L)
    (g : certificate.coverDeckGroup) :
    (certificate.coverDeckAutomorphism g).automorphismExists :=
  certificate.coverDeckAutomorphism_exists g

example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (certificate : ThetaFiniteEtaleGaloisCoverCertificate thetaApproach B L)
    (g : certificate.coverDeckGroup) :
    (certificate.coverDeckAutomorphism g).overTarget :=
  certificate.coverDeckAutomorphism_overTarget g

example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (certificate : ThetaFiniteEtaleGaloisCoverCertificate thetaApproach B L) :
    certificate.coverDeckAutomorphismGroupLaw.identityCompatible ∧
      certificate.coverDeckAutomorphismGroupLaw.multiplicationCompatible :=
  certificate.coverDeckAutomorphism_groupLawCompatible

example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (certificate : ThetaFiniteEtaleGaloisCoverCertificate thetaApproach B L) :
    certificate.coverDeckAutomorphism (1 : certificate.coverDeckGroup) =
      certificate.coverAutomorphismComposition.identityAutomorphism :=
  certificate.coverDeckAutomorphism_identity_eq

example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (certificate : ThetaFiniteEtaleGaloisCoverCertificate thetaApproach B L)
    (g h : certificate.coverDeckGroup) :
    certificate.coverDeckAutomorphism (g * h) =
      certificate.coverAutomorphismComposition.composeAutomorphism
        (certificate.coverDeckAutomorphism g)
        (certificate.coverDeckAutomorphism h) :=
  certificate.coverDeckAutomorphism_mul_eq_comp g h

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (cover : ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L) :
    ThetaApproachFunctionFieldData thetaApproach :=
  cover.toThetaApproachFunctionFieldData

example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (cover : ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L) :
    cover.finiteEtaleGaloisCover :=
  cover.finiteEtaleGaloisCover_proof

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (cover : ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L)
    (q : ThetaApproachQuotientData.deckQuotient thetaApproach) (x : L) :
    cover.toThetaApproachFunctionFieldData.reconstructedFunctionField.deckRingAut q x =
      cover.quotientEquivAlgAut q x :=
  cover.deckRingAut_apply q x

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (cover : ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L)
    (g : cover.coverCertificate.coverDeckGroup) (x : L) :
    cover.coverDeckEquivAlgAut g x =
      cover.quotientEquivAlgAut
        (cover.coverCertificate.coverDeckEquivThetaQuotient g) x :=
  cover.coverDeckAlgAut_apply g x

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (cover : ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L)
    (g : cover.coverCertificate.coverDeckGroup) (x : L) :
    cover.toThetaApproachFunctionFieldData.reconstructedFunctionField.deckRingAut
        (cover.coverCertificate.coverDeckEquivThetaQuotient g) x =
      cover.coverDeckEquivAlgAut g x :=
  cover.coverDeckRingAut_apply_eq_coverDeckAlgAut g x

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (cover : ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L)
    (x : L) :
    (∀ q : ThetaApproachQuotientData.deckQuotient thetaApproach,
        cover.toThetaApproachFunctionFieldData.reconstructedFunctionField.deckRingAut q x = x) ↔
      ∃ b : B, algebraMap B L b = x :=
  cover.fixed_iff_in_base x

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (cover : ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L)
    (x : L) :
    (∀ g : cover.coverCertificate.coverDeckGroup,
        cover.toThetaApproachFunctionFieldData.reconstructedFunctionField.deckRingAut
          (cover.coverCertificate.coverDeckEquivThetaQuotient g) x = x) ↔
      ∃ b : B, algebraMap B L b = x :=
  cover.coverDeck_fixed_iff_in_base x

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (cover : ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L)
    (g : thetaApproach.piCK.carrier) (x : L) :
    cover.toThetaApproachFunctionFieldData.piCKRingAut g x =
      cover.toThetaApproachFunctionFieldData.deckRingAut
        (ThetaApproachQuotientData.quotientHom thetaApproach g) x :=
  cover.piCKRingAut_apply_eq_deckRingAut g x

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (cover : ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L)
    (g : thetaApproach.piCK.carrier) (x : L) :
    cover.toThetaApproachFunctionFieldData.piCKRingAut g x =
      cover.quotientEquivAlgAut
        (ThetaApproachQuotientData.quotientHom thetaApproach g) x :=
  cover.piCKRingAut_apply_eq_quotientAction g x

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (cover : ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L) :
    cover.toThetaApproachFunctionFieldData.piCKRingAutHom =
      cover.toThetaApproachFunctionFieldData.deckRingAutHom.comp
        (ThetaApproachQuotientData.quotientHom thetaApproach) :=
  cover.piCKRingAutHom_eq_deckRingAutHom_comp

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (cover : ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L)
    (g : thetaApproach.piXK.carrier)
    (x : cover.toThetaApproachFunctionFieldData.functionField) :
    thetaApproach.piXK_to_piCK.openEmbedding.hom g • x = x :=
  cover.piXK_smul_trivial g x

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (cover : ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L)
    (g : thetaApproach.piXK.carrier) (x : L) :
    cover.toThetaApproachFunctionFieldData.piCKRingAut
      (thetaApproach.piXK_to_piCK.openEmbedding.hom g) x = x :=
  cover.piXKRingAut_apply g x

example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (cover : ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L)
    (g : thetaApproach.piXK.carrier) :
    thetaApproach.piXK_to_piCK.openEmbedding.hom g ∈
      (cover.toThetaApproachFunctionFieldData.piCKRingAutHom).ker :=
  cover.piXK_to_piCK_mem_piCKRingAutHom_ker g

noncomputable example
    (thetaApproach : ThetaApproachQuotientData)
    {B L : Type} [Field B] [Field L] [Algebra B L]
    [FiniteDimensional B L] [IsGalois B L]
    (cover : ThetaFiniteGaloisFunctionFieldCoverData thetaApproach B L) :
    (cover.toThetaApproachFunctionFieldData.piCKRingAutHom).ker =
      thetaApproach.piXK_to_piCK.openEmbedding.imageSubgroup :=
  cover.piCKRingAutHom_ker

example :
    (zmodOneNonzeroQuotientElement primeFive).element ≠
      (zmodPointedQuotient primeFive).zero :=
  (zmodOneNonzeroQuotientElement primeFive).element_ne_zero

example (a : (ZMod primeFive.value)ˣ) (x : ZMod primeFive.value) (hx : x ≠ 0) :
    (zmodUnitActionData primeFive).smul a x ≠ (zmodPointedQuotient primeFive).zero :=
  (zmodUnitActionData primeFive).smul_nonzero a x hx

example :
    (zmodSignAction primeFive).InSignOrbit
      (-(1 : ZMod primeFive.value)) (1 : ZMod primeFive.value) :=
  (zmodSignAction primeFive).neg_generator_mem_signOrbit (1 : ZMod primeFive.value)

example (x : ZMod primeFive.value) :
    (zmodUnitActionData primeFive).smul
        (zmodSignUnitCompatibility primeFive).signUnit x =
      (zmodSignAction primeFive).neg x :=
  (zmodSignUnitCompatibility primeFive).signUnit_smul_eq_neg x

example :
    (-1 : (ZMod primeFive.value)ˣ) ∈ zmodSignUnitSubgroup primeFive :=
  neg_one_mem_zmodSignUnitSubgroup primeFive

example (a : (ZMod primeFive.value)ˣ) (x : ZMod primeFive.value)
    (ha : a ∈ zmodSignUnitSubgroup primeFive) :
    (zmodUnitActionData primeFive).smul a x = x ∨
      (zmodUnitActionData primeFive).smul a x =
        (zmodSignAction primeFive).neg x :=
  zmodSignUnitSubgroup_smul_eq_self_or_neg primeFive ha x

example (x generator : ZMod primeFive.value) :
    (∃ a : (ZMod primeFive.value)ˣ,
      a ∈ zmodSignUnitSubgroup primeFive ∧
        (zmodUnitActionData primeFive).smul a generator = x) ↔
      (zmodSignAction primeFive).InSignOrbit x generator :=
  zmodSignUnitSubgroup_orbit_iff_signOrbit primeFive x generator

example :
    (zmodSignAction primeFive).SignLabelQuotient :=
  zmodCanonicalSignLabelQuotient primeFive

example :
    (zmodSignAction primeFive).toSignLabelQuotient
        ((zmodSignAction primeFive).negNonzero (zmodOneNonzeroLabel primeFive)) =
      zmodCanonicalSignLabelQuotient primeFive :=
  zmodCanonicalSignLabelQuotient_neg_one_eq primeFive

example (t : ZMod primeFive.value) (ht : t ≠ 0) :
    (zmodNonzeroLabelFromCoordinate primeFive t ht).1 = t :=
  zmodNonzeroLabelFromCoordinate_val primeFive t ht

example (t : ZMod primeFive.value) (ht : t ≠ 0) :
    zmodSignLabelFromCoordinate primeFive (-t)
        (zmod_neg_ne_zero_of_ne_zero primeFive ht) =
      zmodSignLabelFromCoordinate primeFive t ht :=
  zmodSignLabelFromCoordinate_neg_eq primeFive t ht

example :
    zmodSignLabelFromCoordinate primeFive (1 : ZMod primeFive.value)
        (zmodOneNonzeroLabel primeFive).2 =
      zmodCanonicalSignLabelQuotient primeFive :=
  zmodSignLabelFromCoordinate_one_eq_canonical primeFive

example (a : (ZMod primeFive.value)ˣ)
    (x : (zmodPointedQuotient primeFive).NonzeroCarrier) :
    zmodUnitActionOnSignLabelQuotient primeFive a
        ((zmodSignAction primeFive).toSignLabelQuotient x) =
      (zmodSignAction primeFive).toSignLabelQuotient
        (zmodUnitSmulNonzeroLabel primeFive a x) :=
  zmodUnitActionOnSignLabelQuotient_apply primeFive a x

example (x : (zmodSignAction primeFive).SignLabelQuotient) :
    zmodUnitActionOnSignLabelQuotient primeFive 1 x = x :=
  zmodUnitActionOnSignLabelQuotient_one primeFive x

example (a b : (ZMod primeFive.value)ˣ)
    (x : (zmodSignAction primeFive).SignLabelQuotient) :
    zmodUnitActionOnSignLabelQuotient primeFive (a * b) x =
      zmodUnitActionOnSignLabelQuotient primeFive a
        (zmodUnitActionOnSignLabelQuotient primeFive b x) :=
  zmodUnitActionOnSignLabelQuotient_mul primeFive a b x

example (x : (zmodSignAction primeFive).SignLabelQuotient) :
    zmodUnitActionOnSignLabelQuotient primeFive
      (-1 : (ZMod primeFive.value)ˣ) x = x :=
  zmodUnitActionOnSignLabelQuotient_neg_one primeFive x

example {a : (ZMod primeFive.value)ˣ}
    (ha : a ∈ zmodSignUnitSubgroup primeFive)
    (x : (zmodSignAction primeFive).SignLabelQuotient) :
    zmodUnitActionOnSignLabelQuotient primeFive a x = x :=
  zmodSignUnitSubgroup_action_trivial_on_signLabelQuotient primeFive ha x

example :
    (zmodCanonicalGeneratorUpToSignElement primeFive).canonicalGeneratorUpToSign :=
  (zmodCanonicalGeneratorUpToSignElement primeFive).canonicalGeneratorUpToSign_holds

example :
    (zmodLocalLabCuspModel primeFive).canonicalCoordinate =
      (1 : ZMod primeFive.value) :=
  rfl

example :
    (zmodBadLocalQuotientZData primeFive).canonicalCoordinateZ =
      (1 : ZMod primeFive.value) :=
  rfl

example :
    (zmodBadLocalQuotientZData primeFive).toLocalLabCuspModel =
      zmodLocalLabCuspModel primeFive :=
  rfl

example :
    (BadLocalQuotientZData.canonicalGeneratorUpToSignElement
      (zmodBadLocalQuotientZData primeFive)).canonicalGeneratorUpToSign :=
  (zmodBadLocalQuotientZData primeFive).canonicalGeneratorUpToSign

example :
    (zmodLocalLabCuspModel primeFive).canonicalNonzeroQuotientElement.element ≠
      (zmodLocalLabCuspModel primeFive).labelQuotient.zero :=
  (zmodLocalLabCuspModel primeFive).canonicalNonzeroQuotientElement_ne_zero

example :
    CanonicalGeneratorUpToSignElement.canonicalGeneratorUpToSign
      (zmodLocalLabCuspModel primeFive).canonicalGeneratorUpToSignElement :=
  (zmodLocalLabCuspModel primeFive).canonicalGeneratorUpToSign

example :
    (zmodLocalLabCuspModel primeFive).canonicalSignLabel =
      (zmodSignAction primeFive).toSignLabelQuotient
        (zmodLocalLabCuspModel primeFive).canonicalNonzeroLabel :=
  (zmodLocalLabCuspModel primeFive).canonicalSignLabelEq

example (C : HyperbolicOrbicurveModel F) :
    ((zmodLocalLabCuspModel primeFive).toCuspData C "epsilon").arisesFromNonzeroQuotientElement :=
  CuspData.arisesFromNonzeroQuotientElement_holds
    ((zmodLocalLabCuspModel primeFive).toCuspData C "epsilon")

example :
    (zmodCanonicalCuspLabelClassData primeFive).labelClass =
      (zmodSignAction primeFive).toSignLabelQuotient
        (zmodLocalLabCuspModel primeFive).canonicalNonzeroLabel :=
  (zmodCanonicalCuspLabelClassData primeFive).labelClass_eq_model_quotient

example (C : HyperbolicOrbicurveModel F) :
    ((zmodModeledCuspData C "epsilon" primeFive).cusp).arisesFromNonzeroQuotientElement :=
  (zmodModeledCuspData C "epsilon" primeFive).cusp_arisesFromNonzeroQuotientElement

example (C : HyperbolicOrbicurveModel F) :
    (zmodModeledCuspData C "epsilon" primeFive).cusp.quotientOrigin =
      LocalLabCuspModel.canonicalNonzeroQuotientElement
        ((zmodModeledCuspData C "epsilon" primeFive).labelClassData.model) :=
  (zmodModeledCuspData C "epsilon" primeFive).cusp_quotientOrigin_eq_model

/-- A constructor smoke test for the finite-place valuation section. -/
def abstractThetaValuationData
    (chosenLift : NumberField.FinitePlace Fmod -> NumberField.FinitePlace K)
    (hSection :
      ∀ w, ThetaFinitePlace.comap (chosenLift w) = w)
    (chosenInfiniteLift :
      NumberField.InfinitePlace Fmod -> NumberField.InfinitePlace K)
    (hInfiniteSection :
      ∀ w,
        (chosenInfiniteLift w).comap (algebraMap Fmod K) = w)
    (badMod : Set (NumberField.FinitePlace Fmod))
    (hBad : ∃ w, w ∈ badMod)
    (hOdd : ∀ w, w ∈ badMod ->
      Odd (ThetaFinitePlace.residueCharacteristic w))
    (hPrime : ∀ w, w ∈ badMod ->
      Nat.Prime (ThetaFinitePlace.residueCharacteristic w))
    (hCoprime : ∀ w, w ∈ badMod ->
      Nat.Coprime
        (ThetaFinitePlace.residueCharacteristic w) primeFive.value) :
    ThetaValuationData primeFive Fmod K where
  chosenLift := chosenLift
  toModuli_chosenLift := hSection
  chosenInfiniteLift := chosenInfiniteLift
  toModuliInfinite_chosenLift := hInfiniteSection
  badMod := badMod
  badMod_nonempty := hBad
  badMod_oddResidueCharacteristic := hOdd
  badMod_residueCharacteristic_prime := hPrime
  badMod_residueCharacteristic_coprime_l := hCoprime

/-- A constructor smoke test for the field tower part of initial theta data. -/
def abstractThetaFieldTower
    (sqrtMinusOne : SqrtMinusOneData F)
    (hDegree : Nat.Coprime (Module.finrank Fmod F) primeFive.value) :
    ThetaFieldTower primeFive Fmod F K where
  sqrtMinusOne := sqrtMinusOne
  degreePrimeToL_holds := hDegree

/-- A constructor smoke test for the curve/moduli part of initial theta data. -/
noncomputable def abstractThetaCurveModuliData
    (cF : HyperbolicOrbicurveModel F)
    (cF_is_quotient_by_neg_one fmod_is_fieldOfModuli : Prop)
    (hQuotient : cF_is_quotient_by_neg_one)
    (hFmod : fmod_is_fieldOfModuli)
    (hStable :
      (PuncturedEllipticCurve.ofJ F (37 : F)).HasStableReductionEverywhere)
    (hTorsion :
      (PuncturedEllipticCurve.ofJ F (37 : F)).Torsion23Rational) :
    ThetaCurveModuliData Fmod F where
  xF := PuncturedEllipticCurve.ofJ F (37 : F)
  cF := cF
  cF_is_quotient_by_neg_one := cF_is_quotient_by_neg_one
  cF_is_quotient_by_neg_one_holds := hQuotient
  fmod_is_fieldOfModuli := fmod_is_fieldOfModuli
  fmod_is_fieldOfModuli_holds := hFmod
  stableReductionOverNonarchimedean := hStable
  torsion23RationalOverF := hTorsion

/-- A constructor smoke test for the `C_K`/`X_K` cover data. -/
def abstractThetaOrbicurveCoverData
    (curveModuli : ThetaCurveModuliData Fmod F)
    (cK xK : HyperbolicOrbicurveModel K)
    (cK_type : OrbicurveTypeData primeFive cK OrbicurveTypeKind.oneLTorsPM)
    (xK_type : OrbicurveTypeData primeFive xK OrbicurveTypeKind.oneLTors)
    (thetaApproachQuotient : ThetaApproachQuotientData)
    (thetaApproachFunctionField :
      ThetaApproachFunctionFieldData thetaApproachQuotient)
    (cK_core_is_baseChange_cF cK_determined_by_cF finiteEtaleCoveringDiagrams
      profiniteGroupOpenImmersions : Prop)
    (hCore : cK_core_is_baseChange_cF)
    (hDetermined : cK_determined_by_cF)
    (hEtale : finiteEtaleCoveringDiagrams)
    (hOpen : profiniteGroupOpenImmersions) :
    ThetaOrbicurveCoverData primeFive Fmod F K curveModuli where
  cK := cK
  xK := xK
  cK_type := cK_type
  thetaApproachQuotient := thetaApproachQuotient
  thetaApproachFunctionField := thetaApproachFunctionField
  cK_core_is_baseChange_cF := cK_core_is_baseChange_cF
  cK_core_is_baseChange_cF_holds := hCore
  cK_determined_by_cF := cK_determined_by_cF
  cK_determined_by_cF_holds := hDetermined
  xK_type := xK_type
  finiteEtaleCoveringDiagrams := finiteEtaleCoveringDiagrams
  finiteEtaleCoveringDiagrams_holds := hEtale
  profiniteGroupOpenImmersions := profiniteGroupOpenImmersions
  profiniteGroupOpenImmersions_holds := hOpen

/-- A constructor smoke test for bad local finite-place data. -/
def abstractThetaBadLocalData
    (curveModuli : ThetaCurveModuliData Fmod F)
    (coverData : ThetaOrbicurveCoverData primeFive Fmod F K curveModuli)
    (valuations : ThetaValuationData primeFive Fmod K)
    (localX :
      (v : NumberField.FinitePlace K) -> v ∈ valuations.selected ->
        HyperbolicOrbicurveModel (v.maximalIdeal.adicCompletion K))
    (localC :
      (v : NumberField.FinitePlace K) -> v ∈ valuations.selected ->
        HyperbolicOrbicurveModel (v.maximalIdeal.adicCompletion K))
    (localBaseChangeDiagrams
      decompositionGroupOuterSurjection :
      (v : NumberField.FinitePlace K) -> v ∈ valuations.selected -> Prop)
    (badLocalCType :
      (v : NumberField.FinitePlace K) -> (hv : v ∈ valuations.bad) ->
        BadLocalOrbicurveTypeData primeFive (localX v hv.1) (localC v hv.1))
    (hBaseChange : ∀ v hv, localBaseChangeDiagrams v hv)
    (hDecomp : ∀ v hv, decompositionGroupOuterSurjection v hv) :
    ThetaBadLocalData primeFive Fmod F K curveModuli coverData valuations where
  localX := localX
  localC := localC
  localBaseChangeDiagrams := localBaseChangeDiagrams
  localBaseChangeDiagrams_holds := hBaseChange
  decompositionGroupOuterSurjection := decompositionGroupOuterSurjection
  decompositionGroupOuterSurjection_holds := hDecomp
  badLocalCType := badLocalCType

/-- A constructor smoke test for the local cusp data of Definition 3.1(f). -/
def abstractThetaCuspLocalData
    (curveModuli : ThetaCurveModuliData Fmod F)
    (coverData : ThetaOrbicurveCoverData primeFive Fmod F K curveModuli)
    (valuations : ThetaValuationData primeFive Fmod K)
    (badLocalData :
      ThetaBadLocalData primeFive Fmod F K curveModuli coverData valuations)
    (epsilon : CuspData coverData.cK)
    (localCusp :
      (v : NumberField.FinitePlace K) -> (hv : v ∈ valuations.selected) ->
        CuspData (badLocalData.localC v hv))
    (localCusp_determinedByGlobal :
      (v : NumberField.FinitePlace K) -> (hv : v ∈ valuations.selected) -> Prop)
    (hBadQuotient :
      ∀ v hv, (localCusp v hv.1).quotientOrigin =
        (badLocalData.badLocalLabCuspModel v hv).canonicalNonzeroQuotientElement)
    (hDetermined : ∀ v hv, localCusp_determinedByGlobal v hv) :
    ThetaCuspLocalData primeFive Fmod F K curveModuli coverData valuations
      badLocalData epsilon where
  localCusp := localCusp
  localCusp_determinedByGlobal := localCusp_determinedByGlobal
  localCusp_determinedByGlobal_holds := hDetermined
  badLocalCusp_quotientOrigin_eq_model := hBadQuotient

/--
A constructor smoke test for full initial theta data under the exact field
hypotheses required by the record.
-/
noncomputable def abstractInitialThetaData
    (fieldTower : ThetaFieldTower primeFive Fmod F K)
    (curveModuli : ThetaCurveModuliData Fmod F)
    (coverData : ThetaOrbicurveCoverData primeFive Fmod F K curveModuli)
    (valuations : ThetaValuationData primeFive Fmod K)
    (badLocalData : ThetaBadLocalData primeFive Fmod F K curveModuli coverData valuations)
    (epsilon : CuspData coverData.cK)
    (cuspLocalData :
      ThetaCuspLocalData primeFive Fmod F K curveModuli coverData valuations
        badLocalData epsilon)
    (lTorsionRepresentation :
      ThetaLTorsionRepresentationData primeFive F K curveModuli.xF)
    (hImage : lTorsionRepresentation.ImageContainsSL2)
    (hBadReduction :
      ∀ v : NumberField.FinitePlace F,
        ThetaFinitePlace.comap v ∈ valuations.badMod →
          curveModuli.xF.HasMultiplicativeReductionAt v)
    (qParameterOrders :
      ThetaFQParameterOrderData primeFive Fmod F valuations.badMod)
    (hQ : qParameterOrders.OrdersPrimeToL) :
    InitialThetaData Fmod F K where
  l := primeFive
  fieldTower := fieldTower
  curveModuli := curveModuli
  coverData := coverData
  lTorsionRepresentation := lTorsionRepresentation
  valuations := valuations
  fPlacesOverBadHaveMultiplicativeReduction := hBadReduction
  badLocalData := badLocalData
  epsilon := epsilon
  cuspLocalData := cuspLocalData
  lTorsionImageContainsSL2 := hImage
  qParameterOrders := qParameterOrders
  qParameterOrdersPrimeToL := hQ

variable (theta : InitialThetaData Fmod F K)

example : Nat.Prime theta.l.value :=
  theta.prime_is_prime

example : 5 ≤ theta.l.value :=
  theta.prime_ge_five

example : ∃ v, v ∈ theta.valuations.bad :=
  theta.badValuations_nonempty

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    ThetaFinitePlace.comap (theta.selectedFPlace v) ∈
      theta.valuations.badMod :=
  theta.selectedFPlace_mem_badMod v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    theta.curveModuli.xF.HasMultiplicativeReductionAt
      (theta.selectedFPlace v) :=
  theta.badValuation_has_multiplicative_reduction hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    theta.selectedFQParameterOrder v hv =
      theta.qParameterOrders.orderAtBadFPlace
        (theta.selectedFPlace v) (theta.selectedFPlace_mem_badMod v hv) :=
  rfl

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.selected) :
    theta.badLocalData.localBaseChangeDiagrams v hv :=
  theta.localBaseChangeDiagrams v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.selected) :
    theta.badLocalData.decompositionGroupOuterSurjection v hv :=
  theta.decompositionGroupOuterSurjection v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    (theta.badLocalData.badLocalCType v hv).typeData.hasType :=
  theta.badLocalType v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    theta.badLocalData.badLocalLabCuspModel v hv =
      BadLocalQuotientZData.toLocalLabCuspModel
        ((theta.badLocalData.badLocalCType v hv).thetaRootData.quotientZData) :=
  theta.badLocalLabCuspModelSource v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    (theta.badLocalData.thetaRootLocalXType v hv).hasType :=
  theta.thetaRootLocalXType v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    (theta.badLocalData.thetaRootLocalCType v hv).hasType :=
  theta.thetaRootLocalCType v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    theta.badLocalData.thetaRootLocalModels v hv :=
  theta.thetaRootLocalModels v hv

noncomputable example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    BadLocalOpenSubgroupData :=
  theta.badLocalOpenSubgroups v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    (theta.badLocalOpenSubgroups v hv).piXbar_to_piCbar.isOpenImage :=
  theta.badLocalPiXbarOpenInPiCbar v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    (theta.badLocalOpenSubgroups v hv).piCbar_to_piCv.isOpenImage :=
  theta.badLocalPiCbarOpenInPiCv v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    (theta.badLocalOpenSubgroups v hv).piXbar_to_piCv_openEmbedding.isOpenImage :=
  theta.badLocalPiXbarOpenInPiCv v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    Topology.IsOpenEmbedding (theta.badLocalOpenSubgroups v hv).piXbar_to_piCv :=
  theta.badLocalPiXbarToPiCvIsOpenEmbedding v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    Function.Injective (theta.badLocalOpenSubgroups v hv).piXbar_to_piCv :=
  theta.badLocalPiXbarToPiCvInjective v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.selected) :
    theta.cuspLocalData.localCusp_determinedByGlobal v hv :=
  theta.localCuspDeterminedByGlobal v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.selected) :
    (theta.localCusp v hv).arisesFromNonzeroQuotientElement :=
  theta.localCusp_arisesFromNonzeroQuotientElement v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    (theta.badLocalCanonicalGenerator v hv).canonicalGeneratorUpToSign :=
  theta.badLocalCusp_arisesFromCanonicalGenerator v hv

noncomputable example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    LocalLabCuspModel theta.l :=
  theta.badLocalLabCuspModel v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    (theta.badLocalCusp v hv).quotientOrigin =
      (theta.badLocalLabCuspModel v hv).canonicalNonzeroQuotientElement :=
  theta.badLocalCusp_quotientOrigin_eq_model v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    theta.badLocalCusp v hv =
      (theta.badLocalLabCuspModel v hv).toCuspData
        (theta.badLocalData.localC v hv.1) (theta.badLocalCusp v hv).label :=
  theta.badLocalCusp_eq_modelCusp v hv

noncomputable example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    ModeledCuspData (theta.badLocalData.localC v hv.1) theta.l :=
  theta.badLocalModeledCusp v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    (theta.badLocalModeledCusp v hv).cusp = theta.badLocalCusp v hv :=
  theta.badLocalModeledCusp_cusp v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    (theta.badLocalModeledCusp v hv).labelClassData.labelClass =
      QuotientSignAction.toSignLabelQuotient
        ((theta.badLocalModeledCusp v hv).labelClassData.model.signAction)
        (LocalLabCuspModel.canonicalNonzeroLabel
          ((theta.badLocalModeledCusp v hv).labelClassData.model)) :=
  theta.badLocalModeledCusp_labelClass_eq_model_quotient v hv

example (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    theta.badLocalCanonicalGenerator v hv =
      (theta.badLocalLabCuspModel v hv).canonicalGeneratorUpToSignElement :=
  theta.badLocalCanonicalGenerator_eq_model v hv

example (v : NumberField.FinitePlace K) :
    ThetaPlace.finite v ∈ theta.valuations.vnon ↔
      v ∈ theta.valuations.selected :=
  theta.finitePlace_mem_vnon_iff v

example (v : NumberField.InfinitePlace K) :
    ThetaPlace.infinite v ∈ theta.valuations.varc ↔
      v ∈ theta.valuations.selectedInfinite :=
  theta.infinitePlace_mem_varc_iff v

example (v : NumberField.FinitePlace K) :
    ThetaPlace.finite v ∈ theta.valuations.vbad ↔
      v ∈ theta.valuations.bad :=
  theta.finitePlace_mem_vbad_iff v

example (v : NumberField.FinitePlace K) :
    ThetaPlace.finite v ∈ theta.valuations.vgood ↔
      v ∈ theta.valuations.good :=
  theta.finitePlace_mem_vgood_iff v

example : Nat.Coprime (Module.finrank Fmod F) theta.l.value :=
  theta.degree_F_over_Fmod_prime_to_l

example :
    theta.fieldTower.sqrtMinusOne.element ^ 2 = (-1 : F) :=
  theta.sqrtMinusOne_square

example : theta.curveModuli.cF_is_quotient_by_neg_one :=
  theta.quotientByNegOne

example : theta.curveModuli.fmod_is_fieldOfModuli :=
  theta.fmodFieldOfModuli

example : theta.curveModuli.xF.HasStableReductionEverywhere :=
  theta.stableReductionOverNonarchimedean

example : theta.curveModuli.xF.Torsion23Rational :=
  theta.torsion23RationalOverF

example : theta.coverData.cK_type.hasType :=
  theta.cKType

example : theta.coverData.cK_core_is_baseChange_cF :=
  theta.cKCoreBaseChange

example : theta.coverData.cK_determined_by_cF :=
  theta.cKDeterminedByCF

example : theta.coverData.xK_type.hasType :=
  theta.xKType

example :
    theta.coverData.thetaApproachQuotient.piXK_to_piCK.openEmbedding.isOpenImage :=
  theta.thetaApproachPiXKOpenInPiCK

example :
    theta.coverData.thetaApproachQuotient.piXK_to_piCK.openEmbedding.imageSubgroup.Normal :=
  theta.thetaApproachPiXKNormalInPiCK

example :
    Function.Surjective
      (ThetaApproachQuotientData.quotientMap theta.coverData.thetaApproachQuotient) :=
  theta.thetaApproachQuotientMapSurjective

example :
    Function.Surjective
      (ThetaApproachQuotientData.quotientHom theta.coverData.thetaApproachQuotient) :=
  theta.thetaApproachQuotientHomSurjective

example (g : theta.coverData.thetaApproachQuotient.piXK.carrier) :
    ThetaApproachQuotientData.quotientHom theta.coverData.thetaApproachQuotient
        (theta.coverData.thetaApproachQuotient.piXK_to_piCK.openEmbedding.hom g) = 1 :=
  theta.thetaApproachQuotientHomPiXK_eq_one g

example :
    (ThetaApproachQuotientData.quotientHom theta.coverData.thetaApproachQuotient).ker =
      theta.coverData.thetaApproachQuotient.piXK_to_piCK.openEmbedding.imageSubgroup :=
  theta.thetaApproachQuotientHomKer

variable (galData :
  ThetaApproachGaloisQuotientData theta.coverData.thetaApproachQuotient)

example :
    Function.Surjective
      (InitialThetaData.thetaApproachGalPiCKHom theta galData) :=
  theta.thetaApproachGalPiCKHomSurjective galData

example :
    (InitialThetaData.thetaApproachGalPiCKHom theta galData).ker =
      theta.coverData.thetaApproachQuotient.piXK_to_piCK.openEmbedding.imageSubgroup :=
  theta.thetaApproachGalPiCKHomKer galData

example (g : theta.coverData.thetaApproachQuotient.piXK.carrier) :
    InitialThetaData.thetaApproachGalPiCKHom theta galData
        (theta.coverData.thetaApproachQuotient.piXK_to_piCK.openEmbedding.hom g) = 1 :=
  theta.thetaApproachPiXK_toGal_eq_one galData g

example
    (γ : galData.galXKCK)
    (x : ThetaApproachFunctionFieldData.functionField
      theta.coverData.thetaApproachFunctionField) :
    γ • x =
      ThetaApproachGaloisQuotientData.toDeckHom galData γ • x :=
  ThetaApproachGaloisQuotientData.gal_smul_eq_deck_smul galData
    theta.coverData.thetaApproachFunctionField γ x

example
    (g : theta.coverData.thetaApproachQuotient.piCK.carrier)
    (x : ThetaApproachFunctionFieldData.functionField
      theta.coverData.thetaApproachFunctionField) :
    g • x =
      InitialThetaData.thetaApproachGalPiCKHom theta galData g • x :=
  ThetaApproachGaloisQuotientData.piCK_smul_eq_gal_smul galData
    theta.coverData.thetaApproachFunctionField g x

example
    (g : ThetaApproachQuotientData.deckQuotient theta.coverData.thetaApproachQuotient)
    (x : ThetaApproachFunctionFieldData.functionField
      theta.coverData.thetaApproachFunctionField) :
    InitialThetaData.thetaApproachDeckRingAutHom theta g x = g • x :=
  theta.thetaApproachDeckRingAut_apply g x

example
    (g : theta.coverData.thetaApproachQuotient.piCK.carrier)
    (x : ThetaApproachFunctionFieldData.functionField
      theta.coverData.thetaApproachFunctionField) :
    InitialThetaData.thetaApproachPiCKRingAutHom theta g x = g • x :=
  theta.thetaApproachPiCKRingAut_apply g x

example
    (γ : galData.galXKCK)
    (x : ThetaApproachFunctionFieldData.functionField
      theta.coverData.thetaApproachFunctionField) :
    InitialThetaData.thetaApproachGalRingAutHom theta galData γ x = γ • x :=
  theta.thetaApproachGalRingAut_apply galData γ x

example (g : theta.coverData.thetaApproachQuotient.piCK.carrier) :
    InitialThetaData.thetaApproachPiCKRingAutHom theta g =
      InitialThetaData.thetaApproachGalRingAutHom theta galData
        (InitialThetaData.thetaApproachGalPiCKHom theta galData g) :=
  theta.thetaApproachPiCKRingAut_eq_galRingAut galData g

example :
    Function.Injective (InitialThetaData.thetaApproachDeckRingAutHom theta) :=
  theta.thetaApproachDeckRingAutHomInjective

example :
    (InitialThetaData.thetaApproachPiCKRingAutHom theta).ker =
      theta.coverData.thetaApproachQuotient.piXK_to_piCK.openEmbedding.imageSubgroup :=
  theta.thetaApproachPiCKRingAutHomKer

example :
    Function.Injective (InitialThetaData.thetaApproachGalRingAutHom theta galData) :=
  theta.thetaApproachGalRingAutHomInjective galData

example :
    Function.Injective (InitialThetaData.thetaApproachBaseToFunctionField theta) :=
  theta.thetaApproachBaseToFunctionFieldInjective

example
    (g : ThetaApproachQuotientData.deckQuotient theta.coverData.thetaApproachQuotient)
    (b : theta.thetaApproachBaseFunctionFieldCarrier) :
    g • InitialThetaData.thetaApproachBaseToFunctionField theta b =
      InitialThetaData.thetaApproachBaseToFunctionField theta b :=
  theta.thetaApproachDeck_smul_base g b

example
    (g : theta.coverData.thetaApproachQuotient.piCK.carrier)
    (b : theta.thetaApproachBaseFunctionFieldCarrier) :
    g • InitialThetaData.thetaApproachBaseToFunctionField theta b =
      InitialThetaData.thetaApproachBaseToFunctionField theta b :=
  theta.thetaApproachPiCK_smul_base g b

example
    (γ : galData.galXKCK)
    (b : theta.thetaApproachBaseFunctionFieldCarrier) :
    γ • InitialThetaData.thetaApproachBaseToFunctionField theta b =
      InitialThetaData.thetaApproachBaseToFunctionField theta b :=
  theta.thetaApproachGal_smul_base galData γ b

example
    (g : ThetaApproachQuotientData.deckQuotient theta.coverData.thetaApproachQuotient)
    (b : theta.thetaApproachBaseFunctionFieldCarrier) :
    InitialThetaData.thetaApproachDeckRingAutHom theta g
        (InitialThetaData.thetaApproachBaseToFunctionField theta b) =
      InitialThetaData.thetaApproachBaseToFunctionField theta b :=
  theta.thetaApproachDeckRingAut_fixesBase g b

example
    (g : theta.coverData.thetaApproachQuotient.piCK.carrier)
    (b : theta.thetaApproachBaseFunctionFieldCarrier) :
    InitialThetaData.thetaApproachPiCKRingAutHom theta g
        (InitialThetaData.thetaApproachBaseToFunctionField theta b) =
      InitialThetaData.thetaApproachBaseToFunctionField theta b :=
  theta.thetaApproachPiCKRingAut_fixesBase g b

example
    (γ : galData.galXKCK)
    (b : theta.thetaApproachBaseFunctionFieldCarrier) :
    InitialThetaData.thetaApproachGalRingAutHom theta galData γ
        (InitialThetaData.thetaApproachBaseToFunctionField theta b) =
      InitialThetaData.thetaApproachBaseToFunctionField theta b :=
  theta.thetaApproachGalRingAut_fixesBase galData γ b

example
    (x : ThetaApproachFunctionFieldData.functionField
      theta.coverData.thetaApproachFunctionField) :
    (∀ g : ThetaApproachQuotientData.deckQuotient theta.coverData.thetaApproachQuotient,
        g • x = x) ↔
      ∃ b : theta.thetaApproachBaseFunctionFieldCarrier,
        InitialThetaData.thetaApproachBaseToFunctionField theta b = x :=
  theta.thetaApproachDeck_fixed_iff_in_base x

example
    (x : ThetaApproachFunctionFieldData.functionField
      theta.coverData.thetaApproachFunctionField) :
    (∀ g : theta.coverData.thetaApproachQuotient.piCK.carrier, g • x = x) ↔
      ∃ b : theta.thetaApproachBaseFunctionFieldCarrier,
        InitialThetaData.thetaApproachBaseToFunctionField theta b = x :=
  theta.thetaApproachPiCK_fixed_iff_in_base x

example
    (x : ThetaApproachFunctionFieldData.functionField
      theta.coverData.thetaApproachFunctionField) :
    (∀ γ : galData.galXKCK, γ • x = x) ↔
      ∃ b : theta.thetaApproachBaseFunctionFieldCarrier,
        InitialThetaData.thetaApproachBaseToFunctionField theta b = x :=
  theta.thetaApproachGal_fixed_iff_in_base galData x

example :
    theta.coverData.thetaApproachQuotient.galXKCK_identifiedWithQuotient :=
  theta.thetaApproachGalQuotientIdentification

example :
    theta.coverData.thetaApproachQuotient.thetaApproachReconstruction :=
  theta.thetaApproachReconstruction

example :
    theta.coverData.thetaApproachFunctionField.reconstructedFunctionFieldOfXK :=
  theta.coverData.thetaApproachFunctionFieldOfXK

example :
    theta.coverData.thetaApproachFunctionField.deckActionMatchesGalQuotient :=
  theta.coverData.thetaApproachDeckActionMatchesQuotient

example
    (g : theta.coverData.thetaApproachQuotient.piCK.carrier)
    (x : ThetaApproachFunctionFieldData.functionField
      theta.coverData.thetaApproachFunctionField) :
    g • x =
      (ThetaApproachQuotientData.quotientHom theta.coverData.thetaApproachQuotient g) • x :=
  theta.coverData.thetaApproachFunctionField.piCK_smul_eq_deck_smul g x

example
    (g : theta.coverData.thetaApproachQuotient.piCK.carrier)
    (x y : ThetaApproachFunctionFieldData.functionField
      theta.coverData.thetaApproachFunctionField) :
    g • (x * y) = g • x * g • y :=
  theta.coverData.thetaApproachFunctionField.piCK_smul_mul g x y

example
    (g : theta.coverData.thetaApproachQuotient.piXK.carrier)
    (x : ThetaApproachFunctionFieldData.functionField
      theta.coverData.thetaApproachFunctionField) :
    theta.coverData.thetaApproachQuotient.piXK_to_piCK.openEmbedding.hom g • x = x :=
  theta.thetaApproachPiXK_smul_trivial g x

example : theta.coverData.finiteEtaleCoveringDiagrams :=
  theta.finiteEtaleCoveringDiagrams

example : theta.coverData.profiniteGroupOpenImmersions :=
  theta.profiniteGroupOpenImmersions

example : theta.lTorsionRepresentation.IsKernelField :=
  theta.kIsLTorsionKernelField

example (j : F) :
    (PuncturedEllipticCurve.ofJ F j).jInvariant = j :=
  PuncturedEllipticCurve.jInvariant_ofJ F j

end AbstractConstructor

end InitialThetaDataExample

end Iut
