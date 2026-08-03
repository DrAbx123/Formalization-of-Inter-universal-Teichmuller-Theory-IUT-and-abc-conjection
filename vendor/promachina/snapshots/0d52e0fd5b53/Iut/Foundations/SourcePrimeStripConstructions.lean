/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceDefinition52Sequential
import Iut.Foundations.SourceTimesMuReconstructionAlgorithm

/-!
# Canonical source prime strips

This file implements the constructors that are immediate from the local and
global models of IUT I, Examples 3.2--3.5.  In particular, the canonical
`D`, `F`, `F^tilde`, and globally realified `F^tilde` strips do not accept
component equivalences, Kummer squares, characteristic splittings, or
currency-exchange maps as additional input: those data are the corresponding
model data and every comparison is the identity comparison.

Constructing the Examples 3.2--3.5 model package itself from initial theta
data is a separate arithmetic reconstruction theorem.  Keeping that theorem
separate prevents an arbitrary collection of categories from being presented
as the canonical strip.
-/

open CategoryTheory

namespace Iut

universe u

namespace AutHolomorphicOrbispaceIso

/-- The identity isomorphism of an Aut-holomorphic orbispace presentation. -/
def refl (X : AutHolomorphicOrbispacePresentation.{u}) :
    AutHolomorphicOrbispaceIso X X where
  underlying := CategoryTheory.Equivalence.refl
  automorphisms := TopologicalMonoidIso.refl X.automorphisms
  action_compatible _ :=
    (Functor.comp_id _).trans (Functor.id_comp _).symm

end AutHolomorphicOrbispaceIso

namespace SourceDPrimeStrip

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : SourceInitialThetaCore Fmod F K}

/--
The model `D`-prime-strip of IUT I, Definition 4.1(i)--(ii).

Its finite constituents are the actual `D_v` categories of the supplied
Examples 3.2--3.3 models; its infinite constituents are the actual
Aut-holomorphic orbispaces of Example 3.4.  The label class is the literal
nonzero `ell`-torsion label modulo inversion.
-/
def canonical
    (models : IUTIThetaHodgeTheaterModels theta)
    (history : SourceThetaArithmeticHistory theta) :
    SourceDPrimeStrip models where
  history := history
  nonarchimedean v := (models.nonarchimedean v).d
  nonarchimedeanEquivalence _ := CategoryTheory.Equivalence.refl
  archimedean v := (models.archimedean v).d
  archimedeanIso _ := AutHolomorphicOrbispaceIso.refl _
  labelClasses _ :=
    ULift.{u}
      (EtaleTheta.SignLabel
        (EtaleTheta.LTorsionLabel theta.l.value))
  labelEquiv _ := Equiv.ulift
  canonicalLabelClass _ :=
    ULift.up
      (EtaleTheta.canonicalTateSignLabel theta.l.value
        (lt_of_lt_of_le (by decide : 1 < 5) theta.l.ge_five))
  canonicalLabelClass_eq _ := rfl

end SourceDPrimeStrip

namespace SourceDMonoAnalyticPrimeStrip

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : SourceInitialThetaCore Fmod F K}

/-- The model mono-analytic `D^tilde`-prime-strip of Definition 4.1(iii). -/
def canonical (models : IUTIThetaHodgeTheaterModels theta) :
    SourceDMonoAnalyticPrimeStrip models where
  nonarchimedean v := (models.nonarchimedean v).dTilde
  nonarchimedeanEquivalence _ := CategoryTheory.Equivalence.refl
  archimedean v := (models.archimedean v).dTilde
  archimedeanIso _ := AutHolomorphicOrbispaceIso.refl _

end SourceDMonoAnalyticPrimeStrip

namespace SourceFPrimeStrip

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : SourceInitialThetaCore Fmod F K}

/--
The canonical holomorphic `F`-prime-strip of Definition 5.2(i).

At finite places this is the packaged local Frobenioid itself.  At infinite
places it is the complete `(C_v,D_v,kappa_v)` model, so Kummer compatibility
is definitional rather than a separately chosen square.
-/
def canonical
    (models : IUTIThetaHodgeTheaterModels theta)
    (history : SourceThetaArithmeticHistory theta) :
    SourceFPrimeStrip models where
  history := history
  nonarchimedean v := (models.nonarchimedean v).frobenioid
  nonarchimedeanEquivalence _ := CategoryTheory.Equivalence.refl
  nonarchimedeanBaseEquivalence v :=
    (models.nonarchimedean v).baseDerivedFromCategory
  archimedean v := models.archimedean v
  archimedeanCategoryEquivalence _ := CategoryTheory.Equivalence.refl
  archimedeanOrbispaceIso _ := AutHolomorphicOrbispaceIso.refl _
  archimedeanUnitIso _ := TopologicalMonoidIso.refl _
  kummer_compatible _ _ := rfl

/--
At a finite place, forgetting the canonical `F`-strip is identified with the
canonical `D`-constituent by the base-category comparison of Example 3.2.
-/
def associatedDNonarchimedeanEquivalence
    (models : IUTIThetaHodgeTheaterModels theta)
    (history : SourceThetaArithmeticHistory theta)
    (v : SourceSelectedFinitePlace theta) :
    CategoryTheory.Equivalence
      ((canonical models history).associatedD.nonarchimedean v)
      ((SourceDPrimeStrip.canonical models history).nonarchimedean v) :=
  (models.nonarchimedean v).baseDerivedFromCategory

/-- At infinity, the associated and canonical `D`-constituents coincide. -/
theorem associatedD_archimedean_eq
    (models : IUTIThetaHodgeTheaterModels theta)
    (history : SourceThetaArithmeticHistory theta)
    (v : SourceSelectedInfinitePlace theta) :
    (canonical models history).associatedD.archimedean v =
      (SourceDPrimeStrip.canonical models history).archimedean v :=
  rfl

end SourceFPrimeStrip

namespace SourceFMonoAnalyticPrimeStrip

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : SourceInitialThetaCore Fmod F K}

/--
The canonical mono-analytic `F^tilde`-prime-strip of Definition 5.2(ii).

The selected characteristic splittings and, at infinity, the distinguished
`TM^tilde` factors are exactly those of the local models.
-/
def canonical (models : IUTIThetaHodgeTheaterModels theta) :
    SourceFMonoAnalyticPrimeStrip models :=
  SourceFMonoAnalyticPrimeStripEquivalence.model models

end SourceFMonoAnalyticPrimeStrip

/-! ## Definition 5.2(iii): the mono-analytic isomorphism category -/

/--
Mono-analytic `F^tilde`-prime-strips form the isomorphism-only category of
Definition 5.2(iii).  Its arrows are the already constructed Section 0
full-poly classes, so associativity and the unit laws are inherited from the
proved quotient laws rather than imposed on representatives.
-/
instance sourceFMonoAnalyticPrimeStripCategory
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta} :
    Category (SourceFMonoAnalyticPrimeStrip models) where
  Hom := SourceFMonoAnalyticPrimeStripFullPolyIsomorphism
  id := SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.id
  comp := SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.comp
  id_comp := SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.id_comp
  comp_id := SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.comp_id
  assoc := SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.comp_assoc

/-- Finite capsules in the mono-analytic isomorphism category. -/
abbrev SourceFMonoAnalyticPrimeStripCapsule
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta} :=
  CategoryCapsule (CategoryTheory.Cat.of (SourceFMonoAnalyticPrimeStrip models))

namespace SourceFGloballyRealifiedMonoAnalyticPrimeStrip

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : SourceInitialThetaCore Fmod F K}

/--
The canonical globally realified mono-analytic strip of Definition 5.2(iv).

Every `rho_v` is the Example 3.5 currency-exchange isomorphism.  In
particular, this constructor cannot be used with an unrelated local monoid or
an independently supplied prime type.
-/
def canonical (models : IUTIThetaHodgeTheaterModels theta) :
    SourceFGloballyRealifiedMonoAnalyticPrimeStrip models where
  globalFrobenioid := models.global.frobenioid
  globalEquivalence := CategoryTheory.Equivalence.refl
  Prime := models.global.Prime
  primeEquivSelectedPlace := models.global.primeEquivSelectedPlace
  primeModelEquiv := Equiv.refl _
  prime_compatible _ := rfl
  monoAnalytic := SourceFMonoAnalyticPrimeStrip.canonical models
  characteristicLocal := models.global.characteristicLocal
  realifiedLocal := models.global.realifiedLocal
  rho := models.global.rho
  characteristicLocalIso _ := TopologicalMonoidIso.refl _
  realifiedLocalIso _ := TopologicalMonoidIso.refl _
  rho_compatible _ _ := rfl

end SourceFGloballyRealifiedMonoAnalyticPrimeStrip

/-! ## The constructed finite-place Definition 5.2(v) core -/

namespace SourceSelectedFinitePlace

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : SourceInitialThetaCore Fmod F K}

/--
The literal filtered ind-system of integral elements at a selected finite
place.  This is the constructed `O_(Kbar_v)^triangle` part of Definition
5.2(v), not an output field of a prime-strip record.
-/
noncomputable def integralIndSystem
    (v : SourceSelectedFinitePlace theta) :=
  SourceFinitePlaceReconstruction.integralIndSystem v.1

/-- The exhaustive algebraic limit of the selected-place integral system. -/
noncomputable def integralIndSystemLimit
    (v : SourceSelectedFinitePlace theta) :=
  SourceFinitePlaceReconstruction.integralIndSystemLimit v.1

/-- The source's positive-integer cofinal presentation at a selected place. -/
noncomputable def integralIndSequentialPresentation
    (v : SourceSelectedFinitePlace theta) :=
  SourceFinitePlaceReconstruction.integralIndSourceSequentialPresentation v.1

end SourceSelectedFinitePlace

end Iut
