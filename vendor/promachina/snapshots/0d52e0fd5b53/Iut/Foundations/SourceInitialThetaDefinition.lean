/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceInitialThetaData
import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# IUT I, Definition 3.1, clause by clause

This module is the canonical constructor boundary for the initial theta datum
of IUT I, Definition 3.1(a)--(f).  Each clause is represented by typed
mathematical data.  The compatibility records used by the rest of the
formalization are constructed from those clauses; in particular, callers do
not separately supply a field tower or a valuation package which could
disagree with the source clauses.
-/

namespace Iut

universe u

noncomputable section

namespace ThetaFinitePlace

/-- The residue characteristic at a nonarchimedean place is automatically prime. -/
theorem residueCharacteristic_prime
    {K : Type u} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :
    Nat.Prime (residueCharacteristic v) := by
  unfold residueCharacteristic
  exact CharP.prime_ringChar (ResidueField v)

end ThetaFinitePlace

/-- The nonempty odd-characteristic set `V_mod^bad` of Definition 3.1(b). -/
structure SourceThetaBadModuliData
    (Fmod : Type u) [Field Fmod] [NumberField Fmod] where
  badMod : Set (NumberField.FinitePlace Fmod)
  nonempty : badMod.Nonempty
  oddResidueCharacteristic :
    ∀ w ∈ badMod, Odd (ThetaFinitePlace.residueCharacteristic w)

/-- The section `V -> V_mod` on finite and infinite places in Definition 3.1(e). -/
structure SourceThetaSelectedPlaceData
    (Fmod K : Type u)
    [Field Fmod] [NumberField Fmod]
    [Field K] [NumberField K]
    [Algebra Fmod K] where
  finiteLift :
    NumberField.FinitePlace Fmod -> NumberField.FinitePlace K
  finiteLift_comap :
    ∀ w, ThetaFinitePlace.comap (finiteLift w) = w
  infiniteLift :
    NumberField.InfinitePlace Fmod -> NumberField.InfinitePlace K
  infiniteLift_comap :
    ∀ w, (infiniteLift w).comap (algebraMap Fmod K) = w

namespace SourceThetaSelectedPlaceData

variable {l : PrimeGeFive}
variable {Fmod K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field K] [NumberField K]
variable [Algebra Fmod K]

/--
The old mixed valuation record, derived from the independent data of clauses
(b), (c), and (e).  Residue-characteristic primality is a theorem about the
residue field and is therefore not an input.
-/
def toValuations
    (selection : SourceThetaSelectedPlaceData Fmod K)
    (bad : SourceThetaBadModuliData Fmod)
    (residueCoprime :
      ∀ w ∈ bad.badMod,
        Nat.Coprime
          (ThetaFinitePlace.residueCharacteristic w) l.value) :
    ThetaValuationData l Fmod K where
  chosenLift := selection.finiteLift
  toModuli_chosenLift := selection.finiteLift_comap
  chosenInfiniteLift := selection.infiniteLift
  toModuliInfinite_chosenLift := selection.infiniteLift_comap
  badMod := bad.badMod
  badMod_nonempty := bad.nonempty
  badMod_oddResidueCharacteristic := bad.oddResidueCharacteristic
  badMod_residueCharacteristic_prime :=
    fun w _ => ThetaFinitePlace.residueCharacteristic_prime w
  badMod_residueCharacteristic_coprime_l := residueCoprime

@[simp]
theorem toValuations_badMod
    (selection : SourceThetaSelectedPlaceData Fmod K)
    (bad : SourceThetaBadModuliData Fmod)
    (residueCoprime :
      ∀ w ∈ bad.badMod,
        Nat.Coprime
          (ThetaFinitePlace.residueCharacteristic w) l.value) :
    (selection.toValuations bad residueCoprime).badMod = bad.badMod :=
  rfl

@[simp]
theorem toValuations_chosenLift
    (selection : SourceThetaSelectedPlaceData Fmod K)
    (bad : SourceThetaBadModuliData Fmod)
    (residueCoprime :
      ∀ w ∈ bad.badMod,
        Nat.Coprime
          (ThetaFinitePlace.residueCharacteristic w) l.value) :
    (selection.toValuations bad residueCoprime).chosenLift =
      selection.finiteLift :=
  rfl

end SourceThetaSelectedPlaceData

/-- Clause (a): the number field `F` contains a square root of `-1`. -/
structure SourceInitialThetaClauseA
    (F : Type u) [Field F] where
  sqrtMinusOne : SqrtMinusOneData F

/--
Clause (b): the punctured elliptic curve, quotient orbicurve, field of
moduli, bad moduli places, and the conditions imposed on them.

The maximal solvable extension and absolute Galois groups mentioned in the
paper are canonical constructions from these fields and are not supplied.
-/
structure SourceInitialThetaClauseB
    (l : PrimeGeFive)
    (Fmod F : Type u)
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Algebra Fmod F]
    [FiniteDimensional Fmod F] where
  curveModuli : SourceThetaCurveModuliData Fmod F
  badModuli : SourceThetaBadModuliData Fmod
  degreePrimeToL :
    Nat.Coprime (Module.finrank Fmod F) l.value
  fPlacesOverBadHaveMultiplicativeReduction :
    ∀ v : NumberField.FinitePlace F,
      ThetaFinitePlace.comap v ∈ badModuli.badMod ->
        curveModuli.xF.HasMultiplicativeReductionAt v

/--
Clause (c): the mod-`l` representation, its literal kernel field `K`, the
large-image condition, and the two prime-to-`l` conditions at bad places.
-/
structure SourceInitialThetaClauseC
    (l : PrimeGeFive)
    (Fmod F K : Type u)
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K]
    [FiniteDimensional Fmod F]
    (clauseB : SourceInitialThetaClauseB l Fmod F) where
  representation :
    ThetaLTorsionRepresentationData l F K clauseB.curveModuli.xF
  imageContainsSL2 : representation.ImageContainsSL2
  badResidueCharacteristicsPrimeToL :
    ∀ w ∈ clauseB.badModuli.badMod,
      Nat.Coprime
        (ThetaFinitePlace.residueCharacteristic w) l.value
  fBadLocalCurves :
    ∀ v : NumberField.FinitePlace F,
      ThetaFinitePlace.comap v ∈ clauseB.badModuli.badMod ->
        PuncturedEllipticCurveScalarExtension F
          (ThetaFinitePlace.Completion v) clauseB.curveModuli.xF
  fBadQParameters :
    ∀ v (hv : ThetaFinitePlace.comap v ∈ clauseB.badModuli.badMod),
      ThetaTateParameterData v (fBadLocalCurves v hv).result
  fBadQParameterOrdersPrimeToL :
    ∀ v hv,
      Nat.Coprime (fBadQParameters v hv).order l.value

/--
Clause (d): the scalar-extended `K`-core and the global type
`(1,l-tors)^±` and theta-root covering diagrams.
-/
structure SourceInitialThetaClauseD
    (l : PrimeGeFive)
    (Fmod F K : Type u)
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K]
    [FiniteDimensional Fmod F]
    (clauseB : SourceInitialThetaClauseB l Fmod F) where
  kCore :
    SourceThetaKCoreData F K
      clauseB.curveModuli.xF clauseB.curveModuli.signQuotient
  globalLTorsionCover :
    GlobalLTorsionCoverInput l kCore.orbicurves
  globalLTorsionStack :
    TypeOneLTorsionStackRealization l globalLTorsionCover
  globalThetaRootStack :
    ThetaRootStackRealization l globalLTorsionCover

/--
Clause (f), global part: the nonzero cusp and its arrowed orbicurves.  The
localized cusp compatibility is carried by clause (e), because its types
depend on the selected local base changes.
-/
structure SourceInitialThetaClauseF
    (l : PrimeGeFive)
    (Fmod F K : Type u)
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K]
    [FiniteDimensional Fmod F]
    (clauseB : SourceInitialThetaClauseB l Fmod F)
    (clauseD : SourceInitialThetaClauseD l Fmod F K clauseB) where
  epsilon :
    TypeOneNonzeroCusp l
      clauseD.globalLTorsionCover clauseD.globalLTorsionStack
  arrowedEigenspaces :
    ArrowedCuspidalEigenspaceData l epsilon
  arrowedPositiveTopology :
    ArrowedPositiveProfiniteRealization l arrowedEigenspaces
  arrowedJQuotients :
    ArrowedJQuotientData l arrowedPositiveTopology
  globalArrowedStack :
    ArrowedTypeOneStackRealization l
      arrowedEigenspaces arrowedPositiveTopology arrowedJQuotients

/-- The valuation compatibility record canonically assembled from clauses (b), (c), and (e). -/
def sourceInitialThetaValuations
    {l : PrimeGeFive}
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [FiniteDimensional Fmod F]
    (clauseB : SourceInitialThetaClauseB l Fmod F)
    (clauseC : SourceInitialThetaClauseC l Fmod F K clauseB)
    (selection : SourceThetaSelectedPlaceData Fmod K) :
    ThetaValuationData l Fmod K :=
  selection.toValuations clauseB.badModuli
    clauseC.badResidueCharacteristicsPrimeToL

/--
Clause (e), together with the local portion of clause (f): the selected-place
section, actual local base changes and decomposition-group data, local
theta-root models, and compatible local cusps/arrows.
-/
structure SourceInitialThetaClauseE
    (l : PrimeGeFive)
    (Fmod F K : Type u)
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [FiniteDimensional Fmod F]
    (clauseB : SourceInitialThetaClauseB l Fmod F)
    (clauseC : SourceInitialThetaClauseC l Fmod F K clauseB)
    (clauseD : SourceInitialThetaClauseD l Fmod F K clauseB)
    (clauseF : SourceInitialThetaClauseF l Fmod F K clauseB clauseD) where
  selection : SourceThetaSelectedPlaceData Fmod K
  finiteLocalCores :
    ∀ v,
      SourceThetaFiniteLocalCoreData K
        clauseD.kCore.curveExtension.result
        clauseD.kCore.orbicurves v
  infiniteLocalCores :
    ∀ v,
      SourceThetaInfiniteLocalCoreData K
        clauseD.kCore.curveExtension.result
        clauseD.kCore.orbicurves v
  finiteLocalLTorsionCovers :
    ∀ v
      (_hv : v ∈
        (sourceInitialThetaValuations clauseB clauseC selection).selected),
      SourceThetaFiniteLTorsionCoverScalarExtension l
        (finiteLocalCores v)
        clauseD.globalLTorsionCover clauseD.globalLTorsionStack
  infiniteLocalLTorsionCovers :
    ∀ v
      (_hv : v ∈
        (sourceInitialThetaValuations clauseB clauseC selection).selectedInfinite),
      SourceThetaInfiniteLTorsionCoverScalarExtension l
        (infiniteLocalCores v)
        clauseD.globalLTorsionCover clauseD.globalLTorsionStack
  finiteLocalCuspidalAtlases :
    ∀ v
      (hv : v ∈
        (sourceInitialThetaValuations clauseB clauseC selection).selected),
      SourceThetaFiniteCuspidalAtlasScalarExtension l
        (finiteLocalLTorsionCovers v hv) clauseF.epsilon.atlas
  infiniteLocalCuspidalAtlases :
    ∀ v
      (hv : v ∈
        (sourceInitialThetaValuations clauseB clauseC selection).selectedInfinite),
      SourceThetaInfiniteCuspidalAtlasScalarExtension l
        (infiniteLocalLTorsionCovers v hv) clauseF.epsilon.atlas
  goodLocalArrowedEigenspaces :
    ∀ v
      (hv : v ∈
        (sourceInitialThetaValuations clauseB clauseC selection).good),
      SourceThetaGoodFiniteArrowedEigenspaceScalarExtension l
        (TypeOneCuspidalAtlasScalarExtension.toNonzeroCuspScalarExtension
          (finiteLocalCuspidalAtlases v hv.1))
        clauseF.arrowedEigenspaces clauseF.arrowedPositiveTopology
  goodLocalArrowedJQuotients :
    ∀ v
      (hv : v ∈
        (sourceInitialThetaValuations clauseB clauseC selection).good),
      SourceThetaGoodFiniteArrowedJScalarExtension l
        (goodLocalArrowedEigenspaces v hv) clauseF.arrowedJQuotients
  goodLocalArrowedStacks :
    ∀ v
      (hv : v ∈
        (sourceInitialThetaValuations clauseB clauseC selection).good),
      SourceThetaGoodFiniteArrowedStackScalarExtension l
        (goodLocalArrowedJQuotients v hv) clauseF.globalArrowedStack
  badLocalStandard :
    ∀ v
      (hv : v ∈
        (sourceInitialThetaValuations clauseB clauseC selection).bad),
      SourceThetaBadLocalStandardData l
        (finiteLocalCores v)
        (finiteLocalLTorsionCovers v hv.1)
        (TypeOneCuspidalAtlasScalarExtension.toNonzeroCuspScalarExtension
          (finiteLocalCuspidalAtlases v hv.1))
  badLocalThetaRootStacks :
    ∀ v
      (hv : v ∈
        (sourceInitialThetaValuations clauseB clauseC selection).bad),
      SourceThetaBadLocalThetaRootStackRealization l
        (finiteLocalCores v)
        (finiteLocalLTorsionCovers v hv.1)

/--
All six clauses of IUT I, Definition 3.1.  The prime `l` is declared first
because clauses (b)--(f) contain conditions depending on it, although the
paper introduces it textually in clause (c).
-/
structure SourceInitialThetaDefinition
    (Fmod F K : Type u)
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K] where
  l : PrimeGeFive
  clauseA : SourceInitialThetaClauseA F
  clauseB : SourceInitialThetaClauseB l Fmod F
  clauseC : SourceInitialThetaClauseC l Fmod F K clauseB
  clauseD : SourceInitialThetaClauseD l Fmod F K clauseB
  clauseF : SourceInitialThetaClauseF l Fmod F K clauseB clauseD
  clauseE : SourceInitialThetaClauseE l Fmod F K clauseB clauseC clauseD clauseF

namespace SourceInitialThetaDefinition

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]

/-- The explicit clause-by-clause constructor for Definition 3.1 data. -/
def ofClauses
    (l : PrimeGeFive)
    (clauseA : SourceInitialThetaClauseA F)
    (clauseB : SourceInitialThetaClauseB l Fmod F)
    (clauseC : SourceInitialThetaClauseC l Fmod F K clauseB)
    (clauseD : SourceInitialThetaClauseD l Fmod F K clauseB)
    (clauseF : SourceInitialThetaClauseF l Fmod F K clauseB clauseD)
    (clauseE :
      SourceInitialThetaClauseE l Fmod F K
        clauseB clauseC clauseD clauseF) :
    SourceInitialThetaDefinition Fmod F K where
  l := l
  clauseA := clauseA
  clauseB := clauseB
  clauseC := clauseC
  clauseD := clauseD
  clauseF := clauseF
  clauseE := clauseE

/-- The field-tower compatibility record is derived, never independently supplied. -/
def fieldTower
    (data : SourceInitialThetaDefinition Fmod F K) :
    ThetaFieldTower data.l Fmod F K where
  sqrtMinusOne := data.clauseA.sqrtMinusOne
  degreePrimeToL_holds := data.clauseB.degreePrimeToL

/-- The selected valuation package is derived, never independently supplied. -/
def valuations
    (data : SourceInitialThetaDefinition Fmod F K) :
    ThetaValuationData data.l Fmod K :=
  sourceInitialThetaValuations
    data.clauseB data.clauseC data.clauseE.selection

/--
The canonical initial-theta core constructed clause by clause from Definition
3.1.  Every projection is either a source hypothesis at its exact boundary or
is derived by `fieldTower`/`valuations` above.
-/
def toCore
    (data : SourceInitialThetaDefinition Fmod F K) :
    SourceInitialThetaCore Fmod F K where
  l := data.l
  fieldTower := data.fieldTower
  curveModuli := data.clauseB.curveModuli
  kCore := data.clauseD.kCore
  globalLTorsionCover := data.clauseD.globalLTorsionCover
  globalLTorsionStack := data.clauseD.globalLTorsionStack
  epsilon := data.clauseF.epsilon
  arrowedEigenspaces := data.clauseF.arrowedEigenspaces
  arrowedPositiveTopology := data.clauseF.arrowedPositiveTopology
  arrowedJQuotients := data.clauseF.arrowedJQuotients
  globalArrowedStack := data.clauseF.globalArrowedStack
  globalThetaRootStack := data.clauseD.globalThetaRootStack
  lTorsionRepresentation := data.clauseC.representation
  lTorsionImageContainsSL2 := data.clauseC.imageContainsSL2
  valuations := data.valuations
  finiteLocalCores := data.clauseE.finiteLocalCores
  infiniteLocalCores := data.clauseE.infiniteLocalCores
  finiteLocalLTorsionCovers := data.clauseE.finiteLocalLTorsionCovers
  infiniteLocalLTorsionCovers := data.clauseE.infiniteLocalLTorsionCovers
  finiteLocalCuspidalAtlases := data.clauseE.finiteLocalCuspidalAtlases
  infiniteLocalCuspidalAtlases := data.clauseE.infiniteLocalCuspidalAtlases
  goodLocalArrowedEigenspaces := data.clauseE.goodLocalArrowedEigenspaces
  goodLocalArrowedJQuotients := data.clauseE.goodLocalArrowedJQuotients
  goodLocalArrowedStacks := data.clauseE.goodLocalArrowedStacks
  badLocalStandard := data.clauseE.badLocalStandard
  badLocalThetaRootStacks := data.clauseE.badLocalThetaRootStacks
  fPlacesOverBadHaveMultiplicativeReduction :=
    data.clauseB.fPlacesOverBadHaveMultiplicativeReduction
  fBadLocalCurves := data.clauseC.fBadLocalCurves
  fBadQParameters := data.clauseC.fBadQParameters
  fBadQParameterOrdersPrimeToL :=
    data.clauseC.fBadQParameterOrdersPrimeToL

@[simp]
theorem toCore_l
    (data : SourceInitialThetaDefinition Fmod F K) :
    data.toCore.l = data.l :=
  rfl

@[simp]
theorem toCore_curveModuli
    (data : SourceInitialThetaDefinition Fmod F K) :
    data.toCore.curveModuli = data.clauseB.curveModuli :=
  rfl

@[simp]
theorem toCore_badMod
    (data : SourceInitialThetaDefinition Fmod F K) :
    data.toCore.valuations.badMod = data.clauseB.badModuli.badMod :=
  rfl

@[simp]
theorem toCore_chosenLift
    (data : SourceInitialThetaDefinition Fmod F K) :
    data.toCore.valuations.chosenLift = data.clauseE.selection.finiteLift :=
  rfl

theorem toCore_kernelField
    (data : SourceInitialThetaDefinition Fmod F K) :
    data.toCore.lTorsionRepresentation.IsKernelField :=
  data.clauseC.representation.isKernelField

end SourceInitialThetaDefinition

/-- The two arithmetic histories attached to one source-native initial-theta datum. -/
inductive SourceThetaArithmeticHistory
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : SourceInitialThetaCore Fmod F K) where
  | zero
  | one
  deriving DecidableEq

namespace SourceThetaArithmeticHistory

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : SourceInitialThetaCore Fmod F K}

theorem zero_ne_one :
    (SourceThetaArithmeticHistory.zero :
      SourceThetaArithmeticHistory theta) ≠ .one := by
  intro h
  cases h

end SourceThetaArithmeticHistory

end


end Iut
