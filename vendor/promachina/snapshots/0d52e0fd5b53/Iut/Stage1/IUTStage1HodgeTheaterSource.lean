/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.QualitativeData
import Iut.Foundations.ThetaHodgeTheater

/-!
Legacy projection from the typed IUT I Hodge-theater source into the current
Stage 1 qualitative bookkeeping types.

These definitions are migration adapters only. New source constructors should
take `Stage1HodgeTheaterSource` and compute these values, rather than accepting
`String`, `HodgeTheaterId`, or `PrimeStripId` arguments.
-/

namespace Iut

universe u

namespace Stage1HodgeTheaterSource

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

private def legacyBaseLabel (source : Stage1HodgeTheaterSource theta) : String :=
  source.inputPrimeStrip.globalOrbicurve.label

/-- Temporary projection of the typed `0`-column theater. -/
def legacyZeroColumnHodgeTheater
    (source : Stage1HodgeTheaterSource theta) :
    RealLineCopy.QualitativeData.HodgeTheaterId :=
  { side := .domain,
    label := legacyBaseLabel source ++ "|theta-pm-ell-nf:column-0" }

/-- Temporary projection of the typed `1`-column theater. -/
def legacyOneColumnHodgeTheater
    (source : Stage1HodgeTheaterSource theta) :
    RealLineCopy.QualitativeData.HodgeTheaterId :=
  { side := .codomain,
    label := legacyBaseLabel source ++ "|theta-pm-ell-nf:column-1" }

/-- Temporary string projection of the typed `0`-column history. -/
def legacyZeroColumnHistoryLabel
    (source : Stage1HodgeTheaterSource theta) : String :=
  legacyBaseLabel source ++ "|arithmetic-history:column-0"

/-- Temporary string projection of the typed `1`-column history. -/
def legacyOneColumnHistoryLabel
    (source : Stage1HodgeTheaterSource theta) : String :=
  legacyBaseLabel source ++ "|arithmetic-history:column-1"

/-- Temporary projection of the typed input prime strip. -/
def legacyInputPrimeStrip
    (source : Stage1HodgeTheaterSource theta) :
    RealLineCopy.QualitativeData.PrimeStripId :=
  { label := source.inputPrimeStrip.globalOrbicurve.label ++
      "|prime-strip:column-0:plus-minus" }

/-- Temporary projection of the typed output prime strip. -/
def legacyOutputPrimeStrip
    (source : Stage1HodgeTheaterSource theta) :
    RealLineCopy.QualitativeData.PrimeStripId :=
  { label := source.outputPrimeStrip.globalOrbicurve.label ++
      "|prime-strip:column-1:theta" }

@[simp]
theorem legacyZeroColumnHodgeTheater_side
    (source : Stage1HodgeTheaterSource theta) :
    source.legacyZeroColumnHodgeTheater.side = .domain :=
  rfl

@[simp]
theorem legacyOneColumnHodgeTheater_side
    (source : Stage1HodgeTheaterSource theta) :
    source.legacyOneColumnHodgeTheater.side = .codomain :=
  rfl

theorem legacyHistories_not_identified
    (source : Stage1HodgeTheaterSource theta) :
    source.legacyZeroColumnHodgeTheater.side ≠
      source.legacyOneColumnHodgeTheater.side := by
  simp

end Stage1HodgeTheaterSource

end Iut
