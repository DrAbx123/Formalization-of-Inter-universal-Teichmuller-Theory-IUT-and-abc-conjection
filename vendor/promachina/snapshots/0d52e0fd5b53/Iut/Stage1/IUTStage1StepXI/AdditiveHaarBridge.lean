/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1StepXI
import Iut.Stage1.IUTStage1Experiments.AdditiveHaar

/-!
Bridge from the additive-Haar/Theorem 1.10 formula-matching tower to the
canonical Step (xi) p-adic arithmetic-degree boundary.

`IUTStage1Experiments.AdditiveHaar` sits below the Step (xi) core in the import
graph, so the projections from its source-backed formula-matching records to
the canonical Step (xi) records live here.
-/

namespace Iut
namespace Stage1
namespace Experiments

open RealLineCopy
open scoped BigOperators
open scoped NormedField
open scoped Valued

universe u v w x y z

namespace IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource

variable {ι : Type u} [Fintype ι]
variable {localPrime : ι -> Nat}
variable [∀ place : ι, Fact (Nat.Prime (localPrime place))]
variable {localField : ι -> Type v}
variable [(place : ι) -> NontriviallyNormedField (localField place)]
variable [∀ place : ι, ProperSpace (localField place)]
variable [∀ place : ι, IsUltrametricDist (localField place)]
variable [(place : ι) -> MeasurableSpace (localField place)]
variable [∀ place : ι, BorelSpace (localField place)]
variable [∀ place : ι, LocallyCompactSpace (localField place)]
variable [∀ place : ι, IsTopologicalAddGroup (localField place)]
variable [(place : ι) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : ι,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {α : Type w}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}

set_option linter.style.longLine false in
/--
Project the experiment-layer p-adic Haar-index source to the canonical
Step~(xi) p-adic Haar-index source.
-/
noncomputable def toCorePadicUnitBallHaarIndexDefectSource
    (source :
      IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource
        ι localPrime localField α hullSystem) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource
      ι localPrime localField α hullSystem :=
  { unitBallHaarSource := source.unitBallHaarSource,
    normalizedPlace := source.normalizedPlace }

theorem localHaarNormalizationDefect_eq_core
    (source :
      IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource
        ι localPrime localField α hullSystem)
    (place : ι) :
    source.localHaarNormalizationDefect place =
      source.toCorePadicUnitBallHaarIndexDefectSource.localHaarNormalizationDefect
        place := by
  rfl

theorem toCorePadicUnitBallHaarIndexDefectSource_endpoint
    (source :
      IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource
        ι localPrime localField α hullSystem) :
    source.toCorePadicUnitBallHaarIndexDefectSource.Endpoint :=
  source.toCorePadicUnitBallHaarIndexDefectSource.endpoint

end IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource

namespace IUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource

variable {β : Type v} [Fintype β]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project additive-Haar formula matching to the canonical p-adic
Step~(xi) arithmetic formula matching source.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (source.theorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      source.localizedStepXISource :=
  { padicUnitBallHaarDefectSource :=
      source.iutIVArithmeticDefectSource.padicHaarDefectSource
        |>.toCorePadicUnitBallHaarIndexDefectSource,
    localStepXI_eq_arithmeticDegreePart :=
      source.localStepXI_eq_arithmeticDegreePart,
    localPrimeErrorContribution_eq_padicIndex_main := by
      intro place
      have hprime :=
        source.localPrimeErrorContribution_eq_iutIVDefect_main place
      have hdefect :=
        source.iutIVArithmeticDefectSource.localIUTIVArithmeticDefect_eq_padicHaarIndex place
      have hcore :=
        source.iutIVArithmeticDefectSource.padicHaarDefectSource
          |>.localHaarNormalizationDefect_eq_core place
      rw [hprime, hdefect, hcore] }

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

set_option linter.style.longLine false in
/--
Project additive-Haar formula matching directly to the canonical local
arithmetic-degree residual package.

This composes the source-backed p-adic unit-ball Haar-index formula equalities
with the core residual constructor, so callers do not have to expose the
intermediate synchronization record.
-/
noncomputable def toCoreLocalArithmeticDegreeResidualSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource
    |>.toLocalArithmeticDegreeResidualSource

theorem toCoreLocalArithmeticDegreeResidualSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  source.toCoreLocalArithmeticDegreeResidualSource.endpoint

end IUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource

namespace IUTStage1AdditiveHaarTheorem110StepXIPadicPrimeErrorFormulaMatchingSource

variable {β : Type v} [Fintype β]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project the stricter p-adic prime-error formula-matching source to the
canonical Step~(xi) p-adic arithmetic formula source.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIPadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (source.primeErrorPadicDefectMainSource.theorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      source.localizedStepXISource :=
  source.toIUTStage1AdditiveHaarTheorem110StepXIArithmeticFormulaMatchingSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIPadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

set_option linter.style.longLine false in
/--
Project the p-adic prime-error split source directly to the canonical residual
package by reconstructing the p-adic arithmetic formula-matching record first.
-/
noncomputable def toCoreLocalArithmeticDegreeResidualSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIPadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource
    |>.toLocalArithmeticDegreeResidualSource

theorem toCoreLocalArithmeticDegreeResidualSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIPadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  source.toCoreLocalArithmeticDegreeResidualSource.endpoint

end IUTStage1AdditiveHaarTheorem110StepXIPadicPrimeErrorFormulaMatchingSource

namespace IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreePadicPrimeErrorFormulaMatchingSource

variable {β : Type v} [Fintype β]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project the fully split additive-Haar formula source to the canonical p-adic
Step~(xi) arithmetic formula source.

Here the Step~(xi) arithmetic-degree equality is no longer primitive: it is
derived inside `arithmeticDegreeCalibrationSource` from local determinant
weights and adjusted raw log-volumes.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (source.primeErrorPadicDefectMainSource.theorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      source.arithmeticDegreeCalibrationSource.localizedStepXISource :=
  source.toIUTStage1AdditiveHaarTheorem110StepXIPadicPrimeErrorFormulaMatchingSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

set_option linter.style.longLine false in
/--
Project the fully split additive-Haar arithmetic-degree/p-adic source directly
to the canonical residual package.
-/
noncomputable def toCoreLocalArithmeticDegreeResidualSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource
    |>.toLocalArithmeticDegreeResidualSource

theorem toCoreLocalArithmeticDegreeResidualSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  source.toCoreLocalArithmeticDegreeResidualSource.endpoint

end IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreePadicPrimeErrorFormulaMatchingSource

set_option linter.style.longLine false

namespace IUTStage1AdditiveHaarTheorem110StepXIConstructedPrimeErrorArithmeticDegreeFormulaMatchingSource

variable {β : Type v} [Fintype β]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project the arithmetic-degree formula source with constructed prime-error
split to the canonical p-adic Step~(xi) arithmetic formula source.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIConstructedPrimeErrorArithmeticDegreeFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (source.constructedPrimeErrorSource.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      source.arithmeticDegreeCalibrationSource.localizedStepXISource :=
  source.toArithmeticDegreePadicPrimeErrorFormulaMatchingSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIConstructedPrimeErrorArithmeticDegreeFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

set_option linter.style.longLine false in
/--
Project the constructed prime-error arithmetic-degree formula source directly
to the canonical local arithmetic-degree residual package.
-/
noncomputable def toCoreLocalArithmeticDegreeResidualSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIConstructedPrimeErrorArithmeticDegreeFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource
    |>.toLocalArithmeticDegreeResidualSource

theorem toCoreLocalArithmeticDegreeResidualSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIConstructedPrimeErrorArithmeticDegreeFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  source.toCoreLocalArithmeticDegreeResidualSource.endpoint

end IUTStage1AdditiveHaarTheorem110StepXIConstructedPrimeErrorArithmeticDegreeFormulaMatchingSource

set_option linter.style.longLine false

namespace IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource

variable {β : Type v} [Fintype β]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project the formula-gap matched, arithmetic-degree calibrated p-adic source to
the canonical p-adic Step~(xi) arithmetic formula source.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (source.toArithmeticFormulaMatchingSource.theorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      source.arithmeticDegreeCalibrationSource.localizedStepXISource :=
  source.toArithmeticFormulaMatchingSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

set_option linter.style.longLine false in
/--
Project the formula-gap matched additive-Haar arithmetic-degree/p-adic source
directly to the canonical local arithmetic-degree residual package.
-/
noncomputable def toCoreLocalArithmeticDegreeResidualSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource
    |>.toLocalArithmeticDegreeResidualSource

theorem toCoreLocalArithmeticDegreeResidualSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  source.toCoreLocalArithmeticDegreeResidualSource.endpoint

end IUTStage1AdditiveHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource

namespace IUTStage1AdditiveHaarTheorem110StepXIMatchedLocalDegreeArithmeticDivisorBackedComponentSource

variable {β : Type v} [Fintype β]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project the arithmetic-divisor-backed local-degree source to the canonical
p-adic Step~(xi) arithmetic formula source.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIMatchedLocalDegreeArithmeticDivisorBackedComponentSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (source.formulaGapMatchedArithmeticDegreePadicFormulaMatchingSource.toArithmeticFormulaMatchingSource.theorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      source.formulaGapMatchedArithmeticDegreePadicFormulaMatchingSource.arithmeticDegreeCalibrationSource.localizedStepXISource :=
  source.formulaGapMatchedArithmeticDegreePadicFormulaMatchingSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIMatchedLocalDegreeArithmeticDivisorBackedComponentSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

set_option linter.style.longLine false in
/--
Project the arithmetic-divisor-backed local-degree component source directly
to the canonical local arithmetic-degree residual package.
-/
noncomputable def toCoreLocalArithmeticDegreeResidualSource
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIMatchedLocalDegreeArithmeticDivisorBackedComponentSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource
    |>.toLocalArithmeticDegreeResidualSource

theorem toCoreLocalArithmeticDegreeResidualSource_endpoint
    (source :
      IUTStage1AdditiveHaarTheorem110StepXIMatchedLocalDegreeArithmeticDivisorBackedComponentSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  source.toCoreLocalArithmeticDegreeResidualSource.endpoint

end IUTStage1AdditiveHaarTheorem110StepXIMatchedLocalDegreeArithmeticDivisorBackedComponentSource

namespace ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]
variable {sourceData :
  IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
    (β := β) record}
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {l : PrimeGeFive}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project the constructed Theorem~3.11/IUT~IV local-term source to the canonical
p-adic Step~(xi) arithmetic formula source.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (constructedSource :
      ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource
        sourceData estimate l η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (constructedSource.matchedLocalDegreeArithmeticDivisorBackedComponentSource.formulaGapMatchedArithmeticDegreePadicFormulaMatchingSource.toArithmeticFormulaMatchingSource.theorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      constructedSource.matchedLocalDegreeArithmeticDivisorBackedComponentSource.formulaGapMatchedArithmeticDegreePadicFormulaMatchingSource.arithmeticDegreeCalibrationSource.localizedStepXISource :=
  constructedSource.matchedLocalDegreeArithmeticDivisorBackedComponentSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (constructedSource :
      ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource
        sourceData estimate l η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    constructedSource.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  constructedSource.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

set_option linter.style.longLine false in
/--
Project the constructed Theorem~3.11/IUT~IV local-term source directly to the
canonical local arithmetic-degree residual package.
-/
noncomputable def toCoreLocalArithmeticDegreeResidualSource
    (constructedSource :
      ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource
        sourceData estimate l η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :=
  constructedSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
    |>.toLocalArithmeticDegreeResidualSource

theorem toCoreLocalArithmeticDegreeResidualSource_endpoint
    (constructedSource :
      ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource
        sourceData estimate l η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    constructedSource.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  constructedSource.toCoreLocalArithmeticDegreeResidualSource.endpoint

end ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource

namespace IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource

variable {β : Type v} [Fintype β]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [∀ place : β, T2Space (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project the valuation-ball formula-gap matched arithmetic-degree/p-adic source
to the canonical p-adic Step~(xi) arithmetic formula source.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (source.toArithmeticFormulaMatchingSource.theorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      source.arithmeticDegreeCalibrationSource.localizedStepXISource :=
  source.toArithmeticFormulaMatchingSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

set_option linter.style.longLine false in
/--
Project the valuation-ball formula-gap matched arithmetic-degree/p-adic source
directly to the canonical local arithmetic-degree residual package.
-/
noncomputable def toCoreLocalArithmeticDegreeResidualSource
    (source :
      IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource
    |>.toLocalArithmeticDegreeResidualSource

theorem toCoreLocalArithmeticDegreeResidualSource_endpoint
    (source :
      IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  source.toCoreLocalArithmeticDegreeResidualSource.endpoint

end IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource

set_option linter.style.longLine true

namespace IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource

variable {β : Type v} [Fintype β]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [∀ place : β, T2Space (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project the valuation-ball arithmetic-degree controlled source to the
canonical p-adic Step~(xi) arithmetic formula matching source.
-/
noncomputable def toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    _root_.Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreePadicUnitBallArithmeticFormulaMatchingSource
      (localPrime := localPrime) (localField := localField)
      (α := αHaar) (hullSystem := hullSystem)
      (source.theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.toThetaPilotArithmeticDivisorLocalEvaluationSource)
      source.arithmeticDegreeCalibrationSource.localizedStepXISource :=
  source.toAdditiveHaarArithmeticFormulaMatchingSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

set_option linter.style.longLine false in
theorem toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

set_option linter.style.longLine false in
/--
Project the valuation-ball arithmetic-degree controlled source directly to the
canonical local arithmetic-degree residual package.

This is the lowest currently source-backed bridge into the canonical residual
consumer: the Step~(xi) arithmetic equality, prime-error/p-adic-index split,
and p-adic Haar lower bound are all reconstructed before entering the core
residual source.
-/
noncomputable def toCoreLocalArithmeticDegreeResidualSource
    (source :
      IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource
    |>.toLocalArithmeticDegreeResidualSource

theorem toCoreLocalArithmeticDegreeResidualSource_endpoint
    (source :
      IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand) :
    source.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  source.toCoreLocalArithmeticDegreeResidualSource.endpoint

end IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource

set_option linter.style.longLine false

namespace ConstructedTheorem311OneSidedIUTIVTheorem110ValuationBallHaarArithmeticDivisorBackedMatchedLocalDegreeComponentStepXILocalTermCThetaSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {recordAdjustedSource :
  IUTStage1SourcePackage.IUTStage1Remark395RecordOb3Ob5AdjustedDeterminantLogVolumeSource
    (β := β) (γ := γ) record}
variable {sourceData :
  IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
    (β := β) record}
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {l : PrimeGeFive}
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [∀ place : β, T2Space (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project a Record-Ob3/Ob5 valuation-ball local-estimate source directly to the
canonical local arithmetic-degree residual package.

The experiment layer already reconstructs the arithmetic-degree-controlled
local arithmetic source from the Record-Ob3/Ob5 valuation-ball data.  This
bridge composes that construction with the core residual projection, so the
canonical residual consumer can cite the Record-Ob3/Ob5 source itself.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedValuationBallSource.toCoreLocalArithmeticDegreeResidualSource
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedValuationBallSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :=
  source.toArithmeticDegreeControlledLocalArithmeticSource
    |>.toCoreLocalArithmeticDegreeResidualSource

theorem RecordOb3Ob5ArithmeticDivisorBackedValuationBallSource.toCoreLocalArithmeticDegreeResidualSource_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedValuationBallSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    source.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  source.toCoreLocalArithmeticDegreeResidualSource.endpoint

set_option linter.style.longLine false in
/--
Project a Record-Ob3/Ob5 valuation-ball local-estimate source directly to the
case-local Theorem~1.10 arithmetic-degree bound source.

This is the bound counterpart of the residual projection above: the lower
Record-Ob3/Ob5 source reconstructs the arithmetic-degree-controlled local
arithmetic source, whose Step~(v), Step~(vi), and Step~(vii) inequalities give
the canonical case-local bound package.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedValuationBallSource.toCoreCaseLocalArithmeticDegreeBoundSource
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedValuationBallSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :=
  source.toArithmeticDegreeControlledLocalArithmeticSource
    |>.toCoreCaseLocalArithmeticDegreeBoundSource

theorem RecordOb3Ob5ArithmeticDivisorBackedValuationBallSource.toCoreCaseLocalArithmeticDegreeBoundSource_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedValuationBallSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    source.toCoreCaseLocalArithmeticDegreeBoundSource.Endpoint :=
  source.toCoreCaseLocalArithmeticDegreeBoundSource.endpoint

end ConstructedTheorem311OneSidedIUTIVTheorem110ValuationBallHaarArithmeticDivisorBackedMatchedLocalDegreeComponentStepXILocalTermCThetaSource

namespace ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource

variable {source target : Copy} {index : Type u}
variable {package : IUTStage1SourcePackage source target index}
variable {record : IUTStage1Theorem311MultiradialSourceRecord package}
variable {β : Type v} [Fintype β]
variable {η : Type y} {γ : Type w} [Fintype γ]
variable {recordAdjustedSource :
  IUTStage1SourcePackage.IUTStage1Remark395RecordOb3Ob5AdjustedDeterminantLogVolumeSource
    (β := β) (γ := γ) record}
variable {sourceData :
  IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
    (β := β) record}
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {l : PrimeGeFive}
variable {localPrime : β -> Nat}
variable [∀ place : β, Fact (Nat.Prime (localPrime place))]
variable {localField : β -> Type x}
variable [(place : β) -> NontriviallyNormedField (localField place)]
variable [∀ place : β, ProperSpace (localField place)]
variable [∀ place : β, IsUltrametricDist (localField place)]
variable [(place : β) -> MeasurableSpace (localField place)]
variable [∀ place : β, BorelSpace (localField place)]
variable [∀ place : β, LocallyCompactSpace (localField place)]
variable [∀ place : β, IsTopologicalAddGroup (localField place)]
variable [∀ place : β, T2Space (localField place)]
variable [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
variable [∀ place : β,
  FiniteDimensional ℚ_[localPrime place] (localField place)]
variable {αHaar : Type z}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
variable {αLocal : Type z} {ηLocal : Type y}
variable {localAnalyticHullSystem :
  IUTStage1Remark395HolomorphicHullSystem αLocal}
variable {archIndex archSummand : β -> Type z}
variable [∀ place : β, Fintype (archIndex place)]
variable [∀ place : β, Fintype (archSummand place)]

set_option linter.style.longLine false in
/--
Project a Record-Ob3/Ob5 component source directly to the canonical residual
package after supplying its valuation-ball formula provenance.

This keeps the genuine source obligation visible: the component source must be
identified with the valuation-ball formula-matching core before it can feed the
valuation-ball residual route.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedComponentSource.toCoreLocalArithmeticDegreeResidualSource
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand)
    (valuationBallFormulaGapMatchedArithmeticDegreePadicFormulaMatchingSource :
      IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand)
    (componentFormulaMatching_eq_valuationBall :
      source.matchedLocalDegreeArithmeticDivisorBackedComponentSource.formulaGapMatchedArithmeticDegreePadicFormulaMatchingSource =
        valuationBallFormulaGapMatchedArithmeticDegreePadicFormulaMatchingSource.toAdditiveHaarFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource) :=
  (source.toRecordOb3Ob5ArithmeticDivisorBackedValuationBallSource
      valuationBallFormulaGapMatchedArithmeticDegreePadicFormulaMatchingSource
      componentFormulaMatching_eq_valuationBall)
    |>.toCoreLocalArithmeticDegreeResidualSource

theorem RecordOb3Ob5ArithmeticDivisorBackedComponentSource.toCoreLocalArithmeticDegreeResidualSource_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand)
    (valuationBallFormulaGapMatchedArithmeticDegreePadicFormulaMatchingSource :
      IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand)
    (componentFormulaMatching_eq_valuationBall :
      source.matchedLocalDegreeArithmeticDivisorBackedComponentSource.formulaGapMatchedArithmeticDegreePadicFormulaMatchingSource =
        valuationBallFormulaGapMatchedArithmeticDegreePadicFormulaMatchingSource.toAdditiveHaarFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource) :
    (source.toCoreLocalArithmeticDegreeResidualSource
      valuationBallFormulaGapMatchedArithmeticDegreePadicFormulaMatchingSource
      componentFormulaMatching_eq_valuationBall).Endpoint :=
  (source.toCoreLocalArithmeticDegreeResidualSource
    valuationBallFormulaGapMatchedArithmeticDegreePadicFormulaMatchingSource
    componentFormulaMatching_eq_valuationBall).endpoint

set_option linter.style.longLine false in
/--
Project a Record-Ob3/Ob5 component source to the canonical residual package
from the lower arithmetic-degree-controlled local arithmetic source.

Compared with `toCoreLocalArithmeticDegreeResidualSource`, this constructor no
longer asks for the valuation-ball formula-gap source as a separate argument:
it is reconstructed internally from the arithmetic-degree-controlled local
arithmetic source before the valuation-ball Record-Ob3/Ob5 residual projection
is applied.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedComponentSource.toCoreLocalArithmeticDegreeResidualSourceOfArithmeticDegreeControlledLocalArithmeticSource
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand)
    (localArithmeticSource :
      IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand)
    (arithmeticDivisorBackedComponent_eq_controlledFormulaMatching :
      source.matchedLocalDegreeArithmeticDivisorBackedComponentSource.formulaGapMatchedArithmeticDegreePadicFormulaMatchingSource =
        (IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.ofArithmeticDegreeControlledLocalArithmeticSource
          localArithmeticSource).toAdditiveHaarFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource) :=
  (source.toRecordOb3Ob5ArithmeticDivisorBackedValuationBallSourceOfArithmeticDegreeControlledLocalArithmeticSource
      localArithmeticSource
      arithmeticDivisorBackedComponent_eq_controlledFormulaMatching)
    |>.toCoreLocalArithmeticDegreeResidualSource

theorem RecordOb3Ob5ArithmeticDivisorBackedComponentSource.toCoreLocalArithmeticDegreeResidualSourceOfArithmeticDegreeControlledLocalArithmeticSource_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand)
    (localArithmeticSource :
      IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand)
    (arithmeticDivisorBackedComponent_eq_controlledFormulaMatching :
      source.matchedLocalDegreeArithmeticDivisorBackedComponentSource.formulaGapMatchedArithmeticDegreePadicFormulaMatchingSource =
        (IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.ofArithmeticDegreeControlledLocalArithmeticSource
          localArithmeticSource).toAdditiveHaarFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource) :
    (source.toCoreLocalArithmeticDegreeResidualSourceOfArithmeticDegreeControlledLocalArithmeticSource
      localArithmeticSource
      arithmeticDivisorBackedComponent_eq_controlledFormulaMatching).Endpoint :=
  (source.toCoreLocalArithmeticDegreeResidualSourceOfArithmeticDegreeControlledLocalArithmeticSource
    localArithmeticSource
    arithmeticDivisorBackedComponent_eq_controlledFormulaMatching).endpoint

set_option linter.style.longLine false in
/--
Project the local-degree-formula valuation-ball Record-Ob3/Ob5 source to the
canonical residual package.

The source already contains the formula-matched p-adic/arithmetic-degree data,
the Step~(v)/(vii) local-degree formula source, and the controlled
Record-Ob3/Ob5 component indexed by the constructed arithmetic-degree local
source.  This wrapper therefore removes the local-degree formula package and
matching equality from the residual consumer surface.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedLocalDegreeFormulaValuationBallControlledComponentSource.toCoreLocalArithmeticDegreeResidualSource
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedLocalDegreeFormulaValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :=
  source.controlledComponentSource.toRecordOb3Ob5ArithmeticDivisorBackedComponentSource
    |>.toCoreLocalArithmeticDegreeResidualSourceOfArithmeticDegreeControlledLocalArithmeticSource
      source.toArithmeticDegreeControlledLocalArithmeticSource
      source.controlledComponentSource.matchedFormula_eq_controlled

theorem RecordOb3Ob5ArithmeticDivisorBackedLocalDegreeFormulaValuationBallControlledComponentSource.toCoreLocalArithmeticDegreeResidualSource_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedLocalDegreeFormulaValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    source.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  source.toCoreLocalArithmeticDegreeResidualSource.endpoint

set_option linter.style.longLine false in
/--
Project the local-degree-formula valuation-ball Record-Ob3/Ob5 source to the
case-local Theorem~1.10 arithmetic-degree bound source.

The local-degree-formula source already reconstructs the same arithmetic-degree
controlled local source used by the residual route, so the pointwise Step~(v),
Step~(vi), and Step~(vii) bound package is obtained without exposing the
formula comparison layer to downstream consumers.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedLocalDegreeFormulaValuationBallControlledComponentSource.toCoreCaseLocalArithmeticDegreeBoundSource
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedLocalDegreeFormulaValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :=
  source.toArithmeticDegreeControlledLocalArithmeticSource
    |>.toCoreCaseLocalArithmeticDegreeBoundSource

theorem RecordOb3Ob5ArithmeticDivisorBackedLocalDegreeFormulaValuationBallControlledComponentSource.toCoreCaseLocalArithmeticDegreeBoundSource_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedLocalDegreeFormulaValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    source.toCoreCaseLocalArithmeticDegreeBoundSource.Endpoint :=
  source.toCoreCaseLocalArithmeticDegreeBoundSource.endpoint

set_option linter.style.longLine false in
/--
Project a controlled Record-Ob3/Ob5 component source to the canonical residual
package through the local-degree formula valuation-ball comparison lowering.

This removes the local-degree formula comparison source as a separate residual
surface when the source has already been synchronized at the controlled
component layer.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedControlledComponentSource.toCoreLocalArithmeticDegreeResidualSource
    {localArithmeticSource :
      IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand}
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand localArithmeticSource) :=
  source.toLocalDegreeFormulaValuationBallControlledComponentSource
    |>.toCoreLocalArithmeticDegreeResidualSource

theorem RecordOb3Ob5ArithmeticDivisorBackedControlledComponentSource.toCoreLocalArithmeticDegreeResidualSource_endpoint
    {localArithmeticSource :
      IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand}
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand localArithmeticSource) :
    source.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  source.toCoreLocalArithmeticDegreeResidualSource.endpoint

set_option linter.style.longLine false in
/--
Project a controlled Record-Ob3/Ob5 component source to the case-local
Theorem~1.10 arithmetic-degree bound source through the local-degree formula
valuation-ball comparison lowering.

This is the pointwise-bound analogue of
`toCoreLocalArithmeticDegreeResidualSource`: the controlled component source
first rebuilds the local-degree-formula valuation-ball source and then uses its
arithmetic-degree-controlled local source projection.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedControlledComponentSource.toCoreCaseLocalArithmeticDegreeBoundSource
    {localArithmeticSource :
      IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand}
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand localArithmeticSource) :=
  source.toLocalDegreeFormulaValuationBallControlledComponentSource
    |>.toCoreCaseLocalArithmeticDegreeBoundSource

theorem RecordOb3Ob5ArithmeticDivisorBackedControlledComponentSource.toCoreCaseLocalArithmeticDegreeBoundSource_endpoint
    {localArithmeticSource :
      IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource
        β estimate η γ localPrime localField αHaar hullSystem
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand}
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand localArithmeticSource) :
    source.toCoreCaseLocalArithmeticDegreeBoundSource.Endpoint :=
  source.toCoreCaseLocalArithmeticDegreeBoundSource.endpoint

set_option linter.style.longLine false in
/--
Project a Record-Ob3/Ob5 component source to the canonical p-adic arithmetic
formula-matching package directly from the p-adic unit-ball Haar-index local
estimate data.

This exposes the lower formula layer used by
`toCoreLocalArithmeticDegreeResidualSourceOfPadicUnitBallHaarIndex`: the
arithmetic-degree-controlled local arithmetic source and the valuation-ball
formula-gap package are reconstructed internally before projecting to the
canonical equalities
`StepXI_v = a_v(D_v+C_v)` and `E_v = delta_v + M_v`.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedComponentSource.toCorePadicUnitBallArithmeticFormulaMatchingSourceOfPadicUnitBallHaarIndex
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand)
    (theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        β estimate αLocal ηLocal localField localAnalyticHullSystem
        archIndex archSummand)
    (padicHaarDefectSource :
      IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource
        β localPrime localField αHaar hullSystem)
    (arithmeticDegreeCalibrationSource :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreeCalibrationSource
        β estimate η γ localField
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand
        theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource)
    (localPrimeErrorContribution_eq_padicHaarDefect_main :
      ∀ place : β,
        (theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
            |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
            |>.toThetaPilotArithmeticDivisorLocalEvaluationSource).localPrimeErrorContribution place =
          padicHaarDefectSource.localHaarNormalizationDefect place +
            (theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
              |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
              |>.toThetaPilotArithmeticDivisorLocalEvaluationSource).localMainLogContribution place)
    (distinguishedProcessionBound_le_arithmeticDegreePart :
      ∀ place : β,
        theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind place =
            IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
          theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.distinguishedProcessionBound place <=
            (let arithmeticSource :=
              theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toThetaPilotArithmeticDivisorLocalEvaluationSource;
            arithmeticSource.arithmeticDegreeCoefficient *
              (arithmeticSource.localDifferentDegree place +
                arithmeticSource.localConductorDegree place)))
    (archimedeanProcessionBound_le_arithmeticDegreePart :
      ∀ place : β,
        theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind place =
            IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
          theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.archimedeanProcessionBound place <=
            (let arithmeticSource :=
              theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toThetaPilotArithmeticDivisorLocalEvaluationSource;
            arithmeticSource.arithmeticDegreeCoefficient *
              (arithmeticSource.localDifferentDegree place +
                arithmeticSource.localConductorDegree place)))
    (arithmeticDivisorBackedComponent_eq_padicHaarFormulaMatching :
      source.matchedLocalDegreeArithmeticDivisorBackedComponentSource.formulaGapMatchedArithmeticDegreePadicFormulaMatchingSource =
        (IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.ofArithmeticDegreeControlledLocalArithmeticSource
          (IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource.ofPadicUnitBallHaarIndex
            theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
            padicHaarDefectSource arithmeticDegreeCalibrationSource
            localPrimeErrorContribution_eq_padicHaarDefect_main
            distinguishedProcessionBound_le_arithmeticDegreePart
            archimedeanProcessionBound_le_arithmeticDegreePart)).toAdditiveHaarFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource) :=
  let localArithmeticSource :=
    IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource.ofPadicUnitBallHaarIndex
      theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
      padicHaarDefectSource arithmeticDegreeCalibrationSource
      localPrimeErrorContribution_eq_padicHaarDefect_main
      distinguishedProcessionBound_le_arithmeticDegreePart
      archimedeanProcessionBound_le_arithmeticDegreePart
  let valuationBallSource :=
    source.toRecordOb3Ob5ArithmeticDivisorBackedValuationBallSourceOfArithmeticDegreeControlledLocalArithmeticSource
      localArithmeticSource
      arithmeticDivisorBackedComponent_eq_padicHaarFormulaMatching
  valuationBallSource.valuationBallFormulaGapMatchedArithmeticDegreePadicFormulaMatchingSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

set_option linter.style.longLine false in
theorem RecordOb3Ob5ArithmeticDivisorBackedComponentSource.toCorePadicUnitBallArithmeticFormulaMatchingSourceOfPadicUnitBallHaarIndex_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand)
    (theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        β estimate αLocal ηLocal localField localAnalyticHullSystem
        archIndex archSummand)
    (padicHaarDefectSource :
      IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource
        β localPrime localField αHaar hullSystem)
    (arithmeticDegreeCalibrationSource :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreeCalibrationSource
        β estimate η γ localField
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand
        theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource)
    (localPrimeErrorContribution_eq_padicHaarDefect_main :
      ∀ place : β,
        (theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
            |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
            |>.toThetaPilotArithmeticDivisorLocalEvaluationSource).localPrimeErrorContribution place =
          padicHaarDefectSource.localHaarNormalizationDefect place +
            (theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
              |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
              |>.toThetaPilotArithmeticDivisorLocalEvaluationSource).localMainLogContribution place)
    (distinguishedProcessionBound_le_arithmeticDegreePart :
      ∀ place : β,
        theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind place =
            IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
          theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.distinguishedProcessionBound place <=
            (let arithmeticSource :=
              theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toThetaPilotArithmeticDivisorLocalEvaluationSource;
            arithmeticSource.arithmeticDegreeCoefficient *
              (arithmeticSource.localDifferentDegree place +
                arithmeticSource.localConductorDegree place)))
    (archimedeanProcessionBound_le_arithmeticDegreePart :
      ∀ place : β,
        theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind place =
            IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
          theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.archimedeanProcessionBound place <=
            (let arithmeticSource :=
              theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toThetaPilotArithmeticDivisorLocalEvaluationSource;
            arithmeticSource.arithmeticDegreeCoefficient *
              (arithmeticSource.localDifferentDegree place +
                arithmeticSource.localConductorDegree place)))
    (arithmeticDivisorBackedComponent_eq_padicHaarFormulaMatching :
      source.matchedLocalDegreeArithmeticDivisorBackedComponentSource.formulaGapMatchedArithmeticDegreePadicFormulaMatchingSource =
        (IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.ofArithmeticDegreeControlledLocalArithmeticSource
          (IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource.ofPadicUnitBallHaarIndex
            theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
            padicHaarDefectSource arithmeticDegreeCalibrationSource
            localPrimeErrorContribution_eq_padicHaarDefect_main
            distinguishedProcessionBound_le_arithmeticDegreePart
            archimedeanProcessionBound_le_arithmeticDegreePart)).toAdditiveHaarFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource) :
    (source.toCorePadicUnitBallArithmeticFormulaMatchingSourceOfPadicUnitBallHaarIndex
      theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
      padicHaarDefectSource arithmeticDegreeCalibrationSource
      localPrimeErrorContribution_eq_padicHaarDefect_main
      distinguishedProcessionBound_le_arithmeticDegreePart
      archimedeanProcessionBound_le_arithmeticDegreePart
      arithmeticDivisorBackedComponent_eq_padicHaarFormulaMatching).Endpoint :=
  (source.toCorePadicUnitBallArithmeticFormulaMatchingSourceOfPadicUnitBallHaarIndex
    theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    padicHaarDefectSource arithmeticDegreeCalibrationSource
    localPrimeErrorContribution_eq_padicHaarDefect_main
    distinguishedProcessionBound_le_arithmeticDegreePart
    archimedeanProcessionBound_le_arithmeticDegreePart
    arithmeticDivisorBackedComponent_eq_padicHaarFormulaMatching).endpoint

set_option linter.style.longLine false in
/--
Project a Record-Ob3/Ob5 component source to the canonical residual package
directly from the p-adic unit-ball Haar-index local estimate data.

This lowers
`toCoreLocalArithmeticDegreeResidualSourceOfArithmeticDegreeControlledLocalArithmeticSource`:
the arithmetic-degree-controlled local arithmetic source is constructed
internally from the valuation-ball local-analytic Theorem~1.10 ledger, the
p-adic Haar-index defect source, the arithmetic-degree calibration, and the
Step~(v)/(vii) comparison bounds.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedComponentSource.toCoreLocalArithmeticDegreeResidualSourceOfPadicUnitBallHaarIndex
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand)
    (theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        β estimate αLocal ηLocal localField localAnalyticHullSystem
        archIndex archSummand)
    (padicHaarDefectSource :
      IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource
        β localPrime localField αHaar hullSystem)
    (arithmeticDegreeCalibrationSource :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreeCalibrationSource
        β estimate η γ localField
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand
        theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource)
    (localPrimeErrorContribution_eq_padicHaarDefect_main :
      ∀ place : β,
        (theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
            |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
            |>.toThetaPilotArithmeticDivisorLocalEvaluationSource).localPrimeErrorContribution place =
          padicHaarDefectSource.localHaarNormalizationDefect place +
            (theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
              |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
              |>.toThetaPilotArithmeticDivisorLocalEvaluationSource).localMainLogContribution place)
    (distinguishedProcessionBound_le_arithmeticDegreePart :
      ∀ place : β,
        theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind place =
            IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
          theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.distinguishedProcessionBound place <=
            (let arithmeticSource :=
              theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toThetaPilotArithmeticDivisorLocalEvaluationSource;
            arithmeticSource.arithmeticDegreeCoefficient *
              (arithmeticSource.localDifferentDegree place +
                arithmeticSource.localConductorDegree place)))
    (archimedeanProcessionBound_le_arithmeticDegreePart :
      ∀ place : β,
        theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind place =
            IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
          theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.archimedeanProcessionBound place <=
            (let arithmeticSource :=
              theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toThetaPilotArithmeticDivisorLocalEvaluationSource;
            arithmeticSource.arithmeticDegreeCoefficient *
              (arithmeticSource.localDifferentDegree place +
                arithmeticSource.localConductorDegree place)))
    (arithmeticDivisorBackedComponent_eq_padicHaarFormulaMatching :
      source.matchedLocalDegreeArithmeticDivisorBackedComponentSource.formulaGapMatchedArithmeticDegreePadicFormulaMatchingSource =
        (IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.ofArithmeticDegreeControlledLocalArithmeticSource
          (IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource.ofPadicUnitBallHaarIndex
            theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
            padicHaarDefectSource arithmeticDegreeCalibrationSource
            localPrimeErrorContribution_eq_padicHaarDefect_main
            distinguishedProcessionBound_le_arithmeticDegreePart
            archimedeanProcessionBound_le_arithmeticDegreePart)).toAdditiveHaarFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource) :=
  (source.toCorePadicUnitBallArithmeticFormulaMatchingSourceOfPadicUnitBallHaarIndex
    theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    padicHaarDefectSource arithmeticDegreeCalibrationSource
    localPrimeErrorContribution_eq_padicHaarDefect_main
    distinguishedProcessionBound_le_arithmeticDegreePart
    archimedeanProcessionBound_le_arithmeticDegreePart
    arithmeticDivisorBackedComponent_eq_padicHaarFormulaMatching)
    |>.toLocalArithmeticDegreeResidualSource

theorem RecordOb3Ob5ArithmeticDivisorBackedComponentSource.toCoreLocalArithmeticDegreeResidualSourceOfPadicUnitBallHaarIndex_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand)
    (theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        β estimate αLocal ηLocal localField localAnalyticHullSystem
        archIndex archSummand)
    (padicHaarDefectSource :
      IUTStage1FinitePlacePadicUnitBallHaarIndexDefectSource
        β localPrime localField αHaar hullSystem)
    (arithmeticDegreeCalibrationSource :
      IUTStage1AdditiveHaarTheorem110StepXIArithmeticDegreeCalibrationSource
        β estimate η γ localField
        αLocal ηLocal localAnalyticHullSystem archIndex archSummand
        theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource)
    (localPrimeErrorContribution_eq_padicHaarDefect_main :
      ∀ place : β,
        (theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
            |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
            |>.toThetaPilotArithmeticDivisorLocalEvaluationSource).localPrimeErrorContribution place =
          padicHaarDefectSource.localHaarNormalizationDefect place +
            (theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
              |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
              |>.toThetaPilotArithmeticDivisorLocalEvaluationSource).localMainLogContribution place)
    (distinguishedProcessionBound_le_arithmeticDegreePart :
      ∀ place : β,
        theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind place =
            IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
          theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.distinguishedProcessionBound place <=
            (let arithmeticSource :=
              theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toThetaPilotArithmeticDivisorLocalEvaluationSource;
            arithmeticSource.arithmeticDegreeCoefficient *
              (arithmeticSource.localDifferentDegree place +
                arithmeticSource.localConductorDegree place)))
    (archimedeanProcessionBound_le_arithmeticDegreePart :
      ∀ place : β,
        theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind place =
            IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
          theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.archimedeanProcessionBound place <=
            (let arithmeticSource :=
              theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
                |>.toThetaPilotArithmeticDivisorLocalEvaluationSource;
            arithmeticSource.arithmeticDegreeCoefficient *
              (arithmeticSource.localDifferentDegree place +
                arithmeticSource.localConductorDegree place)))
    (arithmeticDivisorBackedComponent_eq_padicHaarFormulaMatching :
      source.matchedLocalDegreeArithmeticDivisorBackedComponentSource.formulaGapMatchedArithmeticDegreePadicFormulaMatchingSource =
        (IUTStage1ValuationBallHaarTheorem110StepXIFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource.ofArithmeticDegreeControlledLocalArithmeticSource
          (IUTStage1ValuationBallHaarTheorem110StepXIArithmeticDegreeControlledLocalArithmeticSource.ofPadicUnitBallHaarIndex
            theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
            padicHaarDefectSource arithmeticDegreeCalibrationSource
            localPrimeErrorContribution_eq_padicHaarDefect_main
            distinguishedProcessionBound_le_arithmeticDegreePart
            archimedeanProcessionBound_le_arithmeticDegreePart)).toAdditiveHaarFormulaGapMatchedArithmeticDegreePadicPrimeErrorFormulaMatchingSource) :
    (source.toCoreLocalArithmeticDegreeResidualSourceOfPadicUnitBallHaarIndex
      theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
      padicHaarDefectSource arithmeticDegreeCalibrationSource
      localPrimeErrorContribution_eq_padicHaarDefect_main
      distinguishedProcessionBound_le_arithmeticDegreePart
      archimedeanProcessionBound_le_arithmeticDegreePart
      arithmeticDivisorBackedComponent_eq_padicHaarFormulaMatching).Endpoint :=
  (source.toCoreLocalArithmeticDegreeResidualSourceOfPadicUnitBallHaarIndex
    theorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    padicHaarDefectSource arithmeticDegreeCalibrationSource
    localPrimeErrorContribution_eq_padicHaarDefect_main
    distinguishedProcessionBound_le_arithmeticDegreePart
    archimedeanProcessionBound_le_arithmeticDegreePart
    arithmeticDivisorBackedComponent_eq_padicHaarFormulaMatching).endpoint

set_option linter.style.longLine false in
/--
Project the p-adic-Haar controlled Record-Ob3/Ob5 component source to the
canonical p-adic arithmetic formula-matching package.

This is the strict-source version of
`toCorePadicUnitBallArithmeticFormulaMatchingSourceOfPadicUnitBallHaarIndex`:
the p-adic Haar-index local-estimate data, arithmetic-degree calibration, and
component/formula synchronization are all fields of the source, so the
canonical Step~(v)/(vii) equalities are reached with no extra local-arithmetic
or formula-matching equality argument.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedPadicHaarControlledComponentSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedPadicHaarControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :=
  source.toRecordOb3Ob5ArithmeticDivisorBackedValuationBallSource
    |>.valuationBallFormulaGapMatchedArithmeticDegreePadicFormulaMatchingSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

theorem RecordOb3Ob5ArithmeticDivisorBackedPadicHaarControlledComponentSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedPadicHaarControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

set_option linter.style.longLine false in
/--
Project the p-adic-Haar controlled Record-Ob3/Ob5 component source to the
canonical local arithmetic-degree residual package.

The residual package is now a consumer of the strict p-adic-Haar controlled
source itself.  The old component-level route still records the weaker trust
boundary, but this declaration removes the independent controlled local
arithmetic source and formula-core equality from this consumer surface.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedPadicHaarControlledComponentSource.toCoreLocalArithmeticDegreeResidualSource
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedPadicHaarControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource
    |>.toLocalArithmeticDegreeResidualSource

theorem RecordOb3Ob5ArithmeticDivisorBackedPadicHaarControlledComponentSource.toCoreLocalArithmeticDegreeResidualSource_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedPadicHaarControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    source.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  source.toCoreLocalArithmeticDegreeResidualSource.endpoint

set_option linter.style.longLine false in
/--
Project the p-adic-defect/main valuation-ball controlled Record-Ob3/Ob5 source
to the canonical p-adic arithmetic formula-matching package.

This lowers the strict p-adic-Haar controlled bridge: the valuation-ball
evaluation source, p-adic Haar-index defect source, and equality
`E_v = delta_v + M_v` are projected from the p-adic-defect/main valuation-ball
source before entering the core Step~(xi) formula package.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :=
  source.toPadicHaarControlledComponentSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

theorem RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

set_option linter.style.longLine false in
/--
Project the p-adic-defect/main valuation-ball controlled Record-Ob3/Ob5 source
directly to the canonical local arithmetic-degree residual package.

The residual consumer now sees the lower p-adic-defect/main source rather than
a separately supplied valuation-ball evaluation source, p-adic Haar-index
source, prime-error split, arithmetic-degree-controlled local source, or
component/formula synchronization equality.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource.toCoreLocalArithmeticDegreeResidualSource
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource
    |>.toLocalArithmeticDegreeResidualSource

theorem RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource.toCoreLocalArithmeticDegreeResidualSource_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    source.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  source.toCoreLocalArithmeticDegreeResidualSource.endpoint

set_option linter.style.longLine false in
/--
Project the p-adic-defect/main valuation-ball controlled Record-Ob3/Ob5 source
directly to the case-local Theorem~1.10 arithmetic-degree bound source.

This lowers the public bound surface to the same p-adic-defect/main source that
already feeds the canonical residual package: the valuation-ball local estimate,
p-adic defect/main split, and controlled component synchronization reconstruct
the arithmetic-degree-controlled local source internally.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource.toCoreCaseLocalArithmeticDegreeBoundSource
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :=
  source.toArithmeticDegreeControlledLocalArithmeticSource
    |>.toCoreCaseLocalArithmeticDegreeBoundSource

theorem RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource.toCoreCaseLocalArithmeticDegreeBoundSource_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    source.toCoreCaseLocalArithmeticDegreeBoundSource.Endpoint :=
  source.toCoreCaseLocalArithmeticDegreeBoundSource.endpoint

set_option linter.style.longLine false in
/--
Project the matched local-degree object Record-Ob3/Ob5 source to the canonical
p-adic unit-ball arithmetic formula-matching package.

This is the lower local-estimate boundary for the residual bridge: the
valuation-ball formula-matching source, the local Step~(v)/(vii)
degree-identification objects, and their synchronization reconstruct the
p-adic-defect/main source internally before entering the canonical Step~(xi)
formula package.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource.toCorePadicUnitBallArithmeticFormulaMatchingSource
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :=
  source.toPadicDefectMainValuationBallControlledComponentSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

theorem RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    source.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

set_option linter.style.longLine false in
/--
Project the matched local-degree object Record-Ob3/Ob5 source directly to the
canonical local arithmetic-degree residual package.

Compared with the p-adic-defect/main bridge, this consumer no longer accepts a
p-adic-defect/main valuation-ball package as an independent input.  It derives
that package from the matched local-degree object source, then projects the
canonical p-adic arithmetic formula package and its residual ledger.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource.toCoreLocalArithmeticDegreeResidualSource
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :=
  source.toCorePadicUnitBallArithmeticFormulaMatchingSource
    |>.toLocalArithmeticDegreeResidualSource

theorem RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource.toCoreLocalArithmeticDegreeResidualSource_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    source.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  source.toCoreLocalArithmeticDegreeResidualSource.endpoint

set_option linter.style.longLine false in
/--
Project the matched local-degree object Record-Ob3/Ob5 source to the
case-local Theorem~1.10 arithmetic-degree bound package.

This is the pointwise-bound analogue of
`toCoreLocalArithmeticDegreeResidualSource`: the typed Step~(v)/(vii)
local-degree objects are first projected to the local-degree formula comparison
source, and the canonical Step~(v)/(vi)/(vii) upper-bound package is then
reconstructed from the arithmetic-degree-controlled local source.
-/
noncomputable def RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource.toCoreCaseLocalArithmeticDegreeBoundSource
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :=
  source.toLocalDegreeFormulaValuationBallControlledComponentSource
    |>.toCoreCaseLocalArithmeticDegreeBoundSource

theorem RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource.toCoreCaseLocalArithmeticDegreeBoundSource_endpoint
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    source.toCoreCaseLocalArithmeticDegreeBoundSource.Endpoint :=
  source.toCoreCaseLocalArithmeticDegreeBoundSource.endpoint

set_option linter.style.longLine false in
/--
Audit the matched local-degree object source as the lower formula-gap/residual
source for the canonical Stage~1 bridge.

The formula-gap Theorem~1.10 package and the local arithmetic-degree residual
package are both recovered from the matched local-degree object source, after
reconstructing the p-adic-defect/main valuation-ball source from the typed
Step~(v)/(vii) local-degree objects.
-/
theorem RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource.projectedFormulaGapResidualAudit
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    let padicDefectMainSource :=
      source.toPadicDefectMainValuationBallControlledComponentSource;
    let theorem110ValuationBallFormulaGapSource :=
      padicDefectMainSource.padicDefectMainValuationBallSource
        |>.toValuationBallFormulaGapMatchedPrimeErrorPadicDefectMainSource
        |>.theorem110FormulaGapMatchedArithmeticDivisorEvaluationSource;
    theorem110ValuationBallFormulaGapSource.Endpoint ∧
      source.toCoreLocalArithmeticDegreeResidualSource.Endpoint ∧
      theorem110ValuationBallFormulaGapSource.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.Endpoint ∧
      padicDefectMainSource.toCoreLocalArithmeticDegreeResidualSource.Endpoint := by
  intro padicDefectMainSource theorem110ValuationBallFormulaGapSource
  exact
    ⟨theorem110ValuationBallFormulaGapSource.endpoint,
      source.toCoreLocalArithmeticDegreeResidualSource_endpoint,
      theorem110ValuationBallFormulaGapSource
        |>.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.endpoint,
      padicDefectMainSource.toCoreLocalArithmeticDegreeResidualSource_endpoint⟩

set_option linter.style.longLine false in
/--
Audit that the matched local-degree object source supplies both local
Theorem~1.10 consumers: the residual ledger and the pointwise case-local
upper-bound package.

Thus the local-degree formula comparison source is no longer an independent
input for either the residual consumer or the case-local bound consumer at this
Record-Ob3/Ob5 handoff.
-/
theorem RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource.projectedCaseBoundResidualAudit
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedMatchedLocalDegreeObjectValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    source.matchedLocalDegreeIdentificationObjectSource.Endpoint ∧
      source.toCoreCaseLocalArithmeticDegreeBoundSource.Endpoint ∧
      source.toCoreLocalArithmeticDegreeResidualSource.Endpoint ∧
      source.toLocalDegreeFormulaValuationBallControlledComponentSource.toCoreCaseLocalArithmeticDegreeBoundSource.Endpoint :=
  ⟨source.matchedLocalDegreeIdentificationObjectSource.endpoint,
    source.toCoreCaseLocalArithmeticDegreeBoundSource_endpoint,
    source.toCoreLocalArithmeticDegreeResidualSource_endpoint,
    source.toLocalDegreeFormulaValuationBallControlledComponentSource
      |>.toCoreCaseLocalArithmeticDegreeBoundSource_endpoint⟩

set_option linter.style.longLine false in
/--
Audit the lower p-adic-defect/main source as a formula-gap and residual source.

The p-adic-defect/main valuation-ball source does not merely map to the generic
residual package.  It also projects the formula-gap Theorem~1.10 package that
the projected-weighted residual endpoint consumes.  This records the exact
source-backed replacement for the former pair of public inputs: a separate
formula-gap package and a separate local arithmetic-degree residual package.
-/
theorem RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource.projectedFormulaGapResidualAudit
    (source :
      RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource
        recordAdjustedSource sourceData estimate l η localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand) :
    let theorem110ValuationBallFormulaGapSource :=
      source.padicDefectMainValuationBallSource
        |>.toValuationBallFormulaGapMatchedPrimeErrorPadicDefectMainSource
        |>.theorem110FormulaGapMatchedArithmeticDivisorEvaluationSource;
    theorem110ValuationBallFormulaGapSource.Endpoint ∧
      source.toCoreLocalArithmeticDegreeResidualSource.Endpoint ∧
      theorem110ValuationBallFormulaGapSource.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.Endpoint :=
  ⟨source.padicDefectMainValuationBallSource
      |>.toValuationBallFormulaGapMatchedPrimeErrorPadicDefectMainSource
      |>.theorem110FormulaGapMatchedArithmeticDivisorEvaluationSource
      |>.endpoint,
    source.toCoreLocalArithmeticDegreeResidualSource_endpoint,
    source.padicDefectMainValuationBallSource
      |>.toValuationBallFormulaGapMatchedPrimeErrorPadicDefectMainSource
      |>.theorem110FormulaGapMatchedArithmeticDivisorEvaluationSource
      |>.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
      |>.endpoint⟩

set_option linter.style.longLine false in
set_option maxHeartbeats 1200000 in
-- The endpoint elaborates the full projected-weighted formula-gap residual boundary.
/--
Constructor-level signed endpoint from the p-adic-defect/main valuation-ball
Record-Ob3/Ob5 source.

This lowers the formula-gap residual consumer: the public source no longer
supplies the valuation-ball formula-gap Theorem 1.10 package and the local
arithmetic-degree residual package separately.  Lean projects the formula-gap
package and residual package from the single p-adic-defect/main Record-Ob3/Ob5
source, then transports the residual package across the explicit equality
identifying its arithmetic-degree calibration localized Step (xi) source with
the principal-product p-adic finite localized Step (xi) source consumed by the
formula-gap residual constructor.
-/
theorem RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource.goalEvidence_projectedWeightedFormulaGapResidual_fromPadicDefectMain
    {source target : Copy} {index : Type u}
    {package : IUTStage1SourcePackage source target index}
    {record : IUTStage1Theorem311MultiradialSourceRecord package}
    {coric : Type u} {l : PrimeGeFive}
    {theorem311Source :
      IUTStage1Theorem311ToCorollary312PaperTrace.Theorem311HodgeTheaterLogThetaLogKummerSource
        (target := target) coric l}
    {ΛStepXI : Type v}
    {principalSource :
      IUTStage1Remark395PrincipalProductHullSystemSource
        (Point target) ΛStepXI}
    {β : Type a} [Fintype β]
    {γStepXI : Type w} [Fintype γStepXI]
    {lStepXI : PrimeGeFive} {FStepXI : Type} [Field FStepXI]
    {XStepXI CStepXI : HyperbolicOrbicurveModel FStepXI}
    {sourceHA :
      IUTStage1ZModSquareWeightProfile.IUTStage1HodgeArakelovThetaValueEvaluationSource
        lStepXI XStepXI CStepXI}
    {principalHDDSource :
      IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource.PrincipalProductHullConstructedOb3Ob5AdjustedLogVolumeMeasureHodgeGapCanonicalHDDDirectCommonContainerSource
        (β := β) (γ := γStepXI) record sourceHA ΛStepXI}
    {sourceData :
      IUTStage1SourcePackage.IUTStage1Remark395ConstructedHolomorphicHullDeterminantSource
        (β := β) record}
    {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
    {p : Nat} [Fact p.Prime] {KLocal : Type w}
    [NontriviallyNormedField KLocal] [ProperSpace KLocal]
    [IsUltrametricDist KLocal] [MeasurableSpace KLocal]
    [Algebra ℚ_[p] KLocal] [FiniteDimensional ℚ_[p] KLocal]
    {localPrime : β -> Nat}
    [∀ place : β, Fact (Nat.Prime (localPrime place))]
    {localField : β -> Type x}
    [(place : β) -> NontriviallyNormedField (localField place)]
    [∀ place : β, ProperSpace (localField place)]
    [∀ place : β, IsUltrametricDist (localField place)]
    [(place : β) -> MeasurableSpace (localField place)]
    [∀ place : β, BorelSpace (localField place)]
    [∀ place : β, LocallyCompactSpace (localField place)]
    [∀ place : β, IsTopologicalAddGroup (localField place)]
    [∀ place : β, T2Space (localField place)]
    [(place : β) -> Algebra ℚ_[localPrime place] (localField place)]
    [∀ place : β,
      FiniteDimensional ℚ_[localPrime place] (localField place)]
    {αHaar : Type}
    {hullSystem : IUTStage1Remark395HolomorphicHullSystem αHaar}
    {αLocal : Type} {ηLocal : Type w}
    {localAnalyticHullSystem :
      IUTStage1Remark395HolomorphicHullSystem αLocal}
    {archIndex archSummand : β -> Type}
    [∀ place : β, Fintype (archIndex place)]
    [∀ place : β, Fintype (archSummand place)]
    (principalProductPadicFiniteSource :
      IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.PrincipalProductPadicFiniteLocalizedHullVectorBundleDecompositionSource
        theorem311Source principalSource p KLocal β γStepXI)
    (weightedDeterminantSummand_eq_principalProductLocalizedStepXI :
      let normSquareLocalizedStepXISource :=
        principalProductPadicFiniteSource.localizedSource
          |>.toUnitBallValuationHaarCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toAdditiveHaarCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toNormSquareLocalizedVectorBundleDeterminantSource;
      let localizedStepXISource :=
        normSquareLocalizedStepXISource.toLocalizedVectorBundleDeterminantSource;
      ∀ place : β,
        principalHDDSource.ob3ob4Source.toWeightedDeterminantSource.summand place =
          localizedStepXISource.toAdjustedDeterminantSource.toWeightedDeterminantSource.summand place)
    (weightedDeterminantAnchor_eq_principalProductLocalizedStepXI :
      let normSquareLocalizedStepXISource :=
        principalProductPadicFiniteSource.localizedSource
          |>.toUnitBallValuationHaarCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toAdditiveHaarCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toNormSquareLocalizedVectorBundleDeterminantSource;
      let localizedStepXISource :=
        normSquareLocalizedStepXISource.toLocalizedVectorBundleDeterminantSource;
      principalHDDSource.ob3ob4Source.toWeightedDeterminantSource.anchor =
        localizedStepXISource.toAdjustedDeterminantSource.toWeightedDeterminantSource.anchor)
    (weightedDeterminantPositiveTensorPower_eq_principalProductLocalizedStepXI :
      let normSquareLocalizedStepXISource :=
        principalProductPadicFiniteSource.localizedSource
          |>.toUnitBallValuationHaarCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toAdditiveHaarCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toNormSquareLocalizedVectorBundleDeterminantSource;
      let localizedStepXISource :=
        normSquareLocalizedStepXISource.toLocalizedVectorBundleDeterminantSource;
      principalHDDSource.ob3ob4Source.toWeightedDeterminantSource.positiveTensorPower =
        localizedStepXISource.toAdjustedDeterminantSource.toWeightedDeterminantSource.positiveTensorPower)
    (thetaSigned_eq_principalProductLocalizedAdjustedSum_mul_absLogQ :
      let normSquareLocalizedStepXISource :=
        principalProductPadicFiniteSource.localizedSource
          |>.toUnitBallValuationHaarCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toAdditiveHaarCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toNormSquareLocalizedVectorBundleDeterminantSource;
      let localizedStepXISource :=
        normSquareLocalizedStepXISource.toLocalizedVectorBundleDeterminantSource;
      package.preLedger.thetaSigned =
        (∑ place : β,
          localizedStepXISource.weightedAdjustedLogVolume place) *
          (-package.preLedger.qSigned))
    (padicDefectMainSource :
      RecordOb3Ob5ArithmeticDivisorBackedPadicDefectMainValuationBallControlledComponentSource
        principalHDDSource.toRecordOb3Ob5AdjustedDeterminantLogVolumeSource
        sourceData estimate lStepXI (Subring KLocal) localPrime localField
        αHaar hullSystem αLocal ηLocal localAnalyticHullSystem
        archIndex archSummand)
    (calibrationLocalizedStepXI_eq_principalProduct :
      let normSquareLocalizedStepXISource :=
        principalProductPadicFiniteSource.localizedSource
          |>.toUnitBallValuationHaarCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toAdditiveHaarCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toNormSquareLocalizedVectorBundleDeterminantSource;
      let localizedStepXISource :=
        normSquareLocalizedStepXISource.toLocalizedVectorBundleDeterminantSource;
      padicDefectMainSource.arithmeticDegreeCalibrationSource.localizedStepXISource =
        localizedStepXISource) :
    ((package.preLedger.qSigned = package.preLedger.thetaSigned ∧
        package.preLedger.thetaSigned < 0) ∨
      (-1 : Real) < estimate.cTheta) ∧
      (-1 : Real) <= estimate.cTheta := by
  let theorem110ValuationBallFormulaGapSource :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        β estimate αLocal ηLocal localField localAnalyticHullSystem
        archIndex archSummand :=
    padicDefectMainSource.padicDefectMainValuationBallSource
      |>.toValuationBallFormulaGapMatchedPrimeErrorPadicDefectMainSource
      |>.theorem110FormulaGapMatchedArithmeticDivisorEvaluationSource
  let localArithmeticDegreeResidualSource :
      let theorem110ValuationBallLocalAnalyticSource :=
        theorem110ValuationBallFormulaGapSource.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource;
      let normSquareLocalizedStepXISource :=
        principalProductPadicFiniteSource.localizedSource
          |>.toUnitBallValuationHaarCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toAdditiveHaarCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toCompactOpenNormSquareLocalizedVectorBundleDeterminantSource
          |>.toNormSquareLocalizedVectorBundleDeterminantSource;
      let localizedStepXISource :=
        normSquareLocalizedStepXISource.toLocalizedVectorBundleDeterminantSource;
      IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeResidualSource
        theorem110ValuationBallLocalAnalyticSource.toThetaPilotArithmeticDivisorLocalEvaluationSource
        localizedStepXISource := by
    dsimp
    rw [← calibrationLocalizedStepXI_eq_principalProduct]
    simpa [theorem110ValuationBallFormulaGapSource] using
      padicDefectMainSource.toCoreLocalArithmeticDegreeResidualSource
  exact
    IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.ConstructorBuiltPrincipalProductPadicFiniteProjectedWeightedDeterminantQNormalizedFormulaGapResidualHaarSource.goalEvidence_ofLocalArithmeticDegreeResidualSource
      (principalHDDSource := principalHDDSource)
      (αIUTIV := αLocal) (ηIUTIV := ηLocal)
      (KIUTIV := localField) (iutIVHullSystem := localAnalyticHullSystem)
      (archIndex := archIndex) (archSummand := archSummand)
      principalProductPadicFiniteSource
      weightedDeterminantSummand_eq_principalProductLocalizedStepXI
      weightedDeterminantAnchor_eq_principalProductLocalizedStepXI
      weightedDeterminantPositiveTensorPower_eq_principalProductLocalizedStepXI
      thetaSigned_eq_principalProductLocalizedAdjustedSum_mul_absLogQ
      theorem110ValuationBallFormulaGapSource
      localArithmeticDegreeResidualSource

set_option linter.style.longLine false in
/--
Project a named-HDD Record-Ob3/Ob5 valuation-ball boundary directly to the
canonical p-adic arithmetic formula-matching package.

The named-HDD boundary still remembers the valuation-ball Record-Ob3/Ob5
source, but the consumer does not need to expose that source separately.  Lean
first reconstructs the arithmetic-degree-controlled local source from the
valuation-ball boundary, then projects through the canonical Step~(xi) formula
package.
-/
noncomputable def RecordOb3Ob5ValuationBallNamedHDDBoundaryData.toCorePadicUnitBallArithmeticFormulaMatchingSource
    {constructorBuiltSource :
      IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource
        (β := β) record}
    (boundary :
      RecordOb3Ob5ValuationBallNamedHDDBoundaryData
        (recordAdjustedSource := recordAdjustedSource)
        (sourceData := sourceData) (estimate := estimate) (l := l)
        (η := η) (localPrime := localPrime) (localField := localField)
        (αHaar := αHaar) (hullSystem := hullSystem)
        (αLocal := αLocal) (ηLocal := ηLocal)
        (localAnalyticHullSystem := localAnalyticHullSystem)
        (archIndex := archIndex) (archSummand := archSummand)
        constructorBuiltSource) :=
  boundary.valuationBallSource.toArithmeticDegreeControlledLocalArithmeticSource
    |>.toCorePadicUnitBallArithmeticFormulaMatchingSource

theorem RecordOb3Ob5ValuationBallNamedHDDBoundaryData.toCorePadicUnitBallArithmeticFormulaMatchingSource_endpoint
    {constructorBuiltSource :
      IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource
        (β := β) record}
    (boundary :
      RecordOb3Ob5ValuationBallNamedHDDBoundaryData
        (recordAdjustedSource := recordAdjustedSource)
        (sourceData := sourceData) (estimate := estimate) (l := l)
        (η := η) (localPrime := localPrime) (localField := localField)
        (αHaar := αHaar) (hullSystem := hullSystem)
        (αLocal := αLocal) (ηLocal := ηLocal)
        (localAnalyticHullSystem := localAnalyticHullSystem)
        (archIndex := archIndex) (archSummand := archSummand)
        constructorBuiltSource) :
    boundary.toCorePadicUnitBallArithmeticFormulaMatchingSource.Endpoint :=
  boundary.toCorePadicUnitBallArithmeticFormulaMatchingSource.endpoint

set_option linter.style.longLine false in
/--
Project a named-HDD Record-Ob3/Ob5 valuation-ball boundary directly to the
canonical local arithmetic-degree residual package.

This is the named-HDD analogue of the lower p-adic-defect/main residual
projection: the residual consumer receives the formula package produced from
the named boundary, not a separately supplied valuation-ball local-estimate
source, Haar-index source, prime-error split, or component/formula
synchronization equality.
-/
noncomputable def RecordOb3Ob5ValuationBallNamedHDDBoundaryData.toCoreLocalArithmeticDegreeResidualSource
    {constructorBuiltSource :
      IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource
        (β := β) record}
    (boundary :
      RecordOb3Ob5ValuationBallNamedHDDBoundaryData
        (recordAdjustedSource := recordAdjustedSource)
        (sourceData := sourceData) (estimate := estimate) (l := l)
        (η := η) (localPrime := localPrime) (localField := localField)
        (αHaar := αHaar) (hullSystem := hullSystem)
        (αLocal := αLocal) (ηLocal := ηLocal)
        (localAnalyticHullSystem := localAnalyticHullSystem)
        (archIndex := archIndex) (archSummand := archSummand)
        constructorBuiltSource) :=
  boundary.toCorePadicUnitBallArithmeticFormulaMatchingSource
    |>.toLocalArithmeticDegreeResidualSource

theorem RecordOb3Ob5ValuationBallNamedHDDBoundaryData.toCoreLocalArithmeticDegreeResidualSource_endpoint
    {constructorBuiltSource :
      IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource
        (β := β) record}
    (boundary :
      RecordOb3Ob5ValuationBallNamedHDDBoundaryData
        (recordAdjustedSource := recordAdjustedSource)
        (sourceData := sourceData) (estimate := estimate) (l := l)
        (η := η) (localPrime := localPrime) (localField := localField)
        (αHaar := αHaar) (hullSystem := hullSystem)
        (αLocal := αLocal) (ηLocal := ηLocal)
        (localAnalyticHullSystem := localAnalyticHullSystem)
        (archIndex := archIndex) (archSummand := archSummand)
        constructorBuiltSource) :
    boundary.toCoreLocalArithmeticDegreeResidualSource.Endpoint :=
  boundary.toCoreLocalArithmeticDegreeResidualSource.endpoint

set_option linter.style.longLine false in
/--
Audit the named-HDD residual projection.

The projected residual source has its endpoint, and the finite Haar-defect
lower bound is the same one carried by the named-HDD valuation-ball boundary.
-/
theorem RecordOb3Ob5ValuationBallNamedHDDBoundaryData.toCoreLocalArithmeticDegreeResidualSource_audit
    {constructorBuiltSource :
      IUTStage1SourcePackage.IUTStage1PossibleImageConstructorBuiltHolomorphicHullDeterminantSource
        (β := β) record}
    (boundary :
      RecordOb3Ob5ValuationBallNamedHDDBoundaryData
        (recordAdjustedSource := recordAdjustedSource)
        (sourceData := sourceData) (estimate := estimate) (l := l)
        (η := η) (localPrime := localPrime) (localField := localField)
        (αHaar := αHaar) (hullSystem := hullSystem)
        (αLocal := αLocal) (ηLocal := ηLocal)
        (localAnalyticHullSystem := localAnalyticHullSystem)
        (archIndex := archIndex) (archSummand := archSummand)
        constructorBuiltSource) :
    boundary.toCoreLocalArithmeticDegreeResidualSource.Endpoint ∧
      (1 : Real) <= ∑ place : β, boundary.localHaarNormalizationDefect place :=
  ⟨boundary.toCoreLocalArithmeticDegreeResidualSource_endpoint,
    boundary.total_haar_defect_ge_one⟩

end ConstructedTheorem311OneSidedIUTIVTheorem110AdditiveHaarMatchedLocalDegreeArithmeticDivisorBackedComponentStepXILocalTermCThetaSource

end Experiments
end Stage1
end Iut
