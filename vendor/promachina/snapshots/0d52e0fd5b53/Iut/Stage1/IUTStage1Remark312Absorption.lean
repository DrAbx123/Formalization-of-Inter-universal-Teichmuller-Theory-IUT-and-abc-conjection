/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1SourceCore

/-!
Remark 3.12.2(v) zero/one-column absorption shadows.

This module isolates the Fig. 3.9 absorption distinction used near IUT III,
Remark 3.12.2(v): the zero-column absorbs unit indeterminacy by a hull upper
ray, while the one-column absorbs conjugate choices by log-volume equality.
-/

namespace Iut
namespace Stage1

/--
Remark 3.12.2(v) zero-column hull absorption shadow.

For the 0-column, regions in mono-analytic log-shells are related to unit-group
data only up to local `O^×`-multiple indeterminacy.  The source text says that
Step (xi) introduces holomorphic hulls to absorb this indeterminacy.  This record
keeps the ordered log-volume skeleton: both the original and unit-shifted
regions lie below the same hull boundary.
-/
structure IUTStage1ZeroColumnHullAbsorbsUnitIndeterminacy where
  originalRegionLogVolume : Real
  unitShiftedRegionLogVolume : Real
  hullLogVolume : Real
  original_le_hull :
    originalRegionLogVolume <= hullLogVolume
  unit_shifted_le_hull :
    unitShiftedRegionLogVolume <= hullLogVolume

namespace IUTStage1ZeroColumnHullAbsorbsUnitIndeterminacy

def hullUpperRay
    (data : IUTStage1ZeroColumnHullAbsorbsUnitIndeterminacy) : Set Real :=
  { value | value <= data.hullLogVolume }

theorem original_mem_hullUpperRay
    (data : IUTStage1ZeroColumnHullAbsorbsUnitIndeterminacy) :
    data.originalRegionLogVolume ∈ data.hullUpperRay :=
  data.original_le_hull

theorem unitShifted_mem_hullUpperRay
    (data : IUTStage1ZeroColumnHullAbsorbsUnitIndeterminacy) :
    data.unitShiftedRegionLogVolume ∈ data.hullUpperRay :=
  data.unit_shifted_le_hull

theorem both_regions_absorbed_by_hull
    (data : IUTStage1ZeroColumnHullAbsorbsUnitIndeterminacy) :
    data.originalRegionLogVolume ∈ data.hullUpperRay ∧
      data.unitShiftedRegionLogVolume ∈ data.hullUpperRay :=
  ⟨data.original_mem_hullUpperRay, data.unitShifted_mem_hullUpperRay⟩

theorem original_eq_hull_iff_hull_le_original
    (data : IUTStage1ZeroColumnHullAbsorbsUnitIndeterminacy) :
    data.originalRegionLogVolume = data.hullLogVolume ↔
      data.hullLogVolume <= data.originalRegionLogVolume :=
  ⟨fun h => by rw [h],
    fun h => le_antisymm data.original_le_hull h⟩

theorem unitShifted_eq_hull_iff_hull_le_unitShifted
    (data : IUTStage1ZeroColumnHullAbsorbsUnitIndeterminacy) :
    data.unitShiftedRegionLogVolume = data.hullLogVolume ↔
      data.hullLogVolume <= data.unitShiftedRegionLogVolume :=
  ⟨fun h => by rw [h],
    fun h => le_antisymm data.unit_shifted_le_hull h⟩

theorem hullEqualityRequiresReverseBounds
    (data : IUTStage1ZeroColumnHullAbsorbsUnitIndeterminacy) :
    (data.originalRegionLogVolume = data.hullLogVolume ↔
        data.hullLogVolume <= data.originalRegionLogVolume) ∧
      (data.unitShiftedRegionLogVolume = data.hullLogVolume ↔
        data.hullLogVolume <= data.unitShiftedRegionLogVolume) :=
  ⟨data.original_eq_hull_iff_hull_le_original,
    data.unitShifted_eq_hull_iff_hull_le_unitShifted⟩

end IUTStage1ZeroColumnHullAbsorbsUnitIndeterminacy

/--
Remark 3.12.2(v) one-column log-volume compatibility shadow.

For the 1-column, the arithmetic holomorphic structure is held fixed and the
choice among logarithmic conjugates is absorbed by passing to log-volumes via
log-link compatibility.  The numerical content retained here is equality, not
merely an upper bound.
-/
structure IUTStage1OneColumnLogVolumeCompatibilityAbsorbsConjugateChoice where
  sourceRingStructureLogVolume : Real
  conjugateRingStructureLogVolume : Real
  log_volume_compatible :
    sourceRingStructureLogVolume = conjugateRingStructureLogVolume

namespace IUTStage1OneColumnLogVolumeCompatibilityAbsorbsConjugateChoice

theorem precise_logVolume_eq
    (data :
      IUTStage1OneColumnLogVolumeCompatibilityAbsorbsConjugateChoice) :
    data.sourceRingStructureLogVolume =
      data.conjugateRingStructureLogVolume :=
  data.log_volume_compatible

theorem source_le_conjugate
    (data :
      IUTStage1OneColumnLogVolumeCompatibilityAbsorbsConjugateChoice) :
    data.sourceRingStructureLogVolume <=
      data.conjugateRingStructureLogVolume := by
  rw [data.precise_logVolume_eq]

theorem conjugate_le_source
    (data :
      IUTStage1OneColumnLogVolumeCompatibilityAbsorbsConjugateChoice) :
    data.conjugateRingStructureLogVolume <=
      data.sourceRingStructureLogVolume := by
  rw [data.precise_logVolume_eq]

end IUTStage1OneColumnLogVolumeCompatibilityAbsorbsConjugateChoice

theorem zero_one_column_absorption_profile
    (zeroData : IUTStage1ZeroColumnHullAbsorbsUnitIndeterminacy)
    (oneData :
      IUTStage1OneColumnLogVolumeCompatibilityAbsorbsConjugateChoice) :
    IUTStage1LogThetaVerticalColumn.zeroThetaPilot.logShellTreatment =
        IUTStage1LogShellColumnTreatment.monoAnalyticContainers ∧
      zeroData.originalRegionLogVolume ∈ zeroData.hullUpperRay ∧
      zeroData.unitShiftedRegionLogVolume ∈ zeroData.hullUpperRay ∧
      IUTStage1LogThetaVerticalColumn.oneQPilot.logShellTreatment =
        IUTStage1LogShellColumnTreatment.tautologicalLogDocumentation ∧
      oneData.sourceRingStructureLogVolume =
        oneData.conjugateRingStructureLogVolume :=
  ⟨IUTStage1LogThetaVerticalColumn.thetaPilot_logShellTreatment,
    zeroData.original_mem_hullUpperRay,
    zeroData.unitShifted_mem_hullUpperRay,
    IUTStage1LogThetaVerticalColumn.qPilot_logShellTreatment,
    oneData.precise_logVolume_eq⟩

/--
Remark 3.12.2(v) inequality-versus-equality endpoint.

The zero-column treatment records hull upper bounds for the original and
unit-shifted regions.  The one-column treatment records precise log-volume
equality for logarithmic conjugates, hence inequalities in both directions.
-/
theorem zero_one_column_inequality_vs_equality_endpoint
    (zeroData : IUTStage1ZeroColumnHullAbsorbsUnitIndeterminacy)
    (oneData :
      IUTStage1OneColumnLogVolumeCompatibilityAbsorbsConjugateChoice) :
    zeroData.originalRegionLogVolume <= zeroData.hullLogVolume ∧
      zeroData.unitShiftedRegionLogVolume <= zeroData.hullLogVolume ∧
      oneData.sourceRingStructureLogVolume =
        oneData.conjugateRingStructureLogVolume ∧
      oneData.sourceRingStructureLogVolume <=
        oneData.conjugateRingStructureLogVolume ∧
      oneData.conjugateRingStructureLogVolume <=
        oneData.sourceRingStructureLogVolume :=
  ⟨zeroData.original_le_hull,
    zeroData.unit_shifted_le_hull,
    oneData.precise_logVolume_eq,
    oneData.source_le_conjugate,
    oneData.conjugate_le_source⟩

end Stage1
end Iut
