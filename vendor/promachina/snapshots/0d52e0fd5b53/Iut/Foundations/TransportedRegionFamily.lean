/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.CommonTargetBound

/-!
Families of regions equipped with explicit choice-dependent transports.

`RegionComparisonFamily` is already enough to state containment and measured
bound lemmas. This file adds a more structured presentation in which each choice
has a named transport and a named target region before these data are bundled
as a comparison. This keeps transport bookkeeping visible for later APT-style
interfaces.
-/

namespace Iut
namespace RealLineCopy

/--
A family of target regions equipped with explicit transports from a fixed source
copy to a fixed target copy.
-/
structure TransportedRegionFamily (source target : Copy) (index : Type u) where
  transport : index -> Transport source target
  targetRegion : index -> Region target

namespace TransportedRegionFamily

variable {source target : Copy} {index : Type u}
variable {newIndex : Type v}

/--
Reindex a transported region family along a source-side choice map.

For the Stage 1 generated-choice corridor this is the formal operation that
pulls an ambient concrete-choice family back to the generated full-label choice
space via the concrete projection map.
-/
def reindex (family : TransportedRegionFamily source target index)
    (f : newIndex -> index) :
    TransportedRegionFamily source target newIndex :=
  { transport := fun choice => family.transport (f choice),
    targetRegion := fun choice => family.targetRegion (f choice) }

@[simp]
theorem reindex_transport
    (family : TransportedRegionFamily source target index)
    (f : newIndex -> index) (choice : newIndex) :
    (family.reindex f).transport choice = family.transport (f choice) :=
  rfl

@[simp]
theorem reindex_targetRegion
    (family : TransportedRegionFamily source target index)
    (f : newIndex -> index) (choice : newIndex) :
    (family.reindex f).targetRegion choice = family.targetRegion (f choice) :=
  rfl

/-- The region comparison associated to one chosen transported target. -/
def comparison (family : TransportedRegionFamily source target index) (choice : index) :
    RegionComparison source target :=
  { transport := family.transport choice,
    targetRegion := family.targetRegion choice }

/-- Forget the separate fields and view the data as a comparison family. -/
def comparisons (family : TransportedRegionFamily source target index) :
    RegionComparisonFamily source target index :=
  { comparison := family.comparison }

/-- A source point satisfies the chosen transported target. -/
def Holds (family : TransportedRegionFamily source target index)
    (choice : index) (sourcePoint : Point source) : Prop :=
  (family.comparison choice).Holds sourcePoint

@[simp]
theorem reindex_comparison
    (family : TransportedRegionFamily source target index)
    (f : newIndex -> index) (choice : newIndex) :
    (family.reindex f).comparison choice = family.comparison (f choice) :=
  rfl

@[simp]
theorem reindex_Holds
    (family : TransportedRegionFamily source target index)
    (f : newIndex -> index) (choice : newIndex) (sourcePoint : Point source) :
    (family.reindex f).Holds choice sourcePoint ↔
      family.Holds (f choice) sourcePoint :=
  Iff.rfl

@[simp]
theorem holds_iff (family : TransportedRegionFamily source target index)
    (choice : index) (sourcePoint : Point source) :
    family.Holds choice sourcePoint ↔
      (family.targetRegion choice).Contains
        (Transport.map (family.transport choice) sourcePoint) :=
  Iff.rfl

/-- A common target for the transported family after forgetting to comparisons. -/
def CommonTarget (family : TransportedRegionFamily source target index)
    (common : Region target) : Prop :=
  family.comparisons.CommonTarget common

/-- A common target hull for the transported family after forgetting to comparisons. -/
abbrev CommonTargetHull (family : TransportedRegionFamily source target index) :=
  family.comparisons.CommonTargetHull

/-- A measured common-target bound for the transported family. -/
abbrev CommonTargetBound (measure : RegionMeasure target)
    (family : TransportedRegionFamily source target index) (bound : Real) :=
  RegionComparisonFamily.CommonTargetBound measure family.comparisons bound

/-- A measured common-hull bound for the transported family. -/
abbrev CommonTargetHullBound (measure : RegionMeasure target)
    (family : TransportedRegionFamily source target index) (bound : Real) :=
  RegionComparisonFamily.CommonTargetHullBound measure family.comparisons bound

theorem holds_common_of_choice
    {family : TransportedRegionFamily source target index}
    {common : Region target} (hcommon : family.CommonTarget common)
    {choice : index} {sourcePoint : Point source}
    (hholds : family.Holds choice sourcePoint) :
    (RegionComparison.enlargeTarget (family.comparison choice) common).Holds
      sourcePoint :=
  RegionComparisonFamily.holds_commonTarget_of_choice hcommon hholds

theorem holds_commonHull_of_choice
    {family : TransportedRegionFamily source target index}
    (commonHull : family.CommonTargetHull)
    {choice : index} {sourcePoint : Point source}
    (hholds : family.Holds choice sourcePoint) :
    (RegionComparison.enlargeTarget (family.comparison choice) commonHull.hull).Holds
      sourcePoint :=
  RegionComparisonFamily.holds_commonTargetHull_of_choice commonHull hholds

theorem choice_targetVolume_le_of_commonBound
    {measure : RegionMeasure target}
    {family : TransportedRegionFamily source target index} {bound : Real}
    (data : family.CommonTargetBound measure bound) (choice : index) :
    RegionMeasure.targetVolume measure (family.comparison choice) <= bound :=
  data.choice_targetVolume_le choice

theorem allTargetsAtMost_of_commonBound
    {measure : RegionMeasure target}
    {family : TransportedRegionFamily source target index} {bound : Real}
    (data : family.CommonTargetBound measure bound) :
    RegionComparisonFamily.AllTargetsAtMost measure family.comparisons bound :=
  data.allTargetsAtMost

theorem choice_targetVolume_le_of_commonHullBound
    {measure : RegionMeasure target}
    {family : TransportedRegionFamily source target index} {bound : Real}
    (data : family.CommonTargetHullBound measure bound) (choice : index) :
    RegionMeasure.targetVolume measure (family.comparison choice) <= bound :=
  data.choice_targetVolume_le choice

theorem allTargetsAtMost_of_commonHullBound
    {measure : RegionMeasure target}
    {family : TransportedRegionFamily source target index} {bound : Real}
    (data : family.CommonTargetHullBound measure bound) :
    RegionComparisonFamily.AllTargetsAtMost measure family.comparisons bound :=
  data.allTargetsAtMost

end TransportedRegionFamily

end RealLineCopy
end Iut
