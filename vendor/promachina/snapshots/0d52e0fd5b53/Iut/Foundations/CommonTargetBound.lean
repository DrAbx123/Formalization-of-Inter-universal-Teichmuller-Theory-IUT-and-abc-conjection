/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.RegionMeasure

/-!
Measured bounds for common targets of comparison families.

This file packages the order-theoretic output shape needed after a future
`hull+det` construction: a family of possible target regions is contained in a
common target, and the common target has a measured upper bound.

No IUT-specific construction of the common target is asserted here.
-/

namespace Iut
namespace RealLineCopy

namespace RegionComparisonFamily

variable {source target : Copy} {index : Type u}

/--
All target regions in a comparison family have measured volume at most `bound`.

This is the conclusion obtained from a measured common target; keeping it as a
separate predicate makes it easy to state what later IUT-specific constructions
must deliver.
-/
def AllTargetsAtMost (measure : RegionMeasure target)
    (family : RegionComparisonFamily source target index) (bound : Real) : Prop :=
  ∀ choice : index,
    RegionMeasure.targetVolume measure (family.comparison choice) <= bound

/--
A comparison family whose target regions are signed-log upper rays.

Each target is `{x | x.coord <= bound choice}`; see `Region.upperRay` for the
sign convention behind the name.
-/
def upperRayFamily
    (transport : index -> Transport source target) (bound : index -> Real) :
    RegionComparisonFamily source target index :=
  { comparison := fun choice => RegionComparison.upperRay (transport choice) (bound choice) }

theorem upperRayFamily_commonTarget
    (transport : index -> Transport source target) (bound : index -> Real)
    {commonBound : Real} (hbound : ∀ choice : index, bound choice <= commonBound) :
    (upperRayFamily transport bound).CommonTarget
      (Region.upperRay target commonBound) := by
  intro choice
  exact Region.upperRay_subset_upperRay (hbound choice)

def upperRayFamily_commonTargetHull
    (transport : index -> Transport source target) (bound : index -> Real)
    {commonBound : Real} (hbound : ∀ choice : index, bound choice <= commonBound) :
    (upperRayFamily transport bound).CommonTargetHull :=
  { hull := Region.upperRay target commonBound,
    contains_each := upperRayFamily_commonTarget transport bound hbound }

/--
A common target region for a comparison family, together with an upper bound for
the measured volume of that common target.
-/
structure CommonTargetBound (measure : RegionMeasure target)
    (family : RegionComparisonFamily source target index) (bound : Real) where
  common : Region target
  contains_each : family.CommonTarget common
  volume_bound : RegionMeasure.HasVolumeAtMost measure common bound

def upperRayFamily_commonTargetBound
    (measure : RegionMeasure target)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    (transport : index -> Transport source target) (bound : index -> Real)
    {commonBound : Real}
    (hbound : ∀ choice : index, bound choice <= commonBound) :
    CommonTargetBound measure (upperRayFamily transport bound) commonBound :=
  { common := Region.upperRay target commonBound,
    contains_each := upperRayFamily_commonTarget transport bound hbound,
    volume_bound := by
      unfold RegionMeasure.HasVolumeAtMost
      rw [RegionMeasure.upperRay_volume_eq_of_normalized measure hnormalized] }

/--
A common target hull for a comparison family, together with an upper bound for
the measured volume of that hull.
-/
structure CommonTargetHullBound (measure : RegionMeasure target)
    (family : RegionComparisonFamily source target index) (bound : Real) where
  commonHull : family.CommonTargetHull
  volume_bound : RegionMeasure.HasVolumeAtMost measure commonHull.hull bound

def commonTargetHullBoundOfUnionHull
    (measure : RegionMeasure target)
    (family : RegionComparisonFamily source target index)
    (operator : HullOperator target) {bound : Real}
    (hvolume :
      RegionMeasure.HasVolumeAtMost measure
        (operator.hull family.targetUnion) bound) :
    CommonTargetHullBound measure family bound :=
  { commonHull := family.commonTargetHullOfUnionHull operator,
    volume_bound := hvolume }

def commonTargetHullBoundOfUnionSubset
    (measure : RegionMeasure target)
    (family : RegionComparisonFamily source target index)
    (hull : Region target) {bound : Real}
    (hsubset : Region.Subset family.targetUnion hull)
    (hvolume : RegionMeasure.HasVolumeAtMost measure hull bound) :
    CommonTargetHullBound measure family bound :=
  { commonHull := family.commonTargetHullOfUnionSubset hull hsubset,
    volume_bound := hvolume }

def upperRayFamily_commonTargetHullBound
    (measure : RegionMeasure target)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    (transport : index -> Transport source target) (bound : index -> Real)
    {commonBound : Real}
    (hbound : ∀ choice : index, bound choice <= commonBound) :
    CommonTargetHullBound measure (upperRayFamily transport bound) commonBound :=
  { commonHull := upperRayFamily_commonTargetHull transport bound hbound,
    volume_bound := by
      unfold RegionMeasure.HasVolumeAtMost
      change measure.volume (Region.upperRay target commonBound) <= commonBound
      rw [RegionMeasure.upperRay_volume_eq_of_normalized measure hnormalized] }

namespace CommonTargetBound

variable {measure : RegionMeasure target}
variable {family : RegionComparisonFamily source target index}
variable {bound largerBound : Real}

theorem choice_targetVolume_le (data : CommonTargetBound measure family bound)
    (choice : index) :
    RegionMeasure.targetVolume measure (family.comparison choice) <= bound :=
  RegionMeasure.choice_targetVolume_le_common measure data.contains_each choice
    |> fun hle => le_trans hle data.volume_bound

theorem allTargetsAtMost (data : CommonTargetBound measure family bound) :
    AllTargetsAtMost measure family bound :=
  data.choice_targetVolume_le

theorem upperRayFamily_allTargetsAtMost
    (measure : RegionMeasure target)
    (hnormalized : RegionMeasure.NormalizesUpperRays measure)
    (transport : index -> Transport source target) (bound : index -> Real)
    {commonBound : Real}
    (hbound : ∀ choice : index, bound choice <= commonBound) :
    AllTargetsAtMost measure (upperRayFamily transport bound) commonBound :=
  (upperRayFamily_commonTargetBound measure hnormalized transport bound hbound).allTargetsAtMost

theorem choice_region_atMost (data : CommonTargetBound measure family bound)
    (choice : index) :
    RegionMeasure.HasVolumeAtMost measure
      (family.comparison choice).targetRegion bound :=
  data.choice_targetVolume_le choice

theorem holds_common_of_choice (data : CommonTargetBound measure family bound)
    {choice : index} {sourcePoint : Point source}
    (hholds : (family.comparison choice).Holds sourcePoint) :
    (RegionComparison.enlargeTarget (family.comparison choice) data.common).Holds
      sourcePoint :=
  holds_commonTarget_of_choice data.contains_each hholds

def weakenBound (data : CommonTargetBound measure family bound)
    (hle : bound <= largerBound) :
    CommonTargetBound measure family largerBound :=
  { common := data.common,
    contains_each := data.contains_each,
    volume_bound := le_trans data.volume_bound hle }

end CommonTargetBound

namespace CommonTargetHullBound

variable {measure : RegionMeasure target}
variable {family : RegionComparisonFamily source target index}
variable {bound largerBound : Real}

def toCommonTargetBound (data : CommonTargetHullBound measure family bound) :
    CommonTargetBound measure family bound :=
  { common := data.commonHull.hull,
    contains_each := data.commonHull.contains_each,
    volume_bound := data.volume_bound }

theorem choice_targetVolume_le (data : CommonTargetHullBound measure family bound)
    (choice : index) :
    RegionMeasure.targetVolume measure (family.comparison choice) <= bound :=
  data.toCommonTargetBound.choice_targetVolume_le choice

theorem allTargetsAtMost (data : CommonTargetHullBound measure family bound) :
    AllTargetsAtMost measure family bound :=
  data.toCommonTargetBound.allTargetsAtMost

theorem choice_region_atMost (data : CommonTargetHullBound measure family bound)
    (choice : index) :
    RegionMeasure.HasVolumeAtMost measure
      (family.comparison choice).targetRegion bound :=
  data.toCommonTargetBound.choice_region_atMost choice

theorem holds_commonHull_of_choice (data : CommonTargetHullBound measure family bound)
    {choice : index} {sourcePoint : Point source}
    (hholds : (family.comparison choice).Holds sourcePoint) :
    (RegionComparison.enlargeTarget (family.comparison choice) data.commonHull.hull).Holds
      sourcePoint :=
  holds_commonTargetHull_of_choice data.commonHull hholds

def weakenBound (data : CommonTargetHullBound measure family bound)
    (hle : bound <= largerBound) :
    CommonTargetHullBound measure family largerBound :=
  { commonHull := data.commonHull,
    volume_bound := le_trans data.volume_bound hle }

end CommonTargetHullBound

end RegionComparisonFamily

end RealLineCopy
end Iut
