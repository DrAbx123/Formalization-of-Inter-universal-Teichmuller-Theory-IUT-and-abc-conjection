/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.TransportDiagram

/-!
Region-valued comparisons between labeled real-line copies.

This file separates exact equality from indeterminacy-valued membership. In the
IUT III toy model, the exact target `Theta(-2h)` is replaced by the region
`Theta(R_{<= -2h + epsilon})`. Later IUT formalization work will need a richer
notion of hulls and regions; for now, a region is simply a predicate on points of
a labeled real-line copy.
-/

namespace Iut
namespace RealLineCopy

/-- A region in a labeled real-line copy. -/
structure Region (line : Copy) where
  Contains : Point line -> Prop

namespace Region

variable {line : Copy}

/-- Region inclusion, written as pointwise containment. -/
def Subset (small large : Region line) : Prop :=
  ∀ x : Point line, small.Contains x -> large.Contains x

/-- Two regions are extensionally equal when they contain the same points. -/
def ExtEq (left right : Region line) : Prop :=
  ∀ x : Point line, left.Contains x ↔ right.Contains x

def toSet (region : Region line) : Set (Point line) :=
  { x | region.Contains x }

def ofSet (points : Set (Point line)) : Region line :=
  { Contains := fun x => x ∈ points }

/-- The singleton region containing exactly one point. -/
def singleton (x : Point line) : Region line :=
  { Contains := fun y => y.coord = x.coord }

/--
Signed-log upper ray.

In the IUT signed log-volume convention used by this project, membership is
`coord <= bound`. The name "upper ray" follows the source-facing convention
after sign reversal; it is not the ordinary order-theoretic set `{x | bound <= x}`.
-/
def upperRay (line : Copy) (bound : Real) : Region line :=
  { Contains := fun y => y.coord <= bound }

@[simp]
theorem singleton_contains {x y : Point line} :
    (singleton x).Contains y ↔ y.coord = x.coord :=
  Iff.rfl

@[simp]
theorem upperRay_contains {line : Copy} {bound : Real} {y : Point line} :
    (upperRay line bound).Contains y ↔ y.coord <= bound :=
  Iff.rfl

theorem subset_refl (region : Region line) : Subset region region := by
  intro x hx
  exact hx

theorem subset_trans {a b c : Region line} (hab : Subset a b) (hbc : Subset b c) :
    Subset a c := by
  intro x hx
  exact hbc x (hab x hx)

theorem extEq_refl (region : Region line) : ExtEq region region := by
  intro x
  rfl

@[simp]
theorem toSet_mem (region : Region line) (x : Point line) :
    x ∈ region.toSet ↔ region.Contains x :=
  Iff.rfl

@[simp]
theorem ofSet_contains (points : Set (Point line)) (x : Point line) :
    (ofSet points).Contains x ↔ x ∈ points :=
  Iff.rfl

@[simp]
theorem toSet_ofSet (points : Set (Point line)) :
    (ofSet points).toSet = points :=
  rfl

@[simp]
theorem ofSet_toSet_extEq (region : Region line) :
    ExtEq (ofSet region.toSet) region := by
  intro x
  rfl

theorem subset_iff_toSet_subset {small large : Region line} :
    Subset small large ↔ small.toSet ⊆ large.toSet := by
  constructor
  · intro hsubset x hx
    exact hsubset x hx
  · intro hsubset x hx
    exact hsubset hx

theorem extEq_of_subset_of_subset {left right : Region line}
    (hlr : Subset left right) (hrl : Subset right left) : ExtEq left right := by
  intro x
  exact ⟨hlr x, hrl x⟩

theorem contains_of_subset {small large : Region line} (hsubset : Subset small large)
    {x : Point line} (hx : small.Contains x) : large.Contains x :=
  hsubset x hx

theorem singleton_subset_iff {x : Point line} {region : Region line} :
    Subset (singleton x) region ↔ region.Contains x := by
  constructor
  · intro hsubset
    exact hsubset x rfl
  · intro hx y hy
    have hxy : y = x := by
      cases x
      cases y
      simpa using hy
    rw [hxy]
    exact hx

theorem upperRay_subset_upperRay {line : Copy} {smallBound largeBound : Real}
    (hbound : smallBound <= largeBound) :
    Subset (upperRay line smallBound) (upperRay line largeBound) := by
  intro x hx
  exact le_trans hx hbound

theorem upperRay_subset_upperRay_iff {line : Copy} {smallBound largeBound : Real} :
    Subset (upperRay line smallBound) (upperRay line largeBound) ↔
      smallBound <= largeBound := by
  constructor
  · intro hsubset
    exact hsubset (point line smallBound) le_rfl
  · exact upperRay_subset_upperRay

end Region

/--
An abstract hull operation on regions.

This records only the order-theoretic part of IUT III, Remark 3.9.5: a hull
enlarges each region and is monotone with respect to region inclusion.
-/
structure HullOperator (line : Copy) where
  hull : Region line -> Region line
  extensive : ∀ region : Region line, Region.Subset region (hull region)
  monotone : ∀ {small large : Region line},
    Region.Subset small large -> Region.Subset (hull small) (hull large)

namespace HullOperator

variable {line : Copy}

/-- Membership in a region survives passing to its hull. -/
theorem contains_hull (operator : HullOperator line) {region : Region line}
    {x : Point line} (hx : region.Contains x) : (operator.hull region).Contains x :=
  operator.extensive region x hx

/-- Hulls preserve region inclusion. -/
theorem hull_subset_hull (operator : HullOperator line) {small large : Region line}
    (hsubset : Region.Subset small large) :
    Region.Subset (operator.hull small) (operator.hull large) :=
  operator.monotone hsubset

end HullOperator

/-- A family of possible regions, indexed by some type of choices. -/
structure RegionFamily (line : Copy) (index : Type u) where
  region : index -> Region line

namespace RegionFamily

variable {line : Copy} {index : Type u}

/-- The union of all possible regions in a family. -/
def union (family : RegionFamily line index) : Region line :=
  { Contains := fun x => ∃ choice : index, (family.region choice).Contains x }

/-- A region contains every member of a family of possible regions. -/
def ContainedIn (family : RegionFamily line index) (common : Region line) : Prop :=
  ∀ choice : index, Region.Subset (family.region choice) common

theorem choice_subset_union (family : RegionFamily line index) (choice : index) :
    Region.Subset (family.region choice) family.union := by
  intro x hx
  exact ⟨choice, hx⟩

theorem union_subset_iff {family : RegionFamily line index} {common : Region line} :
    Region.Subset family.union common ↔ family.ContainedIn common := by
  constructor
  · intro hsubset choice x hx
    exact hsubset x ⟨choice, hx⟩
  · intro hcontained x hx
    rcases hx with ⟨choice, hchoice⟩
    exact hcontained choice x hchoice

/-- Membership in any chosen possible region implies membership in a common container. -/
theorem contains_common_of_contains_choice {family : RegionFamily line index}
    {common : Region line} (hcommon : family.ContainedIn common)
    {choice : index} {x : Point line} (hx : (family.region choice).Contains x) :
    common.Contains x :=
  hcommon choice x hx

/--
An abstract common hull for a family of possible regions.

This is the family analogue of the extensive part of `HullOperator`: every
possible region is contained in the common hull.
-/
structure CommonHull (family : RegionFamily line index) where
  hull : Region line
  contains_each : family.ContainedIn hull

namespace CommonHull

variable {family : RegionFamily line index}

def ofUnionHull (operator : HullOperator line) (family : RegionFamily line index) :
    CommonHull family :=
  { hull := operator.hull family.union,
    contains_each := fun choice =>
      Region.subset_trans (family.choice_subset_union choice)
        (operator.extensive family.union) }

def ofUnionSubset (family : RegionFamily line index) (hull : Region line)
    (hsubset : Region.Subset family.union hull) : CommonHull family :=
  { hull := hull,
    contains_each := RegionFamily.union_subset_iff.mp hsubset }

theorem union_subset_hull (commonHull : CommonHull family) :
    Region.Subset family.union commonHull.hull :=
  RegionFamily.union_subset_iff.mpr commonHull.contains_each

theorem contains_of_choice (commonHull : CommonHull family)
    {choice : index} {x : Point line} (hx : (family.region choice).Contains x) :
    commonHull.hull.Contains x :=
  commonHull.contains_each choice x hx

/-- Any larger region than a common hull also contains every possible region. -/
def enlarge (commonHull : CommonHull family) {larger : Region line}
    (hsubset : Region.Subset commonHull.hull larger) : CommonHull family :=
  { hull := larger,
    contains_each := fun choice =>
      Region.subset_trans (commonHull.contains_each choice) hsubset }

end CommonHull

end RegionFamily

/-- A named transport together with a target-side region. -/
structure RegionComparison (source target : Copy) where
  transport : Transport source target
  targetRegion : Region target

namespace RegionComparison

variable {source target : Copy}

/-- A source point satisfies a region comparison when its transported image lies in the region. -/
def Holds (comparison : RegionComparison source target) (x : Point source) : Prop :=
  comparison.targetRegion.Contains (Transport.map comparison.transport x)

/-- Exact comparison is region comparison against a singleton target. -/
def exact (transport : Transport source target) (targetPoint : Point target) :
    RegionComparison source target :=
  { transport := transport, targetRegion := Region.singleton targetPoint }

/--
Upper-ray comparison against the signed-log region `{x | x.coord <= bound}`.
See `Region.upperRay` for the sign convention.
-/
def upperRay (transport : Transport source target) (bound : Real) :
    RegionComparison source target :=
  { transport := transport, targetRegion := Region.upperRay target bound }

theorem exact_holds_iff (transport : Transport source target)
    (targetPoint : Point target) (sourcePoint : Point source) :
    Holds (exact transport targetPoint) sourcePoint ↔
      (Transport.map transport sourcePoint).coord = targetPoint.coord :=
  Iff.rfl

theorem upperRay_holds_iff (transport : Transport source target)
    (bound : Real) (sourcePoint : Point source) :
    Holds (upperRay transport bound) sourcePoint ↔
      (Transport.map transport sourcePoint).coord <= bound :=
  Iff.rfl

/-- Enlarge only the target region of a comparison. -/
def enlargeTarget (comparison : RegionComparison source target)
    (larger : Region target) : RegionComparison source target :=
  { transport := comparison.transport, targetRegion := larger }

theorem holds_of_target_subset {comparison : RegionComparison source target}
    {larger : Region target} {sourcePoint : Point source}
    (hsubset : Region.Subset comparison.targetRegion larger)
    (hholds : Holds comparison sourcePoint) :
    Holds (enlargeTarget comparison larger) sourcePoint :=
  hsubset (Transport.map comparison.transport sourcePoint) hholds

/-- Replace the target region by its abstract hull. -/
def hullTarget (operator : HullOperator target)
    (comparison : RegionComparison source target) : RegionComparison source target :=
  { transport := comparison.transport,
    targetRegion := operator.hull comparison.targetRegion }

theorem holds_hullTarget (operator : HullOperator target)
    {comparison : RegionComparison source target} {sourcePoint : Point source}
    (hholds : Holds comparison sourcePoint) :
    Holds (hullTarget operator comparison) sourcePoint :=
  operator.extensive comparison.targetRegion
    (Transport.map comparison.transport sourcePoint) hholds

end RegionComparison

/--
A family of region comparisons sharing a source and target.

This represents a collection of possible comparison outputs produced by an
algorithm, before choosing a specific possibility.
-/
structure RegionComparisonFamily (source target : Copy) (index : Type u) where
  comparison : index -> RegionComparison source target

namespace RegionComparisonFamily

variable {source target : Copy} {index : Type u}

/-- The target-region family underlying a family of comparisons. -/
def targetRegions (family : RegionComparisonFamily source target index) :
    RegionFamily target index :=
  { region := fun choice => (family.comparison choice).targetRegion }

/-- The union of all possible target regions of a comparison family. -/
def targetUnion (family : RegionComparisonFamily source target index) :
    Region target :=
  family.targetRegions.union

/-- A common target region for all comparisons in the family. -/
def CommonTarget (family : RegionComparisonFamily source target index)
    (common : Region target) : Prop :=
  (family.targetRegions).ContainedIn common

/-- Membership for a chosen comparison survives passage to a common target region. -/
theorem holds_commonTarget_of_choice {family : RegionComparisonFamily source target index}
    {common : Region target} (hcommon : family.CommonTarget common)
    {choice : index} {sourcePoint : Point source}
    (hholds : (family.comparison choice).Holds sourcePoint) :
    (RegionComparison.enlargeTarget (family.comparison choice) common).Holds sourcePoint :=
  RegionComparison.holds_of_target_subset (hcommon choice) hholds

/-- A common hull for the target regions of a comparison family. -/
abbrev CommonTargetHull (family : RegionComparisonFamily source target index) :=
  RegionFamily.CommonHull family.targetRegions

def commonTargetHullOfUnionHull
    (operator : HullOperator target)
    (family : RegionComparisonFamily source target index) :
    family.CommonTargetHull :=
  RegionFamily.CommonHull.ofUnionHull operator family.targetRegions

def commonTargetHullOfUnionSubset
    (family : RegionComparisonFamily source target index)
    (hull : Region target)
    (hsubset : Region.Subset family.targetUnion hull) :
    family.CommonTargetHull :=
  RegionFamily.CommonHull.ofUnionSubset family.targetRegions hull hsubset

theorem holds_commonTargetHull_of_choice {family : RegionComparisonFamily source target index}
    (commonHull : family.CommonTargetHull)
    {choice : index} {sourcePoint : Point source}
    (hholds : (family.comparison choice).Holds sourcePoint) :
    (RegionComparison.enlargeTarget (family.comparison choice) commonHull.hull).Holds
      sourcePoint :=
  RegionComparison.holds_of_target_subset (commonHull.contains_each choice) hholds

end RegionComparisonFamily

end RealLineCopy
end Iut
