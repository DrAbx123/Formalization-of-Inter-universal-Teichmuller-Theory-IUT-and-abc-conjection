/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Germ
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.IntermediateValue
import Iut.Foundations.SourceAutHolomorphic

/-!
# Archimedean Aut-holomorphic semi-germs

This module constructs the complex analytic semi-germ surrounding
`S^1 \subset \mathbb C^\times` in IUT III, Remark 1.1.1(ii).  Its levels are
actual open annuli, its transition maps are inclusions, and their intersection
is exactly the unit circle.  The holomorphic and group structures below are
restrictions of the ambient structures on `\mathbb C^\times`.
-/

open CategoryTheory
open scoped Topology

namespace Iut

noncomputable section

namespace SourceAutHolomorphicSemiGerm

open Set

/-- The pointwise unit core `S^1 \subset \mathbb C`. -/
def unitCircle : Set ℂ :=
  Metric.sphere 0 1

theorem mem_unitCircle_iff (value : ℂ) :
    value ∈ unitCircle ↔ ‖value‖ = 1 := by
  simp [unitCircle]

/-- The radius of the `n`-th neighborhood in the semi-germ system. -/
def radius (n : ℕ) : ℝ :=
  1 / (n + 1 : ℝ)

theorem radius_pos (n : ℕ) : 0 < radius n := by
  apply one_div_pos.mpr
  exact_mod_cast Nat.succ_pos n

theorem radius_le_one (n : ℕ) : radius n ≤ 1 := by
  rw [radius]
  apply (div_le_one₀ ?_).mpr
  · exact_mod_cast Nat.succ_pos n
  · exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

theorem radius_antitone : Antitone radius := by
  intro n m hnm
  rw [radius, radius]
  gcongr

/-- The explicit open annulus of norm-distance less than `1/(n+1)` from `S^1`. -/
def neighborhood (n : ℕ) : Set ℂ :=
  {value | |‖value‖ - 1| < radius n}

theorem isOpen_neighborhood (n : ℕ) : IsOpen (neighborhood n) := by
  exact isOpen_lt ((continuous_norm.sub continuous_const).abs) continuous_const

theorem unitCircle_subset_neighborhood (n : ℕ) :
    unitCircle ⊆ neighborhood n := by
  intro value hvalue
  rw [mem_unitCircle_iff] at hvalue
  simp [neighborhood, hvalue, radius_pos]

theorem zero_not_mem_neighborhood (n : ℕ) :
    (0 : ℂ) ∉ neighborhood n := by
  intro hzero
  have : (1 : ℝ) < radius n := by
    simpa [neighborhood] using hzero
  exact (not_lt_of_ge (radius_le_one n)) this

theorem neighborhood_antitone : Antitone neighborhood := by
  intro n m hnm value hvalue
  exact lt_of_lt_of_le hvalue (radius_antitone hnm)

/-- The topological space at a level of the semi-germ. -/
abbrev Level (n : ℕ) :=
  neighborhood n

/-- Restriction from a smaller annulus to a larger annulus. -/
def restriction {n m : ℕ} (hnm : n ≤ m) :
    C(Level m, Level n) where
  toFun value := ⟨value, neighborhood_antitone hnm value.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem restriction_apply {n m : ℕ} (hnm : n ≤ m)
    (value : Level m) :
    (restriction hnm value : ℂ) = value :=
  rfl

/-- The annuli form a projective system in topological spaces. -/
def neighborhoodSystem : ℕᵒᵖ ⥤ TopCat where
  obj n := TopCat.of (Level n.unop)
  map f := TopCat.ofHom (restriction (leOfHom f.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The annulus system is arbitrarily small: its common core is exactly `S^1`. -/
theorem iInter_neighborhood_eq_unitCircle :
    ⋂ n : ℕ, neighborhood n = unitCircle := by
  ext value
  simp only [mem_iInter]
  constructor
  · intro hvalue
    rw [mem_unitCircle_iff]
    by_contra hnorm
    have hdiff : 0 < |‖value‖ - 1| :=
      abs_pos.mpr (sub_ne_zero.mpr hnorm)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdiff
    have hlevel := hvalue n
    change |‖value‖ - 1| < 1 / (n + 1 : ℝ) at hlevel
    exact (not_lt_of_ge hn.le) hlevel
  · intro hvalue n
    exact unitCircle_subset_neighborhood n hvalue

/-- Mathlib's `Circle` is exactly the unit core of the semi-germ. -/
def circleEquivUnitCore : Circle ≃ unitCircle where
  toFun unit := ⟨unit, (mem_unitCircle_iff _).mpr unit.norm_coe⟩
  invFun value :=
    ⟨value, by
      change (value : ℂ) ∈ (↑(Submonoid.unitSphere ℂ) : Set ℂ)
      rw [Submonoid.coe_unitSphere]
      exact mem_sphere_zero_iff_norm.mpr
        ((mem_unitCircle_iff value).mp value.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem circleEquivUnitCore_apply_coe (unit : Circle) :
    (circleEquivUnitCore unit : ℂ) = unit :=
  rfl

/-- Radial projection of a nonzero complex number onto the unit core. -/
def radialUnit (value : ℂ) (hvalue : value ≠ 0) : unitCircle :=
  ⟨value / (‖value‖ : ℂ), by
    rw [mem_unitCircle_iff, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg value)]
    exact div_self (norm_ne_zero_iff.mpr hvalue)⟩

theorem dist_radialUnit (value : ℂ) (hvalue : value ≠ 0) :
    dist value (radialUnit value hvalue : ℂ) = |‖value‖ - 1| := by
  rw [dist_eq_norm]
  change ‖value - value / (‖value‖ : ℂ)‖ = |‖value‖ - 1|
  calc
    ‖value - value / (‖value‖ : ℂ)‖ =
        ‖((‖value‖ : ℂ) - 1) * (value / (‖value‖ : ℂ))‖ := by
      congr 1
      have hnorm : (‖value‖ : ℂ) ≠ 0 := by
        exact_mod_cast norm_ne_zero_iff.mpr hvalue
      field_simp [hnorm]
    _ = |‖value‖ - 1| := by
      have hreal :
          ((‖value‖ : ℂ) - 1) = ((‖value‖ - 1 : ℝ) : ℂ) := by
        norm_num
      have hunitnorm : ‖value / (‖value‖ : ℂ)‖ = 1 := by
        exact (mem_unitCircle_iff _).mp (radialUnit value hvalue).2
      rw [norm_mul, hunitnorm, mul_one, hreal,
        Complex.norm_real, Real.norm_eq_abs]

/-! ## Restricted Aut-holomorphic and group structures -/

/-- Holomorphicity at a level is induced from the ambient complex structure. -/
def IsHolomorphicAtLevel (n : ℕ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (neighborhood n)

theorem IsHolomorphicAtLevel.of_le
    {n m : ℕ} {f : ℂ → ℂ} (h : IsHolomorphicAtLevel n f)
    (hnm : n ≤ m) :
    IsHolomorphicAtLevel m f :=
  DifferentiableOn.mono h (neighborhood_antitone hnm)

theorem isHolomorphicAtLevel_id (n : ℕ) :
    IsHolomorphicAtLevel n id :=
  differentiable_id.differentiableOn

/-- Ambient complex multiplication whose restriction supplies the group germ. -/
def multiplication (value : ℂ × ℂ) : ℂ :=
  value.1 * value.2

theorem multiplication_differentiable : Differentiable ℂ multiplication := by
  exact differentiable_fst.mul differentiable_snd

theorem multiplication_holomorphicOn_levels (n m : ℕ) :
    DifferentiableOn ℂ multiplication
      (neighborhood n ×ˢ neighborhood m) :=
  multiplication_differentiable.differentiableOn

/-- Ambient complex inversion whose restriction supplies the inverse germ. -/
def inversion (value : ℂ) : ℂ :=
  value⁻¹

theorem inversion_holomorphicAtLevel (n : ℕ) :
    IsHolomorphicAtLevel n inversion := by
  intro value hvalue
  exact differentiableAt_inv (fun hzero =>
    zero_not_mem_neighborhood n (hzero ▸ hvalue) : value ≠ 0) |>.differentiableWithinAt

theorem multiplication_maps_unitCircle :
    Set.MapsTo multiplication (unitCircle ×ˢ unitCircle) unitCircle := by
  rintro ⟨first, second⟩ ⟨hfirst, hsecond⟩
  rw [mem_unitCircle_iff, multiplication, norm_mul,
    (mem_unitCircle_iff _).mp hfirst, (mem_unitCircle_iff _).mp hsecond,
    one_mul]

theorem inversion_maps_unitCircle :
    Set.MapsTo inversion unitCircle unitCircle := by
  intro value hvalue
  rw [mem_unitCircle_iff, inversion, norm_inv,
    (mem_unitCircle_iff _).mp hvalue, inv_one]

/-- The neighborhood filter of the unit core. -/
def unitNeighborhoodFilter : Filter ℂ :=
  nhdsSet unitCircle

theorem neighborhood_mem_unitNeighborhoodFilter (n : ℕ) :
    neighborhood n ∈ unitNeighborhoodFilter :=
  (isOpen_neighborhood n).mem_nhdsSet.mpr
    (unitCircle_subset_neighborhood n)

/--
The explicit annuli are cofinal among all neighborhoods of the unit core.
Thus the projective system is arbitrarily small in the topological sense, not
merely a decreasing family with the correct intersection.
-/
theorem exists_neighborhood_subset_of_mem
    {region : Set ℂ} (hregion : region ∈ unitNeighborhoodFilter) :
    ∃ n : ℕ, neighborhood n ⊆ region := by
  obtain ⟨ε, hε, hthickening⟩ :=
    (Metric.mem_nhdsSet_iff (isCompact_sphere (0 : ℂ) 1)).mp hregion
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have hradius : radius n < ε := by
    simpa [radius] using hn
  refine ⟨n, fun value hvalue ↦ hthickening ?_⟩
  have hzero : value ≠ 0 := by
    intro hvalueZero
    exact zero_not_mem_neighborhood n (hvalueZero ▸ hvalue)
  rw [Metric.mem_thickening_iff_exists_edist_lt]
  refine ⟨radialUnit value hzero, (radialUnit value hzero).2, ?_⟩
  rw [edist_lt_ofReal, dist_radialUnit]
  exact hvalue.trans hradius

/-- Multiplication preserves the neighborhood germ of the unit core. -/
theorem multiplication_tendsto_unitNeighborhoodFilter :
    Filter.Tendsto multiplication
      (nhdsSet (unitCircle ×ˢ unitCircle)) unitNeighborhoodFilter :=
  multiplication_differentiable.continuous.tendsto_nhdsSet
    multiplication_maps_unitCircle

/-- Inversion preserves the neighborhood germ of the unit core. -/
theorem inversion_tendsto_unitNeighborhoodFilter :
    Filter.Tendsto inversion unitNeighborhoodFilter unitNeighborhoodFilter := by
  apply (inversion_holomorphicAtLevel 0).continuousOn.tendsto_nhdsSet
    (neighborhood_mem_unitNeighborhoodFilter 0)
  exact inversion_maps_unitCircle

/- The ambient operation germs below are morphisms of the verified filters. -/

/-- The ambient multiplication as a germ along `S^1 × S^1`. -/
def multiplicationGerm :
    Filter.Germ (nhdsSet (unitCircle ×ˢ unitCircle)) ℂ :=
  multiplication

/-- The ambient inversion as a germ along `S^1`. -/
def inversionGerm : Filter.Germ unitNeighborhoodFilter ℂ :=
  inversion

theorem multiplication_assoc
    (first second third : ℂ) :
    multiplication (multiplication (first, second), third) =
      multiplication (first, multiplication (second, third)) := by
  simp [multiplication, mul_assoc]

theorem multiplication_one_left (value : ℂ) :
    multiplication (1, value) = value := by
  simp [multiplication]

theorem multiplication_one_right (value : ℂ) :
    multiplication (value, 1) = value := by
  simp [multiplication]

theorem multiplication_inversion_left
    {value : ℂ} (hvalue : value ≠ 0) :
    multiplication (inversion value, value) = 1 := by
  simp [multiplication, inversion, hvalue]

theorem multiplication_inversion_right
    {value : ℂ} (hvalue : value ≠ 0) :
    multiplication (value, inversion value) = 1 := by
  simp [multiplication, inversion, hvalue]

/-! ## The two components of a punctured annulus -/

/-- Polar multiplication by a nonnegative radius. -/
def polarMap (value : ℝ × Circle) : ℂ :=
  (value.1 : ℂ) * value.2

theorem polarMap_continuous : Continuous polarMap := by
  exact (Complex.continuous_ofReal.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

theorem norm_polarMap
    (value : ℝ × Circle) (hradius : 0 ≤ value.1) :
    ‖polarMap value‖ = value.1 := by
  simp [polarMap, abs_of_nonneg hradius]

/-- A radial open band in the punctured complex plane. -/
def radialBand (lower upper : ℝ) : Set ℂ :=
  {value | lower < ‖value‖ ∧ ‖value‖ < upper}

theorem polarMap_image_Ioo
    {lower upper : ℝ} (hlower : 0 ≤ lower) :
    polarMap '' (Set.Ioo lower upper ×ˢ (Set.univ : Set Circle)) =
      radialBand lower upper := by
  ext value
  constructor
  · rintro ⟨⟨radiusValue, unit⟩, ⟨hradius, -⟩, rfl⟩
    change lower < ‖polarMap (radiusValue, unit)‖ ∧
      ‖polarMap (radiusValue, unit)‖ < upper
    rw [norm_polarMap _ (hlower.trans hradius.1.le)]
    exact hradius
  · intro hvalue
    have hradius : 0 < ‖value‖ := hlower.trans_lt hvalue.1
    let unit : Circle :=
      ⟨value / (‖value‖ : ℂ), by
        change value / (‖value‖ : ℂ) ∈
          (↑(Submonoid.unitSphere ℂ) : Set ℂ)
        rw [Submonoid.coe_unitSphere]
        apply mem_sphere_zero_iff_norm.mpr
        rw [norm_div]
        simp [hradius.ne']⟩
    refine ⟨(‖value‖, unit), ⟨hvalue, Set.mem_univ unit⟩, ?_⟩
    change (‖value‖ : ℂ) * (value / (‖value‖ : ℂ)) = value
    rw [mul_comm, div_mul_cancel₀]
    exact_mod_cast hradius.ne'

theorem radialBand_isPreconnected
    {lower upper : ℝ} (hlower : 0 ≤ lower) :
    IsPreconnected (radialBand lower upper) := by
  rw [← polarMap_image_Ioo hlower]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image
    polarMap polarMap_continuous.continuousOn

/-- The part of the annulus selected by `O^triangleright_C \ S^1`. -/
def innerSide (n : ℕ) : Set ℂ :=
  radialBand (1 - radius n) 1

/-- The other component of the complement of the unit circle. -/
def outerSide (n : ℕ) : Set ℂ :=
  radialBand 1 (1 + radius n)

theorem one_sub_radius_nonneg (n : ℕ) :
    0 ≤ 1 - radius n :=
  sub_nonneg.mpr (radius_le_one n)

theorem innerSide_isPreconnected (n : ℕ) :
    IsPreconnected (innerSide n) :=
  radialBand_isPreconnected (one_sub_radius_nonneg n)

theorem outerSide_isPreconnected (n : ℕ) :
    IsPreconnected (outerSide n) :=
  radialBand_isPreconnected zero_le_one

theorem neighborhood_eq_radialBand (n : ℕ) :
    neighborhood n = radialBand (1 - radius n) (1 + radius n) := by
  ext value
  constructor
  · intro hvalue
    change |‖value‖ - 1| < radius n at hvalue
    change 1 - radius n < ‖value‖ ∧ ‖value‖ < 1 + radius n
    rcases abs_lt.mp hvalue with ⟨hlower, hupper⟩
    constructor <;> linarith
  · intro hvalue
    change 1 - radius n < ‖value‖ ∧ ‖value‖ < 1 + radius n at hvalue
    change |‖value‖ - 1| < radius n
    apply abs_lt.mpr
    constructor <;> linarith

/-- The complement of the unit core inside a level. -/
def puncturedNeighborhood (n : ℕ) : Set ℂ :=
  neighborhood n \ unitCircle

theorem puncturedNeighborhood_eq_inner_union_outer (n : ℕ) :
    puncturedNeighborhood n = innerSide n ∪ outerSide n := by
  rw [puncturedNeighborhood, neighborhood_eq_radialBand]
  ext value
  simp only [Set.mem_diff, Set.mem_union, radialBand, Set.mem_setOf_eq,
    mem_unitCircle_iff]
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hunit⟩
    rcases lt_or_gt_of_ne hunit with hinner | houter
    · exact Or.inl ⟨hlower, hinner⟩
    · exact Or.inr ⟨houter, hupper⟩
  · rintro (hinner | houter)
    · exact ⟨⟨hinner.1, hinner.2.trans (lt_add_of_pos_right 1 (radius_pos n))⟩,
        hinner.2.ne⟩
    · exact ⟨⟨(sub_lt_self 1 (radius_pos n)).trans houter.1, houter.2⟩,
        houter.1.ne'⟩

theorem innerSide_disjoint_outerSide (n : ℕ) :
    Disjoint (innerSide n) (outerSide n) := by
  rw [Set.disjoint_left]
  intro value hinner houter
  exact (lt_asymm hinner.2 houter.1)

theorem innerSide_subset_puncturedNeighborhood (n : ℕ) :
    innerSide n ⊆ puncturedNeighborhood n := by
  rw [puncturedNeighborhood_eq_inner_union_outer]
  exact Set.subset_union_left

theorem outerSide_subset_puncturedNeighborhood (n : ℕ) :
    outerSide n ⊆ puncturedNeighborhood n := by
  rw [puncturedNeighborhood_eq_inner_union_outer]
  exact Set.subset_union_right

/-- A canonical point in the selected inner component. -/
def innerBasepoint (n : ℕ) : ℂ :=
  (1 - radius n / 2 : ℝ)

/-- A canonical point in the outer component. -/
def outerBasepoint (n : ℕ) : ℂ :=
  (1 + radius n / 2 : ℝ)

theorem innerBasepoint_mem_innerSide (n : ℕ) :
    innerBasepoint n ∈ innerSide n := by
  have hradius := radius_pos n
  have hbase : 0 ≤ 1 - radius n / 2 := by
    have := radius_le_one n
    linarith
  change 1 - radius n < ‖innerBasepoint n‖ ∧
    ‖innerBasepoint n‖ < 1
  rw [innerBasepoint]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hbase]
  constructor <;> linarith

theorem outerBasepoint_mem_outerSide (n : ℕ) :
    outerBasepoint n ∈ outerSide n := by
  have hradius := radius_pos n
  change 1 < ‖outerBasepoint n‖ ∧
    ‖outerBasepoint n‖ < 1 + radius n
  rw [outerBasepoint]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  constructor <;> linarith

/-- The selected side as a subset of the punctured level. -/
def innerComponentSet (n : ℕ) : Set (puncturedNeighborhood n) :=
  {value | ‖(value : ℂ)‖ < 1}

/-- The unselected side as a subset of the punctured level. -/
def outerComponentSet (n : ℕ) : Set (puncturedNeighborhood n) :=
  {value | 1 < ‖(value : ℂ)‖}

theorem innerComponentSet_compl_eq_outerComponentSet (n : ℕ) :
    (innerComponentSet n)ᶜ = outerComponentSet n := by
  ext value
  simp only [innerComponentSet, outerComponentSet, Set.mem_compl_iff,
    Set.mem_setOf_eq]
  have hne : ‖(value : ℂ)‖ ≠ 1 :=
    (mem_unitCircle_iff _).not.mp value.2.2
  constructor
  · intro hnot
    rcases lt_or_gt_of_ne hne with hless | hgreater
    · exact False.elim (hnot hless)
    · exact hgreater
  · intro hgreater hless
    exact lt_asymm hless hgreater

theorem innerComponentSet_isClopen (n : ℕ) :
    IsClopen (innerComponentSet n) := by
  have hopen : IsOpen (innerComponentSet n) :=
    isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  refine ⟨?_, hopen⟩
  apply isOpen_compl_iff.mp
  rw [innerComponentSet_compl_eq_outerComponentSet]
  exact isOpen_lt continuous_const
    (continuous_norm.comp continuous_subtype_val)

theorem outerComponentSet_isClopen (n : ℕ) :
    IsClopen (outerComponentSet n) := by
  rw [← innerComponentSet_compl_eq_outerComponentSet]
  exact (innerComponentSet_isClopen n).compl

/-- The selected side is literally one connected component of the complement. -/
theorem innerSide_eq_connectedComponentIn (n : ℕ) :
    innerSide n =
      connectedComponentIn (puncturedNeighborhood n) (innerBasepoint n) := by
  apply Set.Subset.antisymm
  · exact (innerSide_isPreconnected n).subset_connectedComponentIn
      (innerBasepoint_mem_innerSide n)
      (innerSide_subset_puncturedNeighborhood n)
  · have hbasePunctured :
        innerBasepoint n ∈ puncturedNeighborhood n :=
      innerSide_subset_puncturedNeighborhood n
        (innerBasepoint_mem_innerSide n)
    rw [connectedComponentIn_eq_image hbasePunctured]
    rintro value ⟨valueInPunctured, hcomponent, rfl⟩
    have hbaseInner :
        (⟨innerBasepoint n, hbasePunctured⟩ : puncturedNeighborhood n) ∈
          innerComponentSet n :=
      (innerBasepoint_mem_innerSide n).2
    have hinner :=
      (innerComponentSet_isClopen n).connectedComponent_subset
        hbaseInner hcomponent
    have hneighborhood := valueInPunctured.2.1
    rw [neighborhood_eq_radialBand] at hneighborhood
    exact ⟨hneighborhood.1, hinner⟩

/-- The unselected side is the other connected component of the complement. -/
theorem outerSide_eq_connectedComponentIn (n : ℕ) :
    outerSide n =
      connectedComponentIn (puncturedNeighborhood n) (outerBasepoint n) := by
  apply Set.Subset.antisymm
  · exact (outerSide_isPreconnected n).subset_connectedComponentIn
      (outerBasepoint_mem_outerSide n)
      (outerSide_subset_puncturedNeighborhood n)
  · have hbasePunctured :
        outerBasepoint n ∈ puncturedNeighborhood n :=
      outerSide_subset_puncturedNeighborhood n
        (outerBasepoint_mem_outerSide n)
    rw [connectedComponentIn_eq_image hbasePunctured]
    rintro value ⟨valueInPunctured, hcomponent, rfl⟩
    have hbaseOuter :
        (⟨outerBasepoint n, hbasePunctured⟩ : puncturedNeighborhood n) ∈
          outerComponentSet n :=
      (outerBasepoint_mem_outerSide n).1
    have houter :=
      (outerComponentSet_isClopen n).connectedComponent_subset
        hbaseOuter hcomponent
    have hneighborhood := valueInPunctured.2.1
    rw [neighborhood_eq_radialBand] at hneighborhood
    exact ⟨houter, hneighborhood.2⟩

/-! ## The `Aut_hol` assignment on the projective system -/

/-- Every annular level is a connected complex open in the sense of
Absolute Anabelian Topics III, Definition 2.1. -/
def levelConnectedOpen (n : ℕ) :
    SourceAutHolomorphic.ConnectedOpen where
  carrier := neighborhood n
  isOpen_carrier := isOpen_neighborhood n
  isConnected_carrier := by
    constructor
    · refine ⟨1, unitCircle_subset_neighborhood n ?_⟩
      rw [mem_unitCircle_iff]
      simp
    · rw [neighborhood_eq_radialBand]
      exact radialBand_isPreconnected (one_sub_radius_nonneg n)

/-- The actual group `Aut_hol(U_n)` assigned to the `n`-th annulus. -/
abbrev levelAutHolomorphic (n : ℕ) :=
  SourceAutHolomorphic.AutHolomorphic (levelConnectedOpen n)

/-- Inclusion of a smaller annulus into a larger annulus. -/
def levelInclusion {n m : ℕ} (hnm : n ≤ m) :
    (levelConnectedOpen m).carrier → (levelConnectedOpen n).carrier :=
  fun value ↦ ⟨value, neighborhood_antitone hnm value.2⟩

/-- Annular transition inclusions are restrictions of the holomorphic identity
map on the ambient complex plane. -/
theorem levelInclusion_hasAmbientHolomorphicLift
    {n m : ℕ} (hnm : n ≤ m) :
    SourceAutHolomorphic.HasAmbientHolomorphicLift
      (levelConnectedOpen m) (levelConnectedOpen n) (levelInclusion hnm) := by
  refine ⟨id, differentiable_id.differentiableOn, ?_⟩
  intro value
  rfl

@[simp]
theorem levelInclusion_comp
    {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k)
    (value : (levelConnectedOpen k).carrier) :
    levelInclusion hnm (levelInclusion hmk value) =
      levelInclusion (hnm.trans hmk) value :=
  rfl

/-- The `m`-th level regarded as a connected open restriction domain in the
`n`-th level. -/
def levelRestrictionDomain {n m : ℕ} (hnm : n ≤ m) :
    SourceAutHolomorphic.AutHolomorphic.RestrictionDomain
      (levelConnectedOpen n) where
  openSubset := levelConnectedOpen m
  inclusion := neighborhood_antitone hnm

/-- A level automorphism can be restricted precisely when it preserves the
smaller annulus in both directions. -/
def PreservesSmallerLevel
    {n m : ℕ} (hnm : n ≤ m)
    (automorphism : levelAutHolomorphic n) : Prop :=
  SourceAutHolomorphic.AutHolomorphic.Preserves
    (levelRestrictionDomain hnm) automorphism

/-- Restriction along the annular projective system. -/
def restrictToLevel
    {n m : ℕ} (hnm : n ≤ m)
    (automorphism : levelAutHolomorphic n)
    (hpreserves : PreservesSmallerLevel hnm automorphism) :
    levelAutHolomorphic m :=
  SourceAutHolomorphic.AutHolomorphic.restrict
    (levelRestrictionDomain hnm) automorphism hpreserves

theorem levelIdentity_preserves
    {n m : ℕ} (hnm : n ≤ m) :
    PreservesSmallerLevel hnm
      (SourceAutHolomorphic.AutHolomorphic.identity (levelConnectedOpen n)) :=
  SourceAutHolomorphic.AutHolomorphic.identity_preserves
    (levelRestrictionDomain hnm)

@[simp]
theorem restrictToLevel_identity
    {n m : ℕ} (hnm : n ≤ m) :
    restrictToLevel hnm
        (SourceAutHolomorphic.AutHolomorphic.identity (levelConnectedOpen n))
        (levelIdentity_preserves hnm) =
      SourceAutHolomorphic.AutHolomorphic.identity (levelConnectedOpen m) :=
  SourceAutHolomorphic.AutHolomorphic.restrict_identity
    (levelRestrictionDomain hnm)

theorem preservesSmallerLevel_mul
    {n m : ℕ} (hnm : n ≤ m)
    (first second : levelAutHolomorphic n)
    (hfirst : PreservesSmallerLevel hnm first)
    (hsecond : PreservesSmallerLevel hnm second) :
    PreservesSmallerLevel hnm (first * second) :=
  SourceAutHolomorphic.AutHolomorphic.mul_preserves
    (levelRestrictionDomain hnm) first second hfirst hsecond

theorem preservesSmallerLevel_inv
    {n m : ℕ} (hnm : n ≤ m)
    (automorphism : levelAutHolomorphic n)
    (hpreserves : PreservesSmallerLevel hnm automorphism) :
    PreservesSmallerLevel hnm automorphism⁻¹ :=
  SourceAutHolomorphic.AutHolomorphic.inv_preserves
    (levelRestrictionDomain hnm) automorphism hpreserves

@[simp]
theorem restrictToLevel_mul
    {n m : ℕ} (hnm : n ≤ m)
    (first second : levelAutHolomorphic n)
    (hfirst : PreservesSmallerLevel hnm first)
    (hsecond : PreservesSmallerLevel hnm second) :
    restrictToLevel hnm (first * second)
        (preservesSmallerLevel_mul hnm first second hfirst hsecond) =
      restrictToLevel hnm first hfirst * restrictToLevel hnm second hsecond :=
  SourceAutHolomorphic.AutHolomorphic.restrict_mul
    (levelRestrictionDomain hnm) first second hfirst hsecond

@[simp]
theorem restrictToLevel_inv
    {n m : ℕ} (hnm : n ≤ m)
    (automorphism : levelAutHolomorphic n)
    (hpreserves : PreservesSmallerLevel hnm automorphism) :
    restrictToLevel hnm automorphism⁻¹
        (preservesSmallerLevel_inv hnm automorphism hpreserves) =
      (restrictToLevel hnm automorphism hpreserves)⁻¹ :=
  SourceAutHolomorphic.AutHolomorphic.restrict_inv
    (levelRestrictionDomain hnm) automorphism hpreserves

end SourceAutHolomorphicSemiGerm

end

end Iut
