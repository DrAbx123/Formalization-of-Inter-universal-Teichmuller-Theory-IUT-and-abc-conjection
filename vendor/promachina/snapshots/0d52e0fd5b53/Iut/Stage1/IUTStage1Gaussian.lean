/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1StepX

/-!
Gaussian and Hodge--Arakelov theta-evaluation shadows for Stage 1.

This module is a mechanical extraction from `Iut.Stage1.IUTStage1Source`.  It
keeps weighted label averages, `ZMod` square-weight profiles, Gaussian monoid
degree evaluations, Hodge--Arakelov theta-value/evaluation source objects, and
the finite procession-average identities that feed the later Hodge/SHE transport
boundary.
-/

namespace Iut
namespace Stage1

open RealLineCopy
open scoped BigOperators

universe u v w x

namespace IUTStage1WeightedLabelAveragedProcessionLogVolume

variable {label : Type u} [Fintype label]

theorem weightTotal_eq
    (data : IUTStage1WeightedLabelAveragedProcessionLogVolume label) :
    data.weightTotal = Finset.univ.sum data.weight :=
  data.weightTotal_eq_sum

theorem weightedAverage_eq_formula
    (data : IUTStage1WeightedLabelAveragedProcessionLogVolume label) :
    data.weightedAverageLogVolume =
      (Finset.univ.sum fun j => data.weight j * data.normalizedLogVolume j) /
        data.weightTotal :=
  data.weighted_average_eq

theorem weightedAverage_eq_of_pointwise
    {data₁ data₂ : IUTStage1WeightedLabelAveragedProcessionLogVolume label}
    (hweight : ∀ j : label, data₁.weight j = data₂.weight j)
    (hnormalized :
      ∀ j : label,
        data₁.normalizedLogVolume j =
          data₂.normalizedLogVolume j)
    (htotal : data₁.weightTotal = data₂.weightTotal) :
    data₁.weightedAverageLogVolume =
      data₂.weightedAverageLogVolume := by
  calc
    data₁.weightedAverageLogVolume =
        (Finset.univ.sum fun j =>
            data₁.weight j * data₁.normalizedLogVolume j) /
          data₁.weightTotal :=
      data₁.weighted_average_eq
    _ =
        (Finset.univ.sum fun j =>
            data₂.weight j * data₂.normalizedLogVolume j) /
          data₂.weightTotal := by
      rw [htotal]
      congr 1
      exact Finset.sum_congr rfl (by
        intro j _hj
        rw [hweight j, hnormalized j])
    _ = data₂.weightedAverageLogVolume :=
      data₂.weighted_average_eq.symm

theorem const_le_weightedAverage_of_forall_le
    (data : IUTStage1WeightedLabelAveragedProcessionLogVolume label)
    {c : Real}
    (hweight_nonnegative : ∀ j : label, 0 <= data.weight j)
    (hpointwise : ∀ j : label, c <= data.normalizedLogVolume j) :
    c <= data.weightedAverageLogVolume := by
  rw [data.weighted_average_eq]
  rw [le_div_iff₀ data.positive_weightTotal]
  have hsum :
      Finset.univ.sum (fun j : label => data.weight j * c) <=
        Finset.univ.sum
          (fun j : label => data.weight j * data.normalizedLogVolume j) := by
    exact Finset.sum_le_sum (by
      intro j _hj
      exact mul_le_mul_of_nonneg_left (hpointwise j) (hweight_nonnegative j))
  have hleft :
      c * data.weightTotal =
        Finset.univ.sum (fun j : label => data.weight j * c) := by
    rw [data.weightTotal_eq_sum, mul_comm c, Finset.sum_mul]
  calc
    c * data.weightTotal =
        Finset.univ.sum (fun j : label => data.weight j * c) :=
      hleft
    _ <=
        Finset.univ.sum
          (fun j : label => data.weight j * data.normalizedLogVolume j) :=
      hsum

theorem weightedAverage_le_const_of_forall_le
    (data : IUTStage1WeightedLabelAveragedProcessionLogVolume label)
    {c : Real}
    (hweight_nonnegative : ∀ j : label, 0 <= data.weight j)
    (hpointwise : ∀ j : label, data.normalizedLogVolume j <= c) :
    data.weightedAverageLogVolume <= c := by
  rw [data.weighted_average_eq]
  rw [div_le_iff₀ data.positive_weightTotal]
  have hsum :
      Finset.univ.sum
          (fun j : label => data.weight j * data.normalizedLogVolume j) <=
        Finset.univ.sum (fun j : label => data.weight j * c) := by
    exact Finset.sum_le_sum (by
      intro j _hj
      exact mul_le_mul_of_nonneg_left (hpointwise j) (hweight_nonnegative j))
  have hright :
      Finset.univ.sum (fun j : label => data.weight j * c) =
        c * data.weightTotal := by
    rw [data.weightTotal_eq_sum,
      mul_comm c (Finset.univ.sum data.weight), Finset.sum_mul]
  calc
    Finset.univ.sum
        (fun j : label => data.weight j * data.normalizedLogVolume j) <=
        Finset.univ.sum (fun j : label => data.weight j * c) :=
      hsum
    _ = c * data.weightTotal :=
      hright

theorem weightedAverage_le_const_of_weighted_summand_le
    (data : IUTStage1WeightedLabelAveragedProcessionLogVolume label)
    {c : Real}
    (hsummand :
      ∀ j : label, data.weight j * data.normalizedLogVolume j <=
        data.weight j * c) :
    data.weightedAverageLogVolume <= c := by
  rw [data.weighted_average_eq]
  rw [div_le_iff₀ data.positive_weightTotal]
  have hsum :
      Finset.univ.sum
          (fun j : label => data.weight j * data.normalizedLogVolume j) <=
        Finset.univ.sum (fun j : label => data.weight j * c) :=
    Finset.sum_le_sum (by
      intro j _hj
      exact hsummand j)
  have hright :
      Finset.univ.sum (fun j : label => data.weight j * c) =
        c * data.weightTotal := by
    rw [data.weightTotal_eq_sum,
      mul_comm c (Finset.univ.sum data.weight), Finset.sum_mul]
  calc
    Finset.univ.sum
        (fun j : label => data.weight j * data.normalizedLogVolume j) <=
        Finset.univ.sum (fun j : label => data.weight j * c) :=
      hsum
    _ = c * data.weightTotal :=
      hright

theorem weightedAverage_eq_const_of_forall_eq
    (data : IUTStage1WeightedLabelAveragedProcessionLogVolume label)
    {c : Real}
    (hweight_nonnegative : ∀ j : label, 0 <= data.weight j)
    (hpointwise : ∀ j : label, data.normalizedLogVolume j = c) :
    data.weightedAverageLogVolume = c :=
  le_antisymm
    (data.weightedAverage_le_const_of_forall_le hweight_nonnegative
      (by
        intro j
        rw [hpointwise j]))
    (data.const_le_weightedAverage_of_forall_le hweight_nonnegative
      (by
        intro j
        rw [hpointwise j]))

end IUTStage1WeightedLabelAveragedProcessionLogVolume

namespace IUTStage1LabelAveragedProcessionLogVolume

variable {label : Type u} [Fintype label]

noncomputable def toWeighted
    (data : IUTStage1LabelAveragedProcessionLogVolume label)
    (weight : label -> Real)
    (weightTotal : Real)
    (positive_weightTotal : 0 < weightTotal)
    (weightTotal_eq_sum : weightTotal = Finset.univ.sum weight) :
    IUTStage1WeightedLabelAveragedProcessionLogVolume label :=
  { normalizedLogVolume := data.normalizedLogVolume,
    weight := weight,
    weightTotal := weightTotal,
    positive_weightTotal := positive_weightTotal,
    weightTotal_eq_sum := weightTotal_eq_sum,
    weightedAverageLogVolume :=
      (Finset.univ.sum fun j => weight j * data.normalizedLogVolume j) /
        weightTotal,
    weighted_average_eq := rfl }

theorem toWeighted_normalizedLogVolume_eq
    (data : IUTStage1LabelAveragedProcessionLogVolume label)
    (weight : label -> Real)
    (weightTotal : Real)
    (positive_weightTotal : 0 < weightTotal)
    (weightTotal_eq_sum : weightTotal = Finset.univ.sum weight)
    (j : label) :
    (data.toWeighted weight weightTotal positive_weightTotal
      weightTotal_eq_sum).normalizedLogVolume j =
      data.normalizedLogVolume j :=
  rfl

end IUTStage1LabelAveragedProcessionLogVolume

namespace IUTStage1ZModSquareWeightProfile

variable {l : PrimeGeFive}

def representativePointwiseComparisonLevel :
    IUTStage1SquareComparisonLevel :=
  IUTStage1SquareComparisonLevel.pointwiseRepresentative

def representativeAggregateComparisonLevel :
    IUTStage1SquareComparisonLevel :=
  IUTStage1SquareComparisonLevel.aggregateRepresentative

def balancedSignCompatibleComparisonLevel :
    IUTStage1SquareComparisonLevel :=
  IUTStage1SquareComparisonLevel.balancedSignCompatible

theorem representativeAggregateComparisonLevel_ne_pointwise :
    representativeAggregateComparisonLevel ≠
      representativePointwiseComparisonLevel :=
  IUTStage1SquareComparisonLevel.aggregate_ne_pointwise

theorem balancedSignCompatibleComparisonLevel_ne_pointwise :
    balancedSignCompatibleComparisonLevel ≠
      representativePointwiseComparisonLevel :=
  IUTStage1SquareComparisonLevel.balanced_ne_pointwise

def fromSquareWeights
    (l : PrimeGeFive)
    (positive_squareWeightTotal :
      0 < Finset.univ.sum (fun j : ZMod l.value => ((j.val : Real) ^ 2))) :
    IUTStage1ZModSquareWeightProfile l :=
  { weight := fun j => ((j.val : Real) ^ 2),
    weight_eq_square_val := by
      intro j
      rfl,
    weight_nonnegative := by
      intro j
      exact sq_nonneg (j.val : Real),
    weightTotal :=
      Finset.univ.sum (fun j : ZMod l.value => ((j.val : Real) ^ 2)),
    positive_weightTotal := positive_squareWeightTotal,
    weightTotal_eq_sum := rfl }

theorem weightTotal_eq
    (profile : IUTStage1ZModSquareWeightProfile l) :
    profile.weightTotal = Finset.univ.sum profile.weight :=
  profile.weightTotal_eq_sum

theorem profile_weight_eq_square_val
    (profile : IUTStage1ZModSquareWeightProfile l)
    (j : ZMod l.value) :
    profile.weight j = ((j.val : Real) ^ 2) :=
  profile.weight_eq_square_val j

theorem profile_weight_nonnegative
    (profile : IUTStage1ZModSquareWeightProfile l)
    (j : ZMod l.value) :
    0 <= profile.weight j :=
  profile.weight_nonnegative j

noncomputable def toWeighted
    (profile : IUTStage1ZModSquareWeightProfile l)
    (data : IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value)) :
    IUTStage1WeightedLabelAveragedProcessionLogVolume (ZMod l.value) :=
  data.toWeighted profile.weight profile.weightTotal
    profile.positive_weightTotal profile.weightTotal_eq_sum

theorem toWeighted_weight_eq_square_val
    (profile : IUTStage1ZModSquareWeightProfile l)
    (data : IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value))
    (j : ZMod l.value) :
    (profile.toWeighted data).weight j = ((j.val : Real) ^ 2) :=
  profile.weight_eq_square_val j

/-- The representative real square scale attached to a `ZMod l` label. -/
def representativeSquareScale (j : ZMod l.value) : Real :=
  ((j.val : Real) ^ 2)

theorem representativeSquareScale_eq
    (j : ZMod l.value) :
    representativeSquareScale (l := l) j = ((j.val : Real) ^ 2) :=
  rfl

theorem representativeSquareScale_one :
    representativeSquareScale (l := l) (1 : ZMod l.value) = 1 := by
  haveI : Fact (1 < l.value) :=
    ⟨lt_of_lt_of_le (by norm_num) l.ge_five⟩
  unfold representativeSquareScale
  rw [ZMod.val_one]
  norm_num

/--
The Gaussian square-weight profile has positive total mass.

The source square profile is `j ↦ j^2` on `F_l`; since `l ≥ 5`, the label
`j = 1` is present and contributes weight `1`.
-/
theorem squareWeightTotal_pos :
    0 <
      Finset.univ.sum (fun j : ZMod l.value => ((j.val : Real) ^ 2)) := by
  have hnonneg :
      ∀ j : ZMod l.value, 0 <= ((j.val : Real) ^ 2) := by
    intro j
    exact sq_nonneg (j.val : Real)
  have hone :
      (((1 : ZMod l.value).val : Real) ^ 2) = 1 := by
    simpa [representativeSquareScale] using
      (representativeSquareScale_one (l := l))
  have hterm_pos :
      0 < (((1 : ZMod l.value).val : Real) ^ 2) := by
    rw [hone]
    norm_num
  have hterm_le_sum :
      (((1 : ZMod l.value).val : Real) ^ 2) <=
        Finset.univ.sum (fun j : ZMod l.value => ((j.val : Real) ^ 2)) :=
    Finset.single_le_sum
      (s := (Finset.univ : Finset (ZMod l.value)))
      (a := (1 : ZMod l.value))
      (f := fun j : ZMod l.value => ((j.val : Real) ^ 2))
      (by
        intro j _hj
        exact hnonneg j)
      (Finset.mem_univ (1 : ZMod l.value))
  exact lt_of_lt_of_le hterm_pos hterm_le_sum

/--
Canonical representative square-weight profile for the current `F_l = ZMod l`
model.
-/
def canonicalSquareWeights (l : PrimeGeFive) :
    IUTStage1ZModSquareWeightProfile l :=
  fromSquareWeights l (squareWeightTotal_pos (l := l))

theorem canonicalSquareWeights_weight_eq_square_val
    (j : ZMod l.value) :
    (canonicalSquareWeights l).weight j = ((j.val : Real) ^ 2) :=
  (canonicalSquareWeights l).profile_weight_eq_square_val j

theorem canonicalSquareWeights_weight_one :
    (canonicalSquareWeights l).weight (1 : ZMod l.value) = 1 := by
  rw [canonicalSquareWeights_weight_eq_square_val]
  simpa [representativeSquareScale] using
    (representativeSquareScale_one (l := l))

theorem canonicalSquareWeights_weightTotal_pos :
    0 < (canonicalSquareWeights l).weightTotal :=
  (canonicalSquareWeights l).positive_weightTotal

theorem canonicalSquareWeights_toWeighted_constant_average
    (c : Real) :
    ((canonicalSquareWeights l).toWeighted
      (IUTStage1LabelAveragedProcessionLogVolume.constant
        (label := ZMod l.value) c)).weightedAverageLogVolume = c :=
  IUTStage1WeightedLabelAveragedProcessionLogVolume.weightedAverage_eq_const_of_forall_eq
    ((canonicalSquareWeights l).toWeighted
      (IUTStage1LabelAveragedProcessionLogVolume.constant
        (label := ZMod l.value) c))
    (by
      intro j
      exact (canonicalSquareWeights l).profile_weight_nonnegative j)
    (by
      intro _j
      rfl)

theorem zmod_val_image_univ :
    (Finset.univ.image fun j : ZMod l.value => j.val) =
      Finset.range l.value := by
  ext k
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨j, _hj, rfl⟩
    exact Finset.mem_range.mpr j.val_lt
  · intro hk
    have hklt : k < l.value := Finset.mem_range.mp hk
    exact Finset.mem_image.mpr
      ⟨(k : ZMod l.value), Finset.mem_univ _, ZMod.val_natCast_of_lt hklt⟩

theorem sum_representativeSquareScale_eq_range_sum :
    (Finset.univ.sum fun j : ZMod l.value => ((j.val : Real) ^ 2)) =
      (Finset.range l.value).sum fun k => ((k : Real) ^ 2) := by
  have hsum :=
    Finset.sum_image
      (s := (Finset.univ : Finset (ZMod l.value)))
      (g := fun j : ZMod l.value => j.val)
      (f := fun k : Nat => ((k : Real) ^ 2))
      (by
        intro _j _hj _k _hk h
        exact ZMod.val_injective l.value h)
  rw [zmod_val_image_univ] at hsum
  exact hsum.symm

theorem canonicalSquareWeights_weightTotal_mul_six :
    (canonicalSquareWeights l).weightTotal * 6 =
      ((l.value - 1 : Nat) : Real) * (l.value : Real) *
        (2 * ((l.value - 1 : Nat) : Real) + 1) := by
  rw [(canonicalSquareWeights l).weightTotal_eq_sum]
  have hsum_weight :
      Finset.univ.sum (canonicalSquareWeights l).weight =
        Finset.univ.sum (fun j : ZMod l.value => ((j.val : Real) ^ 2)) := by
    exact Finset.sum_congr rfl (by
      intro j _hj
      exact canonicalSquareWeights_weight_eq_square_val (l := l) j)
  rw [hsum_weight]
  rw [sum_representativeSquareScale_eq_range_sum]
  have hpos : 0 < l.value :=
    lt_of_lt_of_le (by norm_num) l.ge_five
  have hsucc : l.value - 1 + 1 = l.value :=
    Nat.succ_pred_eq_of_pos hpos
  have hrange :
      Finset.range l.value = Finset.range (l.value - 1 + 1) := by
    rw [hsucc]
  rw [hrange]
  calc
    ((Finset.range (l.value - 1 + 1)).sum fun k => ((k : Real) ^ 2)) * 6 =
        ((l.value - 1 : Nat) : Real) *
          (((l.value - 1 : Nat) : Real) + 1) *
            (2 * ((l.value - 1 : Nat) : Real) + 1) :=
      iutIVThetaPilot_sum_sq_mul_six (l.value - 1)
    _ =
        ((l.value - 1 : Nat) : Real) * (l.value : Real) *
          (2 * ((l.value - 1 : Nat) : Real) + 1) := by
      have hsucc_real :
          (((l.value - 1 : Nat) : Real) + 1) = (l.value : Real) := by
        exact_mod_cast hsucc
      rw [hsucc_real]

theorem canonicalSquareWeights_averageWeight_mul_six :
    ((canonicalSquareWeights l).weightTotal / (l.value : Real)) * 6 =
      ((l.value - 1 : Nat) : Real) *
        (2 * ((l.value - 1 : Nat) : Real) + 1) := by
  have htotal := canonicalSquareWeights_weightTotal_mul_six (l := l)
  have hl_ne : (l.value : Real) ≠ 0 := by
    exact_mod_cast l.ne_zero
  calc
    ((canonicalSquareWeights l).weightTotal / (l.value : Real)) * 6 =
        ((canonicalSquareWeights l).weightTotal * 6) / (l.value : Real) := by
      ring
    _ =
        (((l.value - 1 : Nat) : Real) * (l.value : Real) *
          (2 * ((l.value - 1 : Nat) : Real) + 1)) /
            (l.value : Real) := by
      rw [htotal]
    _ =
        ((l.value - 1 : Nat) : Real) *
          (2 * ((l.value - 1 : Nat) : Real) + 1) := by
      field_simp [hl_ne]

theorem representativeSquareScale_two :
    representativeSquareScale (l := l) (2 : ZMod l.value) = 4 := by
  have hlt : 2 < l.value :=
    lt_of_lt_of_le (by norm_num) l.ge_five
  unfold representativeSquareScale
  change ((((2 : Nat) : ZMod l.value).val : Real) ^ 2) = 4
  rw [ZMod.val_natCast_of_lt hlt]
  norm_num

theorem representativeSquareScale_one_ne_two :
    representativeSquareScale (l := l) (1 : ZMod l.value) ≠
      representativeSquareScale (l := l) (2 : ZMod l.value) := by
  rw [representativeSquareScale_one, representativeSquareScale_two]
  norm_num

/--
There is no single real scale that simultaneously equals the representative
`j^2` scale at `j = 1` and at `j = 2`.
-/
theorem no_single_scale_matches_one_two
    (scale : Real) :
    ¬ (scale = representativeSquareScale (l := l) (1 : ZMod l.value) ∧
        scale = representativeSquareScale (l := l) (2 : ZMod l.value)) := by
  intro h
  exact representativeSquareScale_one_ne_two (h.1.symm.trans h.2)

/--
A label-independent transport scale cannot absorb all representative `j^2`
scales.
-/
theorem no_label_independent_scale_matches_all_representative_squares
    (scale : Real) :
    ¬ ∀ j : ZMod l.value, scale = representativeSquareScale (l := l) j := by
  intro h
  exact no_single_scale_matches_one_two (l := l) scale
    ⟨h (1 : ZMod l.value), h (2 : ZMod l.value)⟩

/--
Representative-coordinate pilot-degree model for the relation `Theta_j ~ q^{j^2}`.

The field `qPilotDegree` is the real log/degree value attached to the q-pilot,
and `thetaPilotDegree j` is the corresponding raw `ZMod` representative value
at the label `j`. This does not descend to the source `|F_l|` sign quotient by
itself; the descended full-label model is `AbsThetaPilotDegreeProfile`.
-/
structure RepresentativeThetaPilotDegreeProfile
    (l : PrimeGeFive) where
  qPilotDegree : Real
  thetaPilotDegree : ZMod l.value -> Real
  thetaPilotDegree_eq_square_scale :
    ∀ j : ZMod l.value,
      thetaPilotDegree j =
        representativeSquareScale (l := l) j * qPilotDegree

namespace RepresentativeThetaPilotDegreeProfile

variable {l : PrimeGeFive}

theorem thetaPilotDegree_one
    (profile : RepresentativeThetaPilotDegreeProfile l) :
    profile.thetaPilotDegree (1 : ZMod l.value) = profile.qPilotDegree := by
  rw [profile.thetaPilotDegree_eq_square_scale,
    representativeSquareScale_one]
  ring

theorem thetaPilotDegree_two
    (profile : RepresentativeThetaPilotDegreeProfile l) :
    profile.thetaPilotDegree (2 : ZMod l.value) =
      4 * profile.qPilotDegree := by
  rw [profile.thetaPilotDegree_eq_square_scale,
    representativeSquareScale_two]

theorem no_labelIndependent_scale_matches_theta_degrees
    (profile : RepresentativeThetaPilotDegreeProfile l)
    (q_ne_zero : profile.qPilotDegree ≠ 0)
    (scale : Real) :
    ¬ ∀ j : ZMod l.value,
      profile.thetaPilotDegree j = scale * profile.qPilotDegree := by
  intro hscale
  have hone :
      (1 : Real) * profile.qPilotDegree =
        scale * profile.qPilotDegree := by
    simpa [profile.thetaPilotDegree_eq_square_scale,
      representativeSquareScale_one] using hscale (1 : ZMod l.value)
  have htwo :
      (4 : Real) * profile.qPilotDegree =
        scale * profile.qPilotDegree := by
    simpa [profile.thetaPilotDegree_eq_square_scale,
      representativeSquareScale_two] using hscale (2 : ZMod l.value)
  have hone_four :
      (1 : Real) * profile.qPilotDegree =
        (4 : Real) * profile.qPilotDegree :=
    hone.trans htwo.symm
  have hbad : (1 : Real) = 4 := by
    apply mul_right_cancel₀ q_ne_zero
    simpa using hone_four
  norm_num at hbad

theorem thetaPilotDegree_eq_zero_of_qPilotDegree_eq_zero
    (profile : RepresentativeThetaPilotDegreeProfile l)
    (hq : profile.qPilotDegree = 0)
    (j : ZMod l.value) :
    profile.thetaPilotDegree j = 0 := by
  rw [profile.thetaPilotDegree_eq_square_scale, hq, mul_zero]

theorem exists_labelIndependent_scale_matches_theta_degrees_iff_qPilotDegree_eq_zero
    (profile : RepresentativeThetaPilotDegreeProfile l) :
    (∃ scale : Real, ∀ j : ZMod l.value,
      profile.thetaPilotDegree j = scale * profile.qPilotDegree) ↔
      profile.qPilotDegree = 0 := by
  constructor
  · rintro ⟨scale, hscale⟩
    by_contra hq
    exact profile.no_labelIndependent_scale_matches_theta_degrees
      hq scale hscale
  · intro hq
    refine ⟨0, ?_⟩
    intro j
    rw [profile.thetaPilotDegree_eq_zero_of_qPilotDegree_eq_zero hq j,
      hq, mul_zero]

theorem qPilotDegree_ne_zero_of_neg_pos
    (profile : RepresentativeThetaPilotDegreeProfile l)
    (hq_pos : 0 < -profile.qPilotDegree) :
    profile.qPilotDegree ≠ 0 := by
  intro hq
  linarith

theorem not_exists_labelIndependent_scale_matches_theta_degrees_of_neg_pos
    (profile : RepresentativeThetaPilotDegreeProfile l)
    (hq_pos : 0 < -profile.qPilotDegree) :
    ¬ ∃ scale : Real, ∀ j : ZMod l.value,
      profile.thetaPilotDegree j = scale * profile.qPilotDegree := by
  rw [profile.exists_labelIndependent_scale_matches_theta_degrees_iff_qPilotDegree_eq_zero]
  exact profile.qPilotDegree_ne_zero_of_neg_pos hq_pos

theorem no_labelIndependent_scale_matches_theta_degrees_of_neg_pos
    (profile : RepresentativeThetaPilotDegreeProfile l)
    (hq_pos : 0 < -profile.qPilotDegree)
    (scale : Real) :
    ¬ ∀ j : ZMod l.value,
      profile.thetaPilotDegree j = scale * profile.qPilotDegree := by
  intro hscale
  exact
    profile.not_exists_labelIndependent_scale_matches_theta_degrees_of_neg_pos
      hq_pos ⟨scale, hscale⟩

end RepresentativeThetaPilotDegreeProfile

theorem toWeighted_const_le_weightedAverage_of_forall_le
    (profile : IUTStage1ZModSquareWeightProfile l)
    (data : IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value))
    {c : Real}
    (hpointwise : ∀ j : ZMod l.value, c <= data.normalizedLogVolume j) :
    c <= (profile.toWeighted data).weightedAverageLogVolume :=
  IUTStage1WeightedLabelAveragedProcessionLogVolume.const_le_weightedAverage_of_forall_le
      (profile.toWeighted data)
      (by intro j; exact profile.weight_nonnegative j)
      hpointwise

theorem toWeighted_normalizedLogVolume_eq_fullLabelLogVolume
    (profile : IUTStage1ZModSquareWeightProfile l)
    (data : IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value))
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (hcompat :
      ∀ j : ZMod l.value,
        data.normalizedLogVolume j = compat.normalizedLogVolume j)
    (j : ZMod l.value) :
    (profile.toWeighted data).normalizedLogVolume j =
      compat.fullLabelLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  calc
    (profile.toWeighted data).normalizedLogVolume j =
        data.normalizedLogVolume j :=
      rfl
    _ = compat.normalizedLogVolume j :=
      hcompat j
    _ =
        compat.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) :=
      compat.normalizedLogVolume_eq_fullLabelLogVolume_fromCoordinate j

theorem toWeighted_weightedSummand_eq_square_fullLabelLogVolume
    (profile : IUTStage1ZModSquareWeightProfile l)
    (data : IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value))
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (hcompat :
      ∀ j : ZMod l.value,
        data.normalizedLogVolume j = compat.normalizedLogVolume j)
    (j : ZMod l.value) :
    (profile.toWeighted data).weight j *
        (profile.toWeighted data).normalizedLogVolume j =
      ((j.val : Real) ^ 2) *
        compat.fullLabelLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  rw [profile.toWeighted_weight_eq_square_val data j,
    profile.toWeighted_normalizedLogVolume_eq_fullLabelLogVolume
      data compat hcompat j]

theorem toWeighted_weightedAverage_eq_square_fullLabelLogVolume_sum
    (profile : IUTStage1ZModSquareWeightProfile l)
    (data : IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value))
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (hcompat :
      ∀ j : ZMod l.value,
        data.normalizedLogVolume j = compat.normalizedLogVolume j) :
    (profile.toWeighted data).weightedAverageLogVolume =
      (Finset.univ.sum fun j : ZMod l.value =>
        ((j.val : Real) ^ 2) *
          compat.fullLabelLogVolume
            (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) /
        profile.weightTotal := by
  rw [(profile.toWeighted data).weightedAverage_eq_formula]
  congr 1
  exact Finset.sum_congr rfl (by
    intro j _hj
    exact profile.toWeighted_weightedSummand_eq_square_fullLabelLogVolume
      data compat hcompat j)

/--
Coordinate-level condition for transporting the square-weight profile.

The profile is not an anonymous weight function: it is tied to the chosen
`ZMod l.value` coordinate representative by `j.val ^ 2`.  Thus a coordinate
equivalence may be used in the square-weight branch only after one records that
it preserves these real square values.
-/
def CoordinateSquarePreserving
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value) : Prop :=
  ∀ j : ZMod l.value,
    (((coordinateEquiv j).val : Real) ^ 2) = ((j.val : Real) ^ 2)

/--
Coordinate-level preservation of the square map inside `ZMod l.value`.

This is weaker than `CoordinateSquarePreserving`: it records equality of the
finite-field square classes, not equality of the real representative squares
used by the current square-weight profile.
-/
def CoordinateModularSquarePreserving
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value) : Prop :=
  ∀ j : ZMod l.value, (coordinateEquiv j) ^ 2 = j ^ 2

/--
Sign-invariant real square profile built from the minimal absolute
representative of a `ZMod` class.

This is not the default Corollary 3.12 audit profile.  It is a separate
candidate profile used to keep track of what can be preserved by sign
symmetries without preserving the chosen nonnegative representative `j.val`.
-/
def balancedSquareWeight (j : ZMod l.value) : Real :=
  ((j.valMinAbs.natAbs : Real) ^ 2)

def CoordinateBalancedSquarePreserving
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value) : Prop :=
  ∀ j : ZMod l.value,
    balancedSquareWeight (l := l) (coordinateEquiv j) =
      balancedSquareWeight (l := l) j

theorem coordinateSquarePreserving_refl :
    CoordinateSquarePreserving (l := l) (Equiv.refl (ZMod l.value)) := by
  intro j
  rfl

theorem coordinateModularSquarePreserving_refl :
    CoordinateModularSquarePreserving
      (l := l) (Equiv.refl (ZMod l.value)) := by
  intro j
  rfl

theorem coordinateModularSquarePreserving_neg :
    CoordinateModularSquarePreserving
      (l := l) (Equiv.neg (ZMod l.value)) := by
  intro j
  change (-j) ^ 2 = j ^ 2
  simp [pow_two]

theorem balancedSquareWeight_neg_eq (j : ZMod l.value) :
    balancedSquareWeight (l := l) (-j) =
      balancedSquareWeight (l := l) j := by
  unfold balancedSquareWeight
  rw [ZMod.natAbs_valMinAbs_neg]

noncomputable def balancedSquareWeightOnSignQuotient
    (label : (zmodSignAction l).SignLabelQuotient) : Real :=
  Quotient.lift
    (fun x : (zmodPointedQuotient l).NonzeroCarrier =>
      balancedSquareWeight (l := l) x.1)
    (by
      intro x y h
      change balancedSquareWeight (l := l) x.1 =
        balancedSquareWeight (l := l) y.1
      rcases h with h | h
      · rw [h]
      · rw [h]
        exact balancedSquareWeight_neg_eq y.1)
    label

theorem balancedSquareWeightOnSignQuotient_fromCoordinate
    (j : ZMod l.value) (hj : j ≠ 0) :
    balancedSquareWeightOnSignQuotient
        (l := l) (zmodSignLabelFromCoordinate l j hj) =
      balancedSquareWeight (l := l) j := by
  unfold balancedSquareWeightOnSignQuotient zmodSignLabelFromCoordinate
  change balancedSquareWeight (l := l)
      (zmodNonzeroLabelFromCoordinate l j hj).1 =
    balancedSquareWeight (l := l) j
  rw [zmodNonzeroLabelFromCoordinate_val]

/--
Sign-quotient pilot-degree model for the sign-compatible square branch.

This is deliberately not the representative `j.val ^ 2` branch.  It records the
degree relation that actually descends to `F_l / {±1}` in the current finite
model, using `balancedSquareWeightOnSignQuotient`.
-/
structure BalancedThetaPilotDegreeProfile
    (l : PrimeGeFive) where
  qPilotDegree : Real
  thetaPilotDegree : (zmodSignAction l).SignLabelQuotient -> Real
  thetaPilotDegree_eq_balanced_scale :
    ∀ label : (zmodSignAction l).SignLabelQuotient,
      thetaPilotDegree label =
        balancedSquareWeightOnSignQuotient (l := l) label * qPilotDegree

namespace BalancedThetaPilotDegreeProfile

variable {l : PrimeGeFive}

theorem thetaPilotDegree_fromCoordinate
    (profile : BalancedThetaPilotDegreeProfile l)
    (j : ZMod l.value) (hj : j ≠ 0) :
    profile.thetaPilotDegree (zmodSignLabelFromCoordinate l j hj) =
      balancedSquareWeight (l := l) j * profile.qPilotDegree := by
  rw [profile.thetaPilotDegree_eq_balanced_scale,
    balancedSquareWeightOnSignQuotient_fromCoordinate]

theorem thetaPilotDegree_neg_fromCoordinate_eq
    (profile : BalancedThetaPilotDegreeProfile l)
    (j : ZMod l.value) (hj : j ≠ 0) :
    profile.thetaPilotDegree
        (zmodSignLabelFromCoordinate l (-j)
          (zmod_neg_ne_zero_of_ne_zero l hj)) =
      profile.thetaPilotDegree (zmodSignLabelFromCoordinate l j hj) := by
  rw [zmodSignLabelFromCoordinate_neg_eq]

theorem thetaPilotDegree_one
    (profile : BalancedThetaPilotDegreeProfile l) :
    profile.thetaPilotDegree
        (zmodSignLabelFromCoordinate l (1 : ZMod l.value)
          (zmodOneNonzeroLabel l).2) =
      balancedSquareWeight (l := l) (1 : ZMod l.value) *
        profile.qPilotDegree :=
  profile.thetaPilotDegree_fromCoordinate
    (1 : ZMod l.value) (zmodOneNonzeroLabel l).2

end BalancedThetaPilotDegreeProfile

theorem balancedSquareWeight_zero :
    balancedSquareWeight (l := l) (0 : ZMod l.value) = 0 := by
  unfold balancedSquareWeight
  simp

theorem balancedSquareWeight_nonnegative (j : ZMod l.value) :
    0 <= balancedSquareWeight (l := l) j := by
  unfold balancedSquareWeight
  positivity

theorem balancedSquareWeight_ge_one_of_ne_zero
    (j : ZMod l.value) (hj : j ≠ 0) :
    1 <= balancedSquareWeight (l := l) j := by
  unfold balancedSquareWeight
  have hnat_ne : j.valMinAbs.natAbs ≠ 0 := by
    intro hnat
    have hint : j.valMinAbs = 0 := Int.natAbs_eq_zero.mp hnat
    exact hj ((ZMod.valMinAbs_eq_zero j).mp hint)
  have hnat : 1 <= j.valMinAbs.natAbs :=
    Nat.succ_le_of_lt (Nat.pos_of_ne_zero hnat_ne)
  have hreal : (1 : Real) <= (j.valMinAbs.natAbs : Real) := by
    exact_mod_cast hnat
  nlinarith

theorem balancedSquareWeight_eq_zero_iff
    (j : ZMod l.value) :
    balancedSquareWeight (l := l) j = 0 ↔ j = 0 := by
  constructor
  · intro hzero
    by_contra hj
    have hge := balancedSquareWeight_ge_one_of_ne_zero (l := l) j hj
    linarith
  · intro hj
    subst j
    exact balancedSquareWeight_zero

theorem one_valMinAbs_natAbs (l : PrimeGeFive) :
    ((1 : ZMod l.value).valMinAbs.natAbs) = 1 := by
  have hhalf : (1 : Nat) ≤ l.value / 2 := by
    have hge : 5 ≤ l.value := l.ge_five
    omega
  have h := ZMod.valMinAbs_natCast_of_le_half (n := l.value) (a := 1) hhalf
  norm_num at h
  exact congrArg Int.natAbs h

theorem balancedSquareWeight_eq_one_iff_sign
    (j : ZMod l.value) :
    balancedSquareWeight (l := l) j = 1 ↔
      j = 1 ∨ j = -(1 : ZMod l.value) := by
  constructor
  · intro h
    unfold balancedSquareWeight at h
    have hsquares :
        ((j.valMinAbs.natAbs : Real) ^ 2) = ((1 : Real) ^ 2) := by
      simpa using h
    have heq_or := sq_eq_sq_iff_eq_or_eq_neg.mp hsquares
    have hnat : j.valMinAbs.natAbs = 1 := by
      rcases heq_or with heq | hneg
      · exact_mod_cast heq
      · have hnonneg :
            (0 : Real) <= (j.valMinAbs.natAbs : Real) := by
          exact_mod_cast Nat.zero_le _
        linarith
    have habs :
        j.valMinAbs.natAbs =
          (1 : ZMod l.value).valMinAbs.natAbs := by
      rw [hnat, one_valMinAbs_natAbs l]
    exact
      (ZMod.natAbs_valMinAbs_eq_natAbs_valMinAbs
        (a := j) (b := (1 : ZMod l.value))).mp habs
  · intro h
    rcases h with rfl | hneg
    · rw [show balancedSquareWeight (l := l) (1 : ZMod l.value) =
          ((1 : Real) ^ 2) by
          unfold balancedSquareWeight
          rw [one_valMinAbs_natAbs l]
          norm_num]
      norm_num
    · rw [hneg, balancedSquareWeight_neg_eq]
      rw [show balancedSquareWeight (l := l) (1 : ZMod l.value) =
          ((1 : Real) ^ 2) by
          unfold balancedSquareWeight
          rw [one_valMinAbs_natAbs l]
          norm_num]
      norm_num

noncomputable def balancedSquareWeightOnFullLabel :
    IUTStage1ZModCuspFullLabel l -> Real
  | IUTStage1ZModCuspFullLabel.zero => 0
  | IUTStage1ZModCuspFullLabel.nonzero label =>
      balancedSquareWeightOnSignQuotient (l := l) label

theorem balancedSquareWeightOnFullLabel_fromCoordinate
    (j : ZMod l.value) :
    balancedSquareWeightOnFullLabel
        (l := l) (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
      balancedSquareWeight (l := l) j := by
  by_cases hj : j = 0
  · subst j
    rw [IUTStage1ZModCuspFullLabel.fromCoordinate_zero]
    exact balancedSquareWeight_zero.symm
  · rw [IUTStage1ZModCuspFullLabel.fromCoordinate_nonzero l j hj]
    exact balancedSquareWeightOnSignQuotient_fromCoordinate j hj

/--
The `|F_l| = {0} ∪ F_l^×/{±1}` theta-value exponent used by the current finite
model.

IUT II writes the theta values as `q^{j^2}`, with `j` the unique representative
in `{0, ..., (l - 1) / 2}` determined by a label of `|F_l|`.  In the `ZMod`
model this is the square of the minimal absolute representative.
-/
noncomputable def thetaExponentOnAbsLabel :
    IUTStage1ZModCuspFullLabel l -> Real :=
  balancedSquareWeightOnFullLabel (l := l)

theorem thetaExponentOnAbsLabel_zero :
    thetaExponentOnAbsLabel
        (l := l) (IUTStage1ZModCuspFullLabel.zero) = 0 :=
  rfl

theorem thetaExponentOnAbsLabel_nonnegative
    (label : IUTStage1ZModCuspFullLabel l) :
    0 <= thetaExponentOnAbsLabel (l := l) label := by
  cases label with
  | zero =>
      simp [thetaExponentOnAbsLabel, balancedSquareWeightOnFullLabel]
  | nonzero label =>
      unfold thetaExponentOnAbsLabel balancedSquareWeightOnFullLabel
      refine Quotient.inductionOn label ?_
      intro x
      exact balancedSquareWeight_nonnegative x.1

theorem thetaExponentOnAbsLabel_nonzero_ge_one
    (label : (zmodSignAction l).SignLabelQuotient) :
    1 <=
      thetaExponentOnAbsLabel
        (l := l) (IUTStage1ZModCuspFullLabel.nonzero label) := by
  unfold thetaExponentOnAbsLabel balancedSquareWeightOnFullLabel
  refine Quotient.inductionOn label ?_
  intro x
  exact balancedSquareWeight_ge_one_of_ne_zero x.1 x.2

theorem thetaExponentOnAbsLabel_fromCoordinate
    (j : ZMod l.value) :
    thetaExponentOnAbsLabel
        (l := l) (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
      balancedSquareWeight (l := l) j :=
  balancedSquareWeightOnFullLabel_fromCoordinate j

theorem thetaExponentOnAbsLabel_fromCoordinate_eq_zero_iff
    (j : ZMod l.value) :
    thetaExponentOnAbsLabel
        (l := l) (IUTStage1ZModCuspFullLabel.fromCoordinate l j) = 0 ↔
      j = 0 := by
  rw [thetaExponentOnAbsLabel_fromCoordinate]
  exact balancedSquareWeight_eq_zero_iff (l := l) j

theorem thetaExponentOnAbsLabel_fromCoordinate_of_val_le_half
    (j : ZMod l.value) (hhalf : j.val ≤ l.value / 2) :
    thetaExponentOnAbsLabel
        (l := l) (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
      ((j.val : Real) ^ 2) := by
  rw [thetaExponentOnAbsLabel_fromCoordinate]
  unfold balancedSquareWeight
  rw [ZMod.valMinAbs_natAbs_eq_min]
  have hcomp : j.val ≤ l.value - j.val := by
    omega
  rw [Nat.min_eq_left hcomp]

theorem thetaExponentOnAbsLabel_fromCoordinate_neg_eq
    (j : ZMod l.value) (hj : j ≠ 0) :
    thetaExponentOnAbsLabel
        (l := l) (IUTStage1ZModCuspFullLabel.fromCoordinate l (-j)) =
      thetaExponentOnAbsLabel
        (l := l) (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_neg l j hj]

theorem thetaExponentOnAbsLabel_one :
    thetaExponentOnAbsLabel
        (l := l)
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
      1 := by
  haveI : Fact (1 < l.value) :=
    ⟨lt_of_lt_of_le (by norm_num) l.ge_five⟩
  have hhalf : (1 : ZMod l.value).val ≤ l.value / 2 := by
    have hge : 5 ≤ l.value := l.ge_five
    rw [ZMod.val_one]
    omega
  have h :=
    thetaExponentOnAbsLabel_fromCoordinate_of_val_le_half
      (l := l) (1 : ZMod l.value) hhalf
  simpa [ZMod.val_one] using h

theorem thetaExponentOnAbsLabel_two :
    thetaExponentOnAbsLabel
        (l := l)
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (2 : ZMod l.value)) =
      4 := by
  have hlt : 2 < l.value :=
    lt_of_lt_of_le (by norm_num) l.ge_five
  have hval : ZMod.val (2 : ZMod l.value) = 2 :=
    ZMod.val_natCast_of_lt hlt
  have hhalf : (2 : ZMod l.value).val ≤ l.value / 2 := by
    rw [hval]
    exact (Nat.le_div_iff_mul_le (k := 2) (x := 2) (y := l.value)
      (by norm_num)).mpr (by
        have hge : 5 ≤ l.value := l.ge_five
        omega)
  have h :=
    thetaExponentOnAbsLabel_fromCoordinate_of_val_le_half
      (l := l) (2 : ZMod l.value) hhalf
  rw [hval] at h
  norm_num at h
  exact h

/--
Full `|F_l|` pilot-degree model for theta values of the form `q^{j^2}`.

This is still a finite-label degree model, not the Hodge-Arakelov construction of
theta values.  Its role is to make the paper's absolute-label convention explicit:
the exponent is defined on `|F_l|`, not on arbitrary raw representatives.
-/
structure AbsThetaPilotDegreeProfile
    (l : PrimeGeFive) where
  qPilotDegree : Real
  thetaPilotDegree : IUTStage1ZModCuspFullLabel l -> Real
  thetaPilotDegree_eq_abs_exponent :
    ∀ label : IUTStage1ZModCuspFullLabel l,
      thetaPilotDegree label =
        thetaExponentOnAbsLabel (l := l) label * qPilotDegree

namespace AbsThetaPilotDegreeProfile

variable {l : PrimeGeFive}

theorem thetaPilotDegree_zero
    (profile : AbsThetaPilotDegreeProfile l) :
    profile.thetaPilotDegree IUTStage1ZModCuspFullLabel.zero = 0 := by
  rw [profile.thetaPilotDegree_eq_abs_exponent,
    thetaExponentOnAbsLabel_zero]
  ring

theorem thetaPilotDegree_fromCoordinate
    (profile : AbsThetaPilotDegreeProfile l)
    (j : ZMod l.value) :
    profile.thetaPilotDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
      balancedSquareWeight (l := l) j * profile.qPilotDegree := by
  rw [profile.thetaPilotDegree_eq_abs_exponent,
    thetaExponentOnAbsLabel_fromCoordinate]

theorem thetaPilotDegree_fromCoordinate_of_val_le_half
    (profile : AbsThetaPilotDegreeProfile l)
    (j : ZMod l.value) (hhalf : j.val ≤ l.value / 2) :
    profile.thetaPilotDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
      ((j.val : Real) ^ 2) * profile.qPilotDegree := by
  rw [profile.thetaPilotDegree_eq_abs_exponent,
    thetaExponentOnAbsLabel_fromCoordinate_of_val_le_half j hhalf]

theorem thetaPilotDegree_one
    (profile : AbsThetaPilotDegreeProfile l) :
    profile.thetaPilotDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
      profile.qPilotDegree := by
  rw [profile.thetaPilotDegree_eq_abs_exponent,
    thetaExponentOnAbsLabel_one]
  ring

theorem thetaPilotDegree_two
    (profile : AbsThetaPilotDegreeProfile l) :
    profile.thetaPilotDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (2 : ZMod l.value)) =
      4 * profile.qPilotDegree := by
  rw [profile.thetaPilotDegree_eq_abs_exponent,
    thetaExponentOnAbsLabel_two]

theorem thetaPilotDegree_one_ne_two_of_q_ne_zero
    (profile : AbsThetaPilotDegreeProfile l)
    (hq : profile.qPilotDegree ≠ 0) :
    profile.thetaPilotDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) ≠
      profile.thetaPilotDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (2 : ZMod l.value)) := by
  intro h
  rw [profile.thetaPilotDegree_one, profile.thetaPilotDegree_two] at h
  have hone_four : (1 : Real) = 4 := by
    apply mul_right_cancel₀ hq
    simpa using h
  norm_num at hone_four

theorem thetaPilotDegree_one_eq_two_iff_q_zero
    (profile : AbsThetaPilotDegreeProfile l) :
    profile.thetaPilotDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        profile.thetaPilotDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (2 : ZMod l.value)) ↔
      profile.qPilotDegree = 0 := by
  constructor
  · intro h
    by_contra hq
    exact profile.thetaPilotDegree_one_ne_two_of_q_ne_zero hq h
  · intro hq
    rw [profile.thetaPilotDegree_one, profile.thetaPilotDegree_two, hq]
    ring

theorem thetaPilotDegree_neg_fromCoordinate_eq
    (profile : AbsThetaPilotDegreeProfile l)
    (j : ZMod l.value) (hj : j ≠ 0) :
    profile.thetaPilotDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (-j)) =
      profile.thetaPilotDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_neg l j hj]

end AbsThetaPilotDegreeProfile

/--
Log-degree shadow of the IUT II Gaussian monoid evaluation.

The environment side has one q/theta degree.  The Gaussian side is the
`|F_l|`-indexed family obtained by multiplying that degree by the absolute-label
theta exponent.  This records only the degree-level content of
`q -> (q^{j^2})_j`; it does not construct the Frobenioid or its splittings.
-/
structure GaussianMonoidDegreeEvaluation
    (l : PrimeGeFive) where
  environmentDegree : Real
  gaussianDegree : IUTStage1ZModCuspFullLabel l -> Real
  gaussianDegree_eq_eval :
    ∀ label : IUTStage1ZModCuspFullLabel l,
      gaussianDegree label =
        thetaExponentOnAbsLabel (l := l) label * environmentDegree

namespace GaussianMonoidDegreeEvaluation

variable {l : PrimeGeFive}

noncomputable def unitEnvironment
    (l : PrimeGeFive) :
    GaussianMonoidDegreeEvaluation l :=
  { environmentDegree := 1,
    gaussianDegree := fun label =>
      thetaExponentOnAbsLabel (l := l) label,
    gaussianDegree_eq_eval := by
      intro label
      ring }

theorem unitEnvironment_environmentDegree :
    (unitEnvironment l).environmentDegree = 1 :=
  rfl

theorem unitEnvironment_environmentDegree_ne_zero :
    (unitEnvironment l).environmentDegree ≠ 0 := by
  norm_num [unitEnvironment]

def toAbsThetaPilotDegreeProfile
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    AbsThetaPilotDegreeProfile l :=
  { qPilotDegree := evaluation.environmentDegree,
    thetaPilotDegree := evaluation.gaussianDegree,
    thetaPilotDegree_eq_abs_exponent := evaluation.gaussianDegree_eq_eval }

noncomputable def toCuspLabelLogVolumeCompatibility
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    IUTStage1ZModCuspLabelLogVolumeCompatibility l :=
  { normalizedLogVolume := fun j =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j),
    cuspClassLogVolume := fun label =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.nonzero label),
    zeroLogVolume :=
      evaluation.gaussianDegree IUTStage1ZModCuspFullLabel.zero,
    nonzero_eq_cuspClass := by
      intro j hj
      rw [IUTStage1ZModCuspFullLabel.fromCoordinate_nonzero l j hj],
    zero_eq := by
      rw [IUTStage1ZModCuspFullLabel.fromCoordinate_zero] }

theorem toCuspLabelLogVolumeCompatibility_fullLabelLogVolume
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (label : IUTStage1ZModCuspFullLabel l) :
    evaluation.toCuspLabelLogVolumeCompatibility.fullLabelLogVolume label =
      evaluation.gaussianDegree label := by
  cases label <;> rfl

theorem gaussianDegree_eq_of_environmentDegree_eq
    (sourceEvaluation targetEvaluation : GaussianMonoidDegreeEvaluation l)
    (henv :
      targetEvaluation.environmentDegree =
        sourceEvaluation.environmentDegree)
    (label : IUTStage1ZModCuspFullLabel l) :
    targetEvaluation.gaussianDegree label =
      sourceEvaluation.gaussianDegree label := by
  rw [targetEvaluation.gaussianDegree_eq_eval,
    sourceEvaluation.gaussianDegree_eq_eval, henv]

theorem fullLabelLogVolumeValuePreserving_of_environmentDegree_eq
    (sourceEvaluation targetEvaluation : GaussianMonoidDegreeEvaluation l)
    (henv :
      targetEvaluation.environmentDegree =
        sourceEvaluation.environmentDegree) :
    IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelLogVolumeValuePreserving
      sourceEvaluation.toCuspLabelLogVolumeCompatibility
      targetEvaluation.toCuspLabelLogVolumeCompatibility := by
  intro label
  rw [targetEvaluation.toCuspLabelLogVolumeCompatibility_fullLabelLogVolume,
    sourceEvaluation.toCuspLabelLogVolumeCompatibility_fullLabelLogVolume]
  exact sourceEvaluation.gaussianDegree_eq_of_environmentDegree_eq
    targetEvaluation henv label

theorem gaussianDegree_zero
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.gaussianDegree IUTStage1ZModCuspFullLabel.zero = 0 := by
  rw [evaluation.gaussianDegree_eq_eval,
    thetaExponentOnAbsLabel_zero]
  ring

theorem gaussianDegree_eq_zero_of_environment_zero
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv : evaluation.environmentDegree = 0)
    (label : IUTStage1ZModCuspFullLabel l) :
    evaluation.gaussianDegree label = 0 := by
  rw [evaluation.gaussianDegree_eq_eval, henv]
  ring

theorem gaussianDegree_fromCoordinate_eq_zero_of_environment_zero
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv : evaluation.environmentDegree = 0)
    (j : ZMod l.value) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) = 0 :=
  evaluation.gaussianDegree_eq_zero_of_environment_zero henv
    (IUTStage1ZModCuspFullLabel.fromCoordinate l j)

theorem gaussianDegree_nonzero_ne_zero_of_environment_ne_zero
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (label : (zmodSignAction l).SignLabelQuotient)
    (henv : evaluation.environmentDegree ≠ 0) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.nonzero label) ≠ 0 := by
  rw [evaluation.gaussianDegree_eq_eval]
  have hexp_pos :
      0 <
        thetaExponentOnAbsLabel
          (l := l) (IUTStage1ZModCuspFullLabel.nonzero label) :=
    lt_of_lt_of_le zero_lt_one
      (thetaExponentOnAbsLabel_nonzero_ge_one (l := l) label)
  exact mul_ne_zero (ne_of_gt hexp_pos) henv

theorem gaussianDegree_fromCoordinate_ne_zero_of_environment_ne_zero
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (j : ZMod l.value) (hj : j ≠ 0)
    (henv : evaluation.environmentDegree ≠ 0) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) ≠ 0 := by
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_nonzero l j hj]
  exact evaluation.gaussianDegree_nonzero_ne_zero_of_environment_ne_zero
    (zmodSignLabelFromCoordinate l j hj) henv

theorem gaussianDegree_fromCoordinate_eq_zero_iff
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (j : ZMod l.value) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) = 0 ↔
      j = 0 ∨ evaluation.environmentDegree = 0 := by
  constructor
  · intro hzero
    rw [evaluation.gaussianDegree_eq_eval] at hzero
    rcases mul_eq_zero.mp hzero with hexp | henv
    · exact Or.inl
        ((thetaExponentOnAbsLabel_fromCoordinate_eq_zero_iff
          (l := l) j).mp hexp)
    · exact Or.inr henv
  · intro h
    rcases h with hj | henv
    · subst j
      rw [IUTStage1ZModCuspFullLabel.fromCoordinate_zero,
        evaluation.gaussianDegree_zero]
    · rw [evaluation.gaussianDegree_eq_eval, henv]
      ring

theorem gaussianDegree_one
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
      evaluation.environmentDegree := by
  rw [evaluation.gaussianDegree_eq_eval,
    thetaExponentOnAbsLabel_one]
  ring

theorem environmentDegree_eq_of_gaussianDegree_one_eq
    (sourceEvaluation targetEvaluation : GaussianMonoidDegreeEvaluation l)
    (hone :
      targetEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value))) :
    targetEvaluation.environmentDegree =
      sourceEvaluation.environmentDegree := by
  rw [targetEvaluation.gaussianDegree_one,
    sourceEvaluation.gaussianDegree_one] at hone
  exact hone

theorem gaussianDegree_one_eq_iff_environmentDegree_eq
    (sourceEvaluation targetEvaluation : GaussianMonoidDegreeEvaluation l) :
    targetEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) ↔
      targetEvaluation.environmentDegree =
        sourceEvaluation.environmentDegree := by
  constructor
  · exact sourceEvaluation.environmentDegree_eq_of_gaussianDegree_one_eq
      targetEvaluation
  · intro henv
    rw [targetEvaluation.gaussianDegree_one,
      sourceEvaluation.gaussianDegree_one, henv]

theorem environmentDegree_eq_of_fullLabelLogVolumeValuePreserving
    (sourceEvaluation targetEvaluation : GaussianMonoidDegreeEvaluation l)
    (hvalue :
      IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelLogVolumeValuePreserving
        sourceEvaluation.toCuspLabelLogVolumeCompatibility
        targetEvaluation.toCuspLabelLogVolumeCompatibility) :
    targetEvaluation.environmentDegree =
      sourceEvaluation.environmentDegree := by
  have hone :=
    hvalue
      (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value))
  rw [targetEvaluation.toCuspLabelLogVolumeCompatibility_fullLabelLogVolume,
    sourceEvaluation.toCuspLabelLogVolumeCompatibility_fullLabelLogVolume,
    targetEvaluation.gaussianDegree_one,
    sourceEvaluation.gaussianDegree_one] at hone
  exact hone

theorem fullLabelLogVolumeValuePreserving_iff_environmentDegree_eq
    (sourceEvaluation targetEvaluation : GaussianMonoidDegreeEvaluation l) :
    IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelLogVolumeValuePreserving
        sourceEvaluation.toCuspLabelLogVolumeCompatibility
        targetEvaluation.toCuspLabelLogVolumeCompatibility ↔
      targetEvaluation.environmentDegree =
        sourceEvaluation.environmentDegree := by
  constructor
  · exact sourceEvaluation.environmentDegree_eq_of_fullLabelLogVolumeValuePreserving
      targetEvaluation
  · exact sourceEvaluation.fullLabelLogVolumeValuePreserving_of_environmentDegree_eq
      targetEvaluation

theorem gaussianDegree_two
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (2 : ZMod l.value)) =
      4 * evaluation.environmentDegree := by
  rw [evaluation.gaussianDegree_eq_eval,
    thetaExponentOnAbsLabel_two]

theorem gaussianDegree_one_ne_two_of_environment_ne_zero
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv : evaluation.environmentDegree ≠ 0) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) ≠
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (2 : ZMod l.value)) := by
  exact evaluation.toAbsThetaPilotDegreeProfile
    |>.thetaPilotDegree_one_ne_two_of_q_ne_zero henv

theorem gaussianDegree_one_eq_two_iff_environment_zero
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (2 : ZMod l.value)) ↔
      evaluation.environmentDegree = 0 := by
  exact evaluation.toAbsThetaPilotDegreeProfile
    |>.thetaPilotDegree_one_eq_two_iff_q_zero

theorem gaussianDegree_canonicalSignLabel
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.nonzero
          (zmodCanonicalSignLabelQuotient l)) =
      evaluation.environmentDegree := by
  have h := evaluation.gaussianDegree_one
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_one] at h
  exact h

theorem cuspClassLogVolume_canonicalSignLabel
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.toCuspLabelLogVolumeCompatibility.cuspClassLogVolume
        (zmodCanonicalSignLabelQuotient l) =
      evaluation.environmentDegree :=
  evaluation.gaussianDegree_canonicalSignLabel

theorem gaussianDegree_fromCoordinate_of_val_le_half
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (j : ZMod l.value) (hhalf : j.val ≤ l.value / 2) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
      ((j.val : Real) ^ 2) * evaluation.environmentDegree := by
  rw [evaluation.gaussianDegree_eq_eval,
    thetaExponentOnAbsLabel_fromCoordinate_of_val_le_half j hhalf]

theorem gaussianDegree_neg_fromCoordinate_eq
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (j : ZMod l.value) (hj : j ≠ 0) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (-j)) =
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_neg l j hj]

/--
Finite `q^{j^2}` square-weight endpoint.

For canonical representatives of the finite label set, the Gaussian degree is
the square weight times the environment/q-pilot degree.  The same package also
records the zero branch, the canonical one branch, and sign invariance.
-/
theorem finiteQJSquaredSquareWeight_endpoint
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (profile : IUTStage1ZModSquareWeightProfile l) :
    (∀ j : ZMod l.value, j.val ≤ l.value / 2 ->
      evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
        profile.weight j * evaluation.environmentDegree) ∧
      evaluation.gaussianDegree IUTStage1ZModCuspFullLabel.zero = 0 ∧
      evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        evaluation.environmentDegree ∧
      profile.weight (1 : ZMod l.value) = 1 ∧
      (∀ j : ZMod l.value, j ≠ 0 ->
        evaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.fromCoordinate l (-j)) =
          evaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) := by
  refine ⟨?_, evaluation.gaussianDegree_zero, evaluation.gaussianDegree_one,
    ?_, ?_⟩
  · intro j hhalf
    rw [profile.weight_eq_square_val j]
    exact evaluation.gaussianDegree_fromCoordinate_of_val_le_half j hhalf
  · rw [profile.weight_eq_square_val]
    exact representativeSquareScale_one (l := l)
  · intro j hj
    exact evaluation.gaussianDegree_neg_fromCoordinate_eq j hj

theorem gaussianDegree_nonnegative_of_environment_nonnegative
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv : 0 <= evaluation.environmentDegree)
    (label : IUTStage1ZModCuspFullLabel l) :
    0 <= evaluation.gaussianDegree label := by
  rw [evaluation.gaussianDegree_eq_eval]
  exact mul_nonneg (thetaExponentOnAbsLabel_nonnegative label) henv

theorem gaussianDegree_nonpositive_of_environment_nonpositive
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv : evaluation.environmentDegree <= 0)
    (label : IUTStage1ZModCuspFullLabel l) :
    evaluation.gaussianDegree label <= 0 := by
  rw [evaluation.gaussianDegree_eq_eval]
  exact mul_nonpos_of_nonneg_of_nonpos
    (thetaExponentOnAbsLabel_nonnegative label) henv

theorem gaussianDegree_le_of_environment_nonpositive_of_nonnegative_bound
    (evaluation : GaussianMonoidDegreeEvaluation l)
    {c : Real}
    (henv : evaluation.environmentDegree <= 0)
    (hc : 0 <= c)
    (label : IUTStage1ZModCuspFullLabel l) :
    evaluation.gaussianDegree label <= c :=
  le_trans
    (evaluation.gaussianDegree_nonpositive_of_environment_nonpositive
      henv label)
    hc

theorem gaussianDegree_nonzero_le_environment_of_environment_nonpositive
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv : evaluation.environmentDegree <= 0)
    (label : (zmodSignAction l).SignLabelQuotient) :
    evaluation.gaussianDegree (IUTStage1ZModCuspFullLabel.nonzero label) <=
      evaluation.environmentDegree := by
  rw [evaluation.gaussianDegree_eq_eval]
  have hexp_ge_one := thetaExponentOnAbsLabel_nonzero_ge_one (l := l) label
  have hfactor_nonneg :
      0 <=
        thetaExponentOnAbsLabel
            (l := l) (IUTStage1ZModCuspFullLabel.nonzero label) -
          1 := by
    linarith
  have hprod :
      (thetaExponentOnAbsLabel
            (l := l) (IUTStage1ZModCuspFullLabel.nonzero label) -
          1) * evaluation.environmentDegree <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos hfactor_nonneg henv
  nlinarith

theorem gaussianDegree_nonzero_le_of_environment_le_bound
    (evaluation : GaussianMonoidDegreeEvaluation l)
    {c : Real}
    (henv_nonpos : evaluation.environmentDegree <= 0)
    (henv_le : evaluation.environmentDegree <= c)
    (label : (zmodSignAction l).SignLabelQuotient) :
    evaluation.gaussianDegree (IUTStage1ZModCuspFullLabel.nonzero label) <= c :=
  le_trans
    (evaluation.gaussianDegree_nonzero_le_environment_of_environment_nonpositive
      henv_nonpos label)
    henv_le

noncomputable def nonzeroCarrierAveragedLogVolume
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    IUTStage1LabelAveragedProcessionLogVolume
      (zmodPointedQuotient l).NonzeroCarrier :=
  { normalizedLogVolume := fun x =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.nonzero
          ((zmodSignAction l).toSignLabelQuotient x)),
    averageLogVolume :=
      (Finset.univ.sum fun x : (zmodPointedQuotient l).NonzeroCarrier =>
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.nonzero
            ((zmodSignAction l).toSignLabelQuotient x))) /
        (Fintype.card (zmodPointedQuotient l).NonzeroCarrier : Real),
    average_eq := rfl }

theorem nonzeroCarrierAveragedLogVolume_apply
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (x : (zmodPointedQuotient l).NonzeroCarrier) :
    evaluation.nonzeroCarrierAveragedLogVolume.normalizedLogVolume x =
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.nonzero
          ((zmodSignAction l).toSignLabelQuotient x)) :=
  rfl

noncomputable def coordinateAveragedLogVolume
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    IUTStage1LabelAveragedProcessionLogVolume (ZMod l.value) :=
  { normalizedLogVolume := fun j =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j),
    averageLogVolume :=
      (Finset.univ.sum fun j : ZMod l.value =>
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) /
        (l.value : Real),
    average_eq := by rw [ZMod.card] }

theorem coordinateGaussian_sum_translation_eq
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (t : ZMod l.value) :
    (Finset.univ.sum fun j : ZMod l.value =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (zmodLabelTranslate l t j))) =
      Finset.univ.sum fun j : ZMod l.value =>
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) :=
  IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodTranslation_sum_eq
    (l := l) t
    (fun j : ZMod l.value =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j))

theorem coordinateGaussian_sum_unitAffine_eq
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) (t : ZMod l.value) :
    (Finset.univ.sum fun j : ZMod l.value =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j)))) =
      Finset.univ.sum fun j : ZMod l.value =>
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) :=
  IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodUnitAffine_sum_eq
    (l := l) a t
    (fun j : ZMod l.value =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j))

theorem gaussianDegree_unitSmul_fromCoordinate_eq_of_signSubgroup
    (evaluation : GaussianMonoidDegreeEvaluation l)
    {a : (ZMod l.value)ˣ} (ha : a ∈ zmodSignUnitSubgroup l)
    (j : ZMod l.value) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          ((zmodUnitActionData l).smul a j)) =
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  have hlabel :=
    IUTStage1ZModCuspLabelLogVolumeCompatibility.fullLabelMapPreserving_unitSmul_of_signSubgroup
      (l := l) ha j
  rw [IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodUnitSmulEquiv_apply]
    at hlabel
  exact congrArg evaluation.gaussianDegree hlabel

theorem gaussianDegree_unitAffine_fromCoordinate_eq_of_signSubgroup
    (evaluation : GaussianMonoidDegreeEvaluation l)
    {a : (ZMod l.value)ˣ} (ha : a ∈ zmodSignUnitSubgroup l)
    (j : ZMod l.value) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (zmodLabelTranslate l (0 : ZMod l.value)
            ((zmodUnitActionData l).smul a j))) =
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  rw [zmodLabelTranslate_zero]
  exact evaluation.gaussianDegree_unitSmul_fromCoordinate_eq_of_signSubgroup
    ha j

theorem zero_translation_of_unitAffine_pointwise_gaussian_preserving
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) {t : ZMod l.value}
    (henv : evaluation.environmentDegree ≠ 0)
    (hpres : ∀ j : ZMod l.value,
      evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j))) =
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) :
    t = 0 := by
  have hzero := hpres 0
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_zero] at hzero
  rw [evaluation.gaussianDegree_zero] at hzero
  have hcrit_raw :=
    (evaluation.gaussianDegree_fromCoordinate_eq_zero_iff
      (zmodLabelTranslate l t
        ((zmodUnitActionData l).smul a (0 : ZMod l.value)))).mp hzero
  have hcrit : t = 0 ∨ evaluation.environmentDegree = 0 := by
    simpa [zmodLabelTranslate_eq_add, zmodUnitActionData] using hcrit_raw
  rcases hcrit with ht | henv_zero
  · exact ht
  · exact False.elim (henv henv_zero)

theorem no_nonzero_translation_unitAffine_pointwise_gaussian_preserving
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) {t : ZMod l.value}
    (ht : t ≠ 0) (henv : evaluation.environmentDegree ≠ 0) :
    ¬ ∀ j : ZMod l.value,
      evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j))) =
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  intro hpres
  exact ht
    (evaluation.zero_translation_of_unitAffine_pointwise_gaussian_preserving
      a henv hpres)

theorem signSubgroup_of_unitAffine_pointwise_gaussian_preserving
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) {t : ZMod l.value}
    (henv : evaluation.environmentDegree ≠ 0)
    (hpres : ∀ j : ZMod l.value,
      evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j))) =
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) :
    a ∈ zmodSignUnitSubgroup l := by
  have ht :=
    evaluation.zero_translation_of_unitAffine_pointwise_gaussian_preserving
      a henv hpres
  have h1 := hpres (1 : ZMod l.value)
  subst t
  rw [zmodLabelTranslate_zero] at h1
  rw [evaluation.gaussianDegree_eq_eval, evaluation.gaussianDegree_one] at h1
  rw [thetaExponentOnAbsLabel_fromCoordinate] at h1
  have hweight :
      balancedSquareWeight (l := l)
          ((zmodUnitActionData l).smul a (1 : ZMod l.value)) = 1 := by
    have hmul :
        balancedSquareWeight (l := l)
            ((zmodUnitActionData l).smul a (1 : ZMod l.value)) *
            evaluation.environmentDegree =
          1 * evaluation.environmentDegree := by
      simpa using h1
    exact mul_right_cancel₀ henv hmul
  have ha_coord : (a : ZMod l.value) = 1 ∨ (a : ZMod l.value) = -1 := by
    simpa [zmodUnitActionData] using
      (balancedSquareWeight_eq_one_iff_sign (l := l)
        ((zmodUnitActionData l).smul a (1 : ZMod l.value))).mp hweight
  rw [mem_zmodSignUnitSubgroup_iff]
  rcases ha_coord with ha1 | haneg
  · left
    ext
    simpa using ha1
  · right
    ext
    simpa using haneg

theorem unitAffine_pointwise_gaussian_preserving_iff
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) (t : ZMod l.value)
    (henv : evaluation.environmentDegree ≠ 0) :
    (∀ j : ZMod l.value,
      evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j))) =
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) ↔
      t = 0 ∧ a ∈ zmodSignUnitSubgroup l := by
  constructor
  · intro hpres
    exact
      ⟨evaluation.zero_translation_of_unitAffine_pointwise_gaussian_preserving
          a henv hpres,
        evaluation.signSubgroup_of_unitAffine_pointwise_gaussian_preserving
          a henv hpres⟩
  · rintro ⟨ht, ha⟩ j
    subst t
    rw [zmodLabelTranslate_zero]
    exact evaluation.gaussianDegree_unitSmul_fromCoordinate_eq_of_signSubgroup
      ha j

theorem unitAffine_pointwise_gaussian_preserving_iff_fullLabelMapPreserving
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) (t : ZMod l.value)
    (henv : evaluation.environmentDegree ≠ 0) :
    (∀ j : ZMod l.value,
      evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j))) =
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) ↔
      IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
        (l := l)
        (IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodUnitAffineEquiv
          l a t) := by
  rw [evaluation.unitAffine_pointwise_gaussian_preserving_iff a t henv]
  rw [IUTStage1ZModCuspLabelLogVolumeCompatibility.fullLabelMapPreserving_unitAffine_iff]

theorem unitAffine_pointwise_gaussian_preserving_of_environment_zero
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) (t : ZMod l.value)
    (henv : evaluation.environmentDegree = 0) :
    ∀ j : ZMod l.value,
      evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j))) =
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  intro j
  rw [evaluation.gaussianDegree_fromCoordinate_eq_zero_of_environment_zero
    henv]
  rw [evaluation.gaussianDegree_fromCoordinate_eq_zero_of_environment_zero
    henv]

theorem unitAffine_pointwise_gaussian_preserving_iff_environment_zero_or_fullLabelMapPreserving
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) (t : ZMod l.value) :
    (∀ j : ZMod l.value,
      evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j))) =
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) ↔
      evaluation.environmentDegree = 0 ∨
        IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodUnitAffineEquiv
            l a t) := by
  by_cases henv : evaluation.environmentDegree = 0
  · constructor
    · intro _hpres
      exact Or.inl henv
    · intro _h
      exact evaluation.unitAffine_pointwise_gaussian_preserving_of_environment_zero
        a t henv
  · rw [evaluation.unitAffine_pointwise_gaussian_preserving_iff_fullLabelMapPreserving
      a t henv]
    constructor
    · intro hmap
      exact Or.inr hmap
    · intro h
      rcases h with hzero | hmap
      · exact False.elim (henv hzero)
      · exact hmap

theorem unitAffine_all_nonzero_environment_pointwise_gaussian_preserving_iff_fullLabelMapPreserving
    (a : (ZMod l.value)ˣ) (t : ZMod l.value) :
    (∀ evaluation : GaussianMonoidDegreeEvaluation l,
      evaluation.environmentDegree ≠ 0 ->
        ∀ j : ZMod l.value,
          evaluation.gaussianDegree
              (IUTStage1ZModCuspFullLabel.fromCoordinate l
                (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j))) =
            evaluation.gaussianDegree
              (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) ↔
      IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
        (l := l)
        (IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodUnitAffineEquiv
          l a t) := by
  constructor
  · intro hpres
    have hunit :=
      hpres (unitEnvironment l)
        (unitEnvironment_environmentDegree_ne_zero (l := l))
    exact
      ((unitEnvironment l).unitAffine_pointwise_gaussian_preserving_iff_fullLabelMapPreserving
        a t (unitEnvironment_environmentDegree_ne_zero (l := l))).mp hunit
  · intro hmap evaluation henv
    exact
      (evaluation.unitAffine_pointwise_gaussian_preserving_iff_fullLabelMapPreserving
        a t henv).mpr hmap

theorem coordinateAveragedLogVolume_average_translation_eq
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (t : ZMod l.value) :
    ((Finset.univ.sum fun j : ZMod l.value =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (zmodLabelTranslate l t j))) / (l.value : Real)) =
      evaluation.coordinateAveragedLogVolume.averageLogVolume := by
  rw [evaluation.coordinateGaussian_sum_translation_eq t]
  rfl

theorem coordinateAveragedLogVolume_average_unitAffine_eq
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) (t : ZMod l.value) :
    ((Finset.univ.sum fun j : ZMod l.value =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j)))) /
        (l.value : Real)) =
      evaluation.coordinateAveragedLogVolume.averageLogVolume := by
  rw [evaluation.coordinateGaussian_sum_unitAffine_eq a t]
  rfl

theorem coordinateAverage_translationInvariant_but_not_fullLabelDescend
    (evaluation : GaussianMonoidDegreeEvaluation l)
    {t : ZMod l.value} (ht : t ≠ 0) :
    ((Finset.univ.sum fun j : ZMod l.value =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (zmodLabelTranslate l t j))) / (l.value : Real)) =
      evaluation.coordinateAveragedLogVolume.averageLogVolume ∧
    ¬ ∃ T : IUTStage1ZModCuspFullLabel l -> IUTStage1ZModCuspFullLabel l,
      ∀ j : ZMod l.value,
        T (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
          IUTStage1ZModCuspFullLabel.fromCoordinate l
            (zmodLabelTranslate l t j) :=
  ⟨evaluation.coordinateAveragedLogVolume_average_translation_eq t,
    IUTStage1ZModCuspFullLabel.no_fullLabel_map_descends_nonzero_translation
      l t ht⟩

theorem coordinateAverage_unitAffineInvariant_but_not_fullLabelDescend
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) {t : ZMod l.value} (ht : t ≠ 0) :
    ((Finset.univ.sum fun j : ZMod l.value =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j)))) /
        (l.value : Real)) =
      evaluation.coordinateAveragedLogVolume.averageLogVolume ∧
    ¬ ∃ T : IUTStage1ZModCuspFullLabel l -> IUTStage1ZModCuspFullLabel l,
      ∀ j : ZMod l.value,
        T (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
          IUTStage1ZModCuspFullLabel.fromCoordinate l
            (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j)) :=
  ⟨evaluation.coordinateAveragedLogVolume_average_unitAffine_eq a t,
    IUTStage1ZModCuspFullLabel.no_fullLabel_map_descends_unitAffine_nonzero_translation
      l a ht⟩

theorem unitAffine_zeroGaussianComponent_ne_zero_of_environment_ne_zero
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) {t : ZMod l.value}
    (ht : t ≠ 0) (henv : evaluation.environmentDegree ≠ 0) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (zmodLabelTranslate l t
            ((zmodUnitActionData l).smul a (0 : ZMod l.value)))) ≠
      evaluation.gaussianDegree IUTStage1ZModCuspFullLabel.zero := by
  rw [evaluation.gaussianDegree_zero]
  have hcoord :
      zmodLabelTranslate l t
          ((zmodUnitActionData l).smul a (0 : ZMod l.value)) ≠
        0 := by
    simpa [zmodLabelTranslate_eq_add, zmodUnitActionData] using ht
  exact evaluation.gaussianDegree_fromCoordinate_ne_zero_of_environment_ne_zero
    (zmodLabelTranslate l t
      ((zmodUnitActionData l).smul a (0 : ZMod l.value)))
    hcoord henv

theorem unitAffine_zeroGaussianComponent_eq_zero_iff
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) (t : ZMod l.value) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (zmodLabelTranslate l t
            ((zmodUnitActionData l).smul a (0 : ZMod l.value)))) =
      evaluation.gaussianDegree IUTStage1ZModCuspFullLabel.zero ↔
    t = 0 ∨ evaluation.environmentDegree = 0 := by
  rw [evaluation.gaussianDegree_zero]
  simpa [zmodLabelTranslate_eq_add, zmodUnitActionData] using
    (evaluation.gaussianDegree_fromCoordinate_eq_zero_iff
      (zmodLabelTranslate l t
        ((zmodUnitActionData l).smul a (0 : ZMod l.value))))

theorem coordinateAverage_unitAffineInvariant_but_zeroGaussianChanged_and_not_fullLabelDescend
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) {t : ZMod l.value}
    (ht : t ≠ 0) (henv : evaluation.environmentDegree ≠ 0) :
    ((Finset.univ.sum fun j : ZMod l.value =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j)))) /
        (l.value : Real)) =
      evaluation.coordinateAveragedLogVolume.averageLogVolume ∧
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l
          (zmodLabelTranslate l t
            ((zmodUnitActionData l).smul a (0 : ZMod l.value)))) ≠
      evaluation.gaussianDegree IUTStage1ZModCuspFullLabel.zero ∧
    ¬ ∃ T : IUTStage1ZModCuspFullLabel l -> IUTStage1ZModCuspFullLabel l,
      ∀ j : ZMod l.value,
        T (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
          IUTStage1ZModCuspFullLabel.fromCoordinate l
            (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j)) :=
  ⟨evaluation.coordinateAveragedLogVolume_average_unitAffine_eq a t,
    evaluation.unitAffine_zeroGaussianComponent_ne_zero_of_environment_ne_zero
      a ht henv,
    IUTStage1ZModCuspFullLabel.no_fullLabel_map_descends_unitAffine_nonzero_translation
      l a ht⟩

theorem coordinateGaussian_sum_eq_zero_add_nonzero
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    Finset.univ.sum (fun j : ZMod l.value =>
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) =
      evaluation.gaussianDegree IUTStage1ZModCuspFullLabel.zero +
        Finset.univ.sum
          (fun x : (zmodPointedQuotient l).NonzeroCarrier =>
            evaluation.gaussianDegree
              (IUTStage1ZModCuspFullLabel.nonzero
                ((zmodSignAction l).toSignLabelQuotient x))) := by
  classical
  let f : ZMod l.value -> Real := fun j =>
    evaluation.gaussianDegree
      (IUTStage1ZModCuspFullLabel.fromCoordinate l j)
  have hnonzero_sum :
      (Finset.univ.erase (0 : ZMod l.value)).sum f =
        Finset.univ.sum
          (fun x : (zmodPointedQuotient l).NonzeroCarrier =>
            evaluation.gaussianDegree
              (IUTStage1ZModCuspFullLabel.nonzero
                ((zmodSignAction l).toSignLabelQuotient x))) := by
    change (Finset.univ.erase (0 : ZMod l.value)).sum f =
      Finset.univ.sum
        (fun x : {x : ZMod l.value // x ≠ 0} =>
          evaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.nonzero
              ((zmodSignAction l).toSignLabelQuotient x)))
    calc
      (Finset.univ.erase (0 : ZMod l.value)).sum f =
          Finset.univ.sum
            (fun x : {x : ZMod l.value // x ≠ 0} => f x.1) := by
        rw [Finset.sum_subtype (Finset.univ.erase (0 : ZMod l.value))]
        intro j
        simp
      _ =
          Finset.univ.sum
            (fun x : {x : ZMod l.value // x ≠ 0} =>
              evaluation.gaussianDegree
                (IUTStage1ZModCuspFullLabel.nonzero
                  ((zmodSignAction l).toSignLabelQuotient x))) := by
        apply Finset.sum_congr rfl
        intro x _hx
        simp [f, IUTStage1ZModCuspFullLabel.fromCoordinate_nonzero l x.1 x.2,
          zmod_toSignLabelQuotient_eq_fromCoordinate]
  have hsplit :=
    Finset.sum_erase_add Finset.univ f
      (Finset.mem_univ (0 : ZMod l.value))
  rw [← hsplit]
  rw [hnonzero_sum]
  simp [f, IUTStage1ZModCuspFullLabel.fromCoordinate_zero, add_comm]

theorem coordinateAveragedLogVolume_average_eq_nonzero_sum_over_prime
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.coordinateAveragedLogVolume.averageLogVolume =
      (Finset.univ.sum
        (fun x : (zmodPointedQuotient l).NonzeroCarrier =>
          evaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.nonzero
              ((zmodSignAction l).toSignLabelQuotient x)))) /
        (l.value : Real) := by
  rw [coordinateAveragedLogVolume]
  simp only
  rw [coordinateGaussian_sum_eq_zero_add_nonzero]
  rw [evaluation.gaussianDegree_zero]
  ring

theorem coordinateAveragedLogVolume_eq_nonzero_mass_rescale
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.coordinateAveragedLogVolume.averageLogVolume =
      ((l.value - 1 : Nat) : Real) / (l.value : Real) *
        evaluation.nonzeroCarrierAveragedLogVolume.averageLogVolume := by
  rw [coordinateAveragedLogVolume_average_eq_nonzero_sum_over_prime]
  rw [evaluation.nonzeroCarrierAveragedLogVolume.average_eq]
  change
    (Finset.univ.sum
          (fun x : (zmodPointedQuotient l).NonzeroCarrier =>
            evaluation.gaussianDegree
              (IUTStage1ZModCuspFullLabel.nonzero
                ((zmodSignAction l).toSignLabelQuotient x)))) /
        (l.value : Real) =
      ((l.value - 1 : Nat) : Real) / (l.value : Real) *
        ((Finset.univ.sum
            (fun x : (zmodPointedQuotient l).NonzeroCarrier =>
              evaluation.gaussianDegree
                (IUTStage1ZModCuspFullLabel.nonzero
                  ((zmodSignAction l).toSignLabelQuotient x)))) /
          (Fintype.card (zmodPointedQuotient l).NonzeroCarrier : Real))
  rw [zmodNonzeroCarrier_card_eq]
  have hl_ne : (l.value : Real) ≠ 0 := by
    exact_mod_cast l.ne_zero
  have hlm_ne : ((l.value - 1 : Nat) : Real) ≠ 0 := by
    have hpos : 0 < l.value - 1 := by
      have hge : 5 ≤ l.value := l.ge_five
      omega
    exact_mod_cast (ne_of_gt hpos)
  field_simp [hl_ne, hlm_ne]

theorem nonzeroCarrierAverage_le_of_environment_le_bound
    (evaluation : GaussianMonoidDegreeEvaluation l)
    {c : Real}
    (henv_nonpos : evaluation.environmentDegree <= 0)
    (henv_le : evaluation.environmentDegree <= c) :
    evaluation.nonzeroCarrierAveragedLogVolume.averageLogVolume <= c := by
  haveI : Nonempty (zmodPointedQuotient l).NonzeroCarrier :=
    ⟨zmodOneNonzeroLabel l⟩
  exact
    IUTStage1LabelAveragedProcessionLogVolume.average_le_const_of_forall_le
      evaluation.nonzeroCarrierAveragedLogVolume
      (by
        intro x
        exact evaluation.gaussianDegree_nonzero_le_of_environment_le_bound
          henv_nonpos henv_le ((zmodSignAction l).toSignLabelQuotient x))

theorem nonzeroCarrierAveragedLogVolume_lt_zero_of_environment_negative
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_neg : evaluation.environmentDegree < 0) :
    evaluation.nonzeroCarrierAveragedLogVolume.averageLogVolume < 0 := by
  have hle :
      evaluation.nonzeroCarrierAveragedLogVolume.averageLogVolume <=
        evaluation.environmentDegree :=
    evaluation.nonzeroCarrierAverage_le_of_environment_le_bound
      (le_of_lt henv_neg) (le_refl evaluation.environmentDegree)
  linarith

theorem environment_le_gaussianDegree_nonzero_of_environment_nonnegative
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_nonneg : 0 <= evaluation.environmentDegree)
    (label : (zmodSignAction l).SignLabelQuotient) :
    evaluation.environmentDegree <=
      evaluation.gaussianDegree (IUTStage1ZModCuspFullLabel.nonzero label) := by
  rw [evaluation.gaussianDegree_eq_eval]
  have hexp_ge_one := thetaExponentOnAbsLabel_nonzero_ge_one (l := l) label
  have hmul :
      1 * evaluation.environmentDegree <=
        thetaExponentOnAbsLabel
          (l := l) (IUTStage1ZModCuspFullLabel.nonzero label) *
            evaluation.environmentDegree :=
    mul_le_mul_of_nonneg_right hexp_ge_one henv_nonneg
  simpa using hmul

theorem nonzeroCarrierAveragedLogVolume_gt_zero_of_environment_positive
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_pos : 0 < evaluation.environmentDegree) :
    0 < evaluation.nonzeroCarrierAveragedLogVolume.averageLogVolume := by
  haveI : Nonempty (zmodPointedQuotient l).NonzeroCarrier :=
    ⟨zmodOneNonzeroLabel l⟩
  have henv_le :
      evaluation.environmentDegree <=
        evaluation.nonzeroCarrierAveragedLogVolume.averageLogVolume :=
    IUTStage1LabelAveragedProcessionLogVolume.const_le_average_of_forall_le
      evaluation.nonzeroCarrierAveragedLogVolume
      (by
        intro x
        exact
          evaluation.environment_le_gaussianDegree_nonzero_of_environment_nonnegative
            (le_of_lt henv_pos) ((zmodSignAction l).toSignLabelQuotient x))
  exact lt_of_lt_of_le henv_pos henv_le

theorem coordinateAveragedLogVolume_gt_nonzeroCarrierAverage_of_negative
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_neg : evaluation.environmentDegree < 0) :
    evaluation.nonzeroCarrierAveragedLogVolume.averageLogVolume <
      evaluation.coordinateAveragedLogVolume.averageLogVolume := by
  rw [evaluation.coordinateAveragedLogVolume_eq_nonzero_mass_rescale]
  let factor : Real := ((l.value - 1 : Nat) : Real) / (l.value : Real)
  have hfactor_lt : factor < 1 := by
    have hl_pos : 0 < (l.value : Real) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 5) l.ge_five)
    have hlt_nat : l.value - 1 < l.value := by
      have hge : 5 ≤ l.value := l.ge_five
      omega
    have hlt_real : ((l.value - 1 : Nat) : Real) < (l.value : Real) := by
      exact_mod_cast hlt_nat
    dsimp [factor]
    rw [div_lt_one hl_pos]
    exact hlt_real
  have havg_neg :=
    evaluation.nonzeroCarrierAveragedLogVolume_lt_zero_of_environment_negative
      henv_neg
  nlinarith

theorem coordinateAveragedLogVolume_lt_nonzeroCarrierAverage_of_positive
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_pos : 0 < evaluation.environmentDegree) :
    evaluation.coordinateAveragedLogVolume.averageLogVolume <
      evaluation.nonzeroCarrierAveragedLogVolume.averageLogVolume := by
  rw [evaluation.coordinateAveragedLogVolume_eq_nonzero_mass_rescale]
  let factor : Real := ((l.value - 1 : Nat) : Real) / (l.value : Real)
  have hfactor_lt : factor < 1 := by
    have hl_pos : 0 < (l.value : Real) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 5) l.ge_five)
    have hlt_nat : l.value - 1 < l.value := by
      have hge : 5 ≤ l.value := l.ge_five
      omega
    have hlt_real : ((l.value - 1 : Nat) : Real) < (l.value : Real) := by
      exact_mod_cast hlt_nat
    dsimp [factor]
    rw [div_lt_one hl_pos]
    exact hlt_real
  have havg_pos :=
    evaluation.nonzeroCarrierAveragedLogVolume_gt_zero_of_environment_positive
      henv_pos
  nlinarith

theorem nonzeroCarrierAveragedLogVolume_eq_zero_of_environment_zero
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_zero : evaluation.environmentDegree = 0) :
    evaluation.nonzeroCarrierAveragedLogVolume.averageLogVolume = 0 := by
  rw [evaluation.nonzeroCarrierAveragedLogVolume.average_eq]
  change
    (Finset.univ.sum
          (fun x : (zmodPointedQuotient l).NonzeroCarrier =>
            evaluation.gaussianDegree
              (IUTStage1ZModCuspFullLabel.nonzero
                ((zmodSignAction l).toSignLabelQuotient x)))) /
        (Fintype.card (zmodPointedQuotient l).NonzeroCarrier : Real) = 0
  have hsum :
      Finset.univ.sum
          (fun x : (zmodPointedQuotient l).NonzeroCarrier =>
            evaluation.gaussianDegree
              (IUTStage1ZModCuspFullLabel.nonzero
                ((zmodSignAction l).toSignLabelQuotient x))) = 0 := by
    apply Finset.sum_eq_zero
    intro x _hx
    rw [evaluation.gaussianDegree_eq_eval, henv_zero]
    ring
  rw [hsum]
  simp

theorem coordinateAveragedLogVolume_eq_nonzeroCarrierAverage_iff
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.coordinateAveragedLogVolume.averageLogVolume =
        evaluation.nonzeroCarrierAveragedLogVolume.averageLogVolume ↔
      evaluation.environmentDegree = 0 := by
  constructor
  · intro h
    by_cases hneg : evaluation.environmentDegree < 0
    · have hlt :=
        evaluation.coordinateAveragedLogVolume_gt_nonzeroCarrierAverage_of_negative
          hneg
      linarith
    · by_cases hpos : 0 < evaluation.environmentDegree
      · have hlt :=
          evaluation.coordinateAveragedLogVolume_lt_nonzeroCarrierAverage_of_positive
            hpos
        linarith
      · linarith
  · intro henv_zero
    have hnonzero :=
      evaluation.nonzeroCarrierAveragedLogVolume_eq_zero_of_environment_zero
        henv_zero
    rw [evaluation.coordinateAveragedLogVolume_eq_nonzero_mass_rescale]
    rw [hnonzero]
    ring

noncomputable def coordinateNonzeroMassFactor (l : PrimeGeFive) : Real :=
  ((l.value - 1 : Nat) : Real) / (l.value : Real)

theorem coordinateNonzeroMassFactor_pos :
    0 < coordinateNonzeroMassFactor l := by
  unfold coordinateNonzeroMassFactor
  have hl_pos : 0 < (l.value : Real) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 5) l.ge_five)
  have hlm_pos : 0 < ((l.value - 1 : Nat) : Real) := by
    have hpos : 0 < l.value - 1 := by
      have hge : 5 ≤ l.value := l.ge_five
      omega
    exact_mod_cast hpos
  positivity

theorem coordinateAveragedLogVolume_lt_zero_of_environment_negative
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_neg : evaluation.environmentDegree < 0) :
    evaluation.coordinateAveragedLogVolume.averageLogVolume < 0 := by
  rw [evaluation.coordinateAveragedLogVolume_eq_nonzero_mass_rescale]
  have hfactor_pos : 0 < coordinateNonzeroMassFactor l :=
    coordinateNonzeroMassFactor_pos (l := l)
  have havg_neg :=
    evaluation.nonzeroCarrierAveragedLogVolume_lt_zero_of_environment_negative
      henv_neg
  change
    coordinateNonzeroMassFactor l *
      evaluation.nonzeroCarrierAveragedLogVolume.averageLogVolume < 0
  exact mul_neg_of_pos_of_neg hfactor_pos havg_neg

theorem coordinateAveragedLogVolume_gt_zero_of_environment_positive
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_pos : 0 < evaluation.environmentDegree) :
    0 < evaluation.coordinateAveragedLogVolume.averageLogVolume := by
  rw [evaluation.coordinateAveragedLogVolume_eq_nonzero_mass_rescale]
  have hfactor_pos : 0 < coordinateNonzeroMassFactor l :=
    coordinateNonzeroMassFactor_pos (l := l)
  have havg_pos :=
    evaluation.nonzeroCarrierAveragedLogVolume_gt_zero_of_environment_positive
      henv_pos
  change
    0 <
      coordinateNonzeroMassFactor l *
        evaluation.nonzeroCarrierAveragedLogVolume.averageLogVolume
  exact mul_pos hfactor_pos havg_pos

theorem coordinateAveragedLogVolume_eq_zero_iff
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.coordinateAveragedLogVolume.averageLogVolume = 0 ↔
      evaluation.environmentDegree = 0 := by
  constructor
  · intro h
    by_cases hneg : evaluation.environmentDegree < 0
    · have hlt :=
        evaluation.coordinateAveragedLogVolume_lt_zero_of_environment_negative
          hneg
      linarith
    · by_cases hpos : 0 < evaluation.environmentDegree
      · have hgt :=
          evaluation.coordinateAveragedLogVolume_gt_zero_of_environment_positive
            hpos
        linarith
      · linarith
  · intro henv_zero
    rw [evaluation.coordinateAveragedLogVolume_eq_nonzero_mass_rescale]
    rw [evaluation.nonzeroCarrierAveragedLogVolume_eq_zero_of_environment_zero
      henv_zero]
    ring

theorem forall_coordinateFullLabel_le_implies_bound_nonnegative
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value)
    {c : Real}
    (hbound :
      ∀ j : ZMod l.value,
        evaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (coordinateEquiv j)) <= c) :
    0 <= c := by
  have hzero := hbound (coordinateEquiv.symm (0 : ZMod l.value))
  simpa [IUTStage1ZModCuspFullLabel.fromCoordinate_zero,
    gaussianDegree_zero] using hzero

theorem not_forall_coordinateFullLabel_le_of_negative_bound
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value)
    {c : Real}
    (hc : c < 0) :
    ¬ ∀ j : ZMod l.value,
        evaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (coordinateEquiv j)) <= c := by
  intro hbound
  have hnonneg :=
    evaluation.forall_coordinateFullLabel_le_implies_bound_nonnegative
      coordinateEquiv hbound
  linarith

theorem forall_coordinateFullLabel_le_iff_bound_nonnegative
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value)
    (henv_nonpos : evaluation.environmentDegree <= 0)
    {c : Real} :
    (∀ j : ZMod l.value,
        evaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (coordinateEquiv j)) <= c) ↔
      0 <= c := by
  constructor
  · exact evaluation.forall_coordinateFullLabel_le_implies_bound_nonnegative
      coordinateEquiv
  · intro hc j
    exact
      evaluation.gaussianDegree_le_of_environment_nonpositive_of_nonnegative_bound
        henv_nonpos hc
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (coordinateEquiv j))

theorem environment_le_bound_of_forall_coordinateFullLabel_nonzero_le
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value)
    {c : Real}
    (hbound :
      ∀ j : ZMod l.value,
        coordinateEquiv j ≠ 0 ->
          evaluation.gaussianDegree
              (IUTStage1ZModCuspFullLabel.fromCoordinate l
                (coordinateEquiv j)) <= c) :
    evaluation.environmentDegree <= c := by
  haveI : Fact (1 < l.value) :=
    ⟨lt_of_lt_of_le (by norm_num) l.ge_five⟩
  have hone_ne :
      coordinateEquiv (coordinateEquiv.symm (1 : ZMod l.value)) ≠ 0 := by
    simp
  have h :=
    hbound (coordinateEquiv.symm (1 : ZMod l.value)) hone_ne
  simpa [evaluation.gaussianDegree_one] using h

theorem forall_coordinateFullLabel_nonzero_le_of_forall_coordinateFullLabel_le
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value)
    {c : Real}
    (hbound :
      ∀ j : ZMod l.value,
        evaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (coordinateEquiv j)) <= c) :
    ∀ j : ZMod l.value,
      coordinateEquiv j ≠ 0 ->
        evaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (coordinateEquiv j)) <= c := by
  intro j _hj
  exact hbound j

theorem forall_coordinateFullLabel_le_iff_bound_nonnegative_and_nonzero_le
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value)
    {c : Real} :
    (∀ j : ZMod l.value,
        evaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (coordinateEquiv j)) <= c) ↔
      0 <= c ∧
        ∀ j : ZMod l.value,
          coordinateEquiv j ≠ 0 ->
            evaluation.gaussianDegree
                (IUTStage1ZModCuspFullLabel.fromCoordinate l
                  (coordinateEquiv j)) <= c := by
  constructor
  · intro hbound
    exact
      ⟨evaluation.forall_coordinateFullLabel_le_implies_bound_nonnegative
          coordinateEquiv hbound,
        evaluation.forall_coordinateFullLabel_nonzero_le_of_forall_coordinateFullLabel_le
          coordinateEquiv hbound⟩
  · rintro ⟨hc, hnonzero⟩ j
    by_cases hj : coordinateEquiv j = 0
    · rw [hj, IUTStage1ZModCuspFullLabel.fromCoordinate_zero]
      rw [evaluation.gaussianDegree_zero]
      exact hc
    · exact hnonzero j hj

theorem forall_coordinateFullLabel_nonzero_le_iff_environment_le_bound
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value)
    (henv_nonpos : evaluation.environmentDegree <= 0)
    {c : Real} :
    (∀ j : ZMod l.value,
        coordinateEquiv j ≠ 0 ->
          evaluation.gaussianDegree
              (IUTStage1ZModCuspFullLabel.fromCoordinate l
                (coordinateEquiv j)) <= c) ↔
      evaluation.environmentDegree <= c := by
  constructor
  · intro hbound
    exact evaluation.environment_le_bound_of_forall_coordinateFullLabel_nonzero_le
      coordinateEquiv hbound
  · intro henv_le j hj
    rw [IUTStage1ZModCuspFullLabel.fromCoordinate_nonzero l
      (coordinateEquiv j) hj]
    exact evaluation.gaussianDegree_nonzero_le_of_environment_le_bound
      henv_nonpos henv_le
      (zmodSignLabelFromCoordinate l (coordinateEquiv j) hj)

theorem forall_coordinateFullLabel_le_iff_bound_nonnegative_and_environment_le
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value)
    (henv_nonpos : evaluation.environmentDegree <= 0)
    {c : Real} :
    (∀ j : ZMod l.value,
        evaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (coordinateEquiv j)) <= c) ↔
      0 <= c ∧ evaluation.environmentDegree <= c := by
  rw [evaluation.forall_coordinateFullLabel_le_iff_bound_nonnegative_and_nonzero_le
    coordinateEquiv]
  rw [evaluation.forall_coordinateFullLabel_nonzero_le_iff_environment_le_bound
    coordinateEquiv henv_nonpos]

theorem target_nonzeroBound_iff_source_environment_le_of_gaussianDegree_one_eq
    (sourceEvaluation targetEvaluation : GaussianMonoidDegreeEvaluation l)
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value)
    (target_environment_nonpositive :
      targetEvaluation.environmentDegree <= 0)
    (canonical_one_preserved :
      targetEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)))
    {c : Real} :
    (∀ j : ZMod l.value,
        coordinateEquiv j ≠ 0 ->
          targetEvaluation.gaussianDegree
              (IUTStage1ZModCuspFullLabel.fromCoordinate l
                (coordinateEquiv j)) <= c) ↔
      sourceEvaluation.environmentDegree <= c := by
  have henv :
      targetEvaluation.environmentDegree =
        sourceEvaluation.environmentDegree :=
    sourceEvaluation.environmentDegree_eq_of_gaussianDegree_one_eq
      targetEvaluation canonical_one_preserved
  rw [targetEvaluation.forall_coordinateFullLabel_nonzero_le_iff_environment_le_bound
    coordinateEquiv target_environment_nonpositive]
  constructor
  · intro htarget
    simpa [henv] using htarget
  · intro hsource
    simpa [henv] using hsource

theorem target_nonzeroBound_iff_source_nonzeroBound_of_gaussianDegree_one_eq
    (sourceEvaluation targetEvaluation : GaussianMonoidDegreeEvaluation l)
    (targetCoordinateEquiv sourceCoordinateEquiv :
      ZMod l.value ≃ ZMod l.value)
    (target_environment_nonpositive :
      targetEvaluation.environmentDegree <= 0)
    (source_environment_nonpositive :
      sourceEvaluation.environmentDegree <= 0)
    (canonical_one_preserved :
      targetEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)))
    {c : Real} :
    (∀ j : ZMod l.value,
        targetCoordinateEquiv j ≠ 0 ->
          targetEvaluation.gaussianDegree
              (IUTStage1ZModCuspFullLabel.fromCoordinate l
                (targetCoordinateEquiv j)) <= c) ↔
      ∀ j : ZMod l.value,
        sourceCoordinateEquiv j ≠ 0 ->
          sourceEvaluation.gaussianDegree
              (IUTStage1ZModCuspFullLabel.fromCoordinate l
                (sourceCoordinateEquiv j)) <= c := by
  rw [sourceEvaluation
    |>.target_nonzeroBound_iff_source_environment_le_of_gaussianDegree_one_eq
      targetEvaluation targetCoordinateEquiv target_environment_nonpositive
      canonical_one_preserved]
  rw [sourceEvaluation.forall_coordinateFullLabel_nonzero_le_iff_environment_le_bound
    sourceCoordinateEquiv source_environment_nonpositive]

theorem target_allLabelBound_iff_nonnegative_and_source_environment_le_of_gaussianDegree_one_eq
    (sourceEvaluation targetEvaluation : GaussianMonoidDegreeEvaluation l)
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value)
    (target_environment_nonpositive :
      targetEvaluation.environmentDegree <= 0)
    (canonical_one_preserved :
      targetEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)))
    {c : Real} :
    (∀ j : ZMod l.value,
        targetEvaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (coordinateEquiv j)) <= c) ↔
      0 <= c ∧ sourceEvaluation.environmentDegree <= c := by
  rw [targetEvaluation.forall_coordinateFullLabel_le_iff_bound_nonnegative_and_nonzero_le
    coordinateEquiv]
  rw [sourceEvaluation.target_nonzeroBound_iff_source_environment_le_of_gaussianDegree_one_eq
    targetEvaluation coordinateEquiv target_environment_nonpositive
    canonical_one_preserved]

theorem target_allLabelBound_iff_source_allLabelBound_of_gaussianDegree_one_eq
    (sourceEvaluation targetEvaluation : GaussianMonoidDegreeEvaluation l)
    (targetCoordinateEquiv sourceCoordinateEquiv :
      ZMod l.value ≃ ZMod l.value)
    (target_environment_nonpositive :
      targetEvaluation.environmentDegree <= 0)
    (source_environment_nonpositive :
      sourceEvaluation.environmentDegree <= 0)
    (canonical_one_preserved :
      targetEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        sourceEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)))
    {c : Real} :
    (∀ j : ZMod l.value,
        targetEvaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (targetCoordinateEquiv j)) <= c) ↔
      ∀ j : ZMod l.value,
        sourceEvaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.fromCoordinate l
              (sourceCoordinateEquiv j)) <= c := by
  rw [sourceEvaluation
    |>.target_allLabelBound_iff_nonnegative_and_source_environment_le_of_gaussianDegree_one_eq
      targetEvaluation targetCoordinateEquiv target_environment_nonpositive
      canonical_one_preserved]
  rw [sourceEvaluation.forall_coordinateFullLabel_le_iff_bound_nonnegative_and_environment_le
    sourceCoordinateEquiv source_environment_nonpositive]

end GaussianMonoidDegreeEvaluation

/--
Source-facing degree-level Hodge--Arakelov theta-value evaluation.

IUT II describes the operation of passing from theta monoids to Gaussian
monoids by evaluation at `l`-torsion labels, with degree pattern
`q -> (q^{j^2})_j`.  This record keeps the bad-local theta-root/cusp source
next to the theta-monoid degree from which the Gaussian degree evaluation is
constructed.
-/
structure IUTStage1HodgeArakelovThetaValueEvaluationSource
    (l : PrimeGeFive) {F : Type v} [Field F]
    (X C : HyperbolicOrbicurveModel F) where
  thetaRootSource : IUTStage1ThetaRootCuspLabelSourcePackage l X C
  thetaMonoidDegree : Real

namespace IUTStage1HodgeArakelovThetaValueEvaluationSource

variable {l : PrimeGeFive} {F : Type v} [Field F]
variable {X C : HyperbolicOrbicurveModel F}

noncomputable def toGaussianMonoidDegreeEvaluation
    (source :
      IUTStage1HodgeArakelovThetaValueEvaluationSource l X C) :
    IUTStage1ZModSquareWeightProfile.GaussianMonoidDegreeEvaluation l :=
  { environmentDegree := source.thetaMonoidDegree,
    gaussianDegree := fun label =>
      thetaExponentOnAbsLabel (l := l) label * source.thetaMonoidDegree,
    gaussianDegree_eq_eval := by
      intro label
      rfl }

noncomputable def thetaValueDegree
    (source :
      IUTStage1HodgeArakelovThetaValueEvaluationSource l X C)
    (label : IUTStage1ZModCuspFullLabel l) : Real :=
  thetaExponentOnAbsLabel (l := l) label * source.thetaMonoidDegree

theorem gaussianDegree_eq_thetaValueDegree
    (source :
      IUTStage1HodgeArakelovThetaValueEvaluationSource l X C)
    (label : IUTStage1ZModCuspFullLabel l) :
    source.toGaussianMonoidDegreeEvaluation.gaussianDegree label =
      source.thetaValueDegree label :=
  rfl

theorem environmentDegree_eq
    (source :
      IUTStage1HodgeArakelovThetaValueEvaluationSource l X C) :
    source.toGaussianMonoidDegreeEvaluation.environmentDegree =
      source.thetaMonoidDegree :=
  rfl

theorem zeroDegree_eq_zero
    (source :
      IUTStage1HodgeArakelovThetaValueEvaluationSource l X C) :
    source.toGaussianMonoidDegreeEvaluation.gaussianDegree
        IUTStage1ZModCuspFullLabel.zero = 0 :=
  source.toGaussianMonoidDegreeEvaluation.gaussianDegree_zero

theorem canonicalOneDegree_eq_thetaMonoidDegree
    (source :
      IUTStage1HodgeArakelovThetaValueEvaluationSource l X C) :
    source.toGaussianMonoidDegreeEvaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
      source.thetaMonoidDegree :=
  source.toGaussianMonoidDegreeEvaluation.gaussianDegree_one

theorem canonicalThetaRootLabel_ne_zero
    (source :
      IUTStage1HodgeArakelovThetaValueEvaluationSource l X C) :
    source.thetaRootSource.canonicalFullLabel ≠
      IUTStage1ZModCuspFullLabel.zero :=
  source.thetaRootSource.canonicalFullLabel_ne_zero

theorem canonicalThetaRootLabelDegree_eq_thetaMonoidDegree_of_zmodQuotient
    (source :
      IUTStage1HodgeArakelovThetaValueEvaluationSource l X C)
    (hquot :
      source.thetaRootSource.quotientZData = zmodBadLocalQuotientZData l) :
    source.toGaussianMonoidDegreeEvaluation.gaussianDegree
        source.thetaRootSource.canonicalFullLabel =
      source.thetaMonoidDegree := by
  rw [source.thetaRootSource
    |>.canonicalFullLabel_eq_zmodCanonical_of_quotientZData_eq_zmod hquot]
  rw [← IUTStage1ZModCuspFullLabel.fromCoordinate_one l]
  exact source.canonicalOneDegree_eq_thetaMonoidDegree

theorem environmentDegree_eq_of_canonicalOneDegree_eq
    (source target :
      IUTStage1HodgeArakelovThetaValueEvaluationSource l X C)
    (hone :
      target.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        source.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value))) :
    target.toGaussianMonoidDegreeEvaluation.environmentDegree =
      source.toGaussianMonoidDegreeEvaluation.environmentDegree :=
  source.toGaussianMonoidDegreeEvaluation
    |>.environmentDegree_eq_of_gaussianDegree_one_eq
      target.toGaussianMonoidDegreeEvaluation hone

theorem thetaValueEvaluation_endpoint
    (source :
      IUTStage1HodgeArakelovThetaValueEvaluationSource l X C) :
    source.thetaRootSource.canonicalGenerator.canonicalGeneratorUpToSign ∧
      source.thetaRootSource.canonicalFullLabel ≠
        IUTStage1ZModCuspFullLabel.zero ∧
      source.toGaussianMonoidDegreeEvaluation.gaussianDegree
          IUTStage1ZModCuspFullLabel.zero = 0 ∧
      source.toGaussianMonoidDegreeEvaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
        source.thetaMonoidDegree :=
  ⟨source.thetaRootSource.canonicalGeneratorUpToSign,
    source.canonicalThetaRootLabel_ne_zero,
    source.zeroDegree_eq_zero,
    source.canonicalOneDegree_eq_thetaMonoidDegree⟩

end IUTStage1HodgeArakelovThetaValueEvaluationSource

/--
Audited Hodge--Arakelov theta evaluation source for the finite Gaussian
degree corridor.

This wraps the current degree-level theta-value source with the bad-local
quotient identification.  The derived projections expose the objects used by
the finite `q^{j^2}` shadow of IUT II: theta-root labels, the Gaussian monoid
degree evaluation, full-label log-volume compatibility, canonical label
behavior, and the canonical square-weight profile.
-/
structure IUTStage1HodgeArakelovThetaEvaluationSource
    (l : PrimeGeFive) {F : Type v} [Field F]
    (X C : HyperbolicOrbicurveModel F) where
  valueSource : IUTStage1HodgeArakelovThetaValueEvaluationSource l X C
  quotientZData_eq_zmod :
    valueSource.thetaRootSource.quotientZData = zmodBadLocalQuotientZData l

namespace IUTStage1HodgeArakelovThetaEvaluationSource

variable {l : PrimeGeFive} {F : Type v} [Field F]
variable {X C : HyperbolicOrbicurveModel F}

def ofValueSource
    (valueSource :
      IUTStage1HodgeArakelovThetaValueEvaluationSource l X C)
    (quotientZData_eq_zmod :
      valueSource.thetaRootSource.quotientZData =
        zmodBadLocalQuotientZData l) :
    IUTStage1HodgeArakelovThetaEvaluationSource l X C :=
  { valueSource := valueSource,
    quotientZData_eq_zmod := quotientZData_eq_zmod }

def thetaRootSource
    (source : IUTStage1HodgeArakelovThetaEvaluationSource l X C) :
    IUTStage1ThetaRootCuspLabelSourcePackage l X C :=
  source.valueSource.thetaRootSource

def thetaMonoidDegree
    (source : IUTStage1HodgeArakelovThetaEvaluationSource l X C) : Real :=
  source.valueSource.thetaMonoidDegree

noncomputable def toGaussianMonoidDegreeEvaluation
    (source : IUTStage1HodgeArakelovThetaEvaluationSource l X C) :
    GaussianMonoidDegreeEvaluation l :=
  source.valueSource.toGaussianMonoidDegreeEvaluation

noncomputable def fullLabelCompatibility
    (source : IUTStage1HodgeArakelovThetaEvaluationSource l X C) :
    IUTStage1ZModCuspLabelLogVolumeCompatibility l :=
  source.toGaussianMonoidDegreeEvaluation.toCuspLabelLogVolumeCompatibility

def squareWeightProfile
    (_source : IUTStage1HodgeArakelovThetaEvaluationSource l X C) :
    IUTStage1ZModSquareWeightProfile l :=
  IUTStage1ZModSquareWeightProfile.canonicalSquareWeights l

theorem canonicalFullLabel_eq_one
    (source : IUTStage1HodgeArakelovThetaEvaluationSource l X C) :
    source.thetaRootSource.canonicalFullLabel =
      IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value) := by
  rw [source.thetaRootSource
    |>.canonicalFullLabel_eq_zmodCanonical_of_quotientZData_eq_zmod
      source.quotientZData_eq_zmod]
  exact (IUTStage1ZModCuspFullLabel.fromCoordinate_one l).symm

theorem canonicalFullLabel_ne_zero
    (source : IUTStage1HodgeArakelovThetaEvaluationSource l X C) :
    source.thetaRootSource.canonicalFullLabel ≠
      IUTStage1ZModCuspFullLabel.zero :=
  source.valueSource.canonicalThetaRootLabel_ne_zero

theorem zeroDegree_eq_zero
    (source : IUTStage1HodgeArakelovThetaEvaluationSource l X C) :
    source.toGaussianMonoidDegreeEvaluation.gaussianDegree
        IUTStage1ZModCuspFullLabel.zero = 0 :=
  source.valueSource.zeroDegree_eq_zero

theorem canonicalOneDegree_eq_thetaMonoidDegree
    (source : IUTStage1HodgeArakelovThetaEvaluationSource l X C) :
    source.toGaussianMonoidDegreeEvaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
      source.thetaMonoidDegree :=
  source.valueSource.canonicalOneDegree_eq_thetaMonoidDegree

theorem canonicalFullLabelDegree_eq_thetaMonoidDegree
    (source : IUTStage1HodgeArakelovThetaEvaluationSource l X C) :
    source.toGaussianMonoidDegreeEvaluation.gaussianDegree
        source.thetaRootSource.canonicalFullLabel =
      source.thetaMonoidDegree := by
  rw [source.canonicalFullLabel_eq_one]
  exact source.canonicalOneDegree_eq_thetaMonoidDegree

theorem fullLabelCompatibility_fullLabelLogVolume
    (source : IUTStage1HodgeArakelovThetaEvaluationSource l X C)
    (label : IUTStage1ZModCuspFullLabel l) :
    source.fullLabelCompatibility.fullLabelLogVolume label =
      source.toGaussianMonoidDegreeEvaluation.gaussianDegree label :=
  source.toGaussianMonoidDegreeEvaluation
    |>.toCuspLabelLogVolumeCompatibility_fullLabelLogVolume label

theorem coordinateSquareWeight_degree
    (source : IUTStage1HodgeArakelovThetaEvaluationSource l X C)
    (j : ZMod l.value) (hhalf : j.val ≤ l.value / 2) :
    source.toGaussianMonoidDegreeEvaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
      source.squareWeightProfile.weight j * source.thetaMonoidDegree := by
  have h :=
    source.toGaussianMonoidDegreeEvaluation
      |>.finiteQJSquaredSquareWeight_endpoint source.squareWeightProfile
  simpa [thetaMonoidDegree, squareWeightProfile,
    source.valueSource.environmentDegree_eq] using h.1 j hhalf

theorem thetaEvaluation_endpoint
    (source : IUTStage1HodgeArakelovThetaEvaluationSource l X C) :
    source.thetaRootSource.canonicalGenerator.canonicalGeneratorUpToSign ∧
      source.thetaRootSource.canonicalFullLabel =
        IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value) ∧
      source.thetaRootSource.canonicalFullLabel ≠
        IUTStage1ZModCuspFullLabel.zero ∧
      source.toGaussianMonoidDegreeEvaluation.gaussianDegree
          IUTStage1ZModCuspFullLabel.zero = 0 ∧
      source.toGaussianMonoidDegreeEvaluation.gaussianDegree
          source.thetaRootSource.canonicalFullLabel =
        source.thetaMonoidDegree ∧
      (∀ j : ZMod l.value, j.val ≤ l.value / 2 ->
        source.toGaussianMonoidDegreeEvaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
          source.squareWeightProfile.weight j * source.thetaMonoidDegree) :=
  ⟨source.thetaRootSource.canonicalGeneratorUpToSign,
    source.canonicalFullLabel_eq_one,
    source.canonicalFullLabel_ne_zero,
    source.zeroDegree_eq_zero,
    source.canonicalFullLabelDegree_eq_thetaMonoidDegree,
    source.coordinateSquareWeight_degree⟩

end IUTStage1HodgeArakelovThetaEvaluationSource

def absLabelProcessionTop (l : PrimeGeFive) : Nat :=
  l.value / 2

theorem absLabelProcessionTop_eq_half_minus_one (l : PrimeGeFive) :
    absLabelProcessionTop l = (l.value - 1) / 2 := by
  unfold absLabelProcessionTop
  have hodd : Odd l.value := l.prime.odd_of_ne_two l.ne_two
  rcases hodd with ⟨k, hk⟩
  rw [hk]
  omega

theorem absLabelProcession_card_eq_half_plus_one (l : PrimeGeFive) :
    Fintype.card (IUTStage1ProcessionContainer (absLabelProcessionTop l)) =
      (l.value + 1) / 2 := by
  rw [IUTStage1ProcessionContainer.card_eq]
  unfold absLabelProcessionTop
  have hodd : Odd l.value := l.prime.odd_of_ne_two l.ne_two
  rcases hodd with ⟨k, hk⟩
  rw [hk]
  omega

def absLabelFromProcession
    (l : PrimeGeFive)
    (label : IUTStage1ProcessionContainer (absLabelProcessionTop l)) :
    IUTStage1ZModCuspFullLabel l :=
  IUTStage1ZModCuspFullLabel.fromCoordinate l
    (label.val : ZMod l.value)

theorem absLabelProcession_value_le_half
    (label : IUTStage1ProcessionContainer (absLabelProcessionTop l)) :
    label.val ≤ l.value / 2 := by
  have h := label.isLt
  unfold absLabelProcessionTop at h
  omega

theorem absLabelFromProcession_core :
    absLabelFromProcession l
        (IUTStage1ProcessionContainer.core
          (absLabelProcessionTop l)) =
      IUTStage1ZModCuspFullLabel.zero := by
  simp [absLabelFromProcession, IUTStage1ProcessionContainer.core,
    IUTStage1ZModCuspFullLabel.fromCoordinate_zero]

theorem absLabelFromProcession_surjective :
    Function.Surjective (absLabelFromProcession l) := by
  intro label
  rcases IUTStage1ZModCuspFullLabel.fromCoordinate_surjective
      (l := l) label with ⟨j, hj⟩
  let k : Nat := j.valMinAbs.natAbs
  have hk_le : k ≤ absLabelProcessionTop l := by
    dsimp [k]
    unfold absLabelProcessionTop
    exact ZMod.natAbs_valMinAbs_le j
  refine ⟨⟨k, by omega⟩, ?_⟩
  dsimp [absLabelFromProcession, k]
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_natAbs_valMinAbs]
  exact hj

theorem thetaExponentOnAbsLabel_fromProcession
    (label : IUTStage1ProcessionContainer (absLabelProcessionTop l)) :
    thetaExponentOnAbsLabel
        (l := l) (absLabelFromProcession l label) =
      ((label.val : Real) ^ 2) := by
  unfold absLabelFromProcession
  have hle : label.val ≤ l.value / 2 :=
    absLabelProcession_value_le_half (l := l) label
  have hlt : label.val < l.value := by
    have hge : 5 ≤ l.value := l.ge_five
    omega
  have hval :
      ((label.val : ZMod l.value).val) = label.val :=
    ZMod.val_natCast_of_lt hlt
  have hhalf :
      ((label.val : ZMod l.value).val) ≤ l.value / 2 := by
    rw [hval]
    exact hle
  rw [thetaExponentOnAbsLabel_fromCoordinate_of_val_le_half
    (l := l) (label.val : ZMod l.value) hhalf]
  rw [hval]

theorem absLabelFromProcession_injective :
    Function.Injective (absLabelFromProcession l) := by
  intro a b h
  have hexp := congrArg (thetaExponentOnAbsLabel (l := l)) h
  rw [thetaExponentOnAbsLabel_fromProcession,
    thetaExponentOnAbsLabel_fromProcession] at hexp
  have ha_nonneg : 0 <= (a.val : Real) := by
    exact_mod_cast Nat.zero_le a.val
  have hb_nonneg : 0 <= (b.val : Real) := by
    exact_mod_cast Nat.zero_le b.val
  have hval_real : (a.val : Real) = (b.val : Real) := by
    nlinarith
  have hval_nat : a.val = b.val := by
    exact_mod_cast hval_real
  exact Fin.ext hval_nat

noncomputable def absLabelProcessionEquivFullLabel :
    IUTStage1ProcessionContainer (absLabelProcessionTop l) ≃
      IUTStage1ZModCuspFullLabel l :=
  Equiv.ofBijective (absLabelFromProcession l)
    ⟨absLabelFromProcession_injective, absLabelFromProcession_surjective⟩

theorem absLabelProcessionEquivFullLabel_apply
    (label : IUTStage1ProcessionContainer (absLabelProcessionTop l)) :
    absLabelProcessionEquivFullLabel label = absLabelFromProcession l label :=
  rfl

noncomputable instance zmodCuspFullLabelFintype :
    Fintype (IUTStage1ZModCuspFullLabel l) :=
  Fintype.ofEquiv
    (IUTStage1ProcessionContainer (absLabelProcessionTop l))
    (absLabelProcessionEquivFullLabel (l := l))

theorem fullLabel_card_eq_procession :
    Fintype.card (IUTStage1ZModCuspFullLabel l) =
      Fintype.card
        (IUTStage1ProcessionContainer (absLabelProcessionTop l)) :=
  Fintype.card_congr (absLabelProcessionEquivFullLabel (l := l)).symm

theorem fullLabel_card_eq_half_plus_one (l : PrimeGeFive) :
    Fintype.card (IUTStage1ZModCuspFullLabel l) = (l.value + 1) / 2 := by
  rw [fullLabel_card_eq_procession,
    absLabelProcession_card_eq_half_plus_one]

theorem subordinateFullLabel_card_eq_absLabelProcessionTop :
    (@Finset.filter (IUTStage1ZModCuspFullLabel l)
      (fun label : IUTStage1ZModCuspFullLabel l =>
        IUTStage1ZModCuspFullLabel.WeightedVolumeSubordinate
          label IUTStage1ZModCuspFullLabel.zero)
      (Classical.decPred _) Finset.univ).card =
        absLabelProcessionTop l := by
  classical
  have hset :
      (@Finset.filter (IUTStage1ZModCuspFullLabel l)
        (fun label : IUTStage1ZModCuspFullLabel l =>
          IUTStage1ZModCuspFullLabel.WeightedVolumeSubordinate
            label IUTStage1ZModCuspFullLabel.zero)
        (Classical.decPred _) Finset.univ) =
          (Finset.univ.erase IUTStage1ZModCuspFullLabel.zero) := by
    ext label
    simp [IUTStage1ZModCuspFullLabel.weightedVolumeSubordinate_zero_iff_ne_zero]
  rw [hset]
  rw [Finset.card_erase_of_mem (Finset.mem_univ IUTStage1ZModCuspFullLabel.zero)]
  rw [Finset.card_univ, fullLabel_card_eq_procession,
    IUTStage1ProcessionContainer.card_eq]
  omega

theorem fullLabel_sum_eq_zero_add_subordinate_sum
    (f : IUTStage1ZModCuspFullLabel l -> Real) :
    Finset.univ.sum f =
      f IUTStage1ZModCuspFullLabel.zero +
        (@Finset.filter (IUTStage1ZModCuspFullLabel l)
          (fun label : IUTStage1ZModCuspFullLabel l =>
            IUTStage1ZModCuspFullLabel.WeightedVolumeSubordinate
              label IUTStage1ZModCuspFullLabel.zero)
          (Classical.decPred _) Finset.univ).sum f := by
  classical
  have hset :
      (@Finset.filter (IUTStage1ZModCuspFullLabel l)
        (fun label : IUTStage1ZModCuspFullLabel l =>
          IUTStage1ZModCuspFullLabel.WeightedVolumeSubordinate
            label IUTStage1ZModCuspFullLabel.zero)
        (Classical.decPred _) Finset.univ) =
          (Finset.univ.erase IUTStage1ZModCuspFullLabel.zero) := by
    ext label
    simp [IUTStage1ZModCuspFullLabel.weightedVolumeSubordinate_zero_iff_ne_zero]
  rw [hset]
  have hsplit :=
    Finset.sum_erase_add (s := (Finset.univ : Finset (IUTStage1ZModCuspFullLabel l)))
      (f := f)
      (a := IUTStage1ZModCuspFullLabel.zero)
      (Finset.mem_univ IUTStage1ZModCuspFullLabel.zero)
  linarith

theorem fullLabel_average_eq_zero_add_subordinate_sum_div
    (f : IUTStage1ZModCuspFullLabel l -> Real) :
    (Finset.univ.sum f) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) =
      (f IUTStage1ZModCuspFullLabel.zero +
        (@Finset.filter (IUTStage1ZModCuspFullLabel l)
          (fun label : IUTStage1ZModCuspFullLabel l =>
            IUTStage1ZModCuspFullLabel.WeightedVolumeSubordinate
              label IUTStage1ZModCuspFullLabel.zero)
          (Classical.decPred _) Finset.univ).sum f) /
        ((absLabelProcessionTop l : Real) + 1) := by
  rw [fullLabel_sum_eq_zero_add_subordinate_sum]
  rw [fullLabel_card_eq_procession, IUTStage1ProcessionContainer.card_eq]
  norm_num

theorem fullLabel_sum_unitAction_eq
    (a : (ZMod l.value)ˣ) (f : IUTStage1ZModCuspFullLabel l -> Real) :
    (Finset.univ.sum fun label : IUTStage1ZModCuspFullLabel l =>
      f (IUTStage1ZModCuspFullLabel.unitActionOnFullLabel l a label)) =
      Finset.univ.sum f :=
  Fintype.sum_equiv
    (IUTStage1ZModCuspFullLabel.unitActionOnFullLabelEquiv l a)
    (fun label : IUTStage1ZModCuspFullLabel l =>
      f (IUTStage1ZModCuspFullLabel.unitActionOnFullLabel l a label))
    f
    (fun _label => rfl)

theorem fullLabel_average_unitAction_eq
    (a : (ZMod l.value)ˣ) (f : IUTStage1ZModCuspFullLabel l -> Real) :
    (Finset.univ.sum fun label : IUTStage1ZModCuspFullLabel l =>
      f (IUTStage1ZModCuspFullLabel.unitActionOnFullLabel l a label)) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) =
      (Finset.univ.sum f) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) := by
  rw [fullLabel_sum_unitAction_eq]

theorem subordinateFullLabel_sum_unitAction_eq
    (a : (ZMod l.value)ˣ) (f : IUTStage1ZModCuspFullLabel l -> Real) :
    (@Finset.filter (IUTStage1ZModCuspFullLabel l)
      (fun label : IUTStage1ZModCuspFullLabel l =>
        IUTStage1ZModCuspFullLabel.WeightedVolumeSubordinate
          label IUTStage1ZModCuspFullLabel.zero)
      (Classical.decPred _) Finset.univ).sum
        (fun label : IUTStage1ZModCuspFullLabel l =>
          f (IUTStage1ZModCuspFullLabel.unitActionOnFullLabel l a label)) =
      (@Finset.filter (IUTStage1ZModCuspFullLabel l)
        (fun label : IUTStage1ZModCuspFullLabel l =>
          IUTStage1ZModCuspFullLabel.WeightedVolumeSubordinate
            label IUTStage1ZModCuspFullLabel.zero)
        (Classical.decPred _) Finset.univ).sum f := by
  classical
  have hfull := fullLabel_sum_unitAction_eq (l := l) a f
  have hleft :=
    fullLabel_sum_eq_zero_add_subordinate_sum
      (l := l)
      (fun label : IUTStage1ZModCuspFullLabel l =>
        f (IUTStage1ZModCuspFullLabel.unitActionOnFullLabel l a label))
  have hright := fullLabel_sum_eq_zero_add_subordinate_sum (l := l) f
  rw [hleft, hright] at hfull
  rw [IUTStage1ZModCuspFullLabel.unitActionOnFullLabel_zero] at hfull
  linarith

theorem fullLabel_sum_eq_procession_sum
    (f : IUTStage1ZModCuspFullLabel l -> Real) :
    (Finset.univ.sum f) =
      Finset.univ.sum fun label :
        IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
          f (absLabelFromProcession l label) := by
  symm
  exact Fintype.sum_equiv (absLabelProcessionEquivFullLabel (l := l))
    (fun label : IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
      f (absLabelFromProcession l label))
    f
    (by
      intro label
      rw [absLabelProcessionEquivFullLabel_apply])

theorem fullLabel_average_eq_procession_average
    (f : IUTStage1ZModCuspFullLabel l -> Real) :
    (Finset.univ.sum f) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) =
      (Finset.univ.sum fun label :
        IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
          f (absLabelFromProcession l label)) /
        (Fintype.card
          (IUTStage1ProcessionContainer (absLabelProcessionTop l)) : Real) := by
  rw [fullLabel_sum_eq_procession_sum, fullLabel_card_eq_procession]

theorem gaussianDegree_fromProcession
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (label : IUTStage1ProcessionContainer (absLabelProcessionTop l)) :
    evaluation.gaussianDegree (absLabelFromProcession l label) =
      ((label.val : Real) ^ 2) * evaluation.environmentDegree := by
  rw [evaluation.gaussianDegree_eq_eval,
    thetaExponentOnAbsLabel_fromProcession]

theorem gaussianDegree_processionCore
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.gaussianDegree
        (absLabelFromProcession l
          (IUTStage1ProcessionContainer.core
            (absLabelProcessionTop l))) = 0 := by
  rw [absLabelFromProcession_core, evaluation.gaussianDegree_zero]

theorem gaussianDegree_procession_sum_eq_square_sum
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    (Finset.univ.sum fun label :
      IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
        evaluation.gaussianDegree (absLabelFromProcession l label)) =
      (Finset.univ.sum fun label :
        IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
          ((label.val : Real) ^ 2)) *
        evaluation.environmentDegree := by
  calc
    (Finset.univ.sum fun label :
      IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
        evaluation.gaussianDegree (absLabelFromProcession l label)) =
        Finset.univ.sum fun label :
          IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
            ((label.val : Real) ^ 2) * evaluation.environmentDegree := by
      apply Finset.sum_congr rfl
      intro label _hlabel
      exact gaussianDegree_fromProcession evaluation label
    _ =
        (Finset.univ.sum fun label :
          IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
            ((label.val : Real) ^ 2)) *
          evaluation.environmentDegree := by
      rw [Finset.sum_mul]

theorem absLabelProcessionTop_ge_two (l : PrimeGeFive) :
    2 ≤ absLabelProcessionTop l := by
  unfold absLabelProcessionTop
  have hfour : 4 ≤ l.value := by
    have hfive : 5 ≤ l.value := l.ge_five
    omega
  have h : 4 / 2 ≤ l.value / 2 :=
    Nat.div_le_div_right hfour
  norm_num at h
  exact h

theorem absLabelProcessionTop_pos (l : PrimeGeFive) :
    0 < absLabelProcessionTop l :=
  lt_of_lt_of_le (by norm_num) (absLabelProcessionTop_ge_two l)

def absNonzeroLabelFromIndex
    (l : PrimeGeFive)
    (label : Fin (absLabelProcessionTop l)) :
    IUTStage1ZModCuspFullLabel l :=
  IUTStage1ZModCuspFullLabel.fromCoordinate l
    ((label.val + 1 : Nat) : ZMod l.value)

def signedAbsNonzeroIndexToCoordinate
    (l : PrimeGeFive)
    (label : Bool × Fin (absLabelProcessionTop l)) :
    ZMod l.value :=
  if label.1 then
    -((label.2.val + 1 : Nat) : ZMod l.value)
  else
    ((label.2.val + 1 : Nat) : ZMod l.value)

theorem absNonzeroIndexNatCast_ne_zero
    (label : Fin (absLabelProcessionTop l)) :
    ((label.val + 1 : Nat) : ZMod l.value) ≠ 0 := by
  intro hzero
  rw [ZMod.natCast_eq_zero_iff] at hzero
  have hpos : 0 < label.val + 1 := Nat.succ_pos label.val
  have hlt : label.val + 1 < l.value := by
    have htop := label.isLt
    unfold absLabelProcessionTop at htop
    have hge : 5 ≤ l.value := l.ge_five
    omega
  have hle : l.value ≤ label.val + 1 := Nat.le_of_dvd hpos hzero
  omega

theorem signedAbsNonzeroIndexToCoordinate_ne_zero
    (label : Bool × Fin (absLabelProcessionTop l)) :
    signedAbsNonzeroIndexToCoordinate l label ≠ 0 := by
  cases label with
  | mk sign index =>
      cases sign
      · exact absNonzeroIndexNatCast_ne_zero (l := l) index
      · exact zmod_neg_ne_zero_of_ne_zero l
          (absNonzeroIndexNatCast_ne_zero (l := l) index)

def signedAbsNonzeroIndexToCarrier
    (l : PrimeGeFive)
    (label : Bool × Fin (absLabelProcessionTop l)) :
    (zmodPointedQuotient l).NonzeroCarrier :=
  { val := signedAbsNonzeroIndexToCoordinate l label,
    property := signedAbsNonzeroIndexToCoordinate_ne_zero (l := l) label }

theorem signedAbsNonzeroIndexToCoordinate_pos
    (label : Fin (absLabelProcessionTop l)) :
    signedAbsNonzeroIndexToCoordinate l (false, label) =
      ((label.val + 1 : Nat) : ZMod l.value) := by
  simp [signedAbsNonzeroIndexToCoordinate]

theorem signedAbsNonzeroIndexToCoordinate_neg
    (label : Fin (absLabelProcessionTop l)) :
    signedAbsNonzeroIndexToCoordinate l (true, label) =
      -((label.val + 1 : Nat) : ZMod l.value) := by
  simp [signedAbsNonzeroIndexToCoordinate]

theorem signedAbsNonzeroIndexToCarrier_pos
    (label : Fin (absLabelProcessionTop l)) :
    (signedAbsNonzeroIndexToCarrier l (false, label)).1 =
      ((label.val + 1 : Nat) : ZMod l.value) :=
  signedAbsNonzeroIndexToCoordinate_pos (l := l) label

theorem signedAbsNonzeroIndexToCarrier_neg
    (label : Fin (absLabelProcessionTop l)) :
    (signedAbsNonzeroIndexToCarrier l (true, label)).1 =
      -((label.val + 1 : Nat) : ZMod l.value) :=
  signedAbsNonzeroIndexToCoordinate_neg (l := l) label

theorem absNonzeroIndexNatCast_val
    (label : Fin (absLabelProcessionTop l)) :
    (((label.val + 1 : Nat) : ZMod l.value).val) = label.val + 1 := by
  have hlt : label.val + 1 < l.value := by
    have htop := label.isLt
    unfold absLabelProcessionTop at htop
    have hge : 5 ≤ l.value := l.ge_five
    omega
  exact ZMod.val_natCast_of_lt hlt

theorem absNonzeroIndexNatCast_ne_neg
    (a b : Fin (absLabelProcessionTop l)) :
    ((a.val + 1 : Nat) : ZMod l.value) ≠
      -((b.val + 1 : Nat) : ZMod l.value) := by
  intro h
  have hsum_zmod :
      (((a.val + 1) + (b.val + 1) : Nat) : ZMod l.value) = 0 := by
    have hsum :
        ((a.val + 1 : Nat) : ZMod l.value) +
            ((b.val + 1 : Nat) : ZMod l.value) = 0 := by
      rw [h]
      ring
    simpa [Nat.cast_add] using hsum
  rw [ZMod.natCast_eq_zero_iff] at hsum_zmod
  have hpos : 0 < (a.val + 1) + (b.val + 1) := by omega
  have hle :
      l.value ≤ (a.val + 1) + (b.val + 1) :=
    Nat.le_of_dvd hpos hsum_zmod
  have htop := absLabelProcessionTop_eq_half_minus_one l
  have ha := a.isLt
  have hb := b.isLt
  have hge : 5 ≤ l.value := l.ge_five
  omega

theorem signedAbsNonzeroIndexToCarrier_injective :
    Function.Injective (signedAbsNonzeroIndexToCarrier l) := by
  intro a b h
  cases a with
  | mk asign aindex =>
      cases b with
      | mk bsign bindex =>
          cases asign <;> cases bsign
          · have hcoord := congrArg
              (fun x : (zmodPointedQuotient l).NonzeroCarrier => x.1) h
            change
              (signedAbsNonzeroIndexToCarrier l (false, aindex)).1 =
                (signedAbsNonzeroIndexToCarrier l (false, bindex)).1 at hcoord
            rw [signedAbsNonzeroIndexToCarrier_pos,
              signedAbsNonzeroIndexToCarrier_pos] at hcoord
            have hval := congrArg ZMod.val hcoord
            rw [absNonzeroIndexNatCast_val,
              absNonzeroIndexNatCast_val] at hval
            congr
            exact Fin.ext (Nat.succ.inj hval)
          · have hcoord := congrArg (fun x : (zmodPointedQuotient l).NonzeroCarrier => x.1) h
            change
              (signedAbsNonzeroIndexToCarrier l (false, aindex)).1 =
                (signedAbsNonzeroIndexToCarrier l (true, bindex)).1 at hcoord
            rw [signedAbsNonzeroIndexToCarrier_pos,
              signedAbsNonzeroIndexToCarrier_neg] at hcoord
            exact False.elim
              (absNonzeroIndexNatCast_ne_neg (l := l) aindex bindex hcoord)
          · have hcoord := congrArg (fun x : (zmodPointedQuotient l).NonzeroCarrier => x.1) h
            change
              (signedAbsNonzeroIndexToCarrier l (true, aindex)).1 =
                (signedAbsNonzeroIndexToCarrier l (false, bindex)).1 at hcoord
            rw [signedAbsNonzeroIndexToCarrier_neg,
              signedAbsNonzeroIndexToCarrier_pos] at hcoord
            exact False.elim
              (absNonzeroIndexNatCast_ne_neg (l := l) bindex aindex hcoord.symm)
          · have hcoord := congrArg (fun x : (zmodPointedQuotient l).NonzeroCarrier => x.1) h
            change
              (signedAbsNonzeroIndexToCarrier l (true, aindex)).1 =
                (signedAbsNonzeroIndexToCarrier l (true, bindex)).1 at hcoord
            have hpos :
                ((aindex.val + 1 : Nat) : ZMod l.value) =
                  ((bindex.val + 1 : Nat) : ZMod l.value) := by
              rw [signedAbsNonzeroIndexToCarrier_neg,
                signedAbsNonzeroIndexToCarrier_neg] at hcoord
              exact neg_injective hcoord
            have hval := congrArg ZMod.val hpos
            rw [absNonzeroIndexNatCast_val,
              absNonzeroIndexNatCast_val] at hval
            congr
            exact Fin.ext (Nat.succ.inj hval)

theorem signedAbsNonzeroIndexToCarrier_surjective :
    Function.Surjective (signedAbsNonzeroIndexToCarrier l) := by
  intro x
  let m : Nat := x.1.valMinAbs.natAbs
  have hm_pos : 0 < m := by
    have hm_ne : m ≠ 0 := by
      intro hm
      have hmin : x.1.valMinAbs = 0 := Int.natAbs_eq_zero.mp hm
      exact x.2 ((ZMod.valMinAbs_eq_zero x.1).mp hmin)
    exact Nat.pos_of_ne_zero hm_ne
  have hm_le : m ≤ absLabelProcessionTop l := by
    dsimp [m]
    unfold absLabelProcessionTop
    exact ZMod.natAbs_valMinAbs_le x.1
  let index : Fin (absLabelProcessionTop l) :=
    ⟨m - 1, by omega⟩
  have hindex : index.val + 1 = m := by
    dsimp [index]
    omega
  by_cases hhalf : x.1.val ≤ l.value / 2
  · refine ⟨(false, index), Subtype.ext ?_⟩
    rw [signedAbsNonzeroIndexToCarrier_pos, hindex]
    have hcast := ZMod.natCast_natAbs_valMinAbs (n := l.value) x.1
    rw [if_pos hhalf] at hcast
    exact hcast
  · refine ⟨(true, index), Subtype.ext ?_⟩
    rw [signedAbsNonzeroIndexToCarrier_neg, hindex]
    have hcast := ZMod.natCast_natAbs_valMinAbs (n := l.value) x.1
    rw [if_neg hhalf] at hcast
    rw [hcast]
    simp

noncomputable def signedAbsNonzeroIndexEquivCarrier :
    Bool × Fin (absLabelProcessionTop l) ≃
      (zmodPointedQuotient l).NonzeroCarrier :=
  Equiv.ofBijective (signedAbsNonzeroIndexToCarrier l)
    ⟨signedAbsNonzeroIndexToCarrier_injective,
      signedAbsNonzeroIndexToCarrier_surjective⟩

theorem signedAbsNonzeroIndexEquivCarrier_apply
    (label : Bool × Fin (absLabelProcessionTop l)) :
    signedAbsNonzeroIndexEquivCarrier label =
      signedAbsNonzeroIndexToCarrier l label :=
  rfl

theorem fromCoordinate_signedAbsNonzeroIndexToCarrier
    (label : Bool × Fin (absLabelProcessionTop l)) :
    IUTStage1ZModCuspFullLabel.fromCoordinate l
        (signedAbsNonzeroIndexToCarrier l label).1 =
      absNonzeroLabelFromIndex l label.2 := by
  cases label with
  | mk sign index =>
      cases sign
      · rfl
      · rw [signedAbsNonzeroIndexToCarrier_neg]
        unfold absNonzeroLabelFromIndex
        exact IUTStage1ZModCuspFullLabel.fromCoordinate_neg l
          ((index.val + 1 : Nat) : ZMod l.value)
          (absNonzeroIndexNatCast_ne_zero (l := l) index)

theorem fromCoordinate_nonzeroCarrier
    (x : (zmodPointedQuotient l).NonzeroCarrier) :
    IUTStage1ZModCuspFullLabel.fromCoordinate l x.1 =
      IUTStage1ZModCuspFullLabel.nonzero
        ((zmodSignAction l).toSignLabelQuotient x) := by
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_nonzero l x.1 x.2]
  rw [← zmod_toSignLabelQuotient_eq_fromCoordinate x]

theorem gaussianDegree_signedAbsNonzeroIndexToCarrier
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (label : Bool × Fin (absLabelProcessionTop l)) :
    evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.nonzero
          ((zmodSignAction l).toSignLabelQuotient
            (signedAbsNonzeroIndexToCarrier l label))) =
      evaluation.gaussianDegree (absNonzeroLabelFromIndex l label.2) := by
  rw [← fromCoordinate_nonzeroCarrier
    (l := l) (signedAbsNonzeroIndexToCarrier l label)]
  rw [fromCoordinate_signedAbsNonzeroIndexToCarrier]

theorem gaussianDegree_fromAbsNonzeroLabelIndex
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (label : Fin (absLabelProcessionTop l)) :
    evaluation.gaussianDegree (absNonzeroLabelFromIndex l label) =
      (((label.val + 1 : Nat) : Real) ^ 2) *
        evaluation.environmentDegree := by
  unfold absNonzeroLabelFromIndex
  have hle : label.val + 1 ≤ l.value / 2 := by
    have hlt := label.isLt
    unfold absLabelProcessionTop at hlt
    omega
  have hlt_value : label.val + 1 < l.value := by
    have hge : 5 ≤ l.value := l.ge_five
    omega
  have hval :
      (((label.val + 1 : Nat) : ZMod l.value).val) = label.val + 1 :=
    ZMod.val_natCast_of_lt hlt_value
  have hhalf :
      (((label.val + 1 : Nat) : ZMod l.value).val) ≤ l.value / 2 := by
    rw [hval]
    exact hle
  rw [evaluation.gaussianDegree_fromCoordinate_of_val_le_half
    ((label.val + 1 : Nat) : ZMod l.value) hhalf]
  rw [hval]

theorem nonzeroCarrier_gaussianDegree_sum_eq_two_absNonzeroLabel_sum
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    (Finset.univ.sum
        (fun x : (zmodPointedQuotient l).NonzeroCarrier =>
          evaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.nonzero
              ((zmodSignAction l).toSignLabelQuotient x)))) =
      2 *
        (Finset.univ.sum fun label : Fin (absLabelProcessionTop l) =>
          evaluation.gaussianDegree (absNonzeroLabelFromIndex l label)) := by
  classical
  let f : (zmodPointedQuotient l).NonzeroCarrier -> Real := fun x =>
    evaluation.gaussianDegree
      (IUTStage1ZModCuspFullLabel.nonzero
        ((zmodSignAction l).toSignLabelQuotient x))
  have hcarrier :
      (Finset.univ.sum f) =
        Finset.univ.sum
          (fun label : Bool × Fin (absLabelProcessionTop l) =>
            f (signedAbsNonzeroIndexToCarrier l label)) := by
    symm
    exact Fintype.sum_equiv
      (signedAbsNonzeroIndexEquivCarrier (l := l))
      (fun label : Bool × Fin (absLabelProcessionTop l) =>
        f (signedAbsNonzeroIndexToCarrier l label))
      f
      (by
        intro label
        rw [signedAbsNonzeroIndexEquivCarrier_apply])
  change
    (Finset.univ.sum f) =
      2 *
        (Finset.univ.sum fun label : Fin (absLabelProcessionTop l) =>
          evaluation.gaussianDegree (absNonzeroLabelFromIndex l label))
  rw [hcarrier]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [f, gaussianDegree_signedAbsNonzeroIndexToCarrier, two_mul]

noncomputable def absNonzeroLabelAveragedLogVolume
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    IUTStage1LabelAveragedProcessionLogVolume
      (Fin (absLabelProcessionTop l)) :=
  { normalizedLogVolume := fun label =>
      evaluation.gaussianDegree (absNonzeroLabelFromIndex l label),
    averageLogVolume :=
      (Finset.univ.sum fun label : Fin (absLabelProcessionTop l) =>
        evaluation.gaussianDegree (absNonzeroLabelFromIndex l label)) /
        (absLabelProcessionTop l : Real),
    average_eq := by simp }

theorem zmodNonzeroCarrier_card_eq_two_absLabelProcessionTop :
    Fintype.card (zmodPointedQuotient l).NonzeroCarrier =
      2 * absLabelProcessionTop l := by
  rw [zmodNonzeroCarrier_card_eq]
  rw [absLabelProcessionTop_eq_half_minus_one]
  have hodd : Odd l.value := l.prime.odd_of_ne_two l.ne_two
  rcases hodd with ⟨k, hk⟩
  rw [hk]
  omega

theorem primeValue_sub_one_eq_two_absLabelProcessionTop :
    l.value - 1 = 2 * absLabelProcessionTop l := by
  have hcard := zmodNonzeroCarrier_card_eq_two_absLabelProcessionTop (l := l)
  rw [zmodNonzeroCarrier_card_eq] at hcard
  exact hcard

theorem primeValue_eq_two_absLabelProcessionTop_add_one :
    l.value = 2 * absLabelProcessionTop l + 1 := by
  have hsub := primeValue_sub_one_eq_two_absLabelProcessionTop (l := l)
  have hge : 5 ≤ l.value := l.ge_five
  omega

theorem nonzeroCarrierAveragedLogVolume_eq_absNonzeroLabelAveragedLogVolume
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.nonzeroCarrierAveragedLogVolume.averageLogVolume =
      (absNonzeroLabelAveragedLogVolume evaluation).averageLogVolume := by
  unfold GaussianMonoidDegreeEvaluation.nonzeroCarrierAveragedLogVolume
  unfold absNonzeroLabelAveragedLogVolume
  simp only
  rw [nonzeroCarrier_gaussianDegree_sum_eq_two_absNonzeroLabel_sum,
    zmodNonzeroCarrier_card_eq_two_absLabelProcessionTop]
  have hden : (absLabelProcessionTop l : Real) ≠ 0 := by
    exact_mod_cast ne_of_gt (absLabelProcessionTop_pos l)
  norm_num
  field_simp [hden]

theorem coordinateAveragedLogVolume_eq_absNonzero_mass_rescale
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.coordinateAveragedLogVolume.averageLogVolume =
      ((l.value - 1 : Nat) : Real) / (l.value : Real) *
        (absNonzeroLabelAveragedLogVolume evaluation).averageLogVolume := by
  rw [evaluation.coordinateAveragedLogVolume_eq_nonzero_mass_rescale]
  rw [nonzeroCarrierAveragedLogVolume_eq_absNonzeroLabelAveragedLogVolume]

theorem nonzeroProcessionSquareSum_mul_six :
    ((Finset.univ.sum fun label : Fin (absLabelProcessionTop l) =>
      (((label.val + 1 : Nat) : Real) ^ 2)) * 6) =
      (absLabelProcessionTop l : Real) *
        ((absLabelProcessionTop l : Real) + 1) *
          (2 * (absLabelProcessionTop l : Real) + 1) := by
  let k := absLabelProcessionTop l
  change
    ((Finset.univ.sum fun label : Fin k =>
      (((label.val + 1 : Nat) : Real) ^ 2)) * 6) =
      (k : Real) * ((k : Real) + 1) * (2 * (k : Real) + 1)
  rw [Finset.sum_fin_eq_sum_range]
  have hsum_eq :
      (Finset.range k).sum
          (fun x : Nat =>
            if h : x < k then
              (((((⟨x, h⟩ : Fin k).val + 1 : Nat) : Real) ^ 2))
            else 0) =
        (Finset.range k).sum
          (fun x : Nat => (((x + 1 : Nat) : Real) ^ 2)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxlt : x < k := Finset.mem_range.mp hx
    simp [hxlt]
  rw [hsum_eq]
  have hshift :
      (Finset.range k).sum
          (fun x : Nat => (((x + 1 : Nat) : Real) ^ 2)) =
        (Finset.range (k + 1)).sum
          (fun x : Nat => ((x : Real) ^ 2)) := by
    rw [Finset.sum_range_succ']
    simp
  rw [hshift]
  exact iutIVThetaPilot_sum_sq_mul_six k

theorem gaussianDegree_absNonzeroLabelAverage_mul_six
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    ((absNonzeroLabelAveragedLogVolume evaluation).averageLogVolume * 6 =
      ((absLabelProcessionTop l : Real) + 1) *
        (2 * (absLabelProcessionTop l : Real) + 1) *
          evaluation.environmentDegree) := by
  change
    (((Finset.univ.sum fun label : Fin (absLabelProcessionTop l) =>
      evaluation.gaussianDegree (absNonzeroLabelFromIndex l label)) /
      (absLabelProcessionTop l : Real)) * 6 =
      ((absLabelProcessionTop l : Real) + 1) *
        (2 * (absLabelProcessionTop l : Real) + 1) *
          evaluation.environmentDegree)
  have hsum := nonzeroProcessionSquareSum_mul_six (l := l)
  have hden : (absLabelProcessionTop l : Real) ≠ 0 := by
    exact_mod_cast ne_of_gt (absLabelProcessionTop_pos l)
  calc
    ((Finset.univ.sum fun label : Fin (absLabelProcessionTop l) =>
        evaluation.gaussianDegree (absNonzeroLabelFromIndex l label)) /
        (absLabelProcessionTop l : Real)) * 6 =
        ((Finset.univ.sum fun label : Fin (absLabelProcessionTop l) =>
          (((label.val + 1 : Nat) : Real) ^ 2) *
            evaluation.environmentDegree) /
          (absLabelProcessionTop l : Real)) * 6 := by
      congr 1
      congr 1
      exact Finset.sum_congr rfl (by
        intro label _hlabel
        exact gaussianDegree_fromAbsNonzeroLabelIndex evaluation label)
    _ =
        (((Finset.univ.sum fun label : Fin (absLabelProcessionTop l) =>
          (((label.val + 1 : Nat) : Real) ^ 2)) *
          evaluation.environmentDegree) /
          (absLabelProcessionTop l : Real)) * 6 := by
      rw [Finset.sum_mul]
    _ =
        ((((Finset.univ.sum fun label : Fin (absLabelProcessionTop l) =>
          (((label.val + 1 : Nat) : Real) ^ 2)) * 6) *
          evaluation.environmentDegree) /
          (absLabelProcessionTop l : Real)) := by
      ring
    _ =
        (((absLabelProcessionTop l : Real) *
          ((absLabelProcessionTop l : Real) + 1) *
            (2 * (absLabelProcessionTop l : Real) + 1)) *
          evaluation.environmentDegree) /
          (absLabelProcessionTop l : Real) := by
      rw [hsum]
    _ =
        ((absLabelProcessionTop l : Real) + 1) *
          (2 * (absLabelProcessionTop l : Real) + 1) *
            evaluation.environmentDegree := by
      field_simp [hden]

theorem gaussianDegree_absNonzeroLabel_sum_mul_six
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    ((Finset.univ.sum fun label : Fin (absLabelProcessionTop l) =>
      evaluation.gaussianDegree (absNonzeroLabelFromIndex l label)) * 6 =
      ((absLabelProcessionTop l : Real) *
        ((absLabelProcessionTop l : Real) + 1) *
          (2 * (absLabelProcessionTop l : Real) + 1)) *
        evaluation.environmentDegree) := by
  have havg := gaussianDegree_absNonzeroLabelAverage_mul_six evaluation
  unfold absNonzeroLabelAveragedLogVolume at havg
  change
    (((Finset.univ.sum fun label : Fin (absLabelProcessionTop l) =>
      evaluation.gaussianDegree (absNonzeroLabelFromIndex l label)) /
        (absLabelProcessionTop l : Real)) * 6 =
      ((absLabelProcessionTop l : Real) + 1) *
        (2 * (absLabelProcessionTop l : Real) + 1) *
          evaluation.environmentDegree) at havg
  have hden : (absLabelProcessionTop l : Real) ≠ 0 := by
    exact_mod_cast ne_of_gt (absLabelProcessionTop_pos l)
  field_simp [hden] at havg
  nlinarith

/--
Log-volume shadow of the IUT III splitting-monoid action.

IUT III describes splitting monoids of LGP-monoids, generated by the theta values
`q^{j^2}`, acting on the bad nonarchimedean portions of the tensor packets.  This
record does not construct those monoids.  It records the degree/log-volume effect
of the generators on the finite procession tensor packet already present in Stage
1: acting by the generator at a label adds the corresponding Gaussian
`q^{j^2}` log-degree to that tensor factor.
-/
structure LGPSplittingMonoidTensorPacketAction
    (l : PrimeGeFive) where
  evaluation : GaussianMonoidDegreeEvaluation l
  packet :
    IUTStage1ProcessionFiberTensorPacketLogVolume
      IUTStage1PlaceKind.nonarchimedean (absLabelProcessionTop l)
  generatorLogVolume :
    IUTStage1ProcessionContainer (absLabelProcessionTop l) -> Real
  generator_logVolume_eq_gaussian :
    ∀ label : IUTStage1ProcessionContainer (absLabelProcessionTop l),
      generatorLogVolume label =
        evaluation.gaussianDegree (absLabelFromProcession l label)
  actedFactorLogVolume :
    IUTStage1ProcessionContainer (absLabelProcessionTop l) -> Real
  acted_factor_eq :
    ∀ label : IUTStage1ProcessionContainer (absLabelProcessionTop l),
      actedFactorLogVolume label =
        (packet.directSum label).directSumLogVolume + generatorLogVolume label
  actedTensorPacketLogVolume : Real
  acted_tensor_packet_eq_sum :
    actedTensorPacketLogVolume =
      Finset.univ.sum actedFactorLogVolume
  normalizedActedLogVolume : Real
  normalized_acted_eq_average :
    normalizedActedLogVolume =
      actedTensorPacketLogVolume /
        (Fintype.card
          (IUTStage1ProcessionContainer (absLabelProcessionTop l)) : Real)

namespace LGPSplittingMonoidTensorPacketAction

variable {l : PrimeGeFive}

theorem generatorLogVolume_core
    (action : LGPSplittingMonoidTensorPacketAction l) :
    action.generatorLogVolume
        (IUTStage1ProcessionContainer.core (absLabelProcessionTop l)) = 0 := by
  rw [action.generator_logVolume_eq_gaussian, absLabelFromProcession_core]
  exact action.evaluation.gaussianDegree_zero

theorem generatorLogVolume_eq_procession_square
    (action : LGPSplittingMonoidTensorPacketAction l)
    (label : IUTStage1ProcessionContainer (absLabelProcessionTop l)) :
    action.generatorLogVolume label =
      ((label.val : Real) ^ 2) * action.evaluation.environmentDegree := by
  rw [action.generator_logVolume_eq_gaussian,
    action.evaluation.gaussianDegree_eq_eval,
    thetaExponentOnAbsLabel_fromProcession]

theorem actedTensorPacketLogVolume_eq_original_plus_generators
    (action : LGPSplittingMonoidTensorPacketAction l) :
    action.actedTensorPacketLogVolume =
      action.packet.tensorPacketLogVolume +
        Finset.univ.sum action.generatorLogVolume := by
  calc
    action.actedTensorPacketLogVolume =
        Finset.univ.sum action.actedFactorLogVolume :=
      action.acted_tensor_packet_eq_sum
    _ =
        Finset.univ.sum (fun label :
          IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
            (action.packet.directSum label).directSumLogVolume +
              action.generatorLogVolume label) := by
      apply Finset.sum_congr rfl
      intro label _hlabel
      exact action.acted_factor_eq label
    _ =
        (Finset.univ.sum fun label :
          IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
            (action.packet.directSum label).directSumLogVolume) +
          Finset.univ.sum action.generatorLogVolume := by
      rw [Finset.sum_add_distrib]
    _ =
        action.packet.tensorPacketLogVolume +
          Finset.univ.sum action.generatorLogVolume := by
      rw [action.packet.tensor_packet_eq_sum]

theorem normalizedActedLogVolume_eq_original_plus_generators_over_card
    (action : LGPSplittingMonoidTensorPacketAction l) :
    action.normalizedActedLogVolume =
      (action.packet.tensorPacketLogVolume +
        Finset.univ.sum action.generatorLogVolume) /
          (Fintype.card
            (IUTStage1ProcessionContainer (absLabelProcessionTop l)) : Real) := by
  rw [action.normalized_acted_eq_average,
    action.actedTensorPacketLogVolume_eq_original_plus_generators]

theorem generatorLogVolume_sum_eq_procession_square_sum
    (action : LGPSplittingMonoidTensorPacketAction l) :
    Finset.univ.sum action.generatorLogVolume =
      (Finset.univ.sum fun label :
        IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
          ((label.val : Real) ^ 2)) *
        action.evaluation.environmentDegree := by
  calc
    Finset.univ.sum action.generatorLogVolume =
        Finset.univ.sum fun label :
          IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
            ((label.val : Real) ^ 2) *
              action.evaluation.environmentDegree := by
      apply Finset.sum_congr rfl
      intro label _hlabel
      exact action.generatorLogVolume_eq_procession_square label
    _ =
        (Finset.univ.sum fun label :
          IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
            ((label.val : Real) ^ 2)) *
          action.evaluation.environmentDegree := by
      rw [Finset.sum_mul]

theorem processionSquareSum_mul_six :
    ((Finset.univ.sum fun label :
      IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
        ((label.val : Real) ^ 2)) * 6) =
      (absLabelProcessionTop l : Real) *
        ((absLabelProcessionTop l : Real) + 1) *
          (2 * (absLabelProcessionTop l : Real) + 1) := by
  change
    ((Finset.univ.sum fun label : Fin (absLabelProcessionTop l + 1) =>
      ((label.val : Real) ^ 2)) * 6) =
      (absLabelProcessionTop l : Real) *
        ((absLabelProcessionTop l : Real) + 1) *
          (2 * (absLabelProcessionTop l : Real) + 1)
  rw [Finset.sum_fin_eq_sum_range]
  have hsum_eq :
      (Finset.range (absLabelProcessionTop l + 1)).sum
          (fun x : Nat =>
            if h : x < absLabelProcessionTop l + 1 then
              (((⟨x, h⟩ : Fin (absLabelProcessionTop l + 1)).val : Real) ^ 2)
            else 0) =
        (Finset.range (absLabelProcessionTop l + 1)).sum
          (fun x : Nat => ((x : Real) ^ 2)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxlt : x < absLabelProcessionTop l + 1 :=
      Finset.mem_range.mp hx
    simp [hxlt]
  rw [hsum_eq]
  exact iutIVThetaPilot_sum_sq_mul_six (absLabelProcessionTop l)

theorem gaussianDegree_procession_average_mul_six
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    (((Finset.univ.sum fun label :
      IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
        evaluation.gaussianDegree (absLabelFromProcession l label)) /
        (Fintype.card
          (IUTStage1ProcessionContainer (absLabelProcessionTop l)) : Real)) *
      6 =
      (absLabelProcessionTop l : Real) *
        (2 * (absLabelProcessionTop l : Real) + 1) *
          evaluation.environmentDegree) := by
  rw [gaussianDegree_procession_sum_eq_square_sum evaluation]
  have hsum := processionSquareSum_mul_six (l := l)
  have hcard :
      (Fintype.card
        (IUTStage1ProcessionContainer (absLabelProcessionTop l)) : Real) =
      ((absLabelProcessionTop l : Real) + 1) := by
    rw [IUTStage1ProcessionContainer.card_eq]
    norm_num
  have hden : ((absLabelProcessionTop l : Real) + 1) ≠ 0 := by
    positivity
  rw [hcard]
  calc
    (((Finset.univ.sum fun label :
      IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
        ((label.val : Real) ^ 2)) * evaluation.environmentDegree) /
        ((absLabelProcessionTop l : Real) + 1)) * 6 =
        ((((Finset.univ.sum fun label :
          IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
            ((label.val : Real) ^ 2)) * 6) *
          evaluation.environmentDegree) /
          ((absLabelProcessionTop l : Real) + 1)) := by
      ring
    _ =
        (((absLabelProcessionTop l : Real) *
          ((absLabelProcessionTop l : Real) + 1) *
            (2 * (absLabelProcessionTop l : Real) + 1)) *
          evaluation.environmentDegree) /
          ((absLabelProcessionTop l : Real) + 1) := by
      rw [hsum]
    _ =
        (absLabelProcessionTop l : Real) *
          (2 * (absLabelProcessionTop l : Real) + 1) *
            evaluation.environmentDegree := by
      field_simp [hden]

theorem gaussianDegree_fullLabel_average_mul_six
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    (((Finset.univ.sum evaluation.gaussianDegree) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real)) * 6 =
      (absLabelProcessionTop l : Real) *
        (2 * (absLabelProcessionTop l : Real) + 1) *
          evaluation.environmentDegree) := by
  rw [fullLabel_average_eq_procession_average]
  exact gaussianDegree_procession_average_mul_six evaluation

theorem absLabelAverageCoefficient_gt_one :
    (1 : Real) <
      (absLabelProcessionTop l : Real) *
        (2 * (absLabelProcessionTop l : Real) + 1) / 6 := by
  have htop : (2 : Real) <= (absLabelProcessionTop l : Real) := by
    exact_mod_cast absLabelProcessionTop_ge_two l
  nlinarith

theorem gaussianDegree_fullLabel_average_eq_coeff
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    (Finset.univ.sum evaluation.gaussianDegree) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) =
      ((absLabelProcessionTop l : Real) *
        (2 * (absLabelProcessionTop l : Real) + 1) / 6) *
          evaluation.environmentDegree := by
  have h := gaussianDegree_fullLabel_average_mul_six evaluation
  nlinarith

theorem gaussianDegree_absNonzeroLabel_average_eq_coeff
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    (absNonzeroLabelAveragedLogVolume evaluation).averageLogVolume =
      (((absLabelProcessionTop l : Real) + 1) *
        (2 * (absLabelProcessionTop l : Real) + 1) / 6) *
          evaluation.environmentDegree := by
  have h := gaussianDegree_absNonzeroLabelAverage_mul_six evaluation
  nlinarith

theorem gaussianDegree_fullLabel_average_eq_absNonzeroLabel_rescale
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    (Finset.univ.sum evaluation.gaussianDegree) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) =
      (absLabelProcessionTop l : Real) /
        ((absLabelProcessionTop l : Real) + 1) *
          (absNonzeroLabelAveragedLogVolume evaluation).averageLogVolume := by
  rw [gaussianDegree_fullLabel_average_eq_coeff,
    gaussianDegree_absNonzeroLabel_average_eq_coeff]
  have hden : ((absLabelProcessionTop l : Real) + 1) ≠ 0 := by
    positivity
  field_simp [hden]

theorem absNonzeroLabelAverageCoefficient_gt_fullLabelAverageCoefficient :
    (absLabelProcessionTop l : Real) *
        (2 * (absLabelProcessionTop l : Real) + 1) / 6 <
      ((absLabelProcessionTop l : Real) + 1) *
        (2 * (absLabelProcessionTop l : Real) + 1) / 6 := by
  have hpos : 0 < 2 * (absLabelProcessionTop l : Real) + 1 := by
    positivity
  nlinarith

theorem gaussianDegree_absNonzeroLabel_average_lt_fullLabel_average_of_negative
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_neg : evaluation.environmentDegree < 0) :
    (absNonzeroLabelAveragedLogVolume evaluation).averageLogVolume <
      (Finset.univ.sum evaluation.gaussianDegree) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) := by
  rw [gaussianDegree_absNonzeroLabel_average_eq_coeff,
    gaussianDegree_fullLabel_average_eq_coeff]
  let fullCoeff : Real :=
    (absLabelProcessionTop l : Real) *
      (2 * (absLabelProcessionTop l : Real) + 1) / 6
  let nonzeroCoeff : Real :=
    ((absLabelProcessionTop l : Real) + 1) *
      (2 * (absLabelProcessionTop l : Real) + 1) / 6
  have hcoeff : fullCoeff < nonzeroCoeff := by
    simpa [fullCoeff, nonzeroCoeff] using
      absNonzeroLabelAverageCoefficient_gt_fullLabelAverageCoefficient
        (l := l)
  have hmul :
      nonzeroCoeff * evaluation.environmentDegree <
        fullCoeff * evaluation.environmentDegree :=
    mul_lt_mul_of_neg_right hcoeff henv_neg
  simpa [fullCoeff, nonzeroCoeff] using hmul

theorem gaussianDegree_fullLabel_average_lt_absNonzeroLabel_average_of_positive
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_pos : 0 < evaluation.environmentDegree) :
    (Finset.univ.sum evaluation.gaussianDegree) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) <
      (absNonzeroLabelAveragedLogVolume evaluation).averageLogVolume := by
  rw [gaussianDegree_absNonzeroLabel_average_eq_coeff,
    gaussianDegree_fullLabel_average_eq_coeff]
  let fullCoeff : Real :=
    (absLabelProcessionTop l : Real) *
      (2 * (absLabelProcessionTop l : Real) + 1) / 6
  let nonzeroCoeff : Real :=
    ((absLabelProcessionTop l : Real) + 1) *
      (2 * (absLabelProcessionTop l : Real) + 1) / 6
  have hcoeff : fullCoeff < nonzeroCoeff := by
    simpa [fullCoeff, nonzeroCoeff] using
      absNonzeroLabelAverageCoefficient_gt_fullLabelAverageCoefficient
        (l := l)
  have hmul :
      fullCoeff * evaluation.environmentDegree <
        nonzeroCoeff * evaluation.environmentDegree :=
    mul_lt_mul_of_pos_right hcoeff henv_pos
  simpa [fullCoeff, nonzeroCoeff] using hmul

theorem gaussianDegree_absNonzeroLabel_average_eq_fullLabel_average_iff
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    (absNonzeroLabelAveragedLogVolume evaluation).averageLogVolume =
        (Finset.univ.sum evaluation.gaussianDegree) /
          (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) ↔
      evaluation.environmentDegree = 0 := by
  constructor
  · intro h
    rw [gaussianDegree_absNonzeroLabel_average_eq_coeff,
      gaussianDegree_fullLabel_average_eq_coeff] at h
    let fullCoeff : Real :=
      (absLabelProcessionTop l : Real) *
        (2 * (absLabelProcessionTop l : Real) + 1) / 6
    let nonzeroCoeff : Real :=
      ((absLabelProcessionTop l : Real) + 1) *
        (2 * (absLabelProcessionTop l : Real) + 1) / 6
    have hcoeff_ne : nonzeroCoeff ≠ fullCoeff := by
      have hcoeff : fullCoeff < nonzeroCoeff := by
        simpa [fullCoeff, nonzeroCoeff] using
          absNonzeroLabelAverageCoefficient_gt_fullLabelAverageCoefficient
            (l := l)
      exact ne_of_gt hcoeff
    have hmul :
        nonzeroCoeff * evaluation.environmentDegree =
          fullCoeff * evaluation.environmentDegree := by
      simpa [nonzeroCoeff, fullCoeff] using h
    have hfactor :
        (nonzeroCoeff - fullCoeff) * evaluation.environmentDegree = 0 := by
      nlinarith
    have hfactor_ne : nonzeroCoeff - fullCoeff ≠ 0 := by
      intro hzero
      exact hcoeff_ne (sub_eq_zero.mp hzero)
    exact mul_eq_zero.mp hfactor |>.resolve_left hfactor_ne
  · intro henv
    rw [gaussianDegree_absNonzeroLabel_average_eq_coeff,
      gaussianDegree_fullLabel_average_eq_coeff, henv]
    ring

theorem gaussianDegree_fullLabel_average_ne_environment_of_nonzero
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv : evaluation.environmentDegree ≠ 0) :
    (Finset.univ.sum evaluation.gaussianDegree) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) ≠
      evaluation.environmentDegree := by
  rw [gaussianDegree_fullLabel_average_eq_coeff]
  intro h
  let coeff : Real :=
    (absLabelProcessionTop l : Real) *
      (2 * (absLabelProcessionTop l : Real) + 1) / 6
  have hmul :
      coeff * evaluation.environmentDegree =
        1 * evaluation.environmentDegree := by
    simpa [coeff] using h
  have hcoeff : coeff = 1 :=
    mul_right_cancel₀ henv hmul
  have hgt := absLabelAverageCoefficient_gt_one (l := l)
  dsimp [coeff] at hcoeff
  linarith

theorem gaussianDegree_fullLabel_average_le_environment_of_nonpositive
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_nonpos : evaluation.environmentDegree <= 0) :
    (Finset.univ.sum evaluation.gaussianDegree) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) <=
      evaluation.environmentDegree := by
  rw [gaussianDegree_fullLabel_average_eq_coeff]
  let coeff : Real :=
    (absLabelProcessionTop l : Real) *
      (2 * (absLabelProcessionTop l : Real) + 1) / 6
  have hcoeff : 1 <= coeff := by
    exact le_of_lt (by
      simpa [coeff] using absLabelAverageCoefficient_gt_one (l := l))
  have hmul :
      coeff * evaluation.environmentDegree <=
        1 * evaluation.environmentDegree :=
    mul_le_mul_of_nonpos_right hcoeff henv_nonpos
  simpa [coeff] using hmul

theorem gaussianDegree_fullLabel_average_lt_environment_of_negative
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_neg : evaluation.environmentDegree < 0) :
    (Finset.univ.sum evaluation.gaussianDegree) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) <
      evaluation.environmentDegree := by
  rw [gaussianDegree_fullLabel_average_eq_coeff]
  let coeff : Real :=
    (absLabelProcessionTop l : Real) *
      (2 * (absLabelProcessionTop l : Real) + 1) / 6
  have hcoeff : 1 < coeff := by
    simpa [coeff] using absLabelAverageCoefficient_gt_one (l := l)
  have hmul :
      coeff * evaluation.environmentDegree <
        1 * evaluation.environmentDegree :=
    mul_lt_mul_of_neg_right hcoeff henv_neg
  simpa [coeff] using hmul

theorem gaussianDegree_fullLabel_average_gt_environment_of_positive
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_pos : 0 < evaluation.environmentDegree) :
    evaluation.environmentDegree <
      (Finset.univ.sum evaluation.gaussianDegree) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) := by
  rw [gaussianDegree_fullLabel_average_eq_coeff]
  let coeff : Real :=
    (absLabelProcessionTop l : Real) *
      (2 * (absLabelProcessionTop l : Real) + 1) / 6
  have hcoeff : 1 < coeff := by
    simpa [coeff] using absLabelAverageCoefficient_gt_one (l := l)
  have hmul :
      1 * evaluation.environmentDegree <
        coeff * evaluation.environmentDegree :=
    mul_lt_mul_of_pos_right hcoeff henv_pos
  simpa [coeff] using hmul

theorem gaussianDegree_fullLabel_average_le_of_environment_le_bound
    (evaluation : GaussianMonoidDegreeEvaluation l)
    {c : Real}
    (henv_nonpos : evaluation.environmentDegree <= 0)
    (henv_le : evaluation.environmentDegree <= c) :
    (Finset.univ.sum evaluation.gaussianDegree) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) <= c :=
  le_trans
    (gaussianDegree_fullLabel_average_le_environment_of_nonpositive
      evaluation henv_nonpos)
    henv_le

theorem generatorLogVolume_sum_mul_six
    (action : LGPSplittingMonoidTensorPacketAction l) :
    (Finset.univ.sum action.generatorLogVolume) * 6 =
      ((absLabelProcessionTop l : Real) *
        ((absLabelProcessionTop l : Real) + 1) *
          (2 * (absLabelProcessionTop l : Real) + 1)) *
        action.evaluation.environmentDegree := by
  rw [action.generatorLogVolume_sum_eq_procession_square_sum]
  have hsum := processionSquareSum_mul_six (l := l)
  calc
    ((Finset.univ.sum fun label :
      IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
        ((label.val : Real) ^ 2)) *
        action.evaluation.environmentDegree) * 6 =
        (((Finset.univ.sum fun label :
          IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
            ((label.val : Real) ^ 2)) * 6) *
          action.evaluation.environmentDegree) := by
      ring
    _ =
        ((absLabelProcessionTop l : Real) *
          ((absLabelProcessionTop l : Real) + 1) *
            (2 * (absLabelProcessionTop l : Real) + 1)) *
          action.evaluation.environmentDegree := by
      rw [hsum]

theorem generatorLogVolume_average_mul_six
    (action : LGPSplittingMonoidTensorPacketAction l) :
    ((Finset.univ.sum action.generatorLogVolume) /
        (Fintype.card
          (IUTStage1ProcessionContainer (absLabelProcessionTop l)) : Real)) *
      6 =
      (absLabelProcessionTop l : Real) *
        (2 * (absLabelProcessionTop l : Real) + 1) *
          action.evaluation.environmentDegree := by
  have hsum := action.generatorLogVolume_sum_mul_six
  have hcard :
      (Fintype.card
        (IUTStage1ProcessionContainer (absLabelProcessionTop l)) : Real) =
      ((absLabelProcessionTop l : Real) + 1) := by
    rw [IUTStage1ProcessionContainer.card_eq]
    norm_num
  have hden : ((absLabelProcessionTop l : Real) + 1) ≠ 0 := by
    positivity
  rw [hcard]
  calc
    ((Finset.univ.sum action.generatorLogVolume) /
        ((absLabelProcessionTop l : Real) + 1)) * 6 =
        ((Finset.univ.sum action.generatorLogVolume) * 6) /
          ((absLabelProcessionTop l : Real) + 1) := by
      ring
    _ =
        (((absLabelProcessionTop l : Real) *
          ((absLabelProcessionTop l : Real) + 1) *
            (2 * (absLabelProcessionTop l : Real) + 1)) *
          action.evaluation.environmentDegree) /
          ((absLabelProcessionTop l : Real) + 1) := by
      rw [hsum]
    _ =
        (absLabelProcessionTop l : Real) *
          (2 * (absLabelProcessionTop l : Real) + 1) *
            action.evaluation.environmentDegree := by
      field_simp [hden]

theorem normalizedActedLogVolume_eq_packetNormalized_plus_generatorAverage
    (action : LGPSplittingMonoidTensorPacketAction l) :
    action.normalizedActedLogVolume =
      action.packet.normalizedLogVolume +
        (Finset.univ.sum action.generatorLogVolume) /
          (Fintype.card
            (IUTStage1ProcessionContainer (absLabelProcessionTop l)) : Real) := by
  rw [action.normalizedActedLogVolume_eq_original_plus_generators_over_card,
    action.packet.normalized_eq_card_average]
  ring

theorem normalizedActedLogVolume_eq_packetNormalized_plus_squareAverage
    (action : LGPSplittingMonoidTensorPacketAction l) :
    action.normalizedActedLogVolume =
      action.packet.normalizedLogVolume +
        ((Finset.univ.sum fun label :
          IUTStage1ProcessionContainer (absLabelProcessionTop l) =>
            ((label.val : Real) ^ 2)) *
          action.evaluation.environmentDegree) /
          (Fintype.card
            (IUTStage1ProcessionContainer (absLabelProcessionTop l)) : Real) := by
  rw [action.normalizedActedLogVolume_eq_packetNormalized_plus_generatorAverage,
    action.generatorLogVolume_sum_eq_procession_square_sum]

theorem normalizedActedLogVolume_delta_mul_six
    (action : LGPSplittingMonoidTensorPacketAction l) :
    (action.normalizedActedLogVolume - action.packet.normalizedLogVolume) * 6 =
      (absLabelProcessionTop l : Real) *
        (2 * (absLabelProcessionTop l : Real) + 1) *
          action.evaluation.environmentDegree := by
  rw [action.normalizedActedLogVolume_eq_packetNormalized_plus_generatorAverage]
  have havg := action.generatorLogVolume_average_mul_six
  calc
    (action.packet.normalizedLogVolume +
          (Finset.univ.sum action.generatorLogVolume) /
            (Fintype.card
              (IUTStage1ProcessionContainer (absLabelProcessionTop l)) : Real) -
        action.packet.normalizedLogVolume) * 6 =
        ((Finset.univ.sum action.generatorLogVolume) /
          (Fintype.card
            (IUTStage1ProcessionContainer (absLabelProcessionTop l)) : Real)) *
          6 := by
      ring
    _ =
        (absLabelProcessionTop l : Real) *
          (2 * (absLabelProcessionTop l : Real) + 1) *
            action.evaluation.environmentDegree := havg

theorem normalizedActedLogVolume_delta_nonnegative_of_environment_nonnegative
    (action : LGPSplittingMonoidTensorPacketAction l)
    (henv : 0 <= action.evaluation.environmentDegree) :
    0 <= action.normalizedActedLogVolume -
      action.packet.normalizedLogVolume := by
  have hdelta := action.normalizedActedLogVolume_delta_mul_six
  have htop : 0 <= (absLabelProcessionTop l : Real) := by
    exact_mod_cast (absLabelProcessionTop_pos l).le
  have hfactor :
      0 <= (absLabelProcessionTop l : Real) *
        (2 * (absLabelProcessionTop l : Real) + 1) := by
    exact mul_nonneg htop (by positivity)
  have hright :
      0 <= (absLabelProcessionTop l : Real) *
        (2 * (absLabelProcessionTop l : Real) + 1) *
          action.evaluation.environmentDegree :=
    mul_nonneg hfactor henv
  have hdelta6 :
      0 <=
        (action.normalizedActedLogVolume -
          action.packet.normalizedLogVolume) * 6 := by
    rw [hdelta]
    exact hright
  nlinarith

theorem packet_normalizedLogVolume_le_normalizedActedLogVolume_of_environment_nonnegative
    (action : LGPSplittingMonoidTensorPacketAction l)
    (henv : 0 <= action.evaluation.environmentDegree) :
    action.packet.normalizedLogVolume <= action.normalizedActedLogVolume := by
  have hdelta :=
    action.normalizedActedLogVolume_delta_nonnegative_of_environment_nonnegative
      henv
  linarith

theorem generatorLogVolume_average_eq_gaussianFullLabel_average
    (action : LGPSplittingMonoidTensorPacketAction l) :
    (Finset.univ.sum action.generatorLogVolume) /
        (Fintype.card
          (IUTStage1ProcessionContainer (absLabelProcessionTop l)) : Real) =
      (Finset.univ.sum action.evaluation.gaussianDegree) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) := by
  have hgenerator := action.generatorLogVolume_average_mul_six
  have hgaussian := gaussianDegree_fullLabel_average_mul_six action.evaluation
  nlinarith

theorem normalizedActedLogVolume_eq_packetNormalized_plus_gaussianFullLabelAverage
    (action : LGPSplittingMonoidTensorPacketAction l) :
    action.normalizedActedLogVolume =
      action.packet.normalizedLogVolume +
        (Finset.univ.sum action.evaluation.gaussianDegree) /
          (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) := by
  rw [action.normalizedActedLogVolume_eq_packetNormalized_plus_generatorAverage,
    action.generatorLogVolume_average_eq_gaussianFullLabel_average]

theorem environmentDegree_eq_zero_of_normalizedActedLogVolume_eq_packetNormalized
    (action : LGPSplittingMonoidTensorPacketAction l)
    (hfixed :
      action.normalizedActedLogVolume =
        action.packet.normalizedLogVolume) :
    action.evaluation.environmentDegree = 0 := by
  have hdelta := action.normalizedActedLogVolume_delta_mul_six
  have hcoeff_pos :
      0 <
        (absLabelProcessionTop l : Real) *
          (2 * (absLabelProcessionTop l : Real) + 1) := by
    have htop : 0 < (absLabelProcessionTop l : Real) := by
      exact_mod_cast absLabelProcessionTop_pos l
    positivity
  have hmul :
      ((absLabelProcessionTop l : Real) *
          (2 * (absLabelProcessionTop l : Real) + 1)) *
        action.evaluation.environmentDegree = 0 := by
    nlinarith
  exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hcoeff_pos)

theorem normalizedActedLogVolume_eq_packetNormalized_of_environmentDegree_eq_zero
    (action : LGPSplittingMonoidTensorPacketAction l)
    (henv : action.evaluation.environmentDegree = 0) :
    action.normalizedActedLogVolume =
      action.packet.normalizedLogVolume := by
  have hdelta :
      (action.normalizedActedLogVolume -
          action.packet.normalizedLogVolume) * 6 = 0 := by
    simpa [henv] using action.normalizedActedLogVolume_delta_mul_six
  nlinarith

theorem normalizedActedLogVolume_eq_packetNormalized_iff_environmentDegree_eq_zero
    (action : LGPSplittingMonoidTensorPacketAction l) :
    action.normalizedActedLogVolume =
        action.packet.normalizedLogVolume ↔
      action.evaluation.environmentDegree = 0 :=
  ⟨action.environmentDegree_eq_zero_of_normalizedActedLogVolume_eq_packetNormalized,
    action.normalizedActedLogVolume_eq_packetNormalized_of_environmentDegree_eq_zero⟩

theorem packetNormalized_lt_normalizedActedLogVolume_of_environmentDegree_pos
    (action : LGPSplittingMonoidTensorPacketAction l)
    (henv : 0 < action.evaluation.environmentDegree) :
    action.packet.normalizedLogVolume <
      action.normalizedActedLogVolume := by
  have hdelta := action.normalizedActedLogVolume_delta_mul_six
  have hcoeff_pos :
      0 <
        (absLabelProcessionTop l : Real) *
          (2 * (absLabelProcessionTop l : Real) + 1) := by
    have htop : 0 < (absLabelProcessionTop l : Real) := by
      exact_mod_cast absLabelProcessionTop_pos l
    positivity
  have hdelta_pos :
      0 <
        (action.normalizedActedLogVolume -
          action.packet.normalizedLogVolume) * 6 := by
    rw [hdelta]
    positivity
  nlinarith

theorem normalizedActedLogVolume_lt_packetNormalized_of_environmentDegree_neg
    (action : LGPSplittingMonoidTensorPacketAction l)
    (henv : action.evaluation.environmentDegree < 0) :
    action.normalizedActedLogVolume <
      action.packet.normalizedLogVolume := by
  have hdelta := action.normalizedActedLogVolume_delta_mul_six
  have hcoeff_pos :
      0 <
        (absLabelProcessionTop l : Real) *
          (2 * (absLabelProcessionTop l : Real) + 1) := by
    have htop : 0 < (absLabelProcessionTop l : Real) := by
      exact_mod_cast absLabelProcessionTop_pos l
    positivity
  have hdelta_neg :
      (action.normalizedActedLogVolume -
          action.packet.normalizedLogVolume) * 6 < 0 := by
    rw [hdelta]
    exact mul_neg_of_pos_of_neg hcoeff_pos henv
  nlinarith

/--
IUT III Fig. I.4 splitting-action endpoint.

The finite `q^{j^2}` Gaussian generators act on the procession tensor packet by
adding the generator log-volume at each label.  Consequently the normalized
acted log-volume is the original normalized packet log-volume plus the averaged
generator contribution; for nonnegative environment degree this action is
monotone at the normalized log-volume level.
-/
theorem qSquaredGeneratorTensorPacketAction_endpoint
    (action : LGPSplittingMonoidTensorPacketAction l) :
    action.generatorLogVolume
        (IUTStage1ProcessionContainer.core (absLabelProcessionTop l)) = 0 ∧
      (∀ label : IUTStage1ProcessionContainer (absLabelProcessionTop l),
        action.generatorLogVolume label =
          ((label.val : Real) ^ 2) * action.evaluation.environmentDegree) ∧
      action.actedTensorPacketLogVolume =
        action.packet.tensorPacketLogVolume +
          Finset.univ.sum action.generatorLogVolume ∧
      action.normalizedActedLogVolume =
        action.packet.normalizedLogVolume +
          (Finset.univ.sum action.generatorLogVolume) /
            (Fintype.card
              (IUTStage1ProcessionContainer (absLabelProcessionTop l)) : Real) ∧
      action.normalizedActedLogVolume =
        action.packet.normalizedLogVolume +
          (Finset.univ.sum action.evaluation.gaussianDegree) /
            (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) ∧
      (action.normalizedActedLogVolume =
          action.packet.normalizedLogVolume ↔
        action.evaluation.environmentDegree = 0) ∧
      (0 < action.evaluation.environmentDegree ->
        action.packet.normalizedLogVolume <
          action.normalizedActedLogVolume) ∧
      (action.evaluation.environmentDegree < 0 ->
        action.normalizedActedLogVolume <
          action.packet.normalizedLogVolume) ∧
      (0 <= action.evaluation.environmentDegree ->
        action.packet.normalizedLogVolume <= action.normalizedActedLogVolume) :=
  ⟨action.generatorLogVolume_core,
    action.generatorLogVolume_eq_procession_square,
    action.actedTensorPacketLogVolume_eq_original_plus_generators,
    action.normalizedActedLogVolume_eq_packetNormalized_plus_generatorAverage,
    action.normalizedActedLogVolume_eq_packetNormalized_plus_gaussianFullLabelAverage,
    action.normalizedActedLogVolume_eq_packetNormalized_iff_environmentDegree_eq_zero,
    action.packetNormalized_lt_normalizedActedLogVolume_of_environmentDegree_pos,
    action.normalizedActedLogVolume_lt_packetNormalized_of_environmentDegree_neg,
    action.packet_normalizedLogVolume_le_normalizedActedLogVolume_of_environment_nonnegative⟩

end LGPSplittingMonoidTensorPacketAction

namespace GaussianMonoidDegreeEvaluation

variable {l : PrimeGeFive}

open LGPSplittingMonoidTensorPacketAction

noncomputable def fullLabelAveragedLogVolume
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    IUTStage1LabelAveragedProcessionLogVolume
      (IUTStage1ZModCuspFullLabel l) :=
  { normalizedLogVolume := evaluation.gaussianDegree,
    averageLogVolume :=
      (Finset.univ.sum evaluation.gaussianDegree) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real),
    average_eq := rfl }

theorem fullLabelAveragedLogVolume_average_eq_subordinate_sum_div
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.fullLabelAveragedLogVolume.averageLogVolume =
      ((@Finset.filter (IUTStage1ZModCuspFullLabel l)
        (fun label : IUTStage1ZModCuspFullLabel l =>
          IUTStage1ZModCuspFullLabel.WeightedVolumeSubordinate
            label IUTStage1ZModCuspFullLabel.zero)
        (Classical.decPred _) Finset.univ).sum evaluation.gaussianDegree) /
        ((absLabelProcessionTop l : Real) + 1) := by
  classical
  have hsplit :=
    fullLabel_average_eq_zero_add_subordinate_sum_div
      (l := l) evaluation.gaussianDegree
  rw [evaluation.gaussianDegree_zero] at hsplit
  simpa [fullLabelAveragedLogVolume] using hsplit

theorem gaussianDegree_fullLabel_sum_unitAction_eq
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) :
    (Finset.univ.sum fun label : IUTStage1ZModCuspFullLabel l =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.unitActionOnFullLabel l a label)) =
      Finset.univ.sum evaluation.gaussianDegree :=
  fullLabel_sum_unitAction_eq a evaluation.gaussianDegree

theorem fullLabelAveragedLogVolume_average_unitAction_eq
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) :
    (Finset.univ.sum fun label : IUTStage1ZModCuspFullLabel l =>
      evaluation.gaussianDegree
        (IUTStage1ZModCuspFullLabel.unitActionOnFullLabel l a label)) /
        (Fintype.card (IUTStage1ZModCuspFullLabel l) : Real) =
      evaluation.fullLabelAveragedLogVolume.averageLogVolume := by
  rw [evaluation.gaussianDegree_fullLabel_sum_unitAction_eq]
  rfl

theorem gaussianDegree_subordinate_sum_unitAction_eq
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) :
    (@Finset.filter (IUTStage1ZModCuspFullLabel l)
      (fun label : IUTStage1ZModCuspFullLabel l =>
        IUTStage1ZModCuspFullLabel.WeightedVolumeSubordinate
          label IUTStage1ZModCuspFullLabel.zero)
      (Classical.decPred _) Finset.univ).sum
        (fun label : IUTStage1ZModCuspFullLabel l =>
          evaluation.gaussianDegree
            (IUTStage1ZModCuspFullLabel.unitActionOnFullLabel l a label)) =
      (@Finset.filter (IUTStage1ZModCuspFullLabel l)
        (fun label : IUTStage1ZModCuspFullLabel l =>
          IUTStage1ZModCuspFullLabel.WeightedVolumeSubordinate
            label IUTStage1ZModCuspFullLabel.zero)
        (Classical.decPred _) Finset.univ).sum evaluation.gaussianDegree :=
  subordinateFullLabel_sum_unitAction_eq a evaluation.gaussianDegree

theorem fullLabelAveragedLogVolume_average_eq_coeff
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.fullLabelAveragedLogVolume.averageLogVolume =
      ((absLabelProcessionTop l : Real) *
        (2 * (absLabelProcessionTop l : Real) + 1) / 6) *
          evaluation.environmentDegree :=
  LGPSplittingMonoidTensorPacketAction.gaussianDegree_fullLabel_average_eq_coeff
    evaluation

theorem gaussianDegree_subordinate_sum_mul_six
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    ((@Finset.filter (IUTStage1ZModCuspFullLabel l)
      (fun label : IUTStage1ZModCuspFullLabel l =>
        IUTStage1ZModCuspFullLabel.WeightedVolumeSubordinate
          label IUTStage1ZModCuspFullLabel.zero)
      (Classical.decPred _) Finset.univ).sum evaluation.gaussianDegree) * 6 =
      ((absLabelProcessionTop l : Real) *
        ((absLabelProcessionTop l : Real) + 1) *
          (2 * (absLabelProcessionTop l : Real) + 1)) *
        evaluation.environmentDegree := by
  classical
  let subSum : Real :=
    (@Finset.filter (IUTStage1ZModCuspFullLabel l)
      (fun label : IUTStage1ZModCuspFullLabel l =>
        IUTStage1ZModCuspFullLabel.WeightedVolumeSubordinate
          label IUTStage1ZModCuspFullLabel.zero)
      (Classical.decPred _) Finset.univ).sum evaluation.gaussianDegree
  have hcoeff := evaluation.fullLabelAveragedLogVolume_average_eq_coeff
  rw [evaluation.fullLabelAveragedLogVolume_average_eq_subordinate_sum_div] at hcoeff
  change
    subSum / ((absLabelProcessionTop l : Real) + 1) =
      ((absLabelProcessionTop l : Real) *
        (2 * (absLabelProcessionTop l : Real) + 1) / 6) *
          evaluation.environmentDegree at hcoeff
  have hden : ((absLabelProcessionTop l : Real) + 1) ≠ 0 := by
    positivity
  rw [div_eq_iff hden] at hcoeff
  change
    subSum * 6 =
      ((absLabelProcessionTop l : Real) *
        ((absLabelProcessionTop l : Real) + 1) *
          (2 * (absLabelProcessionTop l : Real) + 1)) *
        evaluation.environmentDegree
  nlinarith

theorem gaussianDegree_subordinate_sum_eq_absNonzeroLabel_sum
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    (@Finset.filter (IUTStage1ZModCuspFullLabel l)
      (fun label : IUTStage1ZModCuspFullLabel l =>
        IUTStage1ZModCuspFullLabel.WeightedVolumeSubordinate
          label IUTStage1ZModCuspFullLabel.zero)
      (Classical.decPred _) Finset.univ).sum evaluation.gaussianDegree =
      Finset.univ.sum fun label : Fin (absLabelProcessionTop l) =>
        evaluation.gaussianDegree (absNonzeroLabelFromIndex l label) := by
  have hsub := evaluation.gaussianDegree_subordinate_sum_mul_six
  have habs := gaussianDegree_absNonzeroLabel_sum_mul_six evaluation
  nlinarith

theorem coordinateAveragedLogVolume_average_eq_coeff
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.coordinateAveragedLogVolume.averageLogVolume =
      ((absLabelProcessionTop l : Real) *
        ((absLabelProcessionTop l : Real) + 1) / 3) *
          evaluation.environmentDegree := by
  rw [coordinateAveragedLogVolume_eq_absNonzero_mass_rescale,
    LGPSplittingMonoidTensorPacketAction.gaussianDegree_absNonzeroLabel_average_eq_coeff]
  rw [primeValue_sub_one_eq_two_absLabelProcessionTop,
    primeValue_eq_two_absLabelProcessionTop_add_one]
  have hden :
      (2 * (absLabelProcessionTop l : Real) + 1) ≠ 0 := by
    positivity
  norm_num
  field_simp [hden]
  ring

theorem coordinateAveragedLogVolume_eq_fullLabel_mass_rescale
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.coordinateAveragedLogVolume.averageLogVolume =
      ((l.value + 1 : Nat) : Real) / (l.value : Real) *
        evaluation.fullLabelAveragedLogVolume.averageLogVolume := by
  rw [evaluation.coordinateAveragedLogVolume_average_eq_coeff,
    evaluation.fullLabelAveragedLogVolume_average_eq_coeff]
  rw [primeValue_eq_two_absLabelProcessionTop_add_one]
  have hden :
      (2 * (absLabelProcessionTop l : Real) + 1) ≠ 0 := by
    positivity
  norm_num
  field_simp [hden]
  ring

theorem fullLabelAverageCoefficient_lt_coordinateAverageCoefficient :
    (absLabelProcessionTop l : Real) *
        (2 * (absLabelProcessionTop l : Real) + 1) / 6 <
      (absLabelProcessionTop l : Real) *
        ((absLabelProcessionTop l : Real) + 1) / 3 := by
  have htop_pos : 0 < (absLabelProcessionTop l : Real) := by
    exact_mod_cast absLabelProcessionTop_pos l
  nlinarith

theorem coordinateAveragedLogVolume_lt_fullLabelAverage_of_negative
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_neg : evaluation.environmentDegree < 0) :
    evaluation.coordinateAveragedLogVolume.averageLogVolume <
      evaluation.fullLabelAveragedLogVolume.averageLogVolume := by
  rw [evaluation.coordinateAveragedLogVolume_average_eq_coeff,
    evaluation.fullLabelAveragedLogVolume_average_eq_coeff]
  let fullCoeff : Real :=
    (absLabelProcessionTop l : Real) *
      (2 * (absLabelProcessionTop l : Real) + 1) / 6
  let coordinateCoeff : Real :=
    (absLabelProcessionTop l : Real) *
      ((absLabelProcessionTop l : Real) + 1) / 3
  have hcoeff : fullCoeff < coordinateCoeff := by
    simpa [fullCoeff, coordinateCoeff] using
      fullLabelAverageCoefficient_lt_coordinateAverageCoefficient (l := l)
  have hmul :
      coordinateCoeff * evaluation.environmentDegree <
        fullCoeff * evaluation.environmentDegree :=
    mul_lt_mul_of_neg_right hcoeff henv_neg
  simpa [fullCoeff, coordinateCoeff] using hmul

theorem fullLabelAverage_lt_coordinateAveragedLogVolume_of_positive
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_pos : 0 < evaluation.environmentDegree) :
    evaluation.fullLabelAveragedLogVolume.averageLogVolume <
      evaluation.coordinateAveragedLogVolume.averageLogVolume := by
  rw [evaluation.coordinateAveragedLogVolume_average_eq_coeff,
    evaluation.fullLabelAveragedLogVolume_average_eq_coeff]
  let fullCoeff : Real :=
    (absLabelProcessionTop l : Real) *
      (2 * (absLabelProcessionTop l : Real) + 1) / 6
  let coordinateCoeff : Real :=
    (absLabelProcessionTop l : Real) *
      ((absLabelProcessionTop l : Real) + 1) / 3
  have hcoeff : fullCoeff < coordinateCoeff := by
    simpa [fullCoeff, coordinateCoeff] using
      fullLabelAverageCoefficient_lt_coordinateAverageCoefficient (l := l)
  have hmul :
      fullCoeff * evaluation.environmentDegree <
        coordinateCoeff * evaluation.environmentDegree :=
    mul_lt_mul_of_pos_right hcoeff henv_pos
  simpa [fullCoeff, coordinateCoeff] using hmul

theorem coordinateAveragedLogVolume_eq_fullLabelAverage_iff
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.coordinateAveragedLogVolume.averageLogVolume =
        evaluation.fullLabelAveragedLogVolume.averageLogVolume ↔
      evaluation.environmentDegree = 0 := by
  constructor
  · intro h
    by_cases hneg : evaluation.environmentDegree < 0
    · have hlt :=
        evaluation.coordinateAveragedLogVolume_lt_fullLabelAverage_of_negative
          hneg
      linarith
    · by_cases hpos : 0 < evaluation.environmentDegree
      · have hlt :=
          evaluation.fullLabelAverage_lt_coordinateAveragedLogVolume_of_positive
            hpos
        linarith
      · linarith
  · intro henv
    rw [evaluation.coordinateAveragedLogVolume_average_eq_coeff,
      evaluation.fullLabelAveragedLogVolume_average_eq_coeff, henv]
    ring

theorem fullLabelAveragedLogVolume_canonicalCoordinate_eq_environment
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.fullLabelAveragedLogVolume.normalizedLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) =
      evaluation.environmentDegree :=
  evaluation.gaussianDegree_one

theorem fullLabelAveragedLogVolume_average_ne_canonicalCoordinate_of_nonzero
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv : evaluation.environmentDegree ≠ 0) :
    evaluation.fullLabelAveragedLogVolume.averageLogVolume ≠
      evaluation.fullLabelAveragedLogVolume.normalizedLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) := by
  have hraw :=
    gaussianDegree_fullLabel_average_ne_environment_of_nonzero
      evaluation henv
  intro h
  apply hraw
  rw [← fullLabelAveragedLogVolume_canonicalCoordinate_eq_environment
    evaluation]
  exact h

theorem fullLabelAveragedLogVolume_average_lt_canonicalCoordinate_of_negative
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_neg : evaluation.environmentDegree < 0) :
    evaluation.fullLabelAveragedLogVolume.averageLogVolume <
      evaluation.fullLabelAveragedLogVolume.normalizedLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) := by
  rw [evaluation.fullLabelAveragedLogVolume_canonicalCoordinate_eq_environment]
  exact gaussianDegree_fullLabel_average_lt_environment_of_negative
    evaluation henv_neg

theorem fullLabelAveragedLogVolume_canonicalCoordinate_lt_average_of_positive
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_pos : 0 < evaluation.environmentDegree) :
    evaluation.fullLabelAveragedLogVolume.normalizedLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) <
      evaluation.fullLabelAveragedLogVolume.averageLogVolume := by
  rw [evaluation.fullLabelAveragedLogVolume_canonicalCoordinate_eq_environment]
  exact gaussianDegree_fullLabel_average_gt_environment_of_positive
    evaluation henv_pos

theorem fullLabelAveragedLogVolume_average_eq_canonicalCoordinate_iff
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    evaluation.fullLabelAveragedLogVolume.averageLogVolume =
      evaluation.fullLabelAveragedLogVolume.normalizedLogVolume
        (IUTStage1ZModCuspFullLabel.fromCoordinate l (1 : ZMod l.value)) ↔
      evaluation.environmentDegree = 0 := by
  constructor
  · intro h
    by_contra henv
    exact
      evaluation.fullLabelAveragedLogVolume_average_ne_canonicalCoordinate_of_nonzero
        henv h
  · intro henv
    rw [evaluation.fullLabelAveragedLogVolume_average_eq_coeff]
    rw [evaluation.fullLabelAveragedLogVolume_canonicalCoordinate_eq_environment]
    rw [henv]
    ring

theorem fullLabelAveragedLogVolume_le_environment_of_nonpositive
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (henv_nonpos : evaluation.environmentDegree <= 0) :
    evaluation.fullLabelAveragedLogVolume.averageLogVolume <=
      evaluation.environmentDegree :=
  gaussianDegree_fullLabel_average_le_environment_of_nonpositive
    evaluation henv_nonpos

theorem fullLabelAveragedLogVolume_le_of_environment_le_bound
    (evaluation : GaussianMonoidDegreeEvaluation l)
    {c : Real}
    (henv_nonpos : evaluation.environmentDegree <= 0)
    (henv_le : evaluation.environmentDegree <= c) :
    evaluation.fullLabelAveragedLogVolume.averageLogVolume <= c :=
  le_trans
    (evaluation.fullLabelAveragedLogVolume_le_environment_of_nonpositive
      henv_nonpos)
    henv_le

end GaussianMonoidDegreeEvaluation

noncomputable def balancedFullLabelWeightedSummand
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (label : IUTStage1ZModCuspFullLabel l) : Real :=
  balancedSquareWeightOnFullLabel (l := l) label *
    compat.fullLabelLogVolume label

noncomputable def representativeFullLabelWeightedSummand
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (j : ZMod l.value) : Real :=
  ((j.val : Real) ^ 2) *
    compat.fullLabelLogVolume (IUTStage1ZModCuspFullLabel.fromCoordinate l j)

theorem balancedFullLabelWeightedSummand_fromCoordinate
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (j : ZMod l.value) :
    balancedFullLabelWeightedSummand
        (l := l) compat
        (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
      balancedSquareWeight (l := l) j * compat.normalizedLogVolume j := by
  unfold balancedFullLabelWeightedSummand
  rw [balancedSquareWeightOnFullLabel_fromCoordinate]
  rw [compat.normalizedLogVolume_eq_fullLabelLogVolume_fromCoordinate]

theorem representativeFullLabelWeightedSummand_constant_one
    (j : ZMod l.value) :
    representativeFullLabelWeightedSummand
        (l := l)
        (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
          (l := l) (1 : Real)) j =
      ((j.val : Real) ^ 2) := by
  unfold representativeFullLabelWeightedSummand
  rw [IUTStage1ZModCuspLabelLogVolumeCompatibility.constant_fullLabelLogVolume_fromCoordinate
    (l := l) (1 : Real) j]
  ring

theorem coordinateSquarePreserving_of_representativeSummand_constant_one_preserved
    {coordinateEquiv : ZMod l.value ≃ ZMod l.value}
    (hsummand :
      ∀ j : ZMod l.value,
        representativeFullLabelWeightedSummand
            (l := l)
            (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
              (l := l) (1 : Real)) (coordinateEquiv j) =
          representativeFullLabelWeightedSummand
            (l := l)
            (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
              (l := l) (1 : Real)) j) :
    CoordinateSquarePreserving (l := l) coordinateEquiv := by
  intro j
  have h := hsummand j
  rw [representativeFullLabelWeightedSummand_constant_one,
    representativeFullLabelWeightedSummand_constant_one] at h
  exact h

theorem representativeSummand_constant_one_preserved_of_coordinateSquarePreserving
    {coordinateEquiv : ZMod l.value ≃ ZMod l.value}
    (hcoord : CoordinateSquarePreserving (l := l) coordinateEquiv) :
    ∀ j : ZMod l.value,
      representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
            (l := l) (1 : Real)) (coordinateEquiv j) =
        representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
            (l := l) (1 : Real)) j := by
  intro j
  rw [representativeFullLabelWeightedSummand_constant_one,
    representativeFullLabelWeightedSummand_constant_one]
  exact hcoord j

theorem representativeSummand_constant_one_preserved_iff_coordinateSquarePreserving
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value) :
    (∀ j : ZMod l.value,
      representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
            (l := l) (1 : Real)) (coordinateEquiv j) =
        representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
            (l := l) (1 : Real)) j) ↔
      CoordinateSquarePreserving (l := l) coordinateEquiv := by
  constructor
  · exact coordinateSquarePreserving_of_representativeSummand_constant_one_preserved
  · exact representativeSummand_constant_one_preserved_of_coordinateSquarePreserving

theorem representativeFullLabelWeightedSummand_total_preserved
    (compat : IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value) :
    (Finset.univ.sum fun j : ZMod l.value =>
      representativeFullLabelWeightedSummand
        (l := l) compat (coordinateEquiv j)) =
      Finset.univ.sum fun j : ZMod l.value =>
        representativeFullLabelWeightedSummand (l := l) compat j :=
  Fintype.sum_equiv coordinateEquiv
    (fun j : ZMod l.value =>
      representativeFullLabelWeightedSummand
        (l := l) compat (coordinateEquiv j))
    (fun j : ZMod l.value =>
      representativeFullLabelWeightedSummand (l := l) compat j)
    (fun _j => rfl)

theorem representativeSummand_constant_one_total_preserved_neg :
    (Finset.univ.sum fun j : ZMod l.value =>
      representativeFullLabelWeightedSummand
        (l := l)
        (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
          (l := l) (1 : Real))
        ((Equiv.neg (ZMod l.value)) j)) =
      Finset.univ.sum fun j : ZMod l.value =>
        representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
            (l := l) (1 : Real))
          j :=
  representativeFullLabelWeightedSummand_total_preserved
    (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
      (l := l) (1 : Real))
    (Equiv.neg (ZMod l.value))

theorem fullLabelSummand_preserved_of_fullLabelMap
    {coordinateEquiv : ZMod l.value ≃ ZMod l.value}
    (hmap :
      IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
        (l := l) coordinateEquiv)
    (sourceSummand targetSummand : IUTStage1ZModCuspFullLabel l -> Real)
    (hvalue :
      ∀ label : IUTStage1ZModCuspFullLabel l,
        targetSummand label = sourceSummand label) :
    ∀ j : ZMod l.value,
      targetSummand
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (coordinateEquiv j)) =
        sourceSummand (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  intro j
  rw [hmap j]
  exact hvalue (IUTStage1ZModCuspFullLabel.fromCoordinate l j)

theorem balancedFullLabelWeightedSummand_preserved_of_fullLabelMap
    {coordinateEquiv : ZMod l.value ≃ ZMod l.value}
    (hmap :
      IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
        (l := l) coordinateEquiv)
    (sourceLogVolume targetLogVolume :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (hvalue :
      IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelLogVolumeValuePreserving
        sourceLogVolume targetLogVolume) :
    ∀ j : ZMod l.value,
      balancedFullLabelWeightedSummand (l := l) targetLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l (coordinateEquiv j)) =
        balancedFullLabelWeightedSummand (l := l) sourceLogVolume
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  intro j
  unfold balancedFullLabelWeightedSummand
  rw [hmap j]
  rw [hvalue (IUTStage1ZModCuspFullLabel.fromCoordinate l j)]

theorem balancedSquareWeight_eq_square_val_of_val_le_half
    (j : ZMod l.value) (hhalf : j.val ≤ l.value / 2) :
    balancedSquareWeight (l := l) j = ((j.val : Real) ^ 2) := by
  unfold balancedSquareWeight
  rw [ZMod.valMinAbs_natAbs_eq_min]
  have hcomp : j.val ≤ l.value - j.val := by
    omega
  rw [Nat.min_eq_left hcomp]

theorem coordinateBalancedSquarePreserving_refl :
    CoordinateBalancedSquarePreserving
      (l := l) (Equiv.refl (ZMod l.value)) := by
  intro j
  rfl

theorem coordinateBalancedSquarePreserving_neg :
    CoordinateBalancedSquarePreserving
      (l := l) (Equiv.neg (ZMod l.value)) := by
  intro j
  exact balancedSquareWeight_neg_eq j

/--
Rigidity of the current real representative-square profile.

Since `ZMod.val` takes nonnegative representatives, equality of real squares
forces equality of representatives.
-/
theorem coordinateSquarePreserving_val_eq
    {coordinateEquiv : ZMod l.value ≃ ZMod l.value}
    (hcoord : CoordinateSquarePreserving (l := l) coordinateEquiv) :
    ∀ j : ZMod l.value, (coordinateEquiv j).val = j.val := by
  intro j
  have hsq := hcoord j
  have heq_or := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  rcases heq_or with heq | hneg
  · exact_mod_cast heq
  · have hleft_nonneg : (0 : Real) <= ((coordinateEquiv j).val : Real) := by
      exact_mod_cast Nat.zero_le _
    have hright_nonneg : (0 : Real) <= ((j.val) : Real) := by
      exact_mod_cast Nat.zero_le _
    have hleft_zero : (((coordinateEquiv j).val : Real)) = 0 := by
      nlinarith
    have hright_zero : (((j.val) : Real)) = 0 := by
      nlinarith
    exact_mod_cast hleft_zero.trans hright_zero.symm

theorem coordinateSquarePreserving_apply_eq
    {coordinateEquiv : ZMod l.value ≃ ZMod l.value}
    (hcoord : CoordinateSquarePreserving (l := l) coordinateEquiv) :
    ∀ j : ZMod l.value, coordinateEquiv j = j := by
  intro j
  exact ZMod.val_injective l.value
    (coordinateSquarePreserving_val_eq hcoord j)

theorem coordinateSquarePreserving_eq_refl
    {coordinateEquiv : ZMod l.value ≃ ZMod l.value}
    (hcoord : CoordinateSquarePreserving (l := l) coordinateEquiv) :
    coordinateEquiv = Equiv.refl (ZMod l.value) := by
  ext j
  exact coordinateSquarePreserving_apply_eq hcoord j

theorem coordinateSquarePreserving_unitAffine_iff
    (a : (ZMod l.value)ˣ) (t : ZMod l.value) :
    CoordinateSquarePreserving
        (l := l)
        (IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodUnitAffineEquiv
          l a t) ↔
      t = 0 ∧ a = 1 := by
  constructor
  · intro hcoord
    have hzero := coordinateSquarePreserving_apply_eq hcoord (0 : ZMod l.value)
    rw [IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodUnitAffineEquiv_apply,
      zmodLabelTranslate_eq_add] at hzero
    have ht : t = 0 := by
      simpa [zmodUnitActionData] using hzero
    have hone := coordinateSquarePreserving_apply_eq hcoord (1 : ZMod l.value)
    subst t
    rw [IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodUnitAffineEquiv_apply,
      zmodLabelTranslate_zero] at hone
    have ha_coord : (a : ZMod l.value) = 1 := by
      simpa [zmodUnitActionData] using hone
    have ha : a = 1 := by
      ext
      simpa using ha_coord
    exact ⟨rfl, ha⟩
  · rintro ⟨ht, ha⟩
    subst t
    subst a
    intro j
    rw [IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodUnitAffineEquiv_apply,
      zmodLabelTranslate_zero]
    simp [zmodUnitActionData]

theorem unitAffine_factoredSquareFullLabelPreserving_iff_identity
    (a : (ZMod l.value)ˣ) (t : ZMod l.value) :
    (CoordinateSquarePreserving
        (l := l)
        (IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodUnitAffineEquiv
          l a t) ∧
      IUTStage1ZModCuspLabelLogVolumeCompatibility.FullLabelMapPreserving
        (l := l)
        (IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodUnitAffineEquiv
          l a t)) ↔
      t = 0 ∧ a = 1 := by
  constructor
  · intro hpres
    exact (coordinateSquarePreserving_unitAffine_iff (l := l) a t).mp hpres.1
  · rintro ⟨ht, ha⟩
    constructor
    · exact (coordinateSquarePreserving_unitAffine_iff (l := l) a t).mpr
        ⟨ht, ha⟩
    · rw [IUTStage1ZModCuspLabelLogVolumeCompatibility.fullLabelMapPreserving_unitAffine_iff]
      subst a
      exact ⟨ht, one_mem_zmodSignUnitSubgroup l⟩

namespace GaussianMonoidDegreeEvaluation

theorem unitAffine_pointwise_gaussian_and_coordinateSquarePreserving_iff_identity
    (evaluation : GaussianMonoidDegreeEvaluation l)
    (a : (ZMod l.value)ˣ) (t : ZMod l.value)
    (henv : evaluation.environmentDegree ≠ 0) :
    ((∀ j : ZMod l.value,
      evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (zmodLabelTranslate l t ((zmodUnitActionData l).smul a j))) =
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) ∧
      CoordinateSquarePreserving
        (l := l)
        (IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodUnitAffineEquiv
          l a t)) ↔
      t = 0 ∧ a = 1 := by
  constructor
  · intro hpres
    exact
      (coordinateSquarePreserving_unitAffine_iff (l := l) a t).mp
        hpres.2
  · intro hidentity
    constructor
    · exact
        (evaluation.unitAffine_pointwise_gaussian_preserving_iff a t henv).mpr
          ⟨hidentity.1, by
            rw [hidentity.2]
            exact one_mem_zmodSignUnitSubgroup l⟩
    · exact
        (coordinateSquarePreserving_unitAffine_iff (l := l) a t).mpr
          hidentity

end GaussianMonoidDegreeEvaluation

theorem neg_one_ne_one :
    (-(1 : ZMod l.value)) ≠ (1 : ZMod l.value) := by
  intro h
  haveI : Fact (1 < l.value) :=
    ⟨lt_of_lt_of_le (by norm_num) l.ge_five⟩
  have hval := congrArg ZMod.val h
  have hOneNe : (1 : ZMod l.value) ≠ 0 := one_ne_zero
  haveI : NeZero (1 : ZMod l.value) := ⟨hOneNe⟩
  rw [ZMod.val_neg_of_ne_zero, ZMod.val_one] at hval
  have hge : 5 ≤ l.value := l.ge_five
  omega

theorem neg_unit_ne_one :
    (-1 : (ZMod l.value)ˣ) ≠ 1 := by
  intro h
  exact neg_one_ne_one (l := l) (by
    have hcoord :=
      congrArg (fun a : (ZMod l.value)ˣ => (a : ZMod l.value)) h
    simpa using hcoord)

theorem negUnitAffine_pointwiseGaussianPreserving_and_not_coordinateSquarePreserving
    (evaluation : GaussianMonoidDegreeEvaluation l) :
    (∀ j : ZMod l.value,
      evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l
            (zmodLabelTranslate l (0 : ZMod l.value)
              ((zmodUnitActionData l).smul
                (-1 : (ZMod l.value)ˣ) j))) =
        evaluation.gaussianDegree
          (IUTStage1ZModCuspFullLabel.fromCoordinate l j)) ∧
      ¬ CoordinateSquarePreserving
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.zmodUnitAffineEquiv
            l (-1 : (ZMod l.value)ˣ) (0 : ZMod l.value)) := by
  constructor
  · intro j
    exact evaluation.gaussianDegree_unitAffine_fromCoordinate_eq_of_signSubgroup
      (neg_one_mem_zmodSignUnitSubgroup l) j
  · intro hcoord
    have hstrict :=
      (coordinateSquarePreserving_unitAffine_iff
        (l := l) (-1 : (ZMod l.value)ˣ) (0 : ZMod l.value)).mp hcoord
    exact neg_unit_ne_one (l := l) hstrict.2

theorem not_coordinateSquarePreserving_neg :
    ¬ CoordinateSquarePreserving
      (l := l) (Equiv.neg (ZMod l.value)) := by
  intro hcoord
  exact neg_one_ne_one
    (coordinateSquarePreserving_apply_eq hcoord (1 : ZMod l.value))

theorem coordinateModularSquarePreserving_neg_and_not_coordinateSquarePreserving_neg :
    CoordinateModularSquarePreserving
        (l := l) (Equiv.neg (ZMod l.value)) ∧
      ¬ CoordinateSquarePreserving
        (l := l) (Equiv.neg (ZMod l.value)) :=
  ⟨coordinateModularSquarePreserving_neg,
    not_coordinateSquarePreserving_neg⟩

theorem coordinateBalancedSquarePreserving_neg_and_not_coordinateSquarePreserving_neg :
    CoordinateBalancedSquarePreserving
        (l := l) (Equiv.neg (ZMod l.value)) ∧
      ¬ CoordinateSquarePreserving
        (l := l) (Equiv.neg (ZMod l.value)) :=
  ⟨coordinateBalancedSquarePreserving_neg,
    not_coordinateSquarePreserving_neg⟩

theorem coordinateSquarePreserving_neg_of_representativeSquareWeightOnSignQuotient
    (weightOnQuotient : (zmodSignAction l).SignLabelQuotient -> Real)
    (hweight :
      ∀ (j : ZMod l.value) (hj : j ≠ 0),
        weightOnQuotient (zmodSignLabelFromCoordinate l j hj) =
          ((j.val : Real) ^ 2)) :
    CoordinateSquarePreserving
      (l := l) (Equiv.neg (ZMod l.value)) := by
  intro j
  by_cases hj : j = 0
  · subst j
    simp
  · have hneg : -j ≠ 0 := zmod_neg_ne_zero_of_ne_zero l hj
    change (((-j).val : Real) ^ 2) = ((j.val : Real) ^ 2)
    calc
      (((-j).val : Real) ^ 2) =
          weightOnQuotient (zmodSignLabelFromCoordinate l (-j) hneg) := by
        exact (hweight (-j) hneg).symm
      _ = weightOnQuotient (zmodSignLabelFromCoordinate l j hj) := by
        rw [zmodSignLabelFromCoordinate_neg_eq]
      _ = ((j.val : Real) ^ 2) :=
        hweight j hj

theorem not_exists_representativeSquareWeightOnSignQuotient :
    ¬ ∃ weightOnQuotient : (zmodSignAction l).SignLabelQuotient -> Real,
      ∀ (j : ZMod l.value) (hj : j ≠ 0),
        weightOnQuotient (zmodSignLabelFromCoordinate l j hj) =
          ((j.val : Real) ^ 2) := by
  rintro ⟨weightOnQuotient, hweight⟩
  exact not_coordinateSquarePreserving_neg
    (coordinateSquarePreserving_neg_of_representativeSquareWeightOnSignQuotient
      weightOnQuotient hweight)

/--
The representative q-to-theta degree rule does not descend to sign-quotient
labels when the q-pilot degree is nonzero.

The obstruction is exactly the same as for representative square weights:
dividing a hypothetical quotient-level theta-degree function by the nonzero
q-pilot degree would produce a quotient-level representative `j.val ^ 2`
function, contradicting `not_exists_representativeSquareWeightOnSignQuotient`.
-/
theorem not_exists_signQuotient_representativeThetaPilotDegree
    (qPilotDegree : Real) (q_ne_zero : qPilotDegree ≠ 0) :
    ¬ ∃ thetaOnQuotient :
        (zmodSignAction l).SignLabelQuotient -> Real,
      ∀ (j : ZMod l.value) (hj : j ≠ 0),
        thetaOnQuotient (zmodSignLabelFromCoordinate l j hj) =
          representativeSquareScale (l := l) j * qPilotDegree := by
  rintro ⟨thetaOnQuotient, htheta⟩
  exact not_exists_representativeSquareWeightOnSignQuotient (l := l)
    ⟨fun label => thetaOnQuotient label / qPilotDegree,
      by
        intro j hj
        calc
          thetaOnQuotient (zmodSignLabelFromCoordinate l j hj) /
              qPilotDegree =
              (representativeSquareScale (l := l) j * qPilotDegree) /
                qPilotDegree := by
            rw [htheta j hj]
          _ = representativeSquareScale (l := l) j := by
            exact mul_div_cancel_right₀
              (representativeSquareScale (l := l) j) q_ne_zero
          _ = ((j.val : Real) ^ 2) :=
            representativeSquareScale_eq (l := l) j⟩

theorem not_exists_representativeSquareWeightOnFullLabel :
    ¬ ∃ weightOnFullLabel : IUTStage1ZModCuspFullLabel l -> Real,
      ∀ j : ZMod l.value,
        weightOnFullLabel (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
          ((j.val : Real) ^ 2) := by
  rintro ⟨weightOnFullLabel, hweight⟩
  exact not_exists_representativeSquareWeightOnSignQuotient
    ⟨fun label =>
        weightOnFullLabel (IUTStage1ZModCuspFullLabel.nonzero label),
      by
        intro j hj
        change weightOnFullLabel
            (IUTStage1ZModCuspFullLabel.nonzero
              (zmodSignLabelFromCoordinate l j hj)) =
          ((j.val : Real) ^ 2)
        rw [← IUTStage1ZModCuspFullLabel.fromCoordinate_nonzero l j hj]
        exact hweight j⟩

theorem not_exists_representativeSquareUnitSummandOnFullLabel :
    ¬ ∃ summandOnFullLabel : IUTStage1ZModCuspFullLabel l -> Real,
      ∀ j : ZMod l.value,
        summandOnFullLabel (IUTStage1ZModCuspFullLabel.fromCoordinate l j) =
          ((j.val : Real) ^ 2) *
            (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
              (l := l) (1 : Real)).fullLabelLogVolume
                (IUTStage1ZModCuspFullLabel.fromCoordinate l j) := by
  rintro ⟨summandOnFullLabel, hsummand⟩
  exact not_exists_representativeSquareWeightOnFullLabel
    ⟨summandOnFullLabel, by
      intro j
      have h := hsummand j
      rw [IUTStage1ZModCuspLabelLogVolumeCompatibility.constant_fullLabelLogVolume_fromCoordinate
        (l := l) (1 : Real) j] at h
      simpa using h⟩

theorem coordinateSquarePreserving_neg_of_representativeSummand_constant_one_preserved
    (hsummand :
      ∀ j : ZMod l.value,
        representativeFullLabelWeightedSummand
            (l := l)
            (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
              (l := l) (1 : Real)) (-j) =
          representativeFullLabelWeightedSummand
            (l := l)
            (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
              (l := l) (1 : Real)) j) :
    CoordinateSquarePreserving
      (l := l) (Equiv.neg (ZMod l.value)) := by
  intro j
  change (((-j).val : Real) ^ 2) = ((j.val : Real) ^ 2)
  have h := hsummand j
  rw [representativeFullLabelWeightedSummand_constant_one,
    representativeFullLabelWeightedSummand_constant_one] at h
  exact h

theorem not_representativeSummand_constant_one_preserved_neg :
    ¬ ∀ j : ZMod l.value,
      representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
            (l := l) (1 : Real)) (-j) =
        representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
            (l := l) (1 : Real)) j := by
  intro hsummand
  exact not_coordinateSquarePreserving_neg
    (coordinateSquarePreserving_neg_of_representativeSummand_constant_one_preserved
      hsummand)

theorem exists_representativeSummand_constant_one_total_preserved_not_pointwise :
    ∃ coordinateEquiv : ZMod l.value ≃ ZMod l.value,
      ((Finset.univ.sum fun j : ZMod l.value =>
        representativeFullLabelWeightedSummand
          (l := l)
          (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
            (l := l) (1 : Real))
          (coordinateEquiv j)) =
        Finset.univ.sum fun j : ZMod l.value =>
          representativeFullLabelWeightedSummand
            (l := l)
            (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
              (l := l) (1 : Real))
            j) ∧
        ¬ ∀ j : ZMod l.value,
          representativeFullLabelWeightedSummand
              (l := l)
              (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
                (l := l) (1 : Real))
              (coordinateEquiv j) =
            representativeFullLabelWeightedSummand
              (l := l)
              (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
                (l := l) (1 : Real))
              j := by
  exact
    ⟨Equiv.neg (ZMod l.value),
      representativeSummand_constant_one_total_preserved_neg,
      not_representativeSummand_constant_one_preserved_neg⟩

theorem exists_balancedSquarePreserving_not_representativeSummand_preserved :
    ∃ coordinateEquiv : ZMod l.value ≃ ZMod l.value,
      CoordinateBalancedSquarePreserving (l := l) coordinateEquiv ∧
        ¬ ∀ j : ZMod l.value,
          representativeFullLabelWeightedSummand
              (l := l)
              (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
                (l := l) (1 : Real))
              (coordinateEquiv j) =
            representativeFullLabelWeightedSummand
              (l := l)
              (IUTStage1ZModCuspLabelLogVolumeCompatibility.constant
                (l := l) (1 : Real))
              j :=
  ⟨Equiv.neg (ZMod l.value),
    coordinateBalancedSquarePreserving_neg,
    not_representativeSummand_constant_one_preserved_neg⟩

theorem squareWeight_preserved_of_coordinateSquarePreserving
    (sourceProfile targetProfile : IUTStage1ZModSquareWeightProfile l)
    {coordinateEquiv : ZMod l.value ≃ ZMod l.value}
    (hcoord : CoordinateSquarePreserving (l := l) coordinateEquiv) :
    ∀ j : ZMod l.value,
      targetProfile.weight (coordinateEquiv j) =
        sourceProfile.weight j := by
  intro j
  rw [targetProfile.weight_eq_square_val, sourceProfile.weight_eq_square_val]
  exact hcoord j

theorem coordinateSquarePreserving_of_squareWeight_preserved
    (sourceProfile targetProfile : IUTStage1ZModSquareWeightProfile l)
    {coordinateEquiv : ZMod l.value ≃ ZMod l.value}
    (hweight :
      ∀ j : ZMod l.value,
        targetProfile.weight (coordinateEquiv j) =
          sourceProfile.weight j) :
    CoordinateSquarePreserving (l := l) coordinateEquiv := by
  intro j
  have h := hweight j
  rw [targetProfile.weight_eq_square_val, sourceProfile.weight_eq_square_val] at h
  exact h

theorem squareWeight_preserved_iff_coordinateSquarePreserving
    (sourceProfile targetProfile : IUTStage1ZModSquareWeightProfile l)
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value) :
    (∀ j : ZMod l.value,
      targetProfile.weight (coordinateEquiv j) =
        sourceProfile.weight j) ↔
      CoordinateSquarePreserving (l := l) coordinateEquiv := by
  constructor
  · exact coordinateSquarePreserving_of_squareWeight_preserved
      sourceProfile targetProfile
  · exact squareWeight_preserved_of_coordinateSquarePreserving
      sourceProfile targetProfile

theorem weightTotal_preserved_of_squareWeight_preserved
    (sourceProfile targetProfile : IUTStage1ZModSquareWeightProfile l)
    (coordinateEquiv : ZMod l.value ≃ ZMod l.value)
    (hweight :
      ∀ j : ZMod l.value,
        targetProfile.weight (coordinateEquiv j) =
          sourceProfile.weight j) :
    targetProfile.weightTotal = sourceProfile.weightTotal := by
  rw [targetProfile.weightTotal_eq_sum, sourceProfile.weightTotal_eq_sum]
  have hsum :
      Finset.univ.sum sourceProfile.weight =
        Finset.univ.sum targetProfile.weight :=
    Fintype.sum_equiv coordinateEquiv
      sourceProfile.weight targetProfile.weight
      (fun j => (hweight j).symm)
  exact hsum.symm

theorem weightTotal_preserved_of_coordinateSquarePreserving
    (sourceProfile targetProfile : IUTStage1ZModSquareWeightProfile l)
    {coordinateEquiv : ZMod l.value ≃ ZMod l.value}
    (hcoord : CoordinateSquarePreserving (l := l) coordinateEquiv) :
    targetProfile.weightTotal = sourceProfile.weightTotal :=
  weightTotal_preserved_of_squareWeight_preserved
    sourceProfile targetProfile coordinateEquiv
    (squareWeight_preserved_of_coordinateSquarePreserving
      sourceProfile targetProfile hcoord)

end IUTStage1ZModSquareWeightProfile
end Stage1
end Iut
