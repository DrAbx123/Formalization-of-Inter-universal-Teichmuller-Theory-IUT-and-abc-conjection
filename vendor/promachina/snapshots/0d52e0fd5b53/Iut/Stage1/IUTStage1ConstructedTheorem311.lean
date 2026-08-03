/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1HodgeArakelovPilots
import Iut.Stage1.IUTStage1Theorem311

/-!
Constructed finite Theorem 3.11 data from the canonical M2 pilots.

The choices in this file have two actual `ZMod l` translation coordinates and
one directed upper-semicontinuity level.  Thus `(Ind1)` and `(Ind2)` are
actions, while `(Ind3)` is deliberately a one-sided relation.  No action law,
quotient conclusion, possible-image witness, or log-volume comparison is an
input to the construction.
-/

namespace Iut
namespace Stage1

open scoped BigOperators

universe u

/--
A typed point of the finite multiradial log-theta procession.

The bad place and level are not changed by the equality indeterminacies.
`processionLabel` is the `(Ind1)` coordinate and `tensorLabel` is the `(Ind2)`
coordinate.
-/
structure IUTIIIProcessionChoice
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K) where
  badPlace : {v : NumberField.FinitePlace K // v ∈ theta.valuations.bad}
  processionLabel : ZMod theta.l.value
  tensorLabel : ZMod theta.l.value
  upperSemiLevel : Nat

namespace IUTIIIProcessionChoice

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

/-- The nonempty bad-place index supplies a canonical base procession choice. -/
noncomputable def canonicalBadPlace :
    {v : NumberField.FinitePlace K // v ∈ theta.valuations.bad} :=
  ⟨Classical.choose theta.badValuations_nonempty,
    Classical.choose_spec theta.badValuations_nonempty⟩

/-- The canonical zero-coordinate, zero-level procession choice. -/
noncomputable def base (theta : InitialThetaData Fmod F K) :
    IUTIIIProcessionChoice theta where
  badPlace := canonicalBadPlace
  processionLabel := 0
  tensorLabel := 0
  upperSemiLevel := 0

/-- Actual `(Ind1)` translation of the procession label. -/
def ind1Act
    (t : ZMod theta.l.value) (choice : IUTIIIProcessionChoice theta) :
    IUTIIIProcessionChoice theta :=
  { choice with
    processionLabel :=
      zmodLabelTranslate theta.l t choice.processionLabel }

/-- Actual `(Ind2)` translation of the local tensor label. -/
def ind2Act
    (t : ZMod theta.l.value) (choice : IUTIIIProcessionChoice theta) :
    IUTIIIProcessionChoice theta :=
  { choice with
    tensorLabel :=
      zmodLabelTranslate theta.l t choice.tensorLabel }

/-- Directed `(Ind3)` lift by a nonnegative upper-semi level. -/
def ind3Lift
    (n : Nat) (choice : IUTIIIProcessionChoice theta) :
    IUTIIIProcessionChoice theta :=
  { choice with upperSemiLevel := choice.upperSemiLevel + n }

@[simp]
theorem ind1Act_zero (choice : IUTIIIProcessionChoice theta) :
    ind1Act 0 choice = choice := by
  cases choice
  simp [ind1Act, zmodLabelTranslate_zero]

@[simp]
theorem ind1Act_add
    (g h : ZMod theta.l.value) (choice : IUTIIIProcessionChoice theta) :
    ind1Act (g + h) choice = ind1Act g (ind1Act h choice) := by
  cases choice
  simp [ind1Act, zmodLabelTranslate_add]

@[simp]
theorem ind2Act_zero (choice : IUTIIIProcessionChoice theta) :
    ind2Act 0 choice = choice := by
  cases choice
  simp [ind2Act, zmodLabelTranslate_zero]

@[simp]
theorem ind2Act_add
    (g h : ZMod theta.l.value) (choice : IUTIIIProcessionChoice theta) :
    ind2Act (g + h) choice = ind2Act g (ind2Act h choice) := by
  cases choice
  simp [ind2Act, zmodLabelTranslate_add]

@[simp]
theorem ind3Lift_zero (choice : IUTIIIProcessionChoice theta) :
    ind3Lift 0 choice = choice := by
  cases choice
  simp [ind3Lift]

@[simp]
theorem ind3Lift_add
    (m n : Nat) (choice : IUTIIIProcessionChoice theta) :
    ind3Lift (m + n) choice = ind3Lift n (ind3Lift m choice) := by
  cases choice
  simp only [ind3Lift, Nat.add_assoc]

/-- The orbit relation of the concrete `(Ind1)` action. -/
def Ind1Step
    (choice₁ choice₂ : IUTIIIProcessionChoice theta) : Prop :=
  ∃ t : ZMod theta.l.value, ind1Act t choice₁ = choice₂

/-- The orbit relation of the concrete `(Ind2)` action. -/
def Ind2Step
    (choice₁ choice₂ : IUTIIIProcessionChoice theta) : Prop :=
  ∃ t : ZMod theta.l.value, ind2Act t choice₁ = choice₂

/-- The directed reachability relation of the concrete `(Ind3)` lift. -/
def Ind3Step
    (choice₁ choice₂ : IUTIIIProcessionChoice theta) : Prop :=
  ∃ n : Nat, ind3Lift n choice₁ = choice₂

/-- Procession-normalized average evaluated on the translated M2 theta pilot. -/
noncomputable def processionAverage
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) : Real :=
  (Finset.univ.sum fun j : ZMod theta.l.value =>
    (data.gaussianEvaluation choice.badPlace.1 choice.badPlace.2).gaussianDegree
      (IUTStage1ZModCuspFullLabel.fromCoordinate theta.l
        (zmodLabelTranslate theta.l choice.processionLabel j))) /
    (theta.l.value : Real)

theorem processionAverage_eq_coordinateAverage
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) :
    processionAverage data choice =
      (data.coordinateAverage choice.badPlace.1 choice.badPlace.2).averageLogVolume :=
  data.coordinateAverage_translation_invariant
    choice.badPlace.1 choice.badPlace.2 choice.processionLabel

/-- The normalized volume together with the directed upper-semi correction. -/
noncomputable def logVolume
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) : Real :=
  processionAverage data choice + choice.upperSemiLevel

theorem ind1_preserves_logVolume
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    {choice₁ choice₂ : IUTIIIProcessionChoice theta}
    (hstep : Ind1Step choice₁ choice₂) :
    logVolume data choice₁ = logVolume data choice₂ := by
  rcases hstep with ⟨t, rfl⟩
  rw [logVolume, logVolume, processionAverage_eq_coordinateAverage,
    processionAverage_eq_coordinateAverage]
  rfl

theorem ind2_preserves_logVolume
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    {choice₁ choice₂ : IUTIIIProcessionChoice theta}
    (hstep : Ind2Step choice₁ choice₂) :
    logVolume data choice₁ = logVolume data choice₂ := by
  rcases hstep with ⟨t, rfl⟩
  rw [logVolume, logVolume, processionAverage_eq_coordinateAverage,
    processionAverage_eq_coordinateAverage]
  rfl

theorem ind3_logVolume_le
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    {choice₁ choice₂ : IUTIIIProcessionChoice theta}
    (hstep : Ind3Step choice₁ choice₂) :
    logVolume data choice₁ ≤ logVolume data choice₂ := by
  rcases hstep with ⟨n, rfl⟩
  rw [logVolume, logVolume, processionAverage_eq_coordinateAverage,
    processionAverage_eq_coordinateAverage]
  norm_num [ind3Lift]

/-- The existing typed core, now filled by constructed actions and proofs. -/
noncomputable def typedCore
    (data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    IUTStage1Theorem311TypedIndeterminacyCore
      (IUTIIIProcessionChoice theta) where
  logVolume := logVolume data
  ind1 :=
    { step := Ind1Step
      logVolume := logVolume data
      preserves_processionNormalizedLogVolume :=
        ind1_preserves_logVolume data }
  ind2 :=
    { step := Ind2Step
      logVolume := logVolume data
      preserves_processionNormalizedLogVolume :=
        ind2_preserves_logVolume data }
  ind3 :=
    { step := Ind3Step
      logVolume := logVolume data
      upper_semi_logVolume := ind3_logVolume_le data }
  ind1_logVolume_eq := rfl
  ind2_logVolume_eq := rfl
  ind3_logVolume_eq := rfl

/-- Value family represented by one procession choice. -/
noncomputable def pilotValue
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta)
    (j : ZMod theta.l.value) : Real :=
  (data.gaussianEvaluation choice.badPlace.1 choice.badPlace.2).gaussianDegree
      (IUTStage1ZModCuspFullLabel.fromCoordinate theta.l
        (zmodLabelTranslate theta.l choice.processionLabel j)) +
    choice.upperSemiLevel

/-- The finite possible image represented by one procession choice. -/
noncomputable def possibleImage
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) : Set Real :=
  Set.range (pilotValue data choice)

theorem possibleImage_nonempty
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) :
    (possibleImage data choice).Nonempty :=
  ⟨pilotValue data choice 0, ⟨0, rfl⟩⟩

theorem pilotValue_ind1Act
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (t : ZMod theta.l.value) (choice : IUTIIIProcessionChoice theta)
    (j : ZMod theta.l.value) :
    pilotValue data (ind1Act t choice) j =
      pilotValue data choice (zmodLabelTranslate theta.l t j) := by
  simp only [pilotValue, ind1Act, zmodLabelTranslate_eq_add]
  congr 3
  ac_rfl

theorem possibleImage_ind1Act
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (t : ZMod theta.l.value) (choice : IUTIIIProcessionChoice theta) :
    possibleImage data (ind1Act t choice) = possibleImage data choice := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact
      ⟨zmodLabelTranslate theta.l t j,
        (pilotValue_ind1Act data t choice j).symm⟩
  · rintro ⟨j, rfl⟩
    refine ⟨zmodLabelTranslate theta.l (-t) j, ?_⟩
    rw [pilotValue_ind1Act]
    simp [zmodLabelTranslate_eq_add]

theorem possibleImage_ind2Act
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (t : ZMod theta.l.value) (choice : IUTIIIProcessionChoice theta) :
    possibleImage data (ind2Act t choice) = possibleImage data choice := by
  rfl

theorem ind1_preserves_possibleImage
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    {choice₁ choice₂ : IUTIIIProcessionChoice theta}
    (hstep : Ind1Step choice₁ choice₂) :
    possibleImage data choice₁ = possibleImage data choice₂ := by
  rcases hstep with ⟨t, rfl⟩
  exact (possibleImage_ind1Act data t choice₁).symm

theorem ind2_preserves_possibleImage
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    {choice₁ choice₂ : IUTIIIProcessionChoice theta}
    (hstep : Ind2Step choice₁ choice₂) :
    possibleImage data choice₁ = possibleImage data choice₂ := by
  rcases hstep with ⟨t, rfl⟩
  exact (possibleImage_ind2Act data t choice₁).symm

theorem equalityRelation_preserves_badPlace_level
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    {choice₁ choice₂ : IUTIIIProcessionChoice theta}
    (hrel : (typedCore data).equalityQuotient.relation choice₁ choice₂) :
    choice₁.badPlace = choice₂.badPlace ∧
      choice₁.upperSemiLevel = choice₂.upperSemiLevel := by
  induction hrel with
  | refl choice =>
      exact ⟨rfl, rfl⟩
  | ind1 hstep =>
      rcases hstep with ⟨t, rfl⟩
      exact ⟨rfl, rfl⟩
  | ind2 hstep =>
      rcases hstep with ⟨t, rfl⟩
      exact ⟨rfl, rfl⟩
  | ind3 hstep =>
      exact False.elim hstep
  | symm _ ih =>
      exact ⟨ih.1.symm, ih.2.symm⟩
  | trans _ _ ih₁ ih₂ =>
      exact ⟨ih₁.1.trans ih₂.1, ih₁.2.trans ih₂.2⟩

theorem equalityRelation_iff_badPlace_level_eq
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    {choice₁ choice₂ : IUTIIIProcessionChoice theta} :
    (typedCore data).equalityQuotient.relation choice₁ choice₂ ↔
      choice₁.badPlace = choice₂.badPlace ∧
        choice₁.upperSemiLevel = choice₂.upperSemiLevel := by
  constructor
  · exact equalityRelation_preserves_badPlace_level data
  · intro hinvariants
    rcases choice₁ with ⟨place₁, procession₁, tensor₁, level₁⟩
    rcases choice₂ with ⟨place₂, procession₂, tensor₂, level₂⟩
    rcases hinvariants with ⟨rfl, rfl⟩
    apply IUTStage1GeneratedIndeterminacyRelation.trans
      (choice₂ :=
        ind1Act (procession₂ - procession₁)
          ⟨place₁, procession₁, tensor₁, level₁⟩)
    · apply IUTStage1GeneratedIndeterminacyRelation.ind1
      exact ⟨procession₂ - procession₁, rfl⟩
    · apply IUTStage1GeneratedIndeterminacyRelation.ind2
      refine ⟨tensor₂ - tensor₁, ?_⟩
      simp [ind1Act, ind2Act, zmodLabelTranslate_eq_add]

theorem equalityQuotient_no_level_collapse
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    {choice₁ choice₂ : IUTIIIProcessionChoice theta}
    (hlevel : choice₁.upperSemiLevel ≠ choice₂.upperSemiLevel) :
    (typedCore data).equalitySetoidQuotientMap choice₁ ≠
      (typedCore data).equalitySetoidQuotientMap choice₂ := by
  intro hquot
  exact hlevel
    (equalityRelation_preserves_badPlace_level data
      ((typedCore data).equalitySetoidQuotientMap_eq_iff.mp hquot)).2

theorem equalityRelation_preserves_possibleImage
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    {choice₁ choice₂ : IUTIIIProcessionChoice theta}
    (hrel : (typedCore data).equalityQuotient.relation choice₁ choice₂) :
    possibleImage data choice₁ = possibleImage data choice₂ := by
  induction hrel with
  | refl choice =>
      rfl
  | ind1 hstep =>
      exact ind1_preserves_possibleImage data hstep
  | ind2 hstep =>
      exact ind2_preserves_possibleImage data hstep
  | ind3 hstep =>
      exact False.elim hstep
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Possible images descend to the actual generated equality quotient. -/
noncomputable def quotientPossibleImage
    (data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    Quotient (typedCore data).equalitySetoid -> Set Real :=
  Quotient.lift (possibleImage data) fun _ _ =>
    equalityRelation_preserves_possibleImage data

theorem quotientPossibleImage_nonempty
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (orbit : Quotient (typedCore data).equalitySetoid) :
    (quotientPossibleImage data orbit).Nonempty := by
  refine Quotient.inductionOn orbit ?_
  intro choice
  exact possibleImage_nonempty data choice

end IUTIIIProcessionChoice

/--
The typed target of the vertical log-Kummer map.

Its coordinate is evaluated by the M2 Gaussian pilot after applying the
procession translation and upper-semi level of `choice`.
-/
structure IUTIIIVerticalLogKummerPoint
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : InitialThetaData Fmod F K}
    (_data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (_choice : IUTIIIProcessionChoice theta) where
  coordinate : ZMod theta.l.value
deriving DecidableEq

namespace IUTIIIVerticalLogKummerPoint

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}
variable {data : ToyIUTIIHodgeArakelovEvaluationData theta}
variable {choice : IUTIIIProcessionChoice theta}

/-- Coordinate equivalence for the finite vertical target. -/
def coordinateEquiv :
    IUTIIIVerticalLogKummerPoint data choice ≃ ZMod theta.l.value where
  toFun := coordinate
  invFun := fun j => ⟨j⟩
  left_inv := by intro point; cases point; rfl
  right_inv := by intro j; rfl

noncomputable instance instFintype :
    Fintype (IUTIIIVerticalLogKummerPoint data choice) :=
  Fintype.ofEquiv (ZMod theta.l.value) coordinateEquiv.symm

/-- The finite target carries its explicit discrete topology. -/
instance instTopologicalSpace :
    TopologicalSpace (IUTIIIVerticalLogKummerPoint data choice) :=
  ⊥

instance instDiscreteTopology :
    DiscreteTopology (IUTIIIVerticalLogKummerPoint data choice) :=
  ⟨rfl⟩

/-- Full theta label represented by a vertical log-Kummer point. -/
def fullLabel (point : IUTIIIVerticalLogKummerPoint data choice) :
    IUTStage1ZModCuspFullLabel theta.l :=
  IUTStage1ZModCuspFullLabel.fromCoordinate theta.l point.coordinate

/-- Evaluated log-volume represented by a vertical log-Kummer point. -/
noncomputable def logVolume
    (point : IUTIIIVerticalLogKummerPoint data choice) : Real :=
  IUTIIIProcessionChoice.pilotValue data choice point.coordinate

end IUTIIIVerticalLogKummerPoint

namespace IUTIIIVerticalLogKummer

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

/-- The actual bad-local pointed quotient carrier at a procession choice. -/
abbrev Domain (choice : IUTIIIProcessionChoice theta) :=
  ((theta.badLocalData.badLocalCType choice.badPlace.1 choice.badPlace.2)
    |>.thetaRootData.quotientZData.quotientZ.carrier)

/-- Evaluate a bad-local quotient-torsor point in the procession target. -/
noncomputable def map
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) :
    Domain choice -> IUTIIIVerticalLogKummerPoint data choice :=
  fun point =>
    ⟨(data.quotientCoordinateEquiv
      choice.badPlace.1 choice.badPlace.2).symm point⟩

/-- The graph of the constructed vertical log-Kummer map. -/
noncomputable def graph
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) :
    Set (Domain choice × IUTIIIVerticalLogKummerPoint data choice) :=
  { pair | map data choice pair.1 = pair.2 }

/-- The target image of the constructed vertical log-Kummer map. -/
noncomputable def image
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) :
    Set (IUTIIIVerticalLogKummerPoint data choice) :=
  Set.range (map data choice)

/-- The set of log-volumes realized by the vertical target. -/
noncomputable def logVolumeImage
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) : Set Real :=
  Set.range fun point : IUTIIIVerticalLogKummerPoint data choice =>
    point.logVolume

theorem map_coordinate
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta)
    (point : Domain choice) :
    (map data choice point).coordinate =
      (data.quotientCoordinateEquiv
        choice.badPlace.1 choice.badPlace.2).symm point :=
  rfl

theorem map_coordinate_of_coordinate
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta)
    (j : ZMod theta.l.value) :
    (map data choice
      (data.quotientCoordinateEquiv
        choice.badPlace.1 choice.badPlace.2 j)).coordinate = j := by
  simp [map]

theorem map_canonicalNonzeroLabel
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) :
    (map data choice
      ((theta.badLocalData.badLocalCType
        choice.badPlace.1 choice.badPlace.2).thetaRootData.quotientZData
          |>.canonicalNonzeroLabelZ.1)).coordinate =
      ((theta.badLocalData.badLocalCType
        choice.badPlace.1 choice.badPlace.2).thetaRootData.quotientZData
          |>.canonicalCoordinateZ) := by
  rw [map_coordinate]
  rw [← data.quotientCoordinateEquiv_canonical
    choice.badPlace.1 choice.badPlace.2]
  exact Equiv.symm_apply_apply _ _

theorem map_injective
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) :
    Function.Injective (map data choice) := by
  intro point₁ point₂ hpoint
  apply
    (data.quotientCoordinateEquiv
      choice.badPlace.1 choice.badPlace.2).symm.injective
  exact congrArg IUTIIIVerticalLogKummerPoint.coordinate hpoint

theorem map_surjective
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) :
    Function.Surjective (map data choice) := by
  intro target
  refine
    ⟨data.quotientCoordinateEquiv
      choice.badPlace.1 choice.badPlace.2 target.coordinate, ?_⟩
  cases target
  simp [map]

theorem graph_iff
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta)
    (source : Domain choice)
    (target : IUTIIIVerticalLogKummerPoint data choice) :
    (source, target) ∈ graph data choice ↔ map data choice source = target :=
  Iff.rfl

theorem graph_left_total
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta)
    (source : Domain choice) :
    ∃ target, (source, target) ∈ graph data choice :=
  ⟨map data choice source, rfl⟩

theorem graph_right_unique
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta)
    {source : Domain choice}
    {target₁ target₂ : IUTIIIVerticalLogKummerPoint data choice}
    (h₁ : (source, target₁) ∈ graph data choice)
    (h₂ : (source, target₂) ∈ graph data choice) :
    target₁ = target₂ :=
  h₁.symm.trans h₂

theorem image_eq_univ
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) :
    image data choice = Set.univ := by
  ext target
  simp only [image, Set.mem_range, Set.mem_univ, iff_true]
  exact map_surjective data choice target

theorem image_isOpen
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) :
    IsOpen (image data choice) := by
  rw [image_eq_univ]
  exact isOpen_univ

theorem image_isCompact
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) :
    IsCompact (image data choice) :=
  Set.Finite.isCompact (Set.toFinite (image data choice))

theorem logVolumeImage_eq_possibleImage
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) :
    logVolumeImage data choice =
      IUTIIIProcessionChoice.possibleImage data choice := by
  ext value
  constructor
  · rintro ⟨point, rfl⟩
    exact ⟨point.coordinate, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨⟨j⟩, rfl⟩

/--
All vertical map, graph, image, exactness, and compact-open laws needed by the
finite Theorem 3.11 route.
-/
structure CorrespondenceLaws
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) : Prop where
  graph_exact :
    ∀ source target,
      (source, target) ∈ graph data choice ↔ map data choice source = target
  left_total :
    ∀ source, ∃ target, (source, target) ∈ graph data choice
  right_unique :
    ∀ {source target₁ target₂},
      (source, target₁) ∈ graph data choice ->
      (source, target₂) ∈ graph data choice ->
      target₁ = target₂
  map_bijective : Function.Bijective (map data choice)
  image_exact : image data choice = Set.range (map data choice)
  image_compact : IsCompact (image data choice)
  image_open : IsOpen (image data choice)
  realized_logVolumes :
    logVolumeImage data choice =
      IUTIIIProcessionChoice.possibleImage data choice

theorem correspondenceLaws
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (choice : IUTIIIProcessionChoice theta) :
    CorrespondenceLaws data choice where
  graph_exact := graph_iff data choice
  left_total := graph_left_total data choice
  right_unique := by
    intro source target₁ target₂ h₁ h₂
    exact graph_right_unique data choice h₁ h₂
  map_bijective := ⟨map_injective data choice, map_surjective data choice⟩
  image_exact := rfl
  image_compact := image_isCompact data choice
  image_open := image_isOpen data choice
  realized_logVolumes := logVolumeImage_eq_possibleImage data choice

end IUTIIIVerticalLogKummer

namespace IUTIIIProcessionChoice

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

theorem pilotValue_ind3Lift_le
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (n : Nat) (choice : IUTIIIProcessionChoice theta)
    (j : ZMod theta.l.value) :
    pilotValue data choice j ≤ pilotValue data (ind3Lift n choice) j := by
  simp only [pilotValue, ind3Lift]
  norm_num

theorem ind3_pointwise_upperSemi
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    {choice₁ choice₂ : IUTIIIProcessionChoice theta}
    (hstep : Ind3Step choice₁ choice₂) :
    ∀ j, pilotValue data choice₁ j ≤ pilotValue data choice₂ j := by
  rcases hstep with ⟨n, rfl⟩
  exact pilotValue_ind3Lift_le data n choice₁

end IUTIIIProcessionChoice

/--
The horizontal IPL/SHE/APT data, tied to the M1 histories and the M2 pilot
evaluation.  In particular, the theta link does not identify the histories.
-/
structure IUTIIIHorizontalCompatibility
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : InitialThetaData Fmod F K}
    (data : ToyIUTIIHodgeArakelovEvaluationData theta) where
  inputPrimeStrip :
    ThetaPrimeStrip theta (.zero : ThetaArithmeticHistory theta) .plusMinus
  outputPrimeStrip :
    ThetaPrimeStrip theta (.one : ThetaArithmeticHistory theta) .theta
  thetaLink :
    CategoryTheory.Equivalence
      (data.realization.thetaFPrimeStrip .zero)
      (data.realization.moduliFPrimeStrip .one)
  plusMinusNFGluing :
    ∀ history,
      CategoryTheory.Equivalence
        (data.realization.plusMinusEllTheater history)
        (data.realization.nfTheater history)
  zeroColumnSourceGluing :
    data.hodgeTheaterSource.zeroColumn.plusMinusEll.thetaPMBridge.codomain =
      data.hodgeTheaterSource.zeroColumn.nf.thetaNFBridge.codomain
  oneColumnSourceGluing :
    data.hodgeTheaterSource.oneColumn.plusMinusEll.thetaPMBridge.codomain =
      data.hodgeTheaterSource.oneColumn.nf.thetaNFBridge.codomain
  input_column : inputPrimeStrip.owner.column = .zero
  output_column : outputPrimeStrip.owner.column = .one
  histories_not_identified :
    (ThetaArithmeticHistory.zero : ThetaArithmeticHistory theta) ≠ .one
  she_evaluation :
    ∀ choice : IUTIIIProcessionChoice theta,
      (data.thetaValueEvaluationSource
        choice.badPlace.1 choice.badPlace.2).toGaussianMonoidDegreeEvaluation =
        data.gaussianEvaluation choice.badPlace.1 choice.badPlace.2
  apt_ind1_possibleImage :
    ∀ {choice₁ choice₂ : IUTIIIProcessionChoice theta},
      IUTIIIProcessionChoice.Ind1Step choice₁ choice₂ ->
        IUTIIIProcessionChoice.possibleImage data choice₁ =
          IUTIIIProcessionChoice.possibleImage data choice₂
  apt_ind2_possibleImage :
    ∀ {choice₁ choice₂ : IUTIIIProcessionChoice theta},
      IUTIIIProcessionChoice.Ind2Step choice₁ choice₂ ->
        IUTIIIProcessionChoice.possibleImage data choice₁ =
          IUTIIIProcessionChoice.possibleImage data choice₂
  apt_ind3_upperSemi :
    ∀ {choice₁ choice₂ : IUTIIIProcessionChoice theta},
      IUTIIIProcessionChoice.Ind3Step choice₁ choice₂ ->
        ∀ j,
          IUTIIIProcessionChoice.pilotValue data choice₁ j ≤
            IUTIIIProcessionChoice.pilotValue data choice₂ j

namespace IUTIIIHorizontalCompatibility

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

/-- Construct horizontal compatibility without identifying zero/one histories. -/
noncomputable def ofM2
    (data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    IUTIIIHorizontalCompatibility data where
  inputPrimeStrip := data.qPilot.primeStrip
  outputPrimeStrip := data.thetaPilot.primeStrip
  thetaLink := data.realization.zeroToOneThetaLink
  plusMinusNFGluing := data.realization.plusMinusEllNFGluing
  zeroColumnSourceGluing :=
    data.hodgeTheaterSource.zeroColumn_primeStrip_compatible
  oneColumnSourceGluing :=
    data.hodgeTheaterSource.oneColumn_primeStrip_compatible
  input_column := data.qPilot.primeStrip_column
  output_column := data.thetaPilot.primeStrip_column
  histories_not_identified := data.histories_not_identified
  she_evaluation := by
    intro choice
    exact data.thetaValueEvaluationSource_gaussian_eq
      choice.badPlace.1 choice.badPlace.2
  apt_ind1_possibleImage :=
    IUTIIIProcessionChoice.ind1_preserves_possibleImage data
  apt_ind2_possibleImage :=
    IUTIIIProcessionChoice.ind2_preserves_possibleImage data
  apt_ind3_upperSemi :=
    IUTIIIProcessionChoice.ind3_pointwise_upperSemi data

end IUTIIIHorizontalCompatibility

/-- The canonical selected point of the constructed multiradial procession. -/
structure IUTIIIMultiradialProcession
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : InitialThetaData Fmod F K}
    (_data : ToyIUTIIHodgeArakelovEvaluationData theta) where
  selectedChoice : IUTIIIProcessionChoice theta
  selectedChoice_eq_base :
    selectedChoice = IUTIIIProcessionChoice.base theta

namespace IUTIIIMultiradialProcession

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

noncomputable def ofM2
    (data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    IUTIIIMultiradialProcession data where
  selectedChoice := IUTIIIProcessionChoice.base theta
  selectedChoice_eq_base := rfl

end IUTIIIMultiradialProcession

/--
Canonical M3 source.  Its only stored datum is constrained to be exactly the
canonical M2 construction; all procession, quotient, vertical, and horizontal
objects are computed projections.
-/
structure IUTIIITheorem311ConstructedSource
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K) where
  m2 : ToyIUTIIHodgeArakelovEvaluationData theta
  m2_eq_canonical :
    m2 = ToyIUTIIHodgeArakelovEvaluationData.ofInitialThetaData theta

namespace IUTIIITheorem311ConstructedSource

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

/-- Construct M3 directly from initial theta data. -/
noncomputable def ofInitialThetaData
    (theta : InitialThetaData Fmod F K) :
    IUTIIITheorem311ConstructedSource theta where
  m2 := ToyIUTIIHodgeArakelovEvaluationData.ofInitialThetaData theta
  m2_eq_canonical := rfl

/-- The constructed multiradial procession. -/
noncomputable def procession
    (source : IUTIIITheorem311ConstructedSource theta) :
    IUTIIIMultiradialProcession source.m2 :=
  IUTIIIMultiradialProcession.ofM2 source.m2

/-- Actual typed Ind1/Ind2 actions and one-sided Ind3 relation. -/
noncomputable def indeterminacyCore
    (source : IUTIIITheorem311ConstructedSource theta) :
    IUTStage1Theorem311TypedIndeterminacyCore
      (IUTIIIProcessionChoice theta) :=
  IUTIIIProcessionChoice.typedCore source.m2

/-- Constructed horizontal IPL/SHE/APT compatibility. -/
noncomputable def horizontalCompatibility
    (source : IUTIIITheorem311ConstructedSource theta) :
    IUTIIIHorizontalCompatibility source.m2 :=
  IUTIIIHorizontalCompatibility.ofM2 source.m2

/-- Constructed vertical log-Kummer correspondence at every procession point. -/
theorem verticalLogKummerCorrespondence
    (source : IUTIIITheorem311ConstructedSource theta)
    (choice : IUTIIIProcessionChoice theta) :
    IUTIIIVerticalLogKummer.CorrespondenceLaws source.m2 choice :=
  IUTIIIVerticalLogKummer.correspondenceLaws source.m2 choice

/-- Every quotient possible image in the canonical M3 source is nonempty. -/
theorem quotientPossibleImage_nonempty
    (source : IUTIIITheorem311ConstructedSource theta)
    (orbit :
      Quotient (IUTIIIProcessionChoice.typedCore source.m2).equalitySetoid) :
    (IUTIIIProcessionChoice.quotientPossibleImage source.m2 orbit).Nonempty :=
  IUTIIIProcessionChoice.quotientPossibleImage_nonempty source.m2 orbit

end IUTIIITheorem311ConstructedSource

end Stage1
end Iut
