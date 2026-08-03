/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1Gaussian
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Toy degree model for IUT II pilots

This file retains the finite `ZMod l`/real-degree experiment used by Stage 1.
It computes the square-weight profile expected after Hodge--Arakelov
evaluation, but it does not construct the mono-theta environments, cohomology
classes, Gaussian monoids, or Frobenioids of IUT II.  Every declaration that
could otherwise be confused with the paper-level construction is prefixed
`Toy`.
-/

namespace Iut
namespace Stage1

open scoped BigOperators
open IUTStage1ZModSquareWeightProfile

universe u v

/-- Toy q-pilot carrying only the typed zero-column strip and numerical q-order. -/
structure ToyIUTIIQPilot
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K) where
  primeStrip :
    ThetaPrimeStrip theta (.zero : ThetaArithmeticHistory theta) .plusMinus

namespace ToyIUTIIQPilot

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

/-- Construct the q-pilot directly from the canonical M1 input strip. -/
def ofInitialThetaData (theta : InitialThetaData Fmod F K) :
    ToyIUTIIQPilot theta where
  primeStrip :=
    (Stage1HodgeTheaterSource.ofInitialThetaData theta).inputPrimeStrip

/-- The bad-place q-parameter order represented by the q-pilot. -/
noncomputable def qParameterOrder
    (pilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) : ℕ :=
  pilot.primeStrip.qParameterOrder v hv

/-- The positive degree/log-volume magnitude of the local q-pilot. -/
noncomputable def localLogVolume
    (pilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) : ℝ :=
  pilot.qParameterOrder v hv

/-- The signed q-pilot reading used downstream is the negative magnitude. -/
noncomputable def signedLocalLogVolume
    (pilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) : ℝ :=
  -pilot.localLogVolume v hv

theorem qParameterOrder_pos
    (pilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    0 < pilot.qParameterOrder v hv :=
  pilot.primeStrip.qParameterOrder_pos v hv

theorem qParameterOrder_coprime_l
    (pilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    Nat.Coprime (pilot.qParameterOrder v hv) theta.l.value :=
  pilot.primeStrip.qParameterOrder_coprime_l v hv

theorem localLogVolume_pos
    (pilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    0 < pilot.localLogVolume v hv := by
  change (0 : ℝ) < (pilot.qParameterOrder v hv : ℝ)
  exact_mod_cast pilot.qParameterOrder_pos v hv

theorem signedLocalLogVolume_neg
    (pilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    pilot.signedLocalLogVolume v hv < 0 :=
  neg_lt_zero.mpr (pilot.localLogVolume_pos v hv)

@[simp]
theorem primeStrip_column (pilot : ToyIUTIIQPilot theta) :
    pilot.primeStrip.owner.column = .zero :=
  rfl

end ToyIUTIIQPilot

/-- Toy theta-pilot carrying only the typed one-column strip and square-weight degrees. -/
structure ToyIUTIIThetaPilot
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K) where
  primeStrip :
    ThetaPrimeStrip theta (.one : ThetaArithmeticHistory theta) .theta

namespace ToyIUTIIThetaPilot

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

/-- Construct the theta-pilot directly from the canonical M1 output strip. -/
def ofInitialThetaData (theta : InitialThetaData Fmod F K) :
    ToyIUTIIThetaPilot theta where
  primeStrip :=
    (Stage1HodgeTheaterSource.ofInitialThetaData theta).outputPrimeStrip

/-- Hodge--Arakelov degree of a full theta label at a bad place. -/
noncomputable def fullLabelLogVolume
    (_pilot : ToyIUTIIThetaPilot theta) (qPilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad)
    (label : IUTStage1ZModCuspFullLabel theta.l) : ℝ :=
  IUTStage1ZModSquareWeightProfile.thetaExponentOnAbsLabel label *
    qPilot.localLogVolume v hv

/-- Hodge--Arakelov degree at the concrete coordinate `j : ZMod l`. -/
noncomputable def coordinateLogVolume
    (pilot : ToyIUTIIThetaPilot theta) (qPilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad)
    (j : ZMod theta.l.value) : ℝ :=
  pilot.fullLabelLogVolume qPilot v hv
    (IUTStage1ZModCuspFullLabel.fromCoordinate theta.l j)

/-- The constructed Gaussian degree evaluation `q -> (q^{j^2})_j`. -/
noncomputable def gaussianEvaluation
    (pilot : ToyIUTIIThetaPilot theta) (qPilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    IUTStage1ZModSquareWeightProfile.GaussianMonoidDegreeEvaluation theta.l where
  environmentDegree := qPilot.localLogVolume v hv
  gaussianDegree := pilot.fullLabelLogVolume qPilot v hv
  gaussianDegree_eq_eval := by
    intro label
    rfl

theorem coordinateLogVolume_eq_balancedSquareWeight
    (pilot : ToyIUTIIThetaPilot theta) (qPilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad)
    (j : ZMod theta.l.value) :
    pilot.coordinateLogVolume qPilot v hv j =
      balancedSquareWeight (l := theta.l) j * qPilot.localLogVolume v hv := by
  rw [coordinateLogVolume, fullLabelLogVolume,
    thetaExponentOnAbsLabel_fromCoordinate]

theorem coordinateLogVolume_neg_eq
    (pilot : ToyIUTIIThetaPilot theta) (qPilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad)
    (j : ZMod theta.l.value) :
    pilot.coordinateLogVolume qPilot v hv (-j) =
      pilot.coordinateLogVolume qPilot v hv j := by
  rw [pilot.coordinateLogVolume_eq_balancedSquareWeight,
    pilot.coordinateLogVolume_eq_balancedSquareWeight,
    balancedSquareWeight_neg_eq]

theorem coordinateLogVolume_zero
    (pilot : ToyIUTIIThetaPilot theta) (qPilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    pilot.coordinateLogVolume qPilot v hv 0 = 0 := by
  change
    (pilot.gaussianEvaluation qPilot v hv).gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate theta.l 0) = 0
  rw [IUTStage1ZModCuspFullLabel.fromCoordinate_zero]
  exact (pilot.gaussianEvaluation qPilot v hv).gaussianDegree_zero

theorem coordinateLogVolume_one
    (pilot : ToyIUTIIThetaPilot theta) (qPilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    pilot.coordinateLogVolume qPilot v hv 1 =
      qPilot.localLogVolume v hv :=
  (pilot.gaussianEvaluation qPilot v hv).gaussianDegree_one

theorem coordinateLogVolume_nonnegative
    (pilot : ToyIUTIIThetaPilot theta) (qPilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad)
    (j : ZMod theta.l.value) :
    0 ≤ pilot.coordinateLogVolume qPilot v hv j := by
  rw [pilot.coordinateLogVolume_eq_balancedSquareWeight]
  exact mul_nonneg (balancedSquareWeight_nonnegative j)
    (le_of_lt (qPilot.localLogVolume_pos v hv))

theorem coordinateLogVolume_one_pos
    (pilot : ToyIUTIIThetaPilot theta) (qPilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    0 < pilot.coordinateLogVolume qPilot v hv 1 := by
  rw [pilot.coordinateLogVolume_one]
  exact qPilot.localLogVolume_pos v hv

@[simp]
theorem primeStrip_column (pilot : ToyIUTIIThetaPilot theta) :
    pilot.primeStrip.owner.column = .one :=
  rfl

end ToyIUTIIThetaPilot

/--
An object of the toy bad-local Gaussian degree preorder.

This is not a Gaussian Frobenioid: it retains only a finite label and a real
degree.
-/
structure ToyIUTIIGaussianFrobenioidObject
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) where
  label : ULift.{u} (IUTStage1ZModCuspFullLabel theta.l)
  logDegree : ℝ

namespace ToyIUTIIGaussianFrobenioidObject

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

instance (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    Preorder (ToyIUTIIGaussianFrobenioidObject theta v hv) where
  le source target :=
    source.label.down = target.label.down ∧ source.logDegree ≤ target.logDegree
  le_refl source := ⟨rfl, le_rfl⟩
  le_trans source middle target hsm hmt :=
    ⟨hsm.1.trans hmt.1, hsm.2.trans hmt.2⟩

/-- The Gaussian Frobenioid degree category at a bad place. -/
def category
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    CategoryTheory.Cat.{u, u} :=
  CategoryTheory.Cat.of (ToyIUTIIGaussianFrobenioidObject theta v hv)

/-- The object produced by Hodge--Arakelov evaluation at one full label. -/
noncomputable def evaluated
    (thetaPilot : ToyIUTIIThetaPilot theta) (qPilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad)
    (label : IUTStage1ZModCuspFullLabel theta.l) :
    ToyIUTIIGaussianFrobenioidObject theta v hv where
  label := ULift.up label
  logDegree := thetaPilot.fullLabelLogVolume qPilot v hv label

@[simp]
theorem evaluated_logDegree
    (thetaPilot : ToyIUTIIThetaPilot theta) (qPilot : ToyIUTIIQPilot theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad)
    (label : IUTStage1ZModCuspFullLabel theta.l) :
    (evaluated thetaPilot qPilot v hv label).logDegree =
      thetaPilot.fullLabelLogVolume qPilot v hv label :=
  rfl

end ToyIUTIIGaussianFrobenioidObject

/-- Aggregate data for the toy M2 degree calculation. -/
structure ToyIUTIIHodgeArakelovEvaluationData
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K) where
  realization :
    ToyIUTIHodgeTheaterRealization
      (Stage1HodgeTheaterSource.ofInitialThetaData theta)
  qPilot : ToyIUTIIQPilot theta
  thetaPilot : ToyIUTIIThetaPilot theta

namespace ToyIUTIIHodgeArakelovEvaluationData

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

/-- Construct the complete M2 source from initial theta data. -/
def ofInitialThetaData (theta : InitialThetaData Fmod F K) :
    ToyIUTIIHodgeArakelovEvaluationData theta where
  realization :=
    ToyIUTIHodgeTheaterRealization.ofStage1HodgeTheaterSource
      (Stage1HodgeTheaterSource.ofInitialThetaData theta)
  qPilot := ToyIUTIIQPilot.ofInitialThetaData theta
  thetaPilot := ToyIUTIIThetaPilot.ofInitialThetaData theta

/-- The canonical typed Hodge theater underlying the evaluation. -/
def hodgeTheaterSource (_data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    Stage1HodgeTheaterSource theta :=
  Stage1HodgeTheaterSource.ofInitialThetaData theta

/-- The actual bad-local theta-root/cusp source read from initial theta data. -/
noncomputable def thetaRootSource
    (_data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    IUTStage1ThetaRootCuspLabelSourcePackage theta.l
      (theta.badLocalData.localX v hv.1)
      (theta.badLocalData.localC v hv.1) :=
  IUTStage1ThetaRootCuspLabelSourcePackage.ofBadLocalOrbicurveTypeData
    (theta.badLocalData.badLocalCType v hv)

/--
The `ZMod l` coordinate equivalence supplied by the actual bad-local quotient
torsor, without identifying its carrier definitionally with `ZMod l`.
-/
noncomputable def quotientCoordinateEquiv
    (_data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    ZMod theta.l.value ≃
      ((theta.badLocalData.badLocalCType v hv).thetaRootData
        |>.quotientZData.quotientZ.carrier) :=
  let zData :=
    (theta.badLocalData.badLocalCType v hv).thetaRootData.quotientZData
  zData.additiveTorsorZ.orbitEquiv zData.quotientZ.zero

theorem quotientCoordinateEquiv_canonical
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    data.quotientCoordinateEquiv v hv
        (((theta.badLocalData.badLocalCType v hv).thetaRootData
          |>.quotientZData.canonicalCoordinateZ)) =
      ((theta.badLocalData.badLocalCType v hv).thetaRootData
        |>.quotientZData.canonicalNonzeroLabelZ.1) := by
  change
    ((theta.badLocalData.badLocalCType v hv).thetaRootData.quotientZData
      |>.additiveTorsorZ.vadd
        ((theta.badLocalData.badLocalCType v hv).thetaRootData
          |>.quotientZData.canonicalCoordinateZ)
        ((theta.badLocalData.badLocalCType v hv).thetaRootData
          |>.quotientZData.quotientZ.zero)) =
      ((theta.badLocalData.badLocalCType v hv).thetaRootData
        |>.quotientZData.canonicalNonzeroLabelZ.1)
  exact
    ((theta.badLocalData.badLocalCType v hv).thetaRootData.quotientZData
      |>.canonicalLabelZ_eq_translate).symm

/-- The canonical finite label and sign-class model used by the M2 source. -/
def labelSignModel
    (_data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    IUTStage1FLZModCuspLabelClassModel theta.l :=
  IUTStage1FLZModCuspLabelClassModel.zmod theta.l

/-- The zero/nonzero full label produced by a concrete `ZMod l` coordinate. -/
def fullLabel
    (_data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (j : ZMod theta.l.value) :
    IUTStage1ZModCuspFullLabel theta.l :=
  IUTStage1ZModCuspFullLabel.fromCoordinate theta.l j

/-- The sign class of a nonzero concrete coordinate. -/
def signClass
    (_data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (j : ZMod theta.l.value) (hj : j ≠ 0) :
    (zmodSignAction theta.l).SignLabelQuotient :=
  zmodSignLabelFromCoordinate theta.l j hj

/-- The absolute square weight governing Hodge--Arakelov theta evaluation. -/
noncomputable def squareWeight
    (_data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (j : ZMod theta.l.value) : ℝ :=
  balancedSquareWeight (l := theta.l) j

theorem squareWeight_nonnegative
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (j : ZMod theta.l.value) :
    0 ≤ data.squareWeight j :=
  balancedSquareWeight_nonnegative j

theorem squareWeight_sign_invariant
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (j : ZMod theta.l.value) :
    data.squareWeight (-j) = data.squareWeight j :=
  balancedSquareWeight_neg_eq j

theorem signClass_neg_eq
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (j : ZMod theta.l.value) (hj : j ≠ 0) :
    data.signClass (-j) (zmod_neg_ne_zero_of_ne_zero theta.l hj) =
      data.signClass j hj :=
  zmodSignLabelFromCoordinate_neg_eq theta.l j hj

/-- The constructed source-facing Hodge--Arakelov theta-value packet. -/
noncomputable def thetaValueEvaluationSource
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    IUTStage1HodgeArakelovThetaValueEvaluationSource theta.l
      (theta.badLocalData.localX v hv.1)
      (theta.badLocalData.localC v hv.1) where
  thetaRootSource := data.thetaRootSource v hv
  thetaMonoidDegree := data.qPilot.localLogVolume v hv

/-- The constructed Gaussian evaluation at a bad place. -/
noncomputable def gaussianEvaluation
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    IUTStage1ZModSquareWeightProfile.GaussianMonoidDegreeEvaluation theta.l :=
  data.thetaPilot.gaussianEvaluation data.qPilot v hv

theorem thetaValueEvaluationSource_gaussian_eq
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    (data.thetaValueEvaluationSource v hv).toGaussianMonoidDegreeEvaluation =
      data.gaussianEvaluation v hv := by
  rfl

/-- The constructed Gaussian Frobenioid category at a bad place. -/
def gaussianFrobenioid
    (_data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    CategoryTheory.Cat.{u, u} :=
  ToyIUTIIGaussianFrobenioidObject.category v hv

/-- The unweighted average over all concrete `ZMod l` coordinates. -/
noncomputable def coordinateAverage
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    IUTStage1LabelAveragedProcessionLogVolume (ZMod theta.l.value) :=
  (data.gaussianEvaluation v hv).coordinateAveragedLogVolume

/-- The canonical representative-square-weighted pilot average. -/
noncomputable def weightedPilotAverage
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    IUTStage1WeightedLabelAveragedProcessionLogVolume (ZMod theta.l.value) :=
  (IUTStage1ZModSquareWeightProfile.canonicalSquareWeights theta.l).toWeighted
    (data.coordinateAverage v hv)

/-- Average over the sign orbit `{j,-j}`. -/
noncomputable def signOrbitAverage
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad)
    (j : ZMod theta.l.value) : ℝ :=
  (data.thetaPilot.coordinateLogVolume data.qPilot v hv j +
    data.thetaPilot.coordinateLogVolume data.qPilot v hv (-j)) / 2

theorem signOrbitAverage_eq
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad)
    (j : ZMod theta.l.value) :
    data.signOrbitAverage v hv j =
      data.thetaPilot.coordinateLogVolume data.qPilot v hv j := by
  rw [signOrbitAverage, data.thetaPilot.coordinateLogVolume_neg_eq]
  ring

theorem coordinateAverage_translation_invariant
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad)
    (t : ZMod theta.l.value) :
    ((Finset.univ.sum fun j : ZMod theta.l.value =>
      (data.gaussianEvaluation v hv).gaussianDegree
        (IUTStage1ZModCuspFullLabel.fromCoordinate theta.l
          (zmodLabelTranslate theta.l t j))) / (theta.l.value : ℝ)) =
      (data.coordinateAverage v hv).averageLogVolume :=
  (data.gaussianEvaluation v hv)
    |>.coordinateAveragedLogVolume_average_translation_eq t

theorem weightedPilotAverage_normalization
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    (data.weightedPilotAverage v hv).weightedAverageLogVolume =
      (Finset.univ.sum fun j : ZMod theta.l.value =>
        (data.weightedPilotAverage v hv).weight j *
          (data.weightedPilotAverage v hv).normalizedLogVolume j) /
        (data.weightedPilotAverage v hv).weightTotal :=
  (data.weightedPilotAverage v hv).weightedAverage_eq_formula

theorem qPilot_positive
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    0 < data.qPilot.localLogVolume v hv :=
  data.qPilot.localLogVolume_pos v hv

theorem thetaPilot_one_normalized
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    data.thetaPilot.coordinateLogVolume data.qPilot v hv 1 =
      data.qPilot.localLogVolume v hv :=
  data.thetaPilot.coordinateLogVolume_one data.qPilot v hv

theorem thetaPilot_sign_invariant
    (data : ToyIUTIIHodgeArakelovEvaluationData theta)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad)
    (j : ZMod theta.l.value) :
    data.thetaPilot.coordinateLogVolume data.qPilot v hv (-j) =
      data.thetaPilot.coordinateLogVolume data.qPilot v hv j :=
  data.thetaPilot.coordinateLogVolume_neg_eq data.qPilot v hv j

theorem histories_not_identified
    (data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    (ThetaArithmeticHistory.zero : ThetaArithmeticHistory theta) ≠ .one :=
  data.hodgeTheaterSource.histories_not_identified

/-- Explicit legacy projection for old q-pilot identifier fields. -/
def legacyQPilotId (data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    PilotObjectId :=
  { label :=
      "q-pilot:" ++ data.qPilot.primeStrip.globalOrbicurve.label }

/-- Explicit legacy projection for old theta-pilot identifier fields. -/
def legacyThetaPilotId (data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    PilotObjectId :=
  { label :=
      "Theta-pilot:" ++ data.thetaPilot.primeStrip.globalOrbicurve.label }

/-- Explicit legacy projection for the old q-pilot log-volume identifier. -/
def legacyQPilotLogVolumeId
    (data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    QPilotLogVolumeId :=
  { label :=
      "q-pilot-log-volume:" ++
        data.qPilot.primeStrip.globalOrbicurve.label }

end ToyIUTIIHodgeArakelovEvaluationData

namespace IUTStage1SourceLabels

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

/-- Replace only the legacy pilot labels by projections of the typed M2 source. -/
def withConcretePilots
    (labels : IUTStage1SourceLabels)
    (data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    IUTStage1SourceLabels :=
  { labels with
    thetaPilot := data.legacyThetaPilotId
    qPilot := data.legacyQPilotId
    qPilotLogVolume := data.legacyQPilotLogVolumeId }

end IUTStage1SourceLabels

namespace IUTStage1SourcePackage

variable {source target : RealLineCopy.Copy} {index : Type v}
variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

/--
Legacy Stage 1 package view whose pilot identifiers are generated by M2.

The pre-ledger and all non-pilot labels are preserved.
-/
def withConcretePilots
    (package : IUTStage1SourcePackage source target index)
    (data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    IUTStage1SourcePackage source target index where
  labels := package.labels.withConcretePilots data
  preLedger := package.preLedger
  input_eq := package.input_eq
  multiradialOutput_eq := package.multiradialOutput_eq
  logVolumeComparison_eq := package.logVolumeComparison_eq

@[simp]
theorem withConcretePilots_thetaPilot
    (package : IUTStage1SourcePackage source target index)
    (data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    (package.withConcretePilots data).thetaPilot = data.legacyThetaPilotId :=
  rfl

@[simp]
theorem withConcretePilots_qPilot
    (package : IUTStage1SourcePackage source target index)
    (data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    (package.withConcretePilots data).qPilot = data.legacyQPilotId :=
  rfl

@[simp]
theorem withConcretePilots_qPilotLogVolume
    (package : IUTStage1SourcePackage source target index)
    (data : ToyIUTIIHodgeArakelovEvaluationData theta) :
    (package.withConcretePilots data).qPilotLogVolume =
      data.legacyQPilotLogVolumeId :=
  rfl

/-- Canonical legacy package projection generated from initial theta data. -/
def withInitialThetaPilots
    (package : IUTStage1SourcePackage source target index)
    (theta : InitialThetaData Fmod F K) :
    IUTStage1SourcePackage source target index :=
  package.withConcretePilots
    (ToyIUTIIHodgeArakelovEvaluationData.ofInitialThetaData theta)

@[simp]
theorem withInitialThetaPilots_thetaPilot
    (package : IUTStage1SourcePackage source target index)
    (theta : InitialThetaData Fmod F K) :
    (package.withInitialThetaPilots theta).thetaPilot =
      ToyIUTIIHodgeArakelovEvaluationData.legacyThetaPilotId
        (ToyIUTIIHodgeArakelovEvaluationData.ofInitialThetaData theta) :=
  rfl

@[simp]
theorem withInitialThetaPilots_qPilot
    (package : IUTStage1SourcePackage source target index)
    (theta : InitialThetaData Fmod F K) :
    (package.withInitialThetaPilots theta).qPilot =
      ToyIUTIIHodgeArakelovEvaluationData.legacyQPilotId
        (ToyIUTIIHodgeArakelovEvaluationData.ofInitialThetaData theta) :=
  rfl

end IUTStage1SourcePackage

end Stage1
end Iut
