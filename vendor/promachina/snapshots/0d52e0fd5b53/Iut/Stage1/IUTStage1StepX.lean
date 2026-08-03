/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1FiniteLabels

/-!
Step (x) procession-normalized upper-ray corridor for Stage 1.

This module is a mechanical extraction from `Iut.Stage1.IUTStage1Source`.  It
keeps the procession tensor-packet log-volume lemmas, the Step (x)
indeterminacy corridor, the handoff to the theta-hull upper ray, and the local
Frobenioid shift diagnostics that depend directly on the Step (x) boundary.
Gaussian square-weight, Hodge/SHE, IPL, and Step (xi) source-route declarations
remain in `Iut.Stage1.IUTStage1Source` for now.
-/

namespace Iut
namespace Stage1

open RealLineCopy
open scoped BigOperators

universe u v w x

namespace IUTStage1ProcessionTensorPacketLogVolume

variable {kind : IUTStage1PlaceKind} {j : Nat}

theorem const_le_normalizedLogVolume_of_forall_le
    (data : IUTStage1ProcessionTensorPacketLogVolume kind j)
    {c : Real}
    (hlabel :
      ∀ label : IUTStage1ProcessionContainer j,
        c <= (data.logShellDirectSum label).finiteLogVolume) :
    c <= data.normalizedLogVolume := by
  let averaged := data.toLabelAveraged
  haveI : Nonempty (IUTStage1ProcessionContainer j) :=
    ⟨IUTStage1ProcessionContainer.core j⟩
  exact
    IUTStage1LabelAveragedProcessionLogVolume.const_le_average_of_forall_le
      averaged hlabel

def reindex
    (data : IUTStage1ProcessionTensorPacketLogVolume kind j)
    (perm :
      IUTStage1ProcessionContainer j ≃
        IUTStage1ProcessionContainer j) :
    IUTStage1ProcessionTensorPacketLogVolume kind j :=
  { logShellDirectSum := fun label => data.logShellDirectSum (perm label),
    tensorPacketLogVolume := data.tensorPacketLogVolume,
    tensor_packet_eq_sum := by
      have hsum :
          (Finset.univ.sum fun label : IUTStage1ProcessionContainer j =>
            (data.logShellDirectSum (perm label)).finiteLogVolume) =
            Finset.univ.sum fun label : IUTStage1ProcessionContainer j =>
              (data.logShellDirectSum label).finiteLogVolume :=
        Fintype.sum_equiv perm
          (fun label : IUTStage1ProcessionContainer j =>
            (data.logShellDirectSum (perm label)).finiteLogVolume)
          (fun label : IUTStage1ProcessionContainer j =>
            (data.logShellDirectSum label).finiteLogVolume)
          (fun _label => rfl)
      calc
        data.tensorPacketLogVolume =
            Finset.univ.sum fun label : IUTStage1ProcessionContainer j =>
              (data.logShellDirectSum label).finiteLogVolume :=
          data.tensor_packet_eq_sum
        _ =
            Finset.univ.sum fun label : IUTStage1ProcessionContainer j =>
              (data.logShellDirectSum (perm label)).finiteLogVolume :=
          hsum.symm,
    normalizedLogVolume := data.normalizedLogVolume,
    normalized_eq_average := data.normalized_eq_average }

theorem reindex_tensorPacketLogVolume_eq
    (data : IUTStage1ProcessionTensorPacketLogVolume kind j)
    (perm :
      IUTStage1ProcessionContainer j ≃
        IUTStage1ProcessionContainer j) :
    (data.reindex perm).tensorPacketLogVolume =
      data.tensorPacketLogVolume :=
  rfl

theorem reindex_normalizedLogVolume_eq
    (data : IUTStage1ProcessionTensorPacketLogVolume kind j)
    (perm :
      IUTStage1ProcessionContainer j ≃
        IUTStage1ProcessionContainer j) :
    (data.reindex perm).normalizedLogVolume =
      data.normalizedLogVolume :=
  rfl

end IUTStage1ProcessionTensorPacketLogVolume

namespace IUTStage1LabelAveragedProcessionLogVolume

variable {label : Type u} [Fintype label]

/--
Reindex a finite label-averaged procession log-volume by a label-set
permutation.

This is the concrete finite shadow of the `(Ind1)` permutation part of
Theorem 3.11: labels are not identified or collapsed; they are transported by
an equivalence, and the normalized average is unchanged because finite sums are
invariant under reindexing.
-/
noncomputable def reindex
    (data : IUTStage1LabelAveragedProcessionLogVolume label)
    (perm : label ≃ label) :
    IUTStage1LabelAveragedProcessionLogVolume label :=
  { normalizedLogVolume := fun label => data.normalizedLogVolume (perm label),
    averageLogVolume := data.averageLogVolume,
    average_eq := by
      rw [data.average_eq]
      congr 1
      exact
        (Fintype.sum_equiv perm
          (fun label => data.normalizedLogVolume (perm label))
          data.normalizedLogVolume
          (fun _label => rfl)).symm }

theorem reindex_normalizedLogVolume_eq
    (data : IUTStage1LabelAveragedProcessionLogVolume label)
    (perm : label ≃ label)
    (j : label) :
    (data.reindex perm).normalizedLogVolume j =
      data.normalizedLogVolume (perm j) :=
  rfl

theorem reindex_averageLogVolume_eq
    (data : IUTStage1LabelAveragedProcessionLogVolume label)
    (perm : label ≃ label) :
    (data.reindex perm).averageLogVolume =
      data.averageLogVolume :=
  rfl

theorem averageLogVolume_eq_reindex
    (data : IUTStage1LabelAveragedProcessionLogVolume label)
    (perm : label ≃ label) :
    data.averageLogVolume =
      (data.reindex perm).averageLogVolume :=
  rfl

end IUTStage1LabelAveragedProcessionLogVolume

/--
IUT III Step (x) procession-normalized indeterminacy corridor.

At the averaged log-volume level, `(Ind1)` and `(Ind2)` preserve the value, while
`(Ind3)` supplies an upper bound.  This record keeps precisely that source
shape for label-averaged procession log-volumes.
-/
structure IUTStage1ProcessionNormalizedIndeterminacyCorridor
    (label : Type u) [Fintype label] where
  beforeIndeterminacy :
    IUTStage1LabelAveragedProcessionLogVolume label
  afterInd1 :
    IUTStage1LabelAveragedProcessionLogVolume label
  afterInd2 :
    IUTStage1LabelAveragedProcessionLogVolume label
  ind3UpperBound : Real
  ind1_pointwise_eq :
    ∀ j : label,
      beforeIndeterminacy.normalizedLogVolume j =
        afterInd1.normalizedLogVolume j
  ind2_pointwise_eq :
    ∀ j : label,
      afterInd1.normalizedLogVolume j =
        afterInd2.normalizedLogVolume j
  ind3_upper :
    afterInd2.averageLogVolume <= ind3UpperBound

namespace IUTStage1ProcessionNormalizedIndeterminacyCorridor

variable {label : Type u} [Fintype label]

theorem ind1_preserves_average
    (data : IUTStage1ProcessionNormalizedIndeterminacyCorridor label) :
    data.beforeIndeterminacy.averageLogVolume =
      data.afterInd1.averageLogVolume :=
  IUTStage1LabelAveragedProcessionLogVolume.average_eq_of_pointwise
    data.ind1_pointwise_eq

theorem ind2_preserves_average
    (data : IUTStage1ProcessionNormalizedIndeterminacyCorridor label) :
    data.afterInd1.averageLogVolume =
      data.afterInd2.averageLogVolume :=
  IUTStage1LabelAveragedProcessionLogVolume.average_eq_of_pointwise
    data.ind2_pointwise_eq

theorem afterInd1_average_eq_before
    (data : IUTStage1ProcessionNormalizedIndeterminacyCorridor label) :
    data.afterInd1.averageLogVolume =
      data.beforeIndeterminacy.averageLogVolume :=
  data.ind1_preserves_average.symm

theorem afterInd2_average_eq_before
    (data : IUTStage1ProcessionNormalizedIndeterminacyCorridor label) :
    data.afterInd2.averageLogVolume =
      data.beforeIndeterminacy.averageLogVolume :=
  data.ind2_preserves_average.symm.trans
    data.afterInd1_average_eq_before

theorem before_average_le_ind3UpperBound
    (data : IUTStage1ProcessionNormalizedIndeterminacyCorridor label) :
    data.beforeIndeterminacy.averageLogVolume <= data.ind3UpperBound := by
  rw [data.ind1_preserves_average, data.ind2_preserves_average]
  exact data.ind3_upper

theorem afterInd1_average_le_ind3UpperBound
    (data : IUTStage1ProcessionNormalizedIndeterminacyCorridor label) :
    data.afterInd1.averageLogVolume <= data.ind3UpperBound := by
  rw [data.ind2_preserves_average]
  exact data.ind3_upper

theorem afterInd2_average_le_ind3UpperBound
    (data : IUTStage1ProcessionNormalizedIndeterminacyCorridor label) :
    data.afterInd2.averageLogVolume <= data.ind3UpperBound :=
  data.ind3_upper

/--
Remark 3.12.2(iii) averaged-log-volume endpoint.

The procession-normalized average is unchanged by `(Ind1)` and `(Ind2)`;
the remaining log-link upper-semi ambiguity `(Ind3)` is exactly the one-sided
upper bound recorded by the corridor.
-/
theorem remark3122_logLinkJuggling_ind3_endpoint
    (data : IUTStage1ProcessionNormalizedIndeterminacyCorridor label) :
    data.beforeIndeterminacy.averageLogVolume =
        data.afterInd1.averageLogVolume ∧
      data.afterInd1.averageLogVolume =
        data.afterInd2.averageLogVolume ∧
      data.afterInd2.averageLogVolume <= data.ind3UpperBound ∧
      data.beforeIndeterminacy.averageLogVolume <= data.ind3UpperBound :=
  ⟨data.ind1_preserves_average,
    data.ind2_preserves_average,
    data.afterInd2_average_le_ind3UpperBound,
    data.before_average_le_ind3UpperBound⟩

noncomputable def ofZModCuspLabelLogVolumeCompatibilities
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound) :
    IUTStage1ProcessionNormalizedIndeterminacyCorridor (ZMod l.value) :=
  { beforeIndeterminacy := before.toLabelAveraged,
    afterInd1 := afterInd1.toLabelAveraged,
    afterInd2 := afterInd2.toLabelAveraged,
    ind3UpperBound := ind3UpperBound,
    ind1_pointwise_eq := hind1,
    ind2_pointwise_eq := hind2,
    ind3_upper :=
      afterInd2.toLabelAveraged_average_le_of_zero_and_cuspClass_le
        hzero hcusp }

theorem ofZModCuspLabelLogVolumeCompatibilities_endpoint
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound) :
    let corridor :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp
    corridor.beforeIndeterminacy.averageLogVolume <= ind3UpperBound ∧
      corridor.afterInd1.averageLogVolume =
        corridor.beforeIndeterminacy.averageLogVolume ∧
      corridor.afterInd2.averageLogVolume =
        corridor.beforeIndeterminacy.averageLogVolume ∧
      corridor.afterInd2.averageLogVolume <= ind3UpperBound := by
  intro corridor
  exact
    ⟨corridor.before_average_le_ind3UpperBound,
      corridor.afterInd1_average_eq_before,
      corridor.afterInd2_average_eq_before,
      corridor.afterInd2_average_le_ind3UpperBound⟩

end IUTStage1ProcessionNormalizedIndeterminacyCorridor

/--
Finite-action form of the Step (x) indeterminacy corridor.

The source description of `(Ind1)` includes permutation automorphisms of the
label sets, while `(Ind2)` includes further automorphisms of the prime-strip
data.  At the label-averaged log-volume level both are represented by
permutations of the finite label set.  The record therefore asks for actual
equivalences, not pointwise label identifications, and proves average
invariance by finite-sum reindexing.  `(Ind3)` remains one-sided.
-/
structure IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor
    (label : Type u) [Fintype label] where
  beforeIndeterminacy :
    IUTStage1LabelAveragedProcessionLogVolume label
  ind1Permutation : label ≃ label
  ind2Permutation : label ≃ label
  ind3UpperBound : Real
  ind3_upper :
    ((beforeIndeterminacy.reindex ind1Permutation).reindex
      ind2Permutation).averageLogVolume <= ind3UpperBound

namespace IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor

variable {label : Type u} [Fintype label]

noncomputable def afterInd1
    (data :
      IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor label) :
    IUTStage1LabelAveragedProcessionLogVolume label :=
  data.beforeIndeterminacy.reindex data.ind1Permutation

noncomputable def afterInd2
    (data :
      IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor label) :
    IUTStage1LabelAveragedProcessionLogVolume label :=
  data.afterInd1.reindex data.ind2Permutation

theorem afterInd1_normalizedLogVolume_eq
    (data :
      IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor label)
    (j : label) :
    data.afterInd1.normalizedLogVolume j =
      data.beforeIndeterminacy.normalizedLogVolume
        (data.ind1Permutation j) :=
  rfl

theorem afterInd2_normalizedLogVolume_eq
    (data :
      IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor label)
    (j : label) :
    data.afterInd2.normalizedLogVolume j =
      data.beforeIndeterminacy.normalizedLogVolume
        (data.ind1Permutation (data.ind2Permutation j)) :=
  rfl

theorem ind1_preserves_average
    (data :
      IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor label) :
    data.afterInd1.averageLogVolume =
      data.beforeIndeterminacy.averageLogVolume :=
  rfl

theorem ind2_preserves_average
    (data :
      IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor label) :
    data.afterInd2.averageLogVolume =
      data.afterInd1.averageLogVolume :=
  rfl

theorem afterInd2_average_eq_before
    (data :
      IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor label) :
    data.afterInd2.averageLogVolume =
      data.beforeIndeterminacy.averageLogVolume :=
  rfl

theorem before_average_le_ind3UpperBound
    (data :
      IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor label) :
    data.beforeIndeterminacy.averageLogVolume <= data.ind3UpperBound := by
  simpa [afterInd2] using data.ind3_upper

/--
Permutation-action Step (x) endpoint.

This is the averaged-log-volume statement corresponding to the paper's
Ind1/Ind2/Ind3 split: Ind1 and Ind2 preserve the average by finite label
permutation, while Ind3 contributes only the upper-semi inequality.
-/
theorem permutationIndeterminacy_endpoint
    (data :
      IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor label) :
    data.afterInd1.averageLogVolume =
        data.beforeIndeterminacy.averageLogVolume ∧
      data.afterInd2.averageLogVolume =
        data.afterInd1.averageLogVolume ∧
      data.afterInd2.averageLogVolume <= data.ind3UpperBound ∧
      data.beforeIndeterminacy.averageLogVolume <= data.ind3UpperBound :=
  ⟨data.ind1_preserves_average,
    data.ind2_preserves_average,
    data.ind3_upper,
    data.before_average_le_ind3UpperBound⟩

end IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor

/--
Step (x) to Step (xi) upper-ray bridge.

Step (x) converts the procession-normalized `(Ind3)` ambiguity into an upper
bound.  Step (xi) then uses a hull/determinant log-volume upper ray.  This
record keeps the minimal numerical handoff: the q-pilot real is the
pre-indeterminacy averaged log-volume, and the Theta hull real is the Step (x)
`(Ind3)` upper bound.
-/
structure IUTStage1StepXToHullUpperRayLogVolume
    (label : Type u) [Fintype label] where
  corridor : IUTStage1ProcessionNormalizedIndeterminacyCorridor label
  determinant :
    IUTStage1ArithmeticVectorBundleDeterminantLogVolume
  thetaHullLogVolume : Real
  theta_eq_ind3Upper :
    thetaHullLogVolume = corridor.ind3UpperBound
  theta_eq_normalized_determinant :
    thetaHullLogVolume = determinant.normalizedLogVolume
  qPilotLogVolume : Real
  q_eq_beforeAverage :
    qPilotLogVolume = corridor.beforeIndeterminacy.averageLogVolume

/--
Source-facing Step (x) to Step (xi) handoff.

IUT III, Corollary 3.12, Step (xi-d)--(xi-f), compares the Step (x)
procession-normalized q-pilot log-volume and `(Ind3)` theta upper bound with the
real objects obtained from the holomorphic hull, determinant, and normalized
log-volume.  This proposition records only that compatibility for a fixed
corridor and a fixed hull source.
-/
structure IUTStage1StepXHullApproximantHandoff
    {label : Type u} [Fintype label] {α : Type v} {ι : Type w}
    (corridor : IUTStage1ProcessionNormalizedIndeterminacyCorridor label)
    (hullSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow α ι) :
    Prop where
  theta_eq_ind3Upper :
    hullSource.approximantLogVolume = corridor.ind3UpperBound
  q_eq_beforeAverage :
    hullSource.qPilotLogVolume =
      corridor.beforeIndeterminacy.averageLogVolume

/--
Invariant Step (x)-to-upper-ray payload.

This is the common numerical core used after the procession-normalized
indeterminacy analysis has done its work.  It deliberately records only the
paper-level consequence needed by Step (xi): the q-pilot averaged log-volume
lies in the theta hull upper ray.  Both the older pointwise corridor and the
permutation-action corridor below project to this record.
-/
structure IUTStage1StepXInvariantUpperRayLogVolume
    (label : Type u) [Fintype label] where
  determinant :
    IUTStage1ArithmeticVectorBundleDeterminantLogVolume
  thetaHullLogVolume : Real
  theta_eq_normalized_determinant :
    thetaHullLogVolume = determinant.normalizedLogVolume
  qPilotLogVolume : Real
  q_mem_upperRay : qPilotLogVolume <= thetaHullLogVolume

namespace IUTStage1StepXInvariantUpperRayLogVolume

variable {label : Type u} [Fintype label]

def toHullDetPilotUpperRayLogVolume
    (data : IUTStage1StepXInvariantUpperRayLogVolume label) :
    IUTStage1HullDetPilotUpperRayLogVolume :=
  { determinant := data.determinant,
    thetaHullLogVolume := data.thetaHullLogVolume,
    theta_eq_normalized_determinant :=
      data.theta_eq_normalized_determinant,
    qPilotLogVolume := data.qPilotLogVolume,
    q_mem_upperRay := data.q_mem_upperRay }

theorem qPilotLogVolume_le_thetaHullLogVolume
    (data : IUTStage1StepXInvariantUpperRayLogVolume label) :
    data.qPilotLogVolume <= data.thetaHullLogVolume :=
  data.q_mem_upperRay

theorem qPilotLogVolume_mem_upperRay
    (data : IUTStage1StepXInvariantUpperRayLogVolume label) :
    data.qPilotLogVolume ∈
      data.toHullDetPilotUpperRayLogVolume.upperRay :=
  data.q_mem_upperRay

def toQPilotTwoComputationLogVolume
    (data : IUTStage1StepXInvariantUpperRayLogVolume label) :
    IUTStage1QPilotTwoComputationLogVolume :=
  { upperRayData := data.toHullDetPilotUpperRayLogVolume,
    inputPrimeStripLogVolume := data.qPilotLogVolume,
    outputHullLogVolume := data.qPilotLogVolume,
    input_eq_q := rfl,
    output_eq_q := rfl }

def toQPilotTwoComputationSignedEndpoint
    (data : IUTStage1StepXInvariantUpperRayLogVolume label)
    (q_pilot_positive : 0 < -data.qPilotLogVolume) :
    IUTStage1QPilotTwoComputationSignedEndpoint :=
  { twoComputation := data.toQPilotTwoComputationLogVolume,
    q_pilot_positive := q_pilot_positive }

def toQPilotTwoComputationCThetaEndpoint
    (data : IUTStage1StepXInvariantUpperRayLogVolume label)
    (q_pilot_positive : 0 < -data.qPilotLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <= cTheta * (-data.qPilotLogVolume)) :
    IUTStage1QPilotTwoComputationCThetaEndpoint :=
  { signedEndpoint :=
      data.toQPilotTwoComputationSignedEndpoint q_pilot_positive,
    cTheta := cTheta,
    thetaHullLogVolume_le_cTheta_absLogQ := by
      simpa [toQPilotTwoComputationSignedEndpoint,
        toQPilotTwoComputationLogVolume,
        toHullDetPilotUpperRayLogVolume] using
        thetaHull_le_cTheta_absLogQ }

theorem signedCThetaComparison_endpoint
    (data : IUTStage1StepXInvariantUpperRayLogVolume label)
    (q_pilot_positive : 0 < -data.qPilotLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <= cTheta * (-data.qPilotLogVolume)) :
    let endpoint :=
      data.toQPilotTwoComputationCThetaEndpoint
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ;
    endpoint.toSignedCThetaBound.comparison.qSigned =
        data.qPilotLogVolume ∧
      endpoint.toSignedCThetaBound.comparison.thetaSigned =
        data.thetaHullLogVolume ∧
      endpoint.toSignedCThetaBound.comparison.qSigned <=
        endpoint.toSignedCThetaBound.comparison.thetaSigned ∧
      endpoint.toSignedCThetaBound.comparison.qSigned <=
        endpoint.toSignedCThetaBound.cTheta *
          (-endpoint.toSignedCThetaBound.comparison.qSigned) ∧
      (-1 : Real) <= endpoint.toSignedCThetaBound.cTheta := by
  intro endpoint
  exact
    ⟨by
      simpa [endpoint, toQPilotTwoComputationCThetaEndpoint,
        toQPilotTwoComputationSignedEndpoint,
        toQPilotTwoComputationLogVolume,
        IUTStage1QPilotTwoComputationCThetaEndpoint.toSignedCThetaBound,
        IUTStage1QPilotTwoComputationSignedEndpoint.comparisonData],
      by
        simpa [endpoint, toQPilotTwoComputationCThetaEndpoint,
          toQPilotTwoComputationSignedEndpoint,
          toQPilotTwoComputationLogVolume,
          toHullDetPilotUpperRayLogVolume,
          IUTStage1QPilotTwoComputationCThetaEndpoint.toSignedCThetaBound,
          IUTStage1QPilotTwoComputationSignedEndpoint.comparisonData],
      endpoint.toSignedCThetaBound.comparison.qSigned_le_thetaSigned,
      endpoint.toSignedCThetaBound.qSigned_le_cTheta_absLogQ,
      endpoint.toSignedCThetaBound.cTheta_ge_neg_one⟩

theorem signedCorollary312_magnitudes
    (data : IUTStage1StepXInvariantUpperRayLogVolume label)
    (q_pilot_positive : 0 < -data.qPilotLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <= cTheta * (-data.qPilotLogVolume)) :
    let endpoint :=
      data.toQPilotTwoComputationCThetaEndpoint
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ;
    endpoint.toSignedCThetaBound.comparison.qPilot.value =
        -data.qPilotLogVolume ∧
      endpoint.toSignedCThetaBound.comparison.thetaPilot.value =
        -data.thetaHullLogVolume ∧
      Corollary312Inequality
        endpoint.toSignedCThetaBound.comparison.thetaPilot
        endpoint.toSignedCThetaBound.comparison.qPilot := by
  intro endpoint
  exact
    ⟨by
      simpa [endpoint, toQPilotTwoComputationCThetaEndpoint,
        toQPilotTwoComputationSignedEndpoint,
        toQPilotTwoComputationLogVolume,
        IUTStage1QPilotTwoComputationCThetaEndpoint.toSignedCThetaBound,
        IUTStage1QPilotTwoComputationSignedEndpoint.comparisonData,
        Corollary312ComparisonData.qPilot],
      by
        simpa [endpoint, toQPilotTwoComputationCThetaEndpoint,
          toQPilotTwoComputationSignedEndpoint,
          toQPilotTwoComputationLogVolume,
          toHullDetPilotUpperRayLogVolume,
          IUTStage1QPilotTwoComputationCThetaEndpoint.toSignedCThetaBound,
          IUTStage1QPilotTwoComputationSignedEndpoint.comparisonData,
          Corollary312ComparisonData.thetaPilot],
      endpoint.toSignedCThetaBound.comparison.corollary312⟩

end IUTStage1StepXInvariantUpperRayLogVolume

/--
Step (x) to Step (xi) handoff for the permutation-action form of the
indeterminacy corridor.

Unlike the older same-label route, this record does not ask for pointwise
identification of the normalized label family after \IndOne{} and \IndTwo{}.
The q-pilot average is the pre-indeterminacy average, and membership in the
theta upper ray follows from finite-sum invariance under the two label-set
equivalences plus the one-sided \IndThree{} bound.
-/
structure IUTStage1PermutationStepXToHullUpperRayLogVolume
    (label : Type u) [Fintype label] where
  corridor :
    IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor label
  determinant :
    IUTStage1ArithmeticVectorBundleDeterminantLogVolume
  thetaHullLogVolume : Real
  theta_eq_ind3Upper :
    thetaHullLogVolume = corridor.ind3UpperBound
  theta_eq_normalized_determinant :
    thetaHullLogVolume = determinant.normalizedLogVolume
  qPilotLogVolume : Real
  q_eq_beforeAverage :
    qPilotLogVolume =
      corridor.beforeIndeterminacy.averageLogVolume

namespace IUTStage1PermutationStepXToHullUpperRayLogVolume

variable {label : Type u} [Fintype label]

def qPilotLogVolume_le_thetaHullLogVolume
    (data : IUTStage1PermutationStepXToHullUpperRayLogVolume label) :
    data.qPilotLogVolume <= data.thetaHullLogVolume := by
  rw [data.q_eq_beforeAverage, data.theta_eq_ind3Upper]
  exact data.corridor.before_average_le_ind3UpperBound

def toInvariantUpperRayLogVolume
    (data : IUTStage1PermutationStepXToHullUpperRayLogVolume label) :
    IUTStage1StepXInvariantUpperRayLogVolume label :=
  { determinant := data.determinant,
    thetaHullLogVolume := data.thetaHullLogVolume,
    theta_eq_normalized_determinant :=
      data.theta_eq_normalized_determinant,
    qPilotLogVolume := data.qPilotLogVolume,
    q_mem_upperRay := data.qPilotLogVolume_le_thetaHullLogVolume }

def ofPermutationCorridor
    (corridor :
      IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor label)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = corridor.ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume) :
    IUTStage1PermutationStepXToHullUpperRayLogVolume label :=
  { corridor := corridor,
    determinant := determinant,
    thetaHullLogVolume := thetaHullLogVolume,
    theta_eq_ind3Upper := theta_eq_ind3Upper,
    theta_eq_normalized_determinant :=
      theta_eq_normalized_determinant,
    qPilotLogVolume := corridor.beforeIndeterminacy.averageLogVolume,
    q_eq_beforeAverage := rfl }

theorem ofPermutationCorridor_endpoint
    (corridor :
      IUTStage1ProcessionNormalizedPermutationIndeterminacyCorridor label)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = corridor.ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume) :
    let data :=
      ofPermutationCorridor corridor determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant;
    data.qPilotLogVolume =
        corridor.beforeIndeterminacy.averageLogVolume ∧
      data.qPilotLogVolume <= data.thetaHullLogVolume ∧
      data.thetaHullLogVolume = determinant.normalizedLogVolume :=
  by
    intro data
    exact
      ⟨rfl,
        data.qPilotLogVolume_le_thetaHullLogVolume,
        data.theta_eq_normalized_determinant⟩

theorem signedCThetaComparison_endpoint
    (data : IUTStage1PermutationStepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta *
          (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    let endpoint :=
      data.toInvariantUpperRayLogVolume.toQPilotTwoComputationCThetaEndpoint
        (by
          simpa [toInvariantUpperRayLogVolume, data.q_eq_beforeAverage]
            using q_pilot_positive)
        cTheta
        (by
          simpa [toInvariantUpperRayLogVolume, data.q_eq_beforeAverage]
            using thetaHull_le_cTheta_absLogQ);
    endpoint.toSignedCThetaBound.comparison.qSigned =
        data.corridor.beforeIndeterminacy.averageLogVolume ∧
      endpoint.toSignedCThetaBound.comparison.thetaSigned =
        data.thetaHullLogVolume ∧
      endpoint.toSignedCThetaBound.comparison.qSigned <=
        endpoint.toSignedCThetaBound.comparison.thetaSigned ∧
      endpoint.toSignedCThetaBound.comparison.qSigned <=
        endpoint.toSignedCThetaBound.cTheta *
          (-endpoint.toSignedCThetaBound.comparison.qSigned) ∧
      (-1 : Real) <= endpoint.toSignedCThetaBound.cTheta := by
  intro endpoint
  have hgeneric :=
    data.toInvariantUpperRayLogVolume.signedCThetaComparison_endpoint
      (by
        simpa [toInvariantUpperRayLogVolume, data.q_eq_beforeAverage]
          using q_pilot_positive)
      cTheta
      (by
        simpa [toInvariantUpperRayLogVolume, data.q_eq_beforeAverage]
          using thetaHull_le_cTheta_absLogQ)
  simpa [endpoint, toInvariantUpperRayLogVolume, data.q_eq_beforeAverage]
    using hgeneric

theorem signedCorollary312_magnitudes
    (data : IUTStage1PermutationStepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta *
          (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    let endpoint :=
      data.toInvariantUpperRayLogVolume.toQPilotTwoComputationCThetaEndpoint
        (by
          simpa [toInvariantUpperRayLogVolume, data.q_eq_beforeAverage]
            using q_pilot_positive)
        cTheta
        (by
          simpa [toInvariantUpperRayLogVolume, data.q_eq_beforeAverage]
            using thetaHull_le_cTheta_absLogQ);
    endpoint.toSignedCThetaBound.comparison.qPilot.value =
        -data.corridor.beforeIndeterminacy.averageLogVolume ∧
      endpoint.toSignedCThetaBound.comparison.thetaPilot.value =
        -data.thetaHullLogVolume ∧
      Corollary312Inequality
        endpoint.toSignedCThetaBound.comparison.thetaPilot
        endpoint.toSignedCThetaBound.comparison.qPilot := by
  intro endpoint
  have hgeneric :=
    data.toInvariantUpperRayLogVolume.signedCorollary312_magnitudes
      (by
        simpa [toInvariantUpperRayLogVolume, data.q_eq_beforeAverage]
          using q_pilot_positive)
      cTheta
      (by
        simpa [toInvariantUpperRayLogVolume, data.q_eq_beforeAverage]
          using thetaHull_le_cTheta_absLogQ)
  simpa [endpoint, toInvariantUpperRayLogVolume, data.q_eq_beforeAverage]
    using hgeneric

end IUTStage1PermutationStepXToHullUpperRayLogVolume

namespace IUTStage1StepXToHullUpperRayLogVolume

variable {label : Type u} [Fintype label]

noncomputable def ofZModCuspLabelLogVolumeCompatibilities
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume) :
    IUTStage1StepXToHullUpperRayLogVolume (ZMod l.value) :=
  { corridor :=
      IUTStage1ProcessionNormalizedIndeterminacyCorridor.ofZModCuspLabelLogVolumeCompatibilities
        before afterInd1 afterInd2 ind3UpperBound
        hind1 hind2 hzero hcusp,
    determinant := determinant,
    thetaHullLogVolume := thetaHullLogVolume,
    theta_eq_ind3Upper := theta_eq_ind3Upper,
    theta_eq_normalized_determinant := theta_eq_normalized_determinant,
    qPilotLogVolume := before.toLabelAveraged.averageLogVolume,
    q_eq_beforeAverage := rfl }

noncomputable def ofCorridorAndHullApproximant
    {α : Type v} {ι : Type w}
    (corridor : IUTStage1ProcessionNormalizedIndeterminacyCorridor label)
    (hullSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow α ι)
    (theta_eq_ind3Upper :
      hullSource.approximantLogVolume = corridor.ind3UpperBound)
    (q_eq_beforeAverage :
      hullSource.qPilotLogVolume =
        corridor.beforeIndeterminacy.averageLogVolume) :
    IUTStage1StepXToHullUpperRayLogVolume label :=
  { corridor := corridor,
    determinant := hullSource.determinant,
    thetaHullLogVolume := hullSource.approximantLogVolume,
    theta_eq_ind3Upper := theta_eq_ind3Upper,
    theta_eq_normalized_determinant :=
      hullSource.approximantLogVolume_eq_normalized_determinant,
    qPilotLogVolume := hullSource.qPilotLogVolume,
    q_eq_beforeAverage := q_eq_beforeAverage }

noncomputable def ofCorridorAndHullApproximantHandoff
    {α : Type v} {ι : Type w}
    (corridor : IUTStage1ProcessionNormalizedIndeterminacyCorridor label)
    (hullSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow α ι)
    (handoff :
      IUTStage1StepXHullApproximantHandoff corridor hullSource) :
    IUTStage1StepXToHullUpperRayLogVolume label :=
  ofCorridorAndHullApproximant
    corridor hullSource handoff.theta_eq_ind3Upper
    handoff.q_eq_beforeAverage

noncomputable def ofZModCuspLabelLogVolumeCompatibilitiesAndHullApproximant
    {l : PrimeGeFive} {α : Type v} {ι : Type w}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (hullSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow α ι)
    (theta_eq_ind3Upper :
      hullSource.approximantLogVolume = ind3UpperBound)
    (q_eq_beforeAverage :
      hullSource.qPilotLogVolume = before.toLabelAveraged.averageLogVolume) :
    IUTStage1StepXToHullUpperRayLogVolume (ZMod l.value) :=
  ofCorridorAndHullApproximant
    (IUTStage1ProcessionNormalizedIndeterminacyCorridor.ofZModCuspLabelLogVolumeCompatibilities
      before afterInd1 afterInd2 ind3UpperBound hind1 hind2 hzero hcusp)
    hullSource theta_eq_ind3Upper q_eq_beforeAverage

theorem ofZModCuspLabelLogVolumeCompatibilities_endpoint
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant
    data.qPilotLogVolume = before.toLabelAveraged.averageLogVolume ∧
      data.qPilotLogVolume <= data.thetaHullLogVolume ∧
      data.thetaHullLogVolume = determinant.normalizedLogVolume := by
  intro data
  exact
    ⟨rfl,
      by
        rw [data.q_eq_beforeAverage, data.theta_eq_ind3Upper]
        exact data.corridor.before_average_le_ind3UpperBound,
      data.theta_eq_normalized_determinant⟩

theorem ofCorridorAndHullApproximant_endpoint
    {α : Type v} {ι : Type w}
    (corridor : IUTStage1ProcessionNormalizedIndeterminacyCorridor label)
    (hullSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow α ι)
    (theta_eq_ind3Upper :
      hullSource.approximantLogVolume = corridor.ind3UpperBound)
    (q_eq_beforeAverage :
      hullSource.qPilotLogVolume =
        corridor.beforeIndeterminacy.averageLogVolume) :
    let data :=
      ofCorridorAndHullApproximant
        corridor hullSource theta_eq_ind3Upper q_eq_beforeAverage
    data.qPilotLogVolume = hullSource.qPilotLogVolume ∧
      data.thetaHullLogVolume = hullSource.approximantLogVolume ∧
      hullSource.thetaImageUnionLogVolume <= data.thetaHullLogVolume ∧
      data.qPilotLogVolume <= data.thetaHullLogVolume ∧
      data.thetaHullLogVolume = hullSource.determinant.normalizedLogVolume :=
  by
    intro data
    exact
      ⟨rfl, rfl,
        hullSource.thetaImageUnionLogVolume_le_approximantLogVolume,
        by
          rw [data.q_eq_beforeAverage, data.theta_eq_ind3Upper]
          exact data.corridor.before_average_le_ind3UpperBound,
        data.theta_eq_normalized_determinant⟩

theorem ofZModCuspLabelLogVolumeCompatibilitiesAndHullApproximant_endpoint
    {l : PrimeGeFive} {α : Type v} {ι : Type w}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (hullSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow α ι)
    (theta_eq_ind3Upper :
      hullSource.approximantLogVolume = ind3UpperBound)
    (q_eq_beforeAverage :
      hullSource.qPilotLogVolume = before.toLabelAveraged.averageLogVolume) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilitiesAndHullApproximant
        before afterInd1 afterInd2 ind3UpperBound hind1 hind2 hzero hcusp
        hullSource theta_eq_ind3Upper q_eq_beforeAverage
    data.qPilotLogVolume = hullSource.qPilotLogVolume ∧
      data.thetaHullLogVolume = hullSource.approximantLogVolume ∧
      hullSource.thetaImageUnionLogVolume <= data.thetaHullLogVolume ∧
      data.qPilotLogVolume <= data.thetaHullLogVolume ∧
      data.thetaHullLogVolume = hullSource.determinant.normalizedLogVolume :=
  by
    intro data
    exact
      ofCorridorAndHullApproximant_endpoint
        (IUTStage1ProcessionNormalizedIndeterminacyCorridor.ofZModCuspLabelLogVolumeCompatibilities
          before afterInd1 afterInd2 ind3UpperBound hind1 hind2 hzero hcusp)
        hullSource theta_eq_ind3Upper q_eq_beforeAverage

theorem qPilotLogVolume_le_thetaHullLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    data.qPilotLogVolume <= data.thetaHullLogVolume := by
  rw [data.q_eq_beforeAverage, data.theta_eq_ind3Upper]
  exact data.corridor.before_average_le_ind3UpperBound

theorem thetaHullLogVolume_eq_determinantLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    data.thetaHullLogVolume = data.determinant.determinantLogVolume := by
  rw [data.theta_eq_normalized_determinant,
    data.determinant.normalizedLogVolume_eq_determinant]

theorem thetaHullLogVolume_eq_tensorPowerLogVolume_div
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    data.thetaHullLogVolume =
      data.determinant.tensorPowerLogVolume /
        (data.determinant.positiveTensorPower : Real) := by
  rw [data.theta_eq_normalized_determinant, data.determinant.normalized_eq]

theorem tensorPowerLogVolume_eq_positiveTensorPower_mul_thetaHullLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    data.determinant.tensorPowerLogVolume =
      (data.determinant.positiveTensorPower : Real) *
        data.thetaHullLogVolume := by
  rw [data.thetaHullLogVolume_eq_determinantLogVolume,
    data.determinant.tensor_power_eq]

theorem qPilotLogVolume_le_determinantLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    data.qPilotLogVolume <= data.determinant.determinantLogVolume := by
  rw [← data.thetaHullLogVolume_eq_determinantLogVolume]
  exact data.qPilotLogVolume_le_thetaHullLogVolume

theorem qPilotLogVolume_le_tensorPowerLogVolume_div
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    data.qPilotLogVolume <=
      data.determinant.tensorPowerLogVolume /
        (data.determinant.positiveTensorPower : Real) := by
  rw [← data.thetaHullLogVolume_eq_tensorPowerLogVolume_div]
  exact data.qPilotLogVolume_le_thetaHullLogVolume

theorem determinantLogVolume_endpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    1 < data.determinant.rank ∧
      0 < data.determinant.positiveTensorPower ∧
      data.determinant.tensorPowerLogVolume =
        (data.determinant.positiveTensorPower : Real) *
          data.determinant.determinantLogVolume ∧
      data.thetaHullLogVolume = data.determinant.determinantLogVolume ∧
      data.qPilotLogVolume <= data.determinant.determinantLogVolume ∧
      data.qPilotLogVolume <=
        data.determinant.tensorPowerLogVolume /
          (data.determinant.positiveTensorPower : Real) := by
  exact
    ⟨data.determinant.rank_gt_one,
      data.determinant.tensor_power_pos,
      data.determinant.tensor_power_eq,
      data.thetaHullLogVolume_eq_determinantLogVolume,
      data.qPilotLogVolume_le_determinantLogVolume,
      data.qPilotLogVolume_le_tensorPowerLogVolume_div⟩

def toHullDetPilotUpperRayLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    IUTStage1HullDetPilotUpperRayLogVolume :=
  { determinant := data.determinant,
    thetaHullLogVolume := data.thetaHullLogVolume,
    theta_eq_normalized_determinant := data.theta_eq_normalized_determinant,
    qPilotLogVolume := data.qPilotLogVolume,
    q_mem_upperRay := data.qPilotLogVolume_le_thetaHullLogVolume }

theorem toUpperRay_q_mem
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    data.qPilotLogVolume ∈
      data.toHullDetPilotUpperRayLogVolume.upperRay :=
  data.toHullDetPilotUpperRayLogVolume.qPilot_mem_upperRay

theorem ofCorridorAndHullApproximantHandoff_endpoint
    {α : Type v} {ι : Type w}
    (corridor : IUTStage1ProcessionNormalizedIndeterminacyCorridor label)
    (hullSource :
      IUTStage1ThetaPossibleImagesHullApproximantLogVolumeShadow α ι)
    (handoff :
      IUTStage1StepXHullApproximantHandoff corridor hullSource) :
    let data :=
      ofCorridorAndHullApproximantHandoff corridor hullSource handoff
    data.qPilotLogVolume = hullSource.qPilotLogVolume ∧
      data.thetaHullLogVolume = hullSource.approximantLogVolume ∧
      hullSource.thetaImageUnionLogVolume <= data.thetaHullLogVolume ∧
      data.qPilotLogVolume <= data.thetaHullLogVolume ∧
      data.toHullDetPilotUpperRayLogVolume.qPilotLogVolume ∈
        data.toHullDetPilotUpperRayLogVolume.upperRay ∧
      data.thetaHullLogVolume = hullSource.determinant.normalizedLogVolume :=
  by
    intro data
    exact
      ⟨rfl, rfl,
        hullSource.thetaImageUnionLogVolume_le_approximantLogVolume,
        data.qPilotLogVolume_le_thetaHullLogVolume,
        data.toUpperRay_q_mem,
        data.theta_eq_normalized_determinant⟩

def toThetaFiniteLogVolumeEndpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    IUTStage1Corollary312ThetaFiniteLogVolumeEndpoint :=
  IUTStage1Corollary312ThetaFiniteLogVolumeEndpoint.ofUpperRayData
    data.toHullDetPilotUpperRayLogVolume

theorem thetaFiniteLogVolumeEndpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    let endpoint := data.toThetaFiniteLogVolumeEndpoint;
    endpoint.thetaExtended.IsFinite ∧
      endpoint.thetaExtended ≠
        IUTStage1ExtendedSignedLogVolume.plusInfinity ∧
      endpoint.thetaRealLogVolume = data.thetaHullLogVolume ∧
      endpoint.upperRayData.qPilotLogVolume <=
        endpoint.thetaRealLogVolume := by
  intro endpoint
  exact
    ⟨endpoint.thetaExtendedFinite,
      endpoint.thetaExtended_ne_plusInfinity,
      endpoint.thetaRealLogVolume_eq_hull,
      endpoint.qPilotLogVolume_le_thetaRealLogVolume⟩

theorem thetaFinite_determinantLogVolume_endpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    let finite := data.toThetaFiniteLogVolumeEndpoint;
    finite.thetaRealLogVolume = data.determinant.determinantLogVolume ∧
      data.qPilotLogVolume <= data.determinant.determinantLogVolume ∧
      data.qPilotLogVolume <=
        data.determinant.tensorPowerLogVolume /
          (data.determinant.positiveTensorPower : Real) ∧
      data.determinant.tensorPowerLogVolume =
        (data.determinant.positiveTensorPower : Real) *
          finite.thetaRealLogVolume := by
  intro finite
  exact
    ⟨by
      rw [finite.thetaRealLogVolume_eq_hull]
      simpa [finite, toThetaFiniteLogVolumeEndpoint,
        toHullDetPilotUpperRayLogVolume] using
        data.thetaHullLogVolume_eq_determinantLogVolume,
    data.qPilotLogVolume_le_determinantLogVolume,
    data.qPilotLogVolume_le_tensorPowerLogVolume_div,
    by
      rw [finite.thetaRealLogVolume_eq_hull]
      simpa [finite, toThetaFiniteLogVolumeEndpoint,
        toHullDetPilotUpperRayLogVolume] using
        data.tensorPowerLogVolume_eq_positiveTensorPower_mul_thetaHullLogVolume⟩

def toZeroColumnHullAbsorption
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (originalRegionLogVolume unitShiftedRegionLogVolume : Real)
    (original_le_thetaHull :
      originalRegionLogVolume <= data.thetaHullLogVolume)
    (unit_shifted_le_thetaHull :
      unitShiftedRegionLogVolume <= data.thetaHullLogVolume) :
    IUTStage1ZeroColumnHullAbsorbsUnitIndeterminacy :=
  { originalRegionLogVolume := originalRegionLogVolume,
    unitShiftedRegionLogVolume := unitShiftedRegionLogVolume,
    hullLogVolume := data.thetaHullLogVolume,
    original_le_hull := original_le_thetaHull,
    unit_shifted_le_hull := unit_shifted_le_thetaHull }

def toOneColumnLogVolumeCompatibility
    (_data : IUTStage1StepXToHullUpperRayLogVolume label)
    (sourceRingStructureLogVolume conjugateRingStructureLogVolume : Real)
    (log_volume_compatible :
      sourceRingStructureLogVolume = conjugateRingStructureLogVolume) :
    IUTStage1OneColumnLogVolumeCompatibilityAbsorbsConjugateChoice :=
  { sourceRingStructureLogVolume := sourceRingStructureLogVolume,
    conjugateRingStructureLogVolume := conjugateRingStructureLogVolume,
    log_volume_compatible := log_volume_compatible }

theorem thetaFinite_zeroOneColumnAbsorptionProfile
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (originalRegionLogVolume unitShiftedRegionLogVolume : Real)
    (original_le_thetaHull :
      originalRegionLogVolume <= data.thetaHullLogVolume)
    (unit_shifted_le_thetaHull :
      unitShiftedRegionLogVolume <= data.thetaHullLogVolume)
    (sourceRingStructureLogVolume conjugateRingStructureLogVolume : Real)
    (log_volume_compatible :
      sourceRingStructureLogVolume = conjugateRingStructureLogVolume) :
    let finite := data.toThetaFiniteLogVolumeEndpoint;
    let zeroData :=
      data.toZeroColumnHullAbsorption
        originalRegionLogVolume unitShiftedRegionLogVolume
        original_le_thetaHull unit_shifted_le_thetaHull;
    let oneData :=
      data.toOneColumnLogVolumeCompatibility
        sourceRingStructureLogVolume conjugateRingStructureLogVolume
        log_volume_compatible;
    zeroData.hullLogVolume = finite.thetaRealLogVolume ∧
      zeroData.originalRegionLogVolume ∈ finite.upperRayData.upperRay ∧
      zeroData.unitShiftedRegionLogVolume ∈ finite.upperRayData.upperRay ∧
      oneData.sourceRingStructureLogVolume =
        oneData.conjugateRingStructureLogVolume ∧
      IUTStage1LogThetaVerticalColumn.zeroThetaPilot.logShellTreatment =
        IUTStage1LogShellColumnTreatment.monoAnalyticContainers ∧
      IUTStage1LogThetaVerticalColumn.oneQPilot.logShellTreatment =
        IUTStage1LogShellColumnTreatment.tautologicalLogDocumentation ∧
      IUTStage1LogThetaVerticalColumn.zeroThetaPilot.logShellTreatment ≠
        IUTStage1LogThetaVerticalColumn.oneQPilot.logShellTreatment := by
  intro finite zeroData oneData
  exact
    ⟨by
      rw [finite.thetaRealLogVolume_eq_hull]
      rfl,
    by
      simpa [IUTStage1HullDetPilotUpperRayLogVolume.upperRay,
        toHullDetPilotUpperRayLogVolume] using original_le_thetaHull,
    by
      simpa [IUTStage1HullDetPilotUpperRayLogVolume.upperRay,
        toHullDetPilotUpperRayLogVolume] using unit_shifted_le_thetaHull,
    oneData.precise_logVolume_eq,
    IUTStage1LogThetaVerticalColumn.thetaPilot_logShellTreatment,
    IUTStage1LogThetaVerticalColumn.qPilot_logShellTreatment,
    IUTStage1LogThetaVerticalColumn.logShellTreatment_distinguishes_columns⟩

/--
Remark 3.12.2(v) finite-theta hull equality guard.

After Step (x) to Step (xi), the zero-column hull is the finite theta boundary.
Membership in the associated upper ray supplies upper bounds only.  Equality
with the finite theta boundary is equivalent to supplying the reverse bound.
-/
theorem thetaFinite_zeroColumnHullEqualityRequiresReverseBounds
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (originalRegionLogVolume unitShiftedRegionLogVolume : Real)
    (original_le_thetaHull :
      originalRegionLogVolume <= data.thetaHullLogVolume)
    (unit_shifted_le_thetaHull :
      unitShiftedRegionLogVolume <= data.thetaHullLogVolume) :
    let finite := data.toThetaFiniteLogVolumeEndpoint;
    let zeroData :=
      data.toZeroColumnHullAbsorption
        originalRegionLogVolume unitShiftedRegionLogVolume
        original_le_thetaHull unit_shifted_le_thetaHull;
    zeroData.hullLogVolume = finite.thetaRealLogVolume ∧
      (zeroData.originalRegionLogVolume = finite.thetaRealLogVolume ↔
        finite.thetaRealLogVolume <= zeroData.originalRegionLogVolume) ∧
      (zeroData.unitShiftedRegionLogVolume = finite.thetaRealLogVolume ↔
        finite.thetaRealLogVolume <= zeroData.unitShiftedRegionLogVolume) := by
  intro finite zeroData
  rw [finite.thetaRealLogVolume_eq_hull]
  exact
    ⟨rfl,
      zeroData.original_eq_hull_iff_hull_le_original,
      zeroData.unitShifted_eq_hull_iff_hull_le_unitShifted⟩

def toThetaPilotTensorPowerLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower) :
    IUTStage1ThetaPilotTensorPowerLogVolume :=
  { originalThetaPilotLogVolume := data.thetaHullLogVolume,
    tensorPower := tensorPower,
    tensor_power_ge_two := tensor_power_ge_two,
    tensorPowerLogVolume :=
      (tensorPower : Real) * data.thetaHullLogVolume,
    tensor_power_logVolume_eq := rfl }

theorem thetaFinite_tensorPower_warning
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower)
    (theta_neg : data.thetaHullLogVolume < 0) :
    let finite := data.toThetaFiniteLogVolumeEndpoint;
    let tensor :=
      data.toThetaPilotTensorPowerLogVolume
        tensorPower tensor_power_ge_two;
    tensor.tensorPowerLogVolume < finite.thetaRealLogVolume ∧
      tensor.tensorPowerUpperRay ⊆ finite.upperRayData.upperRay ∧
      finite.thetaRealLogVolume ∉ tensor.tensorPowerUpperRay := by
  intro finite tensor
  have hTensorNeg : tensor.originalThetaPilotLogVolume < 0 := by
    simpa [toThetaPilotTensorPowerLogVolume] using theta_neg
  have hFinite :
      finite.thetaRealLogVolume = tensor.originalThetaPilotLogVolume := by
    simpa [toThetaPilotTensorPowerLogVolume] using
      finite.thetaRealLogVolume_eq_hull
  exact
    ⟨by
      calc
        tensor.tensorPowerLogVolume <
            tensor.originalThetaPilotLogVolume :=
          tensor.tensorPowerLogVolume_lt_original_of_original_neg hTensorNeg
        _ = finite.thetaRealLogVolume := hFinite.symm,
    by
      intro value hvalue
      have hleOriginal :
          value <= tensor.originalThetaPilotLogVolume :=
        le_trans hvalue
          (tensor.tensorPowerLogVolume_le_original_of_original_nonpos
            (le_of_lt hTensorNeg))
      simpa [IUTStage1HullDetPilotUpperRayLogVolume.upperRay, hFinite]
        using hleOriginal,
    by
      intro hmem
      have hnot :=
        tensor.originalBoundary_not_mem_tensorPowerUpperRay_of_original_neg
          hTensorNeg
      rw [hFinite] at hmem
      exact hnot hmem⟩

theorem thetaFinite_qPilot_lt_thetaRealLogVolume_of_mem_tensorPowerUpperRay
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower)
    (theta_neg : data.thetaHullLogVolume < 0)
    (hmem :
      data.toThetaFiniteLogVolumeEndpoint.upperRayData.qPilotLogVolume ∈
        (data.toThetaPilotTensorPowerLogVolume
          tensorPower tensor_power_ge_two).tensorPowerUpperRay) :
    data.toThetaFiniteLogVolumeEndpoint.upperRayData.qPilotLogVolume <
      data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume := by
  have hTensorNeg :
      (data.toThetaPilotTensorPowerLogVolume
        tensorPower tensor_power_ge_two).originalThetaPilotLogVolume < 0 := by
    simpa [toThetaPilotTensorPowerLogVolume] using theta_neg
  have hlt :=
    (data.toThetaPilotTensorPowerLogVolume tensorPower tensor_power_ge_two)
      |>.mem_tensorPowerUpperRay_lt_original_of_original_neg hTensorNeg hmem
  have hFinite :
      data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume =
        (data.toThetaPilotTensorPowerLogVolume
          tensorPower tensor_power_ge_two).originalThetaPilotLogVolume := by
    simpa [toThetaPilotTensorPowerLogVolume] using
      data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume_eq_hull
  rw [hFinite]
  exact hlt

def toLocalFrobenioidLogVolumeAmbiguity
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real) :
    IUTStage1LocalFrobenioidLogVolumeAmbiguity :=
  { unshiftedLogVolume := data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume,
    localExponent := localExponent,
    localPrimeStepLogVolume := localPrimeStepLogVolume,
    shiftedLogVolume :=
      data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume +
        (localExponent : Real) * localPrimeStepLogVolume,
    shifted_logVolume_eq := rfl }

def toGlobalFrobenioidLogVolumeCalibration
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real) :
    IUTStage1GlobalFrobenioidLogVolumeCalibration :=
  { localData :=
      data.toLocalFrobenioidLogVolumeAmbiguity
        localExponent localPrimeStepLogVolume,
    globalExponent := 0,
    global_exponent_eq_zero := rfl,
    calibratedLogVolume :=
      data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume,
    calibrated_logVolume_eq := by
      simp [toLocalFrobenioidLogVolumeAmbiguity] }

theorem thetaFinite_globalFrobenioidCalibration
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real) :
    let finite := data.toThetaFiniteLogVolumeEndpoint;
    let localDatum :=
      data.toLocalFrobenioidLogVolumeAmbiguity
        localExponent localPrimeStepLogVolume;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    localDatum.unshiftedLogVolume = finite.thetaRealLogVolume ∧
      localDatum.shiftedLogVolume =
        finite.thetaRealLogVolume +
          (localExponent : Real) * localPrimeStepLogVolume ∧
      global.calibratedLogVolume = finite.thetaRealLogVolume ∧
      global.calibratedLogVolume = localDatum.unshiftedLogVolume ∧
      (global.calibratedLogVolume = localDatum.shiftedLogVolume ↔
        (localDatum.localExponent : Real) * localDatum.localPrimeStepLogVolume = 0) ∧
      (localExponent ≠ 0 →
        localPrimeStepLogVolume ≠ 0 →
          global.calibratedLogVolume ≠ localDatum.shiftedLogVolume) := by
  intro finite localDatum global
  exact
    ⟨rfl, rfl, global.calibratedLogVolume_eq_unshifted,
      global.calibratedLogVolume_eq_unshifted,
      global.calibratedLogVolume_eq_shifted_iff_shiftTerm_eq_zero,
      fun hExponent hStep =>
        global.calibratedLogVolume_ne_shifted_of_local_nonzero
          hExponent hStep⟩

theorem thetaFinite_globalFrobenioidCalibration_eq_shifted_iff_exponent_zero_or_step_zero
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real) :
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    global.calibratedLogVolume = global.localData.shiftedLogVolume ↔
      localExponent = 0 ∨ localPrimeStepLogVolume = 0 := by
  intro global
  exact
    global.calibratedLogVolume_eq_shifted_iff_exponent_zero_or_step_zero

theorem thetaFinite_globalFrobenioidCalibration_orderedShift
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real) :
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (global.calibratedLogVolume < global.localData.shiftedLogVolume ↔
      0 < (localExponent : Real) * localPrimeStepLogVolume) ∧
      (global.localData.shiftedLogVolume < global.calibratedLogVolume ↔
        (localExponent : Real) * localPrimeStepLogVolume < 0) := by
  intro global
  exact
    ⟨global.calibratedLogVolume_lt_shifted_iff_shiftTerm_pos,
      global.shiftedLogVolume_lt_calibrated_iff_shiftTerm_lt_zero⟩

theorem thetaFinite_localFrobenioidShift_eq_iff_exponent_eq_of_step_nonzero
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (exponent₁ exponent₂ : Int)
    (localPrimeStepLogVolume : Real)
    (hStep : localPrimeStepLogVolume ≠ 0) :
    let local₁ :=
      data.toLocalFrobenioidLogVolumeAmbiguity
        exponent₁ localPrimeStepLogVolume;
    let local₂ :=
      data.toLocalFrobenioidLogVolumeAmbiguity
        exponent₂ localPrimeStepLogVolume;
    local₁.shiftedLogVolume = local₂.shiftedLogVolume ↔
      exponent₁ = exponent₂ := by
  intro local₁ local₂
  have hlocal :=
    IUTStage1LocalFrobenioidLogVolumeAmbiguity.shiftedLogVolume_eq_iff_exponent_eq_of_same_base_step
      local₁ local₂ rfl rfl hStep
  simpa [local₁, local₂, toLocalFrobenioidLogVolumeAmbiguity] using hlocal

theorem thetaFinite_upperSemiQuotient_localShift_eq_iff_exponent_eq_of_step_nonzero
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (collapsedRegion : Set Real)
    (exponent₁ exponent₂ : Int)
    (localPrimeStepLogVolume : Real)
    (hStep : localPrimeStepLogVolume ≠ 0)
    (houtside₁ :
      (data.toLocalFrobenioidLogVolumeAmbiguity
        exponent₁ localPrimeStepLogVolume).shiftedLogVolume ∉ collapsedRegion)
    (houtside₂ :
      (data.toLocalFrobenioidLogVolumeAmbiguity
        exponent₂ localPrimeStepLogVolume).shiftedLogVolume ∉ collapsedRegion) :
    let local₁ :=
      data.toLocalFrobenioidLogVolumeAmbiguity
        exponent₁ localPrimeStepLogVolume;
    let local₂ :=
      data.toLocalFrobenioidLogVolumeAmbiguity
        exponent₂ localPrimeStepLogVolume;
    IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion local₁.shiftedLogVolume =
      IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion local₂.shiftedLogVolume ↔
      exponent₁ = exponent₂ := by
  intro local₁ local₂
  have hquot :
      IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion local₁.shiftedLogVolume =
        IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion local₂.shiftedLogVolume ↔
        local₁.shiftedLogVolume = local₂.shiftedLogVolume :=
    IUTStage1UpperSemiSetQuotient.quotientMap_eq_iff_of_not_mem
      (S := collapsedRegion)
      (x := local₁.shiftedLogVolume)
      (y := local₂.shiftedLogVolume)
      (by simpa [local₁] using houtside₁)
      (by simpa [local₂] using houtside₂)
  have hshift :=
    data.thetaFinite_localFrobenioidShift_eq_iff_exponent_eq_of_step_nonzero
      exponent₁ exponent₂ localPrimeStepLogVolume hStep
  exact hquot.trans hshift

theorem thetaFinite_upperSemiQuotient_collapses_distinct_localShifts_of_mem
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (collapsedRegion : Set Real)
    (exponent₁ exponent₂ : Int)
    (localPrimeStepLogVolume : Real)
    (hStep : localPrimeStepLogVolume ≠ 0)
    (hExponent : exponent₁ ≠ exponent₂)
    (hmem₁ :
      (data.toLocalFrobenioidLogVolumeAmbiguity
        exponent₁ localPrimeStepLogVolume).shiftedLogVolume ∈ collapsedRegion)
    (hmem₂ :
      (data.toLocalFrobenioidLogVolumeAmbiguity
        exponent₂ localPrimeStepLogVolume).shiftedLogVolume ∈ collapsedRegion) :
    let local₁ :=
      data.toLocalFrobenioidLogVolumeAmbiguity
        exponent₁ localPrimeStepLogVolume;
    let local₂ :=
      data.toLocalFrobenioidLogVolumeAmbiguity
        exponent₂ localPrimeStepLogVolume;
    IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion local₁.shiftedLogVolume =
      IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion local₂.shiftedLogVolume ∧
      local₁.shiftedLogVolume ≠ local₂.shiftedLogVolume := by
  intro local₁ local₂
  have hmap :
      IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion local₁.shiftedLogVolume =
        IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion local₂.shiftedLogVolume :=
    IUTStage1UpperSemiSetQuotient.quotientMap_eq_of_mem
      (by simpa [local₁] using hmem₁)
      (by simpa [local₂] using hmem₂)
  have hshift_iff :=
    data.thetaFinite_localFrobenioidShift_eq_iff_exponent_eq_of_step_nonzero
      exponent₁ exponent₂ localPrimeStepLogVolume hStep
  exact
    ⟨hmap, fun hshift =>
      hExponent (hshift_iff.mp hshift)⟩

theorem ofZModCuspLabelLogVolumeCompatibilities_q_mem_upperRay
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant
    data.qPilotLogVolume ∈
      data.toHullDetPilotUpperRayLogVolume.upperRay := by
  intro data
  exact data.toUpperRay_q_mem

theorem ofZModCuspLabelLogVolumeCompatibilities_thetaFiniteEndpoint
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant;
    let endpoint := data.toThetaFiniteLogVolumeEndpoint;
    endpoint.thetaExtended.IsFinite ∧
      endpoint.thetaExtended ≠
        IUTStage1ExtendedSignedLogVolume.plusInfinity ∧
      endpoint.thetaRealLogVolume = thetaHullLogVolume ∧
      endpoint.upperRayData.qPilotLogVolume <=
        endpoint.thetaRealLogVolume := by
  intro data endpoint
  exact data.thetaFiniteLogVolumeEndpoint

theorem ofZModCuspLabelLogVolumeCompatibilities_thetaFinite_tensorPower_warning
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume)
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower)
    (theta_neg : thetaHullLogVolume < 0) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant;
    let finite := data.toThetaFiniteLogVolumeEndpoint;
    let tensor :=
      data.toThetaPilotTensorPowerLogVolume
        tensorPower tensor_power_ge_two;
    tensor.tensorPowerLogVolume < finite.thetaRealLogVolume ∧
      tensor.tensorPowerUpperRay ⊆ finite.upperRayData.upperRay ∧
      finite.thetaRealLogVolume ∉ tensor.tensorPowerUpperRay := by
  intro data finite tensor
  exact data.thetaFinite_tensorPower_warning
    tensorPower tensor_power_ge_two theta_neg

def toQPilotTwoComputationLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    IUTStage1QPilotTwoComputationLogVolume :=
  { upperRayData := data.toHullDetPilotUpperRayLogVolume,
    inputPrimeStripLogVolume :=
      data.corridor.beforeIndeterminacy.averageLogVolume,
    outputHullLogVolume := data.qPilotLogVolume,
    input_eq_q := data.q_eq_beforeAverage.symm,
    output_eq_q := rfl }

theorem twoComputation_input_eq_beforeAverage
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    data.toQPilotTwoComputationLogVolume.inputPrimeStripLogVolume =
      data.corridor.beforeIndeterminacy.averageLogVolume :=
  rfl

theorem twoComputation_output_eq_qPilotLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    data.toQPilotTwoComputationLogVolume.outputHullLogVolume =
      data.qPilotLogVolume :=
  rfl

theorem twoComputation_input_eq_output
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    data.toQPilotTwoComputationLogVolume.inputPrimeStripLogVolume =
      data.toQPilotTwoComputationLogVolume.outputHullLogVolume :=
  data.toQPilotTwoComputationLogVolume.input_eq_output

theorem beforeAverage_eq_twoComputation_output
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    data.corridor.beforeIndeterminacy.averageLogVolume =
      data.toQPilotTwoComputationLogVolume.outputHullLogVolume := by
  rw [← data.twoComputation_input_eq_beforeAverage]
  exact data.twoComputation_input_eq_output

theorem twoComputation_input_le_theta
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    data.toQPilotTwoComputationLogVolume.inputPrimeStripLogVolume <=
      data.toQPilotTwoComputationLogVolume.upperRayData.thetaHullLogVolume :=
  data.toQPilotTwoComputationLogVolume.input_le_thetaHullLogVolume

theorem twoComputation_output_le_theta
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    data.toQPilotTwoComputationLogVolume.outputHullLogVolume <=
      data.toQPilotTwoComputationLogVolume.upperRayData.thetaHullLogVolume :=
  data.toQPilotTwoComputationLogVolume.output_le_thetaHullLogVolume

/--
Source-facing Ob8/Ob9 calibration for the Step (xi-g) handoff.

The log-Kummer correspondence may introduce vertical-shift ambiguity on the
local Frobenioid side.  The global realified Frobenioid calibration selects the
unshifted hull log-volume used as the upper-ray boundary, and the q-pilot
two-computation value remains bounded by this calibrated value.
-/
structure LogKummerVerticalShiftCalibration
    (data : IUTStage1StepXToHullUpperRayLogVolume label) where
  localExponent : Int
  localPrimeStepLogVolume : Real

namespace LogKummerVerticalShiftCalibration

def localData
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (calibration : LogKummerVerticalShiftCalibration data) :
    IUTStage1LocalFrobenioidLogVolumeAmbiguity :=
  data.toLocalFrobenioidLogVolumeAmbiguity
    calibration.localExponent calibration.localPrimeStepLogVolume

def globalData
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (calibration : LogKummerVerticalShiftCalibration data) :
    IUTStage1GlobalFrobenioidLogVolumeCalibration :=
  data.toGlobalFrobenioidLogVolumeCalibration
    calibration.localExponent calibration.localPrimeStepLogVolume

theorem calibratedLogVolume_eq_thetaReal
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (calibration : LogKummerVerticalShiftCalibration data) :
    calibration.globalData.calibratedLogVolume =
      data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume :=
  rfl

theorem calibratedLogVolume_eq_thetaHull
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (calibration : LogKummerVerticalShiftCalibration data) :
    calibration.globalData.calibratedLogVolume =
      data.thetaHullLogVolume := by
  exact
    calibration.calibratedLogVolume_eq_thetaReal.trans
      data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume_eq_hull

theorem qPilotLogVolume_le_calibrated
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (calibration : LogKummerVerticalShiftCalibration data) :
    data.qPilotLogVolume <= calibration.globalData.calibratedLogVolume := by
  rw [calibration.calibratedLogVolume_eq_thetaHull]
  exact data.qPilotLogVolume_le_thetaHullLogVolume

theorem twoComputation_input_le_calibrated
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (calibration : LogKummerVerticalShiftCalibration data) :
    data.toQPilotTwoComputationLogVolume.inputPrimeStripLogVolume <=
      calibration.globalData.calibratedLogVolume := by
  rw [calibration.calibratedLogVolume_eq_thetaHull]
  exact data.twoComputation_input_le_theta

theorem twoComputation_output_le_calibrated
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (calibration : LogKummerVerticalShiftCalibration data) :
    data.toQPilotTwoComputationLogVolume.outputHullLogVolume <=
      calibration.globalData.calibratedLogVolume := by
  rw [calibration.calibratedLogVolume_eq_thetaHull]
  exact data.twoComputation_output_le_theta

theorem calibrated_eq_shifted_iff_shiftTerm_zero
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (calibration : LogKummerVerticalShiftCalibration data) :
    calibration.globalData.calibratedLogVolume =
        calibration.localData.shiftedLogVolume ↔
      (calibration.localExponent : Real) *
        calibration.localPrimeStepLogVolume = 0 := by
  exact
    calibration.globalData.calibratedLogVolume_eq_shifted_iff_shiftTerm_eq_zero

theorem calibrated_eq_shifted_iff_exponent_zero_or_step_zero
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (calibration : LogKummerVerticalShiftCalibration data) :
    calibration.globalData.calibratedLogVolume =
        calibration.localData.shiftedLogVolume ↔
      calibration.localExponent = 0 ∨
        calibration.localPrimeStepLogVolume = 0 := by
  exact
    calibration.globalData
      |>.calibratedLogVolume_eq_shifted_iff_exponent_zero_or_step_zero

theorem calibrated_ne_shifted_of_nonzero_shift
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (calibration : LogKummerVerticalShiftCalibration data)
    (hExponent : calibration.localExponent ≠ 0)
    (hStep : calibration.localPrimeStepLogVolume ≠ 0) :
    calibration.globalData.calibratedLogVolume ≠
      calibration.localData.shiftedLogVolume :=
  calibration.globalData.calibratedLogVolume_ne_shifted_of_local_nonzero
    hExponent hStep

theorem endpoint
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (calibration : LogKummerVerticalShiftCalibration data) :
    calibration.globalData.calibratedLogVolume =
        data.thetaHullLogVolume ∧
      data.qPilotLogVolume <= calibration.globalData.calibratedLogVolume ∧
      data.toQPilotTwoComputationLogVolume.inputPrimeStripLogVolume <=
        calibration.globalData.calibratedLogVolume ∧
      data.toQPilotTwoComputationLogVolume.outputHullLogVolume <=
        calibration.globalData.calibratedLogVolume ∧
      (calibration.globalData.calibratedLogVolume =
          calibration.localData.shiftedLogVolume ↔
        calibration.localExponent = 0 ∨
          calibration.localPrimeStepLogVolume = 0) :=
  ⟨calibration.calibratedLogVolume_eq_thetaHull,
    calibration.qPilotLogVolume_le_calibrated,
    calibration.twoComputation_input_le_calibrated,
    calibration.twoComputation_output_le_calibrated,
    calibration.calibrated_eq_shifted_iff_exponent_zero_or_step_zero⟩

end LogKummerVerticalShiftCalibration

/--
Finite cQ3/cQ4 closed-loop guard for Remark 3.9.5(ix).

The source-paper assertion is not that passing to log-volumes alone preserves
the `F^{×μ}`-prime-strip data.  Rather, the hull/determinant passage (cQ3)
and the log-Kummer vertical-shift adjustment (cQ4) must be traversed before
the log-volume quotient (sQ5).  At the present finite log-volume level, this
record ties the cQ3 hull/determinant value and the cQ4 calibrated value to the
same Step (xi) upper-ray boundary.
-/
structure CQ3CQ4ClosedLoopGuard
    (data : IUTStage1StepXToHullUpperRayLogVolume label) where
  calibration : LogKummerVerticalShiftCalibration data
  cq3HullDetLogVolume : Real
  cq3_eq_thetaHull :
    cq3HullDetLogVolume = data.thetaHullLogVolume
  cq4CalibratedLogVolume : Real
  cq4_eq_calibrated :
    cq4CalibratedLogVolume = calibration.globalData.calibratedLogVolume

namespace CQ3CQ4ClosedLoopGuard

theorem cq3_eq_cq4
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (guard : CQ3CQ4ClosedLoopGuard data) :
    guard.cq3HullDetLogVolume = guard.cq4CalibratedLogVolume := by
  calc
    guard.cq3HullDetLogVolume = data.thetaHullLogVolume :=
      guard.cq3_eq_thetaHull
    _ = guard.calibration.globalData.calibratedLogVolume :=
      guard.calibration.calibratedLogVolume_eq_thetaHull.symm
    _ = guard.cq4CalibratedLogVolume :=
      guard.cq4_eq_calibrated.symm

theorem qPilotLogVolume_le_cq3
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (guard : CQ3CQ4ClosedLoopGuard data) :
    data.qPilotLogVolume <= guard.cq3HullDetLogVolume := by
  rw [guard.cq3_eq_thetaHull]
  exact data.qPilotLogVolume_le_thetaHullLogVolume

theorem twoComputation_input_le_cq4
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (guard : CQ3CQ4ClosedLoopGuard data) :
    data.toQPilotTwoComputationLogVolume.inputPrimeStripLogVolume <=
      guard.cq4CalibratedLogVolume := by
  rw [guard.cq4_eq_calibrated]
  exact guard.calibration.twoComputation_input_le_calibrated

theorem twoComputation_output_le_cq4
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (guard : CQ3CQ4ClosedLoopGuard data) :
    data.toQPilotTwoComputationLogVolume.outputHullLogVolume <=
      guard.cq4CalibratedLogVolume := by
  rw [guard.cq4_eq_calibrated]
  exact guard.calibration.twoComputation_output_le_calibrated

theorem shiftedLocal_eq_cq4_iff_exponent_zero_or_step_zero
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (guard : CQ3CQ4ClosedLoopGuard data) :
    guard.calibration.localData.shiftedLogVolume =
        guard.cq4CalibratedLogVolume ↔
      guard.calibration.localExponent = 0 ∨
        guard.calibration.localPrimeStepLogVolume = 0 := by
  rw [guard.cq4_eq_calibrated]
  rw [eq_comm]
  exact
    guard.calibration.calibrated_eq_shifted_iff_exponent_zero_or_step_zero

theorem endpoint
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (guard : CQ3CQ4ClosedLoopGuard data) :
    guard.cq3HullDetLogVolume = guard.cq4CalibratedLogVolume ∧
      data.qPilotLogVolume <= guard.cq3HullDetLogVolume ∧
      data.toQPilotTwoComputationLogVolume.inputPrimeStripLogVolume <=
        guard.cq4CalibratedLogVolume ∧
      data.toQPilotTwoComputationLogVolume.outputHullLogVolume <=
        guard.cq4CalibratedLogVolume ∧
      (guard.calibration.localData.shiftedLogVolume =
          guard.cq4CalibratedLogVolume ↔
        guard.calibration.localExponent = 0 ∨
          guard.calibration.localPrimeStepLogVolume = 0) :=
  ⟨guard.cq3_eq_cq4,
    guard.qPilotLogVolume_le_cq3,
    guard.twoComputation_input_le_cq4,
    guard.twoComputation_output_le_cq4,
    guard.shiftedLocal_eq_cq4_iff_exponent_zero_or_step_zero⟩

end CQ3CQ4ClosedLoopGuard

/--
cQ3/cQ4 closed-loop guard backed by a finite local-global Frobenioid collection.

The preceding closed-loop guard identifies the cQ3 hull/determinant boundary
with the cQ4 calibrated log-Kummer boundary.  This refinement records that the
cQ3 boundary is the global realified log-volume of a finite local-global
Frobenioid collection in the sense of Remark 3.9.5(ix)'s local-global
collection discussion.
-/
structure CQ3CQ4LocalGlobalClosedLoopGuard
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (V : Type u) [Fintype V] where
  guard : CQ3CQ4ClosedLoopGuard data
  collection : IUTStage1LocalGlobalRealifiedFrobenioidCollection V
  global_eq_cq3 :
    collection.globalObject.realifiedLogVolume = guard.cq3HullDetLogVolume

namespace CQ3CQ4LocalGlobalClosedLoopGuard

variable {V : Type u} [Fintype V]

theorem localScaled_eq_cq3
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (backed : CQ3CQ4LocalGlobalClosedLoopGuard data V)
    (v : V) :
    ((backed.collection.localization v).extensionDegree : Real) *
        (backed.collection.localObject v).realifiedLogVolume =
      backed.guard.cq3HullDetLogVolume := by
  rw [backed.collection.extensionDegree_mul_localRealifiedLogVolume v]
  exact backed.global_eq_cq3

theorem localScaled_eq_cq4
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (backed : CQ3CQ4LocalGlobalClosedLoopGuard data V)
    (v : V) :
    ((backed.collection.localization v).extensionDegree : Real) *
        (backed.collection.localObject v).realifiedLogVolume =
      backed.guard.cq4CalibratedLogVolume := by
  exact (backed.localScaled_eq_cq3 v).trans backed.guard.cq3_eq_cq4

theorem qPilotLogVolume_le_global
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (backed : CQ3CQ4LocalGlobalClosedLoopGuard data V) :
    data.qPilotLogVolume <=
      backed.collection.globalObject.realifiedLogVolume := by
  rw [backed.global_eq_cq3]
  exact backed.guard.qPilotLogVolume_le_cq3

theorem localGlobalClosedLoop_endpoint
    {data : IUTStage1StepXToHullUpperRayLogVolume label}
    (backed : CQ3CQ4LocalGlobalClosedLoopGuard data V) :
    (∀ v : V,
      ((backed.collection.localization v).extensionDegree : Real) *
          (backed.collection.localObject v).realifiedLogVolume =
        backed.guard.cq3HullDetLogVolume ∧
      ((backed.collection.localization v).extensionDegree : Real) *
          (backed.collection.localObject v).realifiedLogVolume =
        backed.guard.cq4CalibratedLogVolume) ∧
      backed.guard.cq3HullDetLogVolume =
        backed.guard.cq4CalibratedLogVolume ∧
      data.qPilotLogVolume <=
        backed.collection.globalObject.realifiedLogVolume :=
  ⟨fun v => ⟨backed.localScaled_eq_cq3 v, backed.localScaled_eq_cq4 v⟩,
    backed.guard.cq3_eq_cq4,
    backed.qPilotLogVolume_le_global⟩

end CQ3CQ4LocalGlobalClosedLoopGuard

theorem twoComputation_determinant_endpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    twoComputation.inputPrimeStripLogVolume =
        data.corridor.beforeIndeterminacy.averageLogVolume ∧
      twoComputation.outputHullLogVolume = data.qPilotLogVolume ∧
      twoComputation.inputPrimeStripLogVolume =
        twoComputation.outputHullLogVolume ∧
      twoComputation.inputPrimeStripLogVolume <=
        data.determinant.determinantLogVolume ∧
      twoComputation.outputHullLogVolume <=
        data.determinant.determinantLogVolume ∧
      twoComputation.inputPrimeStripLogVolume <=
        data.determinant.tensorPowerLogVolume /
          (data.determinant.positiveTensorPower : Real) ∧
      twoComputation.outputHullLogVolume <=
        data.determinant.tensorPowerLogVolume /
          (data.determinant.positiveTensorPower : Real) := by
  intro twoComputation
  exact
    ⟨rfl, rfl, data.twoComputation_input_eq_output,
      by
        simpa [toQPilotTwoComputationLogVolume,
          toHullDetPilotUpperRayLogVolume] using
          twoComputation.input_le_determinant,
      by
        simpa [toQPilotTwoComputationLogVolume,
          toHullDetPilotUpperRayLogVolume] using
          twoComputation.output_le_determinant,
      by
        rw [twoComputation.input_eq_q]
        simpa [toQPilotTwoComputationLogVolume,
          toHullDetPilotUpperRayLogVolume] using
          data.qPilotLogVolume_le_tensorPowerLogVolume_div,
      by
        rw [twoComputation.output_eq_q]
        simpa [toQPilotTwoComputationLogVolume,
          toHullDetPilotUpperRayLogVolume] using
          data.qPilotLogVolume_le_tensorPowerLogVolume_div⟩

theorem twoComputation_determinantEqualityRequiresReverseBounds
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    (twoComputation.inputPrimeStripLogVolume =
        data.determinant.determinantLogVolume ↔
      data.determinant.determinantLogVolume <=
        twoComputation.inputPrimeStripLogVolume) ∧
      (twoComputation.outputHullLogVolume =
          data.determinant.determinantLogVolume ↔
        data.determinant.determinantLogVolume <=
          twoComputation.outputHullLogVolume) := by
  intro twoComputation
  exact
    ⟨by
      simpa [toQPilotTwoComputationLogVolume,
        toHullDetPilotUpperRayLogVolume] using
        twoComputation.input_eq_determinant_iff_reverse_bound,
    by
      simpa [toQPilotTwoComputationLogVolume,
        toHullDetPilotUpperRayLogVolume] using
        twoComputation.output_eq_determinant_iff_reverse_bound⟩

theorem twoComputation_fig38_endpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    twoComputation.inputPrimeStripLogVolume =
        data.corridor.beforeIndeterminacy.averageLogVolume ∧
      twoComputation.outputHullLogVolume = data.qPilotLogVolume ∧
      twoComputation.inputPrimeStripLogVolume =
        twoComputation.outputHullLogVolume ∧
      twoComputation.inputPrimeStripLogVolume <= data.thetaHullLogVolume ∧
      twoComputation.outputHullLogVolume <= data.thetaHullLogVolume ∧
      twoComputation.outputHullLogVolume ∈
        data.toHullDetPilotUpperRayLogVolume.upperRay := by
  intro twoComputation
  exact
    ⟨rfl, rfl, data.twoComputation_input_eq_output,
      by
        simpa [toQPilotTwoComputationLogVolume,
          toHullDetPilotUpperRayLogVolume] using
          data.twoComputation_input_le_theta,
      by
        simpa [toQPilotTwoComputationLogVolume,
          toHullDetPilotUpperRayLogVolume] using
          data.twoComputation_output_le_theta,
      by
        simpa [toQPilotTwoComputationLogVolume] using
          data.toUpperRay_q_mem⟩

def toQPilotTwoComputationSignedEndpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume) :
    IUTStage1QPilotTwoComputationSignedEndpoint :=
  { twoComputation := data.toQPilotTwoComputationLogVolume,
    q_pilot_positive := q_pilot_positive }

theorem signedEndpoint_corollary312
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume) :
    let endpoint :=
      data.toQPilotTwoComputationSignedEndpoint q_pilot_positive;
    Corollary312Inequality
      endpoint.comparisonData.thetaPilot
      endpoint.comparisonData.qPilot := by
  intro endpoint
  exact endpoint.corollary312

theorem signedEndpoint_corollary312_magnitudes
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume) :
    let endpoint :=
      data.toQPilotTwoComputationSignedEndpoint q_pilot_positive;
    endpoint.comparisonData.qPilot.value =
        -data.corridor.beforeIndeterminacy.averageLogVolume ∧
      endpoint.comparisonData.thetaPilot.value =
        -data.thetaHullLogVolume ∧
      Corollary312Inequality
        endpoint.comparisonData.thetaPilot
        endpoint.comparisonData.qPilot := by
  intro endpoint
  exact ⟨rfl, rfl, endpoint.corollary312⟩

theorem thetaFinite_signedEndpoint_agree
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume) :
    let finite := data.toThetaFiniteLogVolumeEndpoint;
    let signed := data.toQPilotTwoComputationSignedEndpoint q_pilot_positive;
    signed.comparisonData.qSigned = finite.upperRayData.qPilotLogVolume ∧
      signed.comparisonData.thetaSigned = finite.thetaRealLogVolume ∧
      finite.upperRayData.qPilotLogVolume <= finite.thetaRealLogVolume ∧
      Corollary312Inequality
        signed.comparisonData.thetaPilot
        signed.comparisonData.qPilot := by
  intro finite signed
  exact
    ⟨by
      simpa [IUTStage1QPilotTwoComputationSignedEndpoint.comparisonData]
        using data.q_eq_beforeAverage.symm,
    by
      simpa [IUTStage1QPilotTwoComputationSignedEndpoint.comparisonData]
        using finite.thetaRealLogVolume_eq_hull.symm,
    finite.qPilotLogVolume_le_thetaRealLogVolume,
    signed.corollary312⟩

theorem thetaFinite_signedEndpoint_agree_with_distinctIntertwining
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (transport : IUTStage1DistinctLabelIntertwiningTransport)
    (hq : transport.qIntertwining) :
    let finite := data.toThetaFiniteLogVolumeEndpoint;
    let signed := data.toQPilotTwoComputationSignedEndpoint q_pilot_positive;
    signed.comparisonData.qSigned = finite.upperRayData.qPilotLogVolume ∧
      signed.comparisonData.thetaSigned = finite.thetaRealLogVolume ∧
      Corollary312Inequality
        signed.comparisonData.thetaPilot
        signed.comparisonData.qPilot ∧
      transport.qLabel ≠ transport.thetaLabel ∧
      transport.weakenedPrimeStripCannotDistinguishPilots ∧
      transport.qIntertwining ∧
      transport.thetaIntertwiningUpToIndeterminacy := by
  intro finite signed
  have hagree :=
    data.thetaFinite_signedEndpoint_agree q_pilot_positive
  exact
    ⟨hagree.1, hagree.2.1, hagree.2.2.2,
      transport.labels_distinct,
      transport.weakenedPrimeStripCondition,
      hq, transport.theta_from_q hq⟩

def toRemark3122IntertwiningUpperRayBound
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (h epsilon : Real)
    (h_pos : 0 < h)
    (epsilon_pos : 0 < epsilon)
    (q_eq_neg_h : data.qPilotLogVolume = -h)
    (theta_eq_neg_two_h_add_epsilon :
      data.thetaHullLogVolume = -2 * h + epsilon) :
    IUTStage1Remark3122IntertwiningUpperRayBound :=
  { h := h,
    epsilon := epsilon,
    h_pos := h_pos,
    epsilon_pos := epsilon_pos,
    qAssignment :=
      data.toThetaFiniteLogVolumeEndpoint.upperRayData.qPilotLogVolume,
    thetaUpperRayBound :=
      data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume,
    q_assignment_eq_neg_h := by
      simpa [toThetaFiniteLogVolumeEndpoint] using q_eq_neg_h,
    theta_upperRay_bound_eq := by
      rw [data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume_eq_hull]
      simpa [toThetaFiniteLogVolumeEndpoint] using
        theta_eq_neg_two_h_add_epsilon,
    q_assignment_mem_theta_upperRay :=
      data.toThetaFiniteLogVolumeEndpoint.qPilotLogVolume_le_thetaRealLogVolume }

theorem remark3122UpperRayBound_fromThetaFinite
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (h epsilon : Real)
    (h_pos : 0 < h)
    (epsilon_pos : 0 < epsilon)
    (q_eq_neg_h : data.qPilotLogVolume = -h)
    (theta_eq_neg_two_h_add_epsilon :
      data.thetaHullLogVolume = -2 * h + epsilon) :
    let toy :=
      data.toRemark3122IntertwiningUpperRayBound h epsilon h_pos
        epsilon_pos q_eq_neg_h theta_eq_neg_two_h_add_epsilon;
    toy.qAssignment ∈ toy.thetaUpperRay ∧
      (-h : Real) <= -2 * h + epsilon ∧
      h <= epsilon := by
  intro toy
  exact toy.ftoy_upper_ray_endpoint

theorem ofZModCuspLabelLogVolumeCompatibilities_signedEndpointCorollary312
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume)
    (q_pilot_positive :
      0 < -before.toLabelAveraged.averageLogVolume) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant;
    let endpoint :=
      data.toQPilotTwoComputationSignedEndpoint q_pilot_positive;
    Corollary312Inequality
      endpoint.comparisonData.thetaPilot
      endpoint.comparisonData.qPilot := by
  intro data endpoint
  exact data.signedEndpoint_corollary312 q_pilot_positive

theorem ofZModCuspLabelLogVolumeCompatibilities_signedEndpointCorollary312_magnitudes
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume)
    (q_pilot_positive :
      0 < -before.toLabelAveraged.averageLogVolume) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant;
    let endpoint :=
      data.toQPilotTwoComputationSignedEndpoint q_pilot_positive;
    endpoint.comparisonData.qPilot.value =
        -before.toLabelAveraged.averageLogVolume ∧
      endpoint.comparisonData.thetaPilot.value =
        -thetaHullLogVolume ∧
      Corollary312Inequality
        endpoint.comparisonData.thetaPilot
        endpoint.comparisonData.qPilot := by
  intro data endpoint
  exact data.signedEndpoint_corollary312_magnitudes q_pilot_positive

theorem ofZModCuspLabelLogVolumeCompatibilities_thetaFinite_signedEndpoint_agree
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume)
    (q_pilot_positive :
      0 < -before.toLabelAveraged.averageLogVolume) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant;
    let finite := data.toThetaFiniteLogVolumeEndpoint;
    let signed := data.toQPilotTwoComputationSignedEndpoint q_pilot_positive;
    signed.comparisonData.qSigned = finite.upperRayData.qPilotLogVolume ∧
      signed.comparisonData.thetaSigned = finite.thetaRealLogVolume ∧
      finite.upperRayData.qPilotLogVolume <= finite.thetaRealLogVolume ∧
      Corollary312Inequality
        signed.comparisonData.thetaPilot
        signed.comparisonData.qPilot := by
  intro data finite signed
  exact data.thetaFinite_signedEndpoint_agree q_pilot_positive

def toQPilotTwoComputationCThetaEndpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    IUTStage1QPilotTwoComputationCThetaEndpoint :=
  { signedEndpoint :=
      data.toQPilotTwoComputationSignedEndpoint q_pilot_positive,
    cTheta := cTheta,
    thetaHullLogVolume_le_cTheta_absLogQ :=
      thetaHull_le_cTheta_absLogQ }

def toQLambdaCThetaBound
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (lambda : Rat)
    (lambda_pos : 0 < lambda)
    (cTheta : Real)
    (qLambda_le_thetaHull :
      -((lambda : Real) *
        (-data.corridor.beforeIndeterminacy.averageLogVolume)) <=
        data.thetaHullLogVolume)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    IUTStage1Corollary312QLambdaCThetaBoundShadow :=
  { lambda := lambda,
    lambda_pos := lambda_pos,
    absLogQ := -data.corridor.beforeIndeterminacy.averageLogVolume,
    absLogQ_pos := q_pilot_positive,
    qLambdaSigned :=
      -((lambda : Real) *
        (-data.corridor.beforeIndeterminacy.averageLogVolume)),
    thetaSigned := data.thetaHullLogVolume,
    cTheta := cTheta,
    qLambdaSigned_eq_neg_lambda_absLogQ := rfl,
    qLambdaSigned_le_thetaSigned := qLambda_le_thetaHull,
    thetaSigned_le_cTheta_absLogQ := thetaHull_le_cTheta_absLogQ }

theorem qLambdaCTheta_endpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (lambda : Rat)
    (lambda_pos : 0 < lambda)
    (cTheta : Real)
    (qLambda_le_thetaHull :
      -((lambda : Real) *
        (-data.corridor.beforeIndeterminacy.averageLogVolume)) <=
        data.thetaHullLogVolume)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    let endpoint :=
      data.toQLambdaCThetaBound q_pilot_positive lambda lambda_pos cTheta
        qLambda_le_thetaHull thetaHull_le_cTheta_absLogQ;
    endpoint.qLambdaSigned =
        -((lambda : Real) *
          (-data.corridor.beforeIndeterminacy.averageLogVolume)) ∧
      endpoint.thetaSigned = data.thetaHullLogVolume ∧
      -((lambda : Real)) <= endpoint.cTheta ∧
      (lambda <= 1 → (-1 : Real) <= endpoint.cTheta) ∧
      (lambda < 1 → (-1 : Real) < endpoint.cTheta) := by
  intro endpoint
  exact
    ⟨rfl, rfl, endpoint.cTheta_ge_neg_lambda,
      endpoint.standard_bound_of_lambda_le_one,
      endpoint.strict_standard_bound_of_lambda_lt_one⟩

theorem qLambdaCTheta_boundary_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (lambda : Rat)
    (lambda_pos : 0 < lambda)
    (cTheta : Real)
    (qLambda_le_thetaHull :
      -((lambda : Real) *
        (-data.corridor.beforeIndeterminacy.averageLogVolume)) <=
        data.thetaHullLogVolume)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    cTheta = -((lambda : Real)) ∨ -((lambda : Real)) < cTheta :=
  (data.toQLambdaCThetaBound q_pilot_positive lambda lambda_pos cTheta
    qLambda_le_thetaHull thetaHull_le_cTheta_absLogQ)
      |>.cTheta_eq_neg_lambda_or_gt_neg_lambda

def toStandardQLambdaCThetaBound
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    IUTStage1Corollary312QLambdaCThetaBoundShadow :=
  data.toQLambdaCThetaBound q_pilot_positive 1 (by norm_num) cTheta
    (by
      simpa [data.q_eq_beforeAverage] using
        data.qPilotLogVolume_le_thetaHullLogVolume)
    thetaHull_le_cTheta_absLogQ

theorem standardQLambdaCTheta_endpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (data.toStandardQLambdaCThetaBound
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ).qLambdaSigned =
        data.qPilotLogVolume ∧
      (data.toStandardQLambdaCThetaBound
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ).thetaSigned =
        data.thetaHullLogVolume ∧
      (-1 : Real) <=
        (data.toStandardQLambdaCThetaBound
          q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ).cTheta := by
  exact
    ⟨by
      simp [toStandardQLambdaCThetaBound, toQLambdaCThetaBound,
        data.q_eq_beforeAverage],
    rfl,
    (data.toStandardQLambdaCThetaBound
      q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).standard_bound_of_lambda_le_one
      (by
        change (1 : Rat) <= 1
        norm_num)⟩

theorem standardQLambdaCTheta_strict_of_qPilot_lt_thetaHullLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hstrict : data.qPilotLogVolume < data.thetaHullLogVolume) :
    (-1 : Real) < cTheta := by
  have hstrict_before :
      data.corridor.beforeIndeterminacy.averageLogVolume <
        data.thetaHullLogVolume := by
    rw [← data.q_eq_beforeAverage]
    exact hstrict
  have h :=
    (data.toStandardQLambdaCThetaBound
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ)
        |>.cTheta_gt_neg_lambda_of_qLambda_lt_theta
          (by
            simpa [toStandardQLambdaCThetaBound, toQLambdaCThetaBound]
              using hstrict_before)
  simpa [toStandardQLambdaCThetaBound, toQLambdaCThetaBound] using h

theorem standardQLambdaCTheta_strict_of_qPilot_lt_determinantLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hstrict : data.qPilotLogVolume < data.determinant.determinantLogVolume) :
    (-1 : Real) < cTheta := by
  apply data.standardQLambdaCTheta_strict_of_qPilot_lt_thetaHullLogVolume
    q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
  simpa [data.thetaHullLogVolume_eq_determinantLogVolume] using hstrict

theorem standardQLambdaCTheta_strict_of_twoComputationInput_lt_determinantLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hstrict :
      data.toQPilotTwoComputationLogVolume.inputPrimeStripLogVolume <
        data.determinant.determinantLogVolume) :
    (-1 : Real) < cTheta := by
  apply data.standardQLambdaCTheta_strict_of_qPilot_lt_determinantLogVolume
    q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
  simpa [toQPilotTwoComputationLogVolume, data.q_eq_beforeAverage] using hstrict

theorem standardQLambdaCTheta_strict_of_twoComputationOutput_lt_determinantLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hstrict :
      data.toQPilotTwoComputationLogVolume.outputHullLogVolume <
        data.determinant.determinantLogVolume) :
    (-1 : Real) < cTheta := by
  apply data.standardQLambdaCTheta_strict_of_qPilot_lt_determinantLogVolume
    q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
  simpa [toQPilotTwoComputationLogVolume] using hstrict

theorem standardQLambdaCTheta_strict_of_qPilot_mem_tensorPowerUpperRay
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower)
    (theta_neg : data.thetaHullLogVolume < 0)
    (hmem :
      data.toThetaFiniteLogVolumeEndpoint.upperRayData.qPilotLogVolume ∈
        (data.toThetaPilotTensorPowerLogVolume
          tensorPower tensor_power_ge_two).tensorPowerUpperRay) :
    (-1 : Real) < cTheta := by
  have hstrict :=
    data.thetaFinite_qPilot_lt_thetaRealLogVolume_of_mem_tensorPowerUpperRay
      tensorPower tensor_power_ge_two theta_neg hmem
  apply data.standardQLambdaCTheta_strict_of_qPilot_lt_thetaHullLogVolume
    q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
  simpa [toThetaFiniteLogVolumeEndpoint, toHullDetPilotUpperRayLogVolume]
    using hstrict

theorem standardQLambdaCTheta_not_qPilot_mem_tensorPowerUpperRay_of_boundary
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower)
    (theta_neg : data.thetaHullLogVolume < 0)
    (hC : cTheta = (-1 : Real)) :
    data.toThetaFiniteLogVolumeEndpoint.upperRayData.qPilotLogVolume ∉
      (data.toThetaPilotTensorPowerLogVolume
        tensorPower tensor_power_ge_two).tensorPowerUpperRay := by
  intro hmem
  have hstrict :
      (-1 : Real) < cTheta :=
    data.standardQLambdaCTheta_strict_of_qPilot_mem_tensorPowerUpperRay
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
      tensorPower tensor_power_ge_two theta_neg hmem
  rw [hC] at hstrict
  norm_num at hstrict

theorem standardQLambdaCTheta_strict_of_twoComputation_mem_tensorPowerUpperRay
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower)
    (theta_neg : data.thetaHullLogVolume < 0) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    (twoComputation.inputPrimeStripLogVolume ∈
        (data.toThetaPilotTensorPowerLogVolume
          tensorPower tensor_power_ge_two).tensorPowerUpperRay →
        (-1 : Real) < cTheta) ∧
      (twoComputation.outputHullLogVolume ∈
        (data.toThetaPilotTensorPowerLogVolume
          tensorPower tensor_power_ge_two).tensorPowerUpperRay →
        (-1 : Real) < cTheta) := by
  intro twoComputation
  have hendpointq :
      data.toThetaFiniteLogVolumeEndpoint.upperRayData.qPilotLogVolume =
        data.qPilotLogVolume := by
    rfl
  exact
    ⟨by
      intro hmem
      apply data.standardQLambdaCTheta_strict_of_qPilot_mem_tensorPowerUpperRay
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
        tensorPower tensor_power_ge_two theta_neg
      rw [hendpointq, data.q_eq_beforeAverage]
      simpa [twoComputation, toQPilotTwoComputationLogVolume] using hmem,
    by
      intro hmem
      apply data.standardQLambdaCTheta_strict_of_qPilot_mem_tensorPowerUpperRay
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
        tensorPower tensor_power_ge_two theta_neg
      rw [hendpointq]
      simpa [twoComputation, toQPilotTwoComputationLogVolume] using hmem⟩

theorem standardQLambdaCTheta_not_twoComputation_mem_tensorPowerUpperRay_of_boundary
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower)
    (theta_neg : data.thetaHullLogVolume < 0)
    (hC : cTheta = (-1 : Real)) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    twoComputation.inputPrimeStripLogVolume ∉
        (data.toThetaPilotTensorPowerLogVolume
          tensorPower tensor_power_ge_two).tensorPowerUpperRay ∧
      twoComputation.outputHullLogVolume ∉
        (data.toThetaPilotTensorPowerLogVolume
          tensorPower tensor_power_ge_two).tensorPowerUpperRay := by
  intro twoComputation
  have hnot :=
    data.standardQLambdaCTheta_not_qPilot_mem_tensorPowerUpperRay_of_boundary
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
      tensorPower tensor_power_ge_two theta_neg hC
  have hendpointq :
      data.toThetaFiniteLogVolumeEndpoint.upperRayData.qPilotLogVolume =
        data.qPilotLogVolume := by
    rfl
  exact
    ⟨by
      intro hmem
      exact hnot (by
        rw [hendpointq, data.q_eq_beforeAverage]
        simpa [twoComputation, toQPilotTwoComputationLogVolume] using hmem),
    by
      intro hmem
      exact hnot (by
        rw [hendpointq]
        simpa [twoComputation, toQPilotTwoComputationLogVolume] using hmem)⟩

theorem standardQLambdaCTheta_tensorPowerBoundary_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower)
    (theta_neg : data.thetaHullLogVolume < 0) :
    (cTheta = (-1 : Real) ∧
        data.toThetaFiniteLogVolumeEndpoint.upperRayData.qPilotLogVolume ∉
          (data.toThetaPilotTensorPowerLogVolume
            tensorPower tensor_power_ge_two).tensorPowerUpperRay) ∨
      (-1 : Real) < cTheta := by
  by_cases hboundary : cTheta = (-1 : Real)
  · left
    exact
      ⟨hboundary,
        data.standardQLambdaCTheta_not_qPilot_mem_tensorPowerUpperRay_of_boundary
          q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
          tensorPower tensor_power_ge_two theta_neg hboundary⟩
  · right
    exact
      lt_of_le_of_ne
        (data.standardQLambdaCTheta_endpoint
          q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ).2.2
        (Ne.symm hboundary)

theorem standardQLambdaCTheta_twoComputationTensorPowerBoundary_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower)
    (theta_neg : data.thetaHullLogVolume < 0) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    (cTheta = (-1 : Real) ∧
        twoComputation.inputPrimeStripLogVolume ∉
          (data.toThetaPilotTensorPowerLogVolume
            tensorPower tensor_power_ge_two).tensorPowerUpperRay ∧
        twoComputation.outputHullLogVolume ∉
          (data.toThetaPilotTensorPowerLogVolume
            tensorPower tensor_power_ge_two).tensorPowerUpperRay) ∨
      (-1 : Real) < cTheta := by
  intro twoComputation
  by_cases hboundary : cTheta = (-1 : Real)
  · left
    have hnot :=
      data.standardQLambdaCTheta_not_twoComputation_mem_tensorPowerUpperRay_of_boundary
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
        tensorPower tensor_power_ge_two theta_neg hboundary
    exact ⟨hboundary, hnot⟩
  · right
    exact
      lt_of_le_of_ne
        (data.standardQLambdaCTheta_endpoint
          q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ).2.2
        (Ne.symm hboundary)

theorem standardQLambdaCTheta_qPilot_eq_thetaHullLogVolume_of_cTheta_eq_neg_one
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    data.qPilotLogVolume = data.thetaHullLogVolume := by
  let endpoint :=
    data.toStandardQLambdaCThetaBound
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
  have hCendpoint : endpoint.cTheta = -((endpoint.lambda : Real)) := by
    simpa [endpoint, toStandardQLambdaCThetaBound, toQLambdaCThetaBound]
      using hC
  have h :=
    endpoint.qLambdaSigned_eq_thetaSigned_of_cTheta_eq_neg_lambda
      hCendpoint
  have hbefore :
      data.corridor.beforeIndeterminacy.averageLogVolume =
        data.thetaHullLogVolume := by
    simpa [endpoint, toStandardQLambdaCThetaBound, toQLambdaCThetaBound] using h
  rw [data.q_eq_beforeAverage]
  exact hbefore

theorem standardQLambdaCTheta_qPilot_eq_determinantLogVolume_of_cTheta_eq_neg_one
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    data.qPilotLogVolume = data.determinant.determinantLogVolume := by
  rw [data.standardQLambdaCTheta_qPilot_eq_thetaHullLogVolume_of_cTheta_eq_neg_one
    q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC,
    data.thetaHullLogVolume_eq_determinantLogVolume]

theorem standardQLambdaCTheta_determinantBoundary_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    (cTheta = (-1 : Real) ∧
        twoComputation.inputPrimeStripLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.outputHullLogVolume =
          data.determinant.determinantLogVolume) ∨
      (-1 : Real) < cTheta := by
  intro twoComputation
  by_cases hC : cTheta = (-1 : Real)
  · left
    have hq :
        data.qPilotLogVolume = data.determinant.determinantLogVolume :=
      data.standardQLambdaCTheta_qPilot_eq_determinantLogVolume_of_cTheta_eq_neg_one
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC
    exact
      ⟨hC,
        by
          rw [twoComputation.input_eq_q]
          simpa [toQPilotTwoComputationLogVolume,
            toHullDetPilotUpperRayLogVolume] using hq,
        by
          rw [twoComputation.output_eq_q]
          simpa [toQPilotTwoComputationLogVolume,
            toHullDetPilotUpperRayLogVolume] using hq⟩
  · right
    exact
      lt_of_le_of_ne
        ((data.toQPilotTwoComputationCThetaEndpoint
          q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ).cTheta_ge_neg_one)
        (Ne.symm hC)

theorem standardQLambdaCTheta_determinantTensorBoundary_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower)
    (theta_neg : data.thetaHullLogVolume < 0) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    (cTheta = (-1 : Real) ∧
        twoComputation.inputPrimeStripLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.outputHullLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.inputPrimeStripLogVolume ∉
          (data.toThetaPilotTensorPowerLogVolume
            tensorPower tensor_power_ge_two).tensorPowerUpperRay ∧
        twoComputation.outputHullLogVolume ∉
          (data.toThetaPilotTensorPowerLogVolume
            tensorPower tensor_power_ge_two).tensorPowerUpperRay) ∨
      (-1 : Real) < cTheta := by
  intro twoComputation
  rcases data.standardQLambdaCTheta_determinantBoundary_or_strict
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ with
    hboundary | hstrict
  · left
    have hnot :=
      data.standardQLambdaCTheta_not_twoComputation_mem_tensorPowerUpperRay_of_boundary
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
        tensorPower tensor_power_ge_two theta_neg hboundary.1
    exact
      ⟨hboundary.1, hboundary.2.1, hboundary.2.2,
        hnot.1, hnot.2⟩
  · exact Or.inr hstrict

theorem boundaryCTheta_globalFrobenioidCalibration_separates_localShift
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real))
    (hExponent : localExponent ≠ 0)
    (hStep : localPrimeStepLogVolume ≠ 0) :
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    global.calibratedLogVolume = data.qPilotLogVolume ∧
      global.calibratedLogVolume = data.determinant.determinantLogVolume ∧
      global.calibratedLogVolume ≠ global.localData.shiftedLogVolume ∧
      global.localData.shiftedLogVolume ≠ data.qPilotLogVolume ∧
      global.localData.shiftedLogVolume ≠
        data.determinant.determinantLogVolume := by
  intro global
  have hqtheta :
      data.qPilotLogVolume = data.thetaHullLogVolume :=
    data.standardQLambdaCTheta_qPilot_eq_thetaHullLogVolume_of_cTheta_eq_neg_one
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC
  have hqdet :
      data.qPilotLogVolume = data.determinant.determinantLogVolume :=
    data.standardQLambdaCTheta_qPilot_eq_determinantLogVolume_of_cTheta_eq_neg_one
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC
  have hglobaltheta :
      global.calibratedLogVolume = data.thetaHullLogVolume := by
    simpa [global, toGlobalFrobenioidLogVolumeCalibration] using
      data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume_eq_hull
  have hglobalq :
      global.calibratedLogVolume = data.qPilotLogVolume :=
    hglobaltheta.trans hqtheta.symm
  have hglobaldet :
      global.calibratedLogVolume = data.determinant.determinantLogVolume :=
    hglobalq.trans hqdet
  have hExponentGlobal :
      global.localData.localExponent ≠ 0 := by
    simpa [global, toGlobalFrobenioidLogVolumeCalibration,
      toLocalFrobenioidLogVolumeAmbiguity] using hExponent
  have hStepGlobal :
      global.localData.localPrimeStepLogVolume ≠ 0 := by
    simpa [global, toGlobalFrobenioidLogVolumeCalibration,
      toLocalFrobenioidLogVolumeAmbiguity] using hStep
  have hcal_ne_shift :
      global.calibratedLogVolume ≠ global.localData.shiftedLogVolume :=
    global.calibratedLogVolume_ne_shifted_of_local_nonzero
      hExponentGlobal hStepGlobal
  exact
    ⟨hglobalq, hglobaldet, hcal_ne_shift,
      by
        intro hshift
        exact hcal_ne_shift (hglobalq.trans hshift.symm),
      by
        intro hshift
        exact hcal_ne_shift (hglobaldet.trans hshift.symm)⟩

theorem boundaryCTheta_upperSemiSingletonQuotient_separates_nonzeroLocalShift
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real))
    (hExponent : localExponent ≠ 0)
    (hStep : localPrimeStepLogVolume ≠ 0) :
    let collapsedRegion : Set Real := {data.qPilotLogVolume};
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion global.localData.shiftedLogVolume ≠
      IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion data.qPilotLogVolume ∧
      IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion global.localData.shiftedLogVolume ≠
        IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion data.determinant.determinantLogVolume := by
  intro collapsedRegion global
  have hsep :=
    data.boundaryCTheta_globalFrobenioidCalibration_separates_localShift
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC hExponent hStep
  have hshift_not_mem :
      global.localData.shiftedLogVolume ∉ collapsedRegion := by
    simpa [collapsedRegion, Set.mem_singleton_iff] using hsep.2.2.2.1
  have hshift_ne_collapsed :
      IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion global.localData.shiftedLogVolume ≠
        IUTStage1UpperSemiSetQuotient.collapsed :=
    IUTStage1UpperSemiSetQuotient.quotientMap_ne_collapsed_of_not_mem
      hshift_not_mem
  have hq_collapsed :
      IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion data.qPilotLogVolume =
        IUTStage1UpperSemiSetQuotient.collapsed :=
    IUTStage1UpperSemiSetQuotient.quotientMap_eq_collapsed_of_mem
      (by simp [collapsedRegion])
  have hdet_eq_q :
      data.determinant.determinantLogVolume = data.qPilotLogVolume :=
    hsep.2.1.symm.trans hsep.1
  have hdet_collapsed :
      IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion data.determinant.determinantLogVolume =
        IUTStage1UpperSemiSetQuotient.collapsed :=
    IUTStage1UpperSemiSetQuotient.quotientMap_eq_collapsed_of_mem
      (by simpa [collapsedRegion, Set.mem_singleton_iff] using hdet_eq_q)
  exact
    ⟨by
      intro hmap
      exact hshift_ne_collapsed (hmap.trans hq_collapsed),
    by
      intro hmap
      exact hshift_ne_collapsed (hmap.trans hdet_collapsed)⟩

theorem upperSemiQuotient_localShift_eq_q_iff_mem_of_q_mem
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (collapsedRegion : Set Real)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (hq_mem : data.qPilotLogVolume ∈ collapsedRegion) :
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion global.localData.shiftedLogVolume =
      IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion data.qPilotLogVolume ↔
      global.localData.shiftedLogVolume ∈ collapsedRegion := by
  intro global
  exact
    IUTStage1UpperSemiSetQuotient.quotientMap_eq_quotientMap_of_mem_iff
      hq_mem

theorem boundaryCTheta_qUpperRayQuotient_classifies_localShift_by_shiftTerm
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    let collapsedRegion : Set Real := {x | x <= data.qPilotLogVolume};
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    ((localExponent : Real) * localPrimeStepLogVolume < 0 ∧
        global.localData.shiftedLogVolume < data.qPilotLogVolume ∧
        IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion global.localData.shiftedLogVolume =
          IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion data.qPilotLogVolume) ∨
      ((localExponent : Real) * localPrimeStepLogVolume = 0 ∧
        global.localData.shiftedLogVolume = data.qPilotLogVolume ∧
        IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion global.localData.shiftedLogVolume =
          IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion data.qPilotLogVolume) ∨
      (0 < (localExponent : Real) * localPrimeStepLogVolume ∧
        data.qPilotLogVolume < global.localData.shiftedLogVolume ∧
        IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion global.localData.shiftedLogVolume ≠
          IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion data.qPilotLogVolume) := by
  intro collapsedRegion global
  have hqtheta :
      data.qPilotLogVolume = data.thetaHullLogVolume :=
    data.standardQLambdaCTheta_qPilot_eq_thetaHullLogVolume_of_cTheta_eq_neg_one
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC
  have hglobaltheta :
      global.calibratedLogVolume = data.thetaHullLogVolume := by
    simpa [global, toGlobalFrobenioidLogVolumeCalibration] using
      data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume_eq_hull
  have hglobalq :
      global.calibratedLogVolume = data.qPilotLogVolume :=
    hglobaltheta.trans hqtheta.symm
  have hcriterion :
      IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion global.localData.shiftedLogVolume =
        IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion data.qPilotLogVolume ↔
        global.localData.shiftedLogVolume <= data.qPilotLogVolume := by
    simpa [collapsedRegion] using
      data.upperSemiQuotient_localShift_eq_q_iff_mem_of_q_mem
        collapsedRegion localExponent localPrimeStepLogVolume
        (by simp [collapsedRegion])
  rcases lt_trichotomy
      ((localExponent : Real) * localPrimeStepLogVolume) 0 with
    hneg | hzero | hpos
  · have hshift_lt_q :
        global.localData.shiftedLogVolume < data.qPilotLogVolume :=
      by
        have hshift_lt_calibrated :
            global.localData.shiftedLogVolume < global.calibratedLogVolume :=
          global.shiftedLogVolume_lt_calibrated_iff_shiftTerm_lt_zero.mpr
            hneg
        simpa [hglobalq] using hshift_lt_calibrated
    exact Or.inl
      ⟨hneg, hshift_lt_q, hcriterion.mpr (le_of_lt hshift_lt_q)⟩
  · have hshift_eq_q :
        global.localData.shiftedLogVolume = data.qPilotLogVolume := by
      have hcalshift :
          global.calibratedLogVolume = global.localData.shiftedLogVolume :=
        global.calibratedLogVolume_eq_shifted_iff_shiftTerm_eq_zero.mpr
          hzero
      exact hcalshift.symm.trans hglobalq
    exact Or.inr (Or.inl
      ⟨hzero, hshift_eq_q, hcriterion.mpr (le_of_eq hshift_eq_q)⟩)
  · have hq_lt_shift :
        data.qPilotLogVolume < global.localData.shiftedLogVolume :=
      by
        have hcalibrated_lt_shift :
            global.calibratedLogVolume < global.localData.shiftedLogVolume :=
          global.calibratedLogVolume_lt_shifted_iff_shiftTerm_pos.mpr
            hpos
        simpa [hglobalq] using hcalibrated_lt_shift
    exact Or.inr (Or.inr
      ⟨hpos, hq_lt_shift, by
        intro hmap
        exact (not_le_of_gt hq_lt_shift) (hcriterion.mp hmap)⟩)

theorem boundaryCTheta_actualUpperRayQuotient_classifies_localShift_by_shiftTerm
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    let collapsedRegion : Set Real :=
      data.toHullDetPilotUpperRayLogVolume.upperRay;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    ((localExponent : Real) * localPrimeStepLogVolume < 0 ∧
        global.localData.shiftedLogVolume < data.qPilotLogVolume ∧
        IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion global.localData.shiftedLogVolume =
          IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion data.qPilotLogVolume) ∨
      ((localExponent : Real) * localPrimeStepLogVolume = 0 ∧
        global.localData.shiftedLogVolume = data.qPilotLogVolume ∧
        IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion global.localData.shiftedLogVolume =
          IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion data.qPilotLogVolume) ∨
      (0 < (localExponent : Real) * localPrimeStepLogVolume ∧
        data.qPilotLogVolume < global.localData.shiftedLogVolume ∧
        IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion global.localData.shiftedLogVolume ≠
          IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion data.qPilotLogVolume) := by
  intro collapsedRegion global
  have hqtheta :
      data.qPilotLogVolume = data.thetaHullLogVolume :=
    data.standardQLambdaCTheta_qPilot_eq_thetaHullLogVolume_of_cTheta_eq_neg_one
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC
  have hglobaltheta :
      global.calibratedLogVolume = data.thetaHullLogVolume := by
    simpa [global, toGlobalFrobenioidLogVolumeCalibration] using
      data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume_eq_hull
  have hglobalq :
      global.calibratedLogVolume = data.qPilotLogVolume :=
    hglobaltheta.trans hqtheta.symm
  have hcriterion :
      IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion global.localData.shiftedLogVolume =
        IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion data.qPilotLogVolume ↔
        global.localData.shiftedLogVolume <= data.qPilotLogVolume := by
    have hmemCriterion :=
      data.upperSemiQuotient_localShift_eq_q_iff_mem_of_q_mem
        collapsedRegion localExponent localPrimeStepLogVolume
        (by
          simpa [collapsedRegion] using data.toUpperRay_q_mem)
    constructor
    · intro hmap
      have hmem := hmemCriterion.mp hmap
      have hle_theta :
          global.localData.shiftedLogVolume <= data.thetaHullLogVolume := by
        simpa [collapsedRegion, IUTStage1HullDetPilotUpperRayLogVolume.upperRay,
          toHullDetPilotUpperRayLogVolume] using hmem
      simpa [hqtheta] using hle_theta
    · intro hle_q
      have hmem :
          global.localData.shiftedLogVolume ∈ collapsedRegion := by
        have hle_theta :
            global.localData.shiftedLogVolume <= data.thetaHullLogVolume := by
          simpa [hqtheta] using hle_q
        simpa [collapsedRegion, IUTStage1HullDetPilotUpperRayLogVolume.upperRay,
          toHullDetPilotUpperRayLogVolume] using hle_theta
      exact hmemCriterion.mpr hmem
  rcases lt_trichotomy
      ((localExponent : Real) * localPrimeStepLogVolume) 0 with
    hneg | hzero | hpos
  · have hshift_lt_q :
        global.localData.shiftedLogVolume < data.qPilotLogVolume :=
      by
        have hshift_lt_calibrated :
            global.localData.shiftedLogVolume < global.calibratedLogVolume :=
          global.shiftedLogVolume_lt_calibrated_iff_shiftTerm_lt_zero.mpr
            hneg
        simpa [hglobalq] using hshift_lt_calibrated
    exact Or.inl
      ⟨hneg, hshift_lt_q, hcriterion.mpr (le_of_lt hshift_lt_q)⟩
  · have hshift_eq_q :
        global.localData.shiftedLogVolume = data.qPilotLogVolume := by
      have hcalshift :
          global.calibratedLogVolume = global.localData.shiftedLogVolume :=
        global.calibratedLogVolume_eq_shifted_iff_shiftTerm_eq_zero.mpr
          hzero
      exact hcalshift.symm.trans hglobalq
    exact Or.inr (Or.inl
      ⟨hzero, hshift_eq_q, hcriterion.mpr (le_of_eq hshift_eq_q)⟩)
  · have hq_lt_shift :
        data.qPilotLogVolume < global.localData.shiftedLogVolume :=
      by
        have hcalibrated_lt_shift :
            global.calibratedLogVolume < global.localData.shiftedLogVolume :=
          global.calibratedLogVolume_lt_shifted_iff_shiftTerm_pos.mpr
            hpos
        simpa [hglobalq] using hcalibrated_lt_shift
    exact Or.inr (Or.inr
      ⟨hpos, hq_lt_shift, by
        intro hmap
        exact (not_le_of_gt hq_lt_shift) (hcriterion.mp hmap)⟩)

theorem boundaryCTheta_actualUpperRayQuotient_collapses_negativeLocalShift
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real))
    (hShiftTerm :
      (localExponent : Real) * localPrimeStepLogVolume < 0) :
    let collapsedRegion : Set Real :=
      data.toHullDetPilotUpperRayLogVolume.upperRay;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    global.localData.shiftedLogVolume < data.qPilotLogVolume ∧
      IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion global.localData.shiftedLogVolume =
        IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion data.qPilotLogVolume ∧
      global.localData.shiftedLogVolume ≠ data.qPilotLogVolume := by
  intro collapsedRegion global
  have hclass :=
    data.boundaryCTheta_actualUpperRayQuotient_classifies_localShift_by_shiftTerm
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC
  rcases hclass with hneg | hrest
  · exact ⟨hneg.2.1, hneg.2.2, ne_of_lt hneg.2.1⟩
  · rcases hrest with hzero | hpos
    · exact False.elim ((ne_of_lt hShiftTerm) hzero.1)
    · exact False.elim ((not_lt_of_gt hpos.1) hShiftTerm)

theorem boundaryCTheta_actualUpperRayQuotient_separates_positiveLocalShift
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real))
    (hShiftTerm :
      0 < (localExponent : Real) * localPrimeStepLogVolume) :
    let collapsedRegion : Set Real :=
      data.toHullDetPilotUpperRayLogVolume.upperRay;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    data.qPilotLogVolume < global.localData.shiftedLogVolume ∧
      IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion global.localData.shiftedLogVolume ≠
        IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion data.qPilotLogVolume ∧
      global.localData.shiftedLogVolume ≠ data.qPilotLogVolume := by
  intro collapsedRegion global
  have hclass :=
    data.boundaryCTheta_actualUpperRayQuotient_classifies_localShift_by_shiftTerm
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC
  rcases hclass with hneg | hrest
  · exact False.elim ((not_lt_of_gt hShiftTerm) hneg.1)
  · rcases hrest with hzero | hpos
    · exact False.elim ((ne_of_gt hShiftTerm) hzero.1)
    · exact ⟨hpos.2.1, hpos.2.2, ne_of_gt hpos.2.1⟩

theorem boundaryCTheta_actualUpperRayQuotient_eq_q_iff_shiftTerm_nonpos
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    let collapsedRegion : Set Real :=
      data.toHullDetPilotUpperRayLogVolume.upperRay;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion global.localData.shiftedLogVolume =
      IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion data.qPilotLogVolume ↔
      (localExponent : Real) * localPrimeStepLogVolume <= 0 := by
  intro collapsedRegion global
  have hclass :=
    data.boundaryCTheta_actualUpperRayQuotient_classifies_localShift_by_shiftTerm
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC
  constructor
  · intro hmap
    rcases hclass with hneg | hrest
    · exact le_of_lt hneg.1
    · rcases hrest with hzero | hpos
      · exact le_of_eq hzero.1
      · exact False.elim (hpos.2.2 hmap)
  · intro hnonpos
    rcases hclass with hneg | hrest
    · exact hneg.2.2
    · rcases hrest with hzero | hpos
      · exact hzero.2.2
      · exact False.elim ((not_lt_of_ge hnonpos) hpos.1)

theorem boundaryCTheta_actualUpperRayQuotient_ne_q_iff_shiftTerm_pos
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    let collapsedRegion : Set Real :=
      data.toHullDetPilotUpperRayLogVolume.upperRay;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion global.localData.shiftedLogVolume ≠
      IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion data.qPilotLogVolume ↔
      0 < (localExponent : Real) * localPrimeStepLogVolume := by
  intro collapsedRegion global
  have heq :=
    data.boundaryCTheta_actualUpperRayQuotient_eq_q_iff_shiftTerm_nonpos
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC
  constructor
  · intro hne
    exact not_le.mp fun hnonpos => hne (heq.mpr hnonpos)
  · intro hpos hmap
    exact (not_le_of_gt hpos) (heq.mp hmap)

theorem boundaryCTheta_actualUpperRayQuotient_eq_q_of_exponent_nonpos_step_pos
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real))
    (hExponent : (localExponent : Real) <= 0)
    (hStep : 0 < localPrimeStepLogVolume) :
    let collapsedRegion : Set Real :=
      data.toHullDetPilotUpperRayLogVolume.upperRay;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion global.localData.shiftedLogVolume =
      IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion data.qPilotLogVolume := by
  intro collapsedRegion global
  have heq :=
    data.boundaryCTheta_actualUpperRayQuotient_eq_q_iff_shiftTerm_nonpos
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC
  exact heq.mpr
    (mul_nonpos_of_nonpos_of_nonneg hExponent (le_of_lt hStep))

theorem boundaryCTheta_actualUpperRayQuotient_ne_q_of_exponent_pos_step_pos
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real))
    (hExponent : 0 < (localExponent : Real))
    (hStep : 0 < localPrimeStepLogVolume) :
    let collapsedRegion : Set Real :=
      data.toHullDetPilotUpperRayLogVolume.upperRay;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion global.localData.shiftedLogVolume ≠
      IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion data.qPilotLogVolume := by
  intro collapsedRegion global
  have hne :=
    data.boundaryCTheta_actualUpperRayQuotient_ne_q_iff_shiftTerm_pos
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC
  exact hne.mpr (mul_pos hExponent hStep)

theorem boundaryCTheta_actualUpperRayQuotient_eq_q_of_intExponent_nonpos_step_pos
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real))
    (hExponent : localExponent <= 0)
    (hStep : 0 < localPrimeStepLogVolume) :
    let collapsedRegion : Set Real :=
      data.toHullDetPilotUpperRayLogVolume.upperRay;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion global.localData.shiftedLogVolume =
      IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion data.qPilotLogVolume := by
  have hExponentReal : (localExponent : Real) <= 0 := by
    exact_mod_cast hExponent
  exact
    data.boundaryCTheta_actualUpperRayQuotient_eq_q_of_exponent_nonpos_step_pos
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC hExponentReal hStep

theorem boundaryCTheta_actualUpperRayQuotient_ne_q_of_intExponent_pos_step_pos
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real))
    (hExponent : 0 < localExponent)
    (hStep : 0 < localPrimeStepLogVolume) :
    let collapsedRegion : Set Real :=
      data.toHullDetPilotUpperRayLogVolume.upperRay;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion global.localData.shiftedLogVolume ≠
      IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion data.qPilotLogVolume := by
  have hExponentReal : 0 < (localExponent : Real) := by
    exact_mod_cast hExponent
  exact
    data.boundaryCTheta_actualUpperRayQuotient_ne_q_of_exponent_pos_step_pos
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC hExponentReal hStep

theorem boundaryCTheta_upperSemiQuotient_collapses_nonzeroLocalShift_of_mem
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (collapsedRegion : Set Real)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real))
    (hExponent : localExponent ≠ 0)
    (hStep : localPrimeStepLogVolume ≠ 0)
    (hq_mem : data.qPilotLogVolume ∈ collapsedRegion)
    (hshift_mem :
      (data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume).localData.shiftedLogVolume ∈
          collapsedRegion) :
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion global.localData.shiftedLogVolume =
      IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion data.qPilotLogVolume ∧
      IUTStage1UpperSemiSetQuotient.quotientMap
        collapsedRegion global.localData.shiftedLogVolume =
        IUTStage1UpperSemiSetQuotient.quotientMap
          collapsedRegion data.determinant.determinantLogVolume ∧
      global.localData.shiftedLogVolume ≠ data.qPilotLogVolume ∧
      global.localData.shiftedLogVolume ≠
        data.determinant.determinantLogVolume := by
  intro global
  have hsep :=
    data.boundaryCTheta_globalFrobenioidCalibration_separates_localShift
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC hExponent hStep
  have hdet_eq_q :
      data.determinant.determinantLogVolume = data.qPilotLogVolume :=
    hsep.2.1.symm.trans hsep.1
  have hshift_mem_global :
      global.localData.shiftedLogVolume ∈ collapsedRegion := by
    simpa [global] using hshift_mem
  have hdet_mem :
      data.determinant.determinantLogVolume ∈ collapsedRegion := by
    simpa [hdet_eq_q] using hq_mem
  exact
    ⟨IUTStage1UpperSemiSetQuotient.quotientMap_eq_of_mem
      hshift_mem_global hq_mem,
    IUTStage1UpperSemiSetQuotient.quotientMap_eq_of_mem
      hshift_mem_global hdet_mem,
    hsep.2.2.2.1, hsep.2.2.2.2⟩

theorem determinantBoundary_upperSemiQuotientCollapsesNonzeroLocalShift_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (collapsedRegion : Set Real)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hExponent : localExponent ≠ 0)
    (hStep : localPrimeStepLogVolume ≠ 0)
    (hq_mem : data.qPilotLogVolume ∈ collapsedRegion)
    (hshift_mem :
      (data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume).localData.shiftedLogVolume ∈
          collapsedRegion) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (cTheta = (-1 : Real) ∧
        twoComputation.inputPrimeStripLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.outputHullLogVolume =
          data.determinant.determinantLogVolume ∧
        IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion global.localData.shiftedLogVolume =
          IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion data.qPilotLogVolume ∧
        IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion global.localData.shiftedLogVolume =
          IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion data.determinant.determinantLogVolume ∧
        global.localData.shiftedLogVolume ≠ data.qPilotLogVolume ∧
        global.localData.shiftedLogVolume ≠
          data.determinant.determinantLogVolume) ∨
      (-1 : Real) < cTheta := by
  intro twoComputation global
  rcases data.standardQLambdaCTheta_determinantBoundary_or_strict
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ with
    hboundary | hstrict
  · left
    have hcollapse :=
      data.boundaryCTheta_upperSemiQuotient_collapses_nonzeroLocalShift_of_mem
        collapsedRegion localExponent localPrimeStepLogVolume q_pilot_positive
        cTheta thetaHull_le_cTheta_absLogQ hboundary.1 hExponent hStep
        hq_mem hshift_mem
    exact
      ⟨hboundary.1, hboundary.2.1, hboundary.2.2,
        hcollapse.1, hcollapse.2.1, hcollapse.2.2.1,
        hcollapse.2.2.2⟩
  · exact Or.inr hstrict

theorem determinantBoundary_actualUpperRayQuotientClassifiesLocalShift_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    let collapsedRegion : Set Real :=
      data.toHullDetPilotUpperRayLogVolume.upperRay;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (cTheta = (-1 : Real) ∧
        twoComputation.inputPrimeStripLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.outputHullLogVolume =
          data.determinant.determinantLogVolume ∧
        (((localExponent : Real) * localPrimeStepLogVolume < 0 ∧
            global.localData.shiftedLogVolume < data.qPilotLogVolume ∧
            IUTStage1UpperSemiSetQuotient.quotientMap
                collapsedRegion global.localData.shiftedLogVolume =
              IUTStage1UpperSemiSetQuotient.quotientMap
                collapsedRegion data.qPilotLogVolume) ∨
          ((localExponent : Real) * localPrimeStepLogVolume = 0 ∧
            global.localData.shiftedLogVolume = data.qPilotLogVolume ∧
            IUTStage1UpperSemiSetQuotient.quotientMap
                collapsedRegion global.localData.shiftedLogVolume =
              IUTStage1UpperSemiSetQuotient.quotientMap
                collapsedRegion data.qPilotLogVolume) ∨
          (0 < (localExponent : Real) * localPrimeStepLogVolume ∧
            data.qPilotLogVolume < global.localData.shiftedLogVolume ∧
            IUTStage1UpperSemiSetQuotient.quotientMap
                collapsedRegion global.localData.shiftedLogVolume ≠
              IUTStage1UpperSemiSetQuotient.quotientMap
                collapsedRegion data.qPilotLogVolume))) ∨
      (-1 : Real) < cTheta := by
  intro twoComputation collapsedRegion global
  rcases data.standardQLambdaCTheta_determinantBoundary_or_strict
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ with
    hboundary | hstrict
  · left
    have hclass :=
      data.boundaryCTheta_actualUpperRayQuotient_classifies_localShift_by_shiftTerm
        localExponent localPrimeStepLogVolume q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ hboundary.1
    exact
      ⟨hboundary.1, hboundary.2.1, hboundary.2.2, hclass⟩
  · exact Or.inr hstrict

theorem determinantBoundary_actualUpperRayCollapseThreshold_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    let collapsedRegion : Set Real :=
      data.toHullDetPilotUpperRayLogVolume.upperRay;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (cTheta = (-1 : Real) ∧
        twoComputation.inputPrimeStripLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.outputHullLogVolume =
          data.determinant.determinantLogVolume ∧
        (IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion global.localData.shiftedLogVolume =
          IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion data.qPilotLogVolume ↔
          (localExponent : Real) * localPrimeStepLogVolume <= 0)) ∨
      (-1 : Real) < cTheta := by
  intro twoComputation collapsedRegion global
  rcases data.standardQLambdaCTheta_determinantBoundary_or_strict
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ with
    hboundary | hstrict
  · left
    have hthreshold :=
      data.boundaryCTheta_actualUpperRayQuotient_eq_q_iff_shiftTerm_nonpos
        localExponent localPrimeStepLogVolume q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ hboundary.1
    exact
      ⟨hboundary.1, hboundary.2.1, hboundary.2.2, hthreshold⟩
  · exact Or.inr hstrict

theorem determinantBoundary_actualUpperRaySeparationThreshold_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    let collapsedRegion : Set Real :=
      data.toHullDetPilotUpperRayLogVolume.upperRay;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (cTheta = (-1 : Real) ∧
        twoComputation.inputPrimeStripLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.outputHullLogVolume =
          data.determinant.determinantLogVolume ∧
        (IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion global.localData.shiftedLogVolume ≠
          IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion data.qPilotLogVolume ↔
          0 < (localExponent : Real) * localPrimeStepLogVolume)) ∨
      (-1 : Real) < cTheta := by
  intro twoComputation collapsedRegion global
  rcases data.standardQLambdaCTheta_determinantBoundary_or_strict
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ with
    hboundary | hstrict
  · left
    have hthreshold :=
      data.boundaryCTheta_actualUpperRayQuotient_ne_q_iff_shiftTerm_pos
        localExponent localPrimeStepLogVolume q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ hboundary.1
    exact
      ⟨hboundary.1, hboundary.2.1, hboundary.2.2, hthreshold⟩
  · exact Or.inr hstrict

theorem determinantBoundary_actualUpperRayIntExponentCollapse_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hExponent : localExponent <= 0)
    (hStep : 0 < localPrimeStepLogVolume) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    let collapsedRegion : Set Real :=
      data.toHullDetPilotUpperRayLogVolume.upperRay;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (cTheta = (-1 : Real) ∧
        twoComputation.inputPrimeStripLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.outputHullLogVolume =
          data.determinant.determinantLogVolume ∧
        IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion global.localData.shiftedLogVolume =
          IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion data.qPilotLogVolume) ∨
      (-1 : Real) < cTheta := by
  intro twoComputation collapsedRegion global
  rcases data.standardQLambdaCTheta_determinantBoundary_or_strict
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ with
    hboundary | hstrict
  · left
    have hcollapse :=
      data.boundaryCTheta_actualUpperRayQuotient_eq_q_of_intExponent_nonpos_step_pos
        localExponent localPrimeStepLogVolume q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ hboundary.1 hExponent hStep
    exact
      ⟨hboundary.1, hboundary.2.1, hboundary.2.2, hcollapse⟩
  · exact Or.inr hstrict

theorem determinantBoundary_actualUpperRayIntExponentSeparation_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hExponent : 0 < localExponent)
    (hStep : 0 < localPrimeStepLogVolume) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    let collapsedRegion : Set Real :=
      data.toHullDetPilotUpperRayLogVolume.upperRay;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (cTheta = (-1 : Real) ∧
        twoComputation.inputPrimeStripLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.outputHullLogVolume =
          data.determinant.determinantLogVolume ∧
        IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion global.localData.shiftedLogVolume ≠
          IUTStage1UpperSemiSetQuotient.quotientMap
            collapsedRegion data.qPilotLogVolume) ∨
      (-1 : Real) < cTheta := by
  intro twoComputation collapsedRegion global
  rcases data.standardQLambdaCTheta_determinantBoundary_or_strict
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ with
    hboundary | hstrict
  · left
    have hseparate :=
      data.boundaryCTheta_actualUpperRayQuotient_ne_q_of_intExponent_pos_step_pos
        localExponent localPrimeStepLogVolume q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ hboundary.1 hExponent hStep
    exact
      ⟨hboundary.1, hboundary.2.1, hboundary.2.2, hseparate⟩
  · exact Or.inr hstrict

theorem determinantTensorBoundary_separatesLocalShift_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower)
    (theta_neg : data.thetaHullLogVolume < 0)
    (hExponent : localExponent ≠ 0)
    (hStep : localPrimeStepLogVolume ≠ 0) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (cTheta = (-1 : Real) ∧
        twoComputation.inputPrimeStripLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.outputHullLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.inputPrimeStripLogVolume ∉
          (data.toThetaPilotTensorPowerLogVolume
            tensorPower tensor_power_ge_two).tensorPowerUpperRay ∧
        twoComputation.outputHullLogVolume ∉
          (data.toThetaPilotTensorPowerLogVolume
            tensorPower tensor_power_ge_two).tensorPowerUpperRay ∧
        global.calibratedLogVolume = data.qPilotLogVolume ∧
        global.calibratedLogVolume =
          data.determinant.determinantLogVolume ∧
        global.calibratedLogVolume ≠ global.localData.shiftedLogVolume ∧
        global.localData.shiftedLogVolume ≠ data.qPilotLogVolume ∧
        global.localData.shiftedLogVolume ≠
          data.determinant.determinantLogVolume) ∨
      (-1 : Real) < cTheta := by
  intro twoComputation global
  rcases data.standardQLambdaCTheta_determinantTensorBoundary_or_strict
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
      tensorPower tensor_power_ge_two theta_neg with
    hboundary | hstrict
  · left
    have hsep :=
      data.boundaryCTheta_globalFrobenioidCalibration_separates_localShift
        localExponent localPrimeStepLogVolume q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ hboundary.1 hExponent hStep
    exact
      ⟨hboundary.1, hboundary.2.1, hboundary.2.2.1,
        hboundary.2.2.2.1, hboundary.2.2.2.2,
        hsep.1, hsep.2.1, hsep.2.2.1,
        hsep.2.2.2.1, hsep.2.2.2.2⟩
  · exact Or.inr hstrict

theorem determinantTensorBoundary_separatesLocalShiftFromTwoComputation_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower)
    (theta_neg : data.thetaHullLogVolume < 0)
    (hExponent : localExponent ≠ 0)
    (hStep : localPrimeStepLogVolume ≠ 0) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (cTheta = (-1 : Real) ∧
        twoComputation.inputPrimeStripLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.outputHullLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.inputPrimeStripLogVolume ∉
          (data.toThetaPilotTensorPowerLogVolume
            tensorPower tensor_power_ge_two).tensorPowerUpperRay ∧
        twoComputation.outputHullLogVolume ∉
          (data.toThetaPilotTensorPowerLogVolume
            tensorPower tensor_power_ge_two).tensorPowerUpperRay ∧
        global.localData.shiftedLogVolume ≠
          twoComputation.inputPrimeStripLogVolume ∧
        global.localData.shiftedLogVolume ≠
          twoComputation.outputHullLogVolume) ∨
      (-1 : Real) < cTheta := by
  intro twoComputation global
  rcases data.determinantTensorBoundary_separatesLocalShift_or_strict
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ tensorPower tensor_power_ge_two theta_neg
      hExponent hStep with
    hboundary | hstrict
  · left
    exact
      ⟨hboundary.1, hboundary.2.1, hboundary.2.2.1,
        hboundary.2.2.2.1, hboundary.2.2.2.2.1,
        by
          intro hshift
          exact hboundary.2.2.2.2.2.2.2.2.2
            (hshift.trans hboundary.2.1),
        by
          intro hshift
          exact hboundary.2.2.2.2.2.2.2.2.2
            (hshift.trans hboundary.2.2.1)⟩
  · exact Or.inr hstrict

theorem boundaryCTheta_localShift_eq_q_or_det_iff_trivial
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (global.localData.shiftedLogVolume = data.qPilotLogVolume ↔
        localExponent = 0 ∨ localPrimeStepLogVolume = 0) ∧
      (global.localData.shiftedLogVolume =
          data.determinant.determinantLogVolume ↔
        localExponent = 0 ∨ localPrimeStepLogVolume = 0) := by
  intro global
  have hqtheta :
      data.qPilotLogVolume = data.thetaHullLogVolume :=
    data.standardQLambdaCTheta_qPilot_eq_thetaHullLogVolume_of_cTheta_eq_neg_one
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC
  have hqdet :
      data.qPilotLogVolume = data.determinant.determinantLogVolume :=
    data.standardQLambdaCTheta_qPilot_eq_determinantLogVolume_of_cTheta_eq_neg_one
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC
  have hglobaltheta :
      global.calibratedLogVolume = data.thetaHullLogVolume := by
    simpa [global, toGlobalFrobenioidLogVolumeCalibration] using
      data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume_eq_hull
  have hglobalq :
      global.calibratedLogVolume = data.qPilotLogVolume :=
    hglobaltheta.trans hqtheta.symm
  have hglobaldet :
      global.calibratedLogVolume = data.determinant.determinantLogVolume :=
    hglobalq.trans hqdet
  exact
    ⟨by
      constructor
      · intro hshiftq
        exact
          global.calibratedLogVolume_eq_shifted_iff_exponent_zero_or_step_zero.mp
            (hglobalq.trans hshiftq.symm)
      · intro htrivial
        have hcalshift :
            global.calibratedLogVolume = global.localData.shiftedLogVolume :=
          global.calibratedLogVolume_eq_shifted_iff_exponent_zero_or_step_zero.mpr
            htrivial
        exact hcalshift.symm.trans hglobalq,
    by
      constructor
      · intro hshiftdet
        exact
          global.calibratedLogVolume_eq_shifted_iff_exponent_zero_or_step_zero.mp
            (hglobaldet.trans hshiftdet.symm)
      · intro htrivial
        have hcalshift :
            global.calibratedLogVolume = global.localData.shiftedLogVolume :=
          global.calibratedLogVolume_eq_shifted_iff_exponent_zero_or_step_zero.mpr
            htrivial
        exact hcalshift.symm.trans hglobaldet⟩

theorem boundaryCTheta_localShift_orderedAround_q_and_det
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (data.qPilotLogVolume < global.localData.shiftedLogVolume ↔
        0 < (localExponent : Real) * localPrimeStepLogVolume) ∧
      (global.localData.shiftedLogVolume < data.qPilotLogVolume ↔
        (localExponent : Real) * localPrimeStepLogVolume < 0) ∧
      (data.determinant.determinantLogVolume <
          global.localData.shiftedLogVolume ↔
        0 < (localExponent : Real) * localPrimeStepLogVolume) ∧
      (global.localData.shiftedLogVolume <
          data.determinant.determinantLogVolume ↔
        (localExponent : Real) * localPrimeStepLogVolume < 0) := by
  intro global
  have hqtheta :
      data.qPilotLogVolume = data.thetaHullLogVolume :=
    data.standardQLambdaCTheta_qPilot_eq_thetaHullLogVolume_of_cTheta_eq_neg_one
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC
  have hqdet :
      data.qPilotLogVolume = data.determinant.determinantLogVolume :=
    data.standardQLambdaCTheta_qPilot_eq_determinantLogVolume_of_cTheta_eq_neg_one
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC
  have hglobaltheta :
      global.calibratedLogVolume = data.thetaHullLogVolume := by
    simpa [global, toGlobalFrobenioidLogVolumeCalibration] using
      data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume_eq_hull
  have hglobalq :
      global.calibratedLogVolume = data.qPilotLogVolume :=
    hglobaltheta.trans hqtheta.symm
  have hglobaldet :
      global.calibratedLogVolume = data.determinant.determinantLogVolume :=
    hglobalq.trans hqdet
  exact
    ⟨by
      rw [← hglobalq]
      exact global.calibratedLogVolume_lt_shifted_iff_shiftTerm_pos,
    by
      rw [← hglobalq]
      exact global.shiftedLogVolume_lt_calibrated_iff_shiftTerm_lt_zero,
    by
      rw [← hglobaldet]
      exact global.calibratedLogVolume_lt_shifted_iff_shiftTerm_pos,
    by
      rw [← hglobaldet]
      exact global.shiftedLogVolume_lt_calibrated_iff_shiftTerm_lt_zero⟩

theorem boundaryCTheta_localShift_orderedAround_twoComputation
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (twoComputation.inputPrimeStripLogVolume <
        global.localData.shiftedLogVolume ↔
        0 < (localExponent : Real) * localPrimeStepLogVolume) ∧
      (global.localData.shiftedLogVolume <
        twoComputation.inputPrimeStripLogVolume ↔
        (localExponent : Real) * localPrimeStepLogVolume < 0) ∧
      (twoComputation.outputHullLogVolume <
        global.localData.shiftedLogVolume ↔
        0 < (localExponent : Real) * localPrimeStepLogVolume) ∧
      (global.localData.shiftedLogVolume <
        twoComputation.outputHullLogVolume ↔
        (localExponent : Real) * localPrimeStepLogVolume < 0) := by
  intro twoComputation global
  have hordered :=
    data.boundaryCTheta_localShift_orderedAround_q_and_det
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC
  exact
    ⟨by
      rw [twoComputation.input_eq_q]
      exact hordered.1,
    by
      rw [twoComputation.input_eq_q]
      exact hordered.2.1,
    by
      rw [twoComputation.output_eq_q]
      exact hordered.1,
    by
      rw [twoComputation.output_eq_q]
      exact hordered.2.1⟩

theorem boundaryCTheta_localShift_trichotomyAround_twoComputation
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    ((localExponent : Real) * localPrimeStepLogVolume < 0 ∧
        global.localData.shiftedLogVolume <
          twoComputation.inputPrimeStripLogVolume ∧
        global.localData.shiftedLogVolume <
          twoComputation.outputHullLogVolume) ∨
      ((localExponent : Real) * localPrimeStepLogVolume = 0 ∧
        global.localData.shiftedLogVolume =
          twoComputation.inputPrimeStripLogVolume ∧
        global.localData.shiftedLogVolume =
          twoComputation.outputHullLogVolume) ∨
      (0 < (localExponent : Real) * localPrimeStepLogVolume ∧
        twoComputation.inputPrimeStripLogVolume <
          global.localData.shiftedLogVolume ∧
        twoComputation.outputHullLogVolume <
          global.localData.shiftedLogVolume) := by
  intro twoComputation global
  have hordered :=
    data.boundaryCTheta_localShift_orderedAround_twoComputation
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC
  have hqtheta :
      data.qPilotLogVolume = data.thetaHullLogVolume :=
    data.standardQLambdaCTheta_qPilot_eq_thetaHullLogVolume_of_cTheta_eq_neg_one
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC
  have hglobaltheta :
      global.calibratedLogVolume = data.thetaHullLogVolume := by
    simpa [global, toGlobalFrobenioidLogVolumeCalibration] using
      data.toThetaFiniteLogVolumeEndpoint.thetaRealLogVolume_eq_hull
  have hglobalq :
      global.calibratedLogVolume = data.qPilotLogVolume :=
    hglobaltheta.trans hqtheta.symm
  have hinputZero :
      global.localData.shiftedLogVolume =
          twoComputation.inputPrimeStripLogVolume ↔
        (localExponent : Real) * localPrimeStepLogVolume = 0 := by
    rw [twoComputation.input_eq_q]
    constructor
    · intro hshift
      exact
        global.calibratedLogVolume_eq_shifted_iff_shiftTerm_eq_zero.mp
          (hglobalq.trans hshift.symm)
    · intro hzero
      have hcalshift :
          global.calibratedLogVolume = global.localData.shiftedLogVolume :=
        global.calibratedLogVolume_eq_shifted_iff_shiftTerm_eq_zero.mpr hzero
      exact hcalshift.symm.trans hglobalq
  have houtputZero :
      global.localData.shiftedLogVolume =
          twoComputation.outputHullLogVolume ↔
        (localExponent : Real) * localPrimeStepLogVolume = 0 := by
    rw [twoComputation.output_eq_q]
    constructor
    · intro hshift
      exact
        global.calibratedLogVolume_eq_shifted_iff_shiftTerm_eq_zero.mp
          (hglobalq.trans hshift.symm)
    · intro hzero
      have hcalshift :
          global.calibratedLogVolume = global.localData.shiftedLogVolume :=
        global.calibratedLogVolume_eq_shifted_iff_shiftTerm_eq_zero.mpr hzero
      exact hcalshift.symm.trans hglobalq
  rcases lt_trichotomy
      ((localExponent : Real) * localPrimeStepLogVolume) 0 with
    hneg | hzero | hpos
  · exact Or.inl
      ⟨hneg, hordered.2.1.mpr hneg, hordered.2.2.2.mpr hneg⟩
  · exact Or.inr (Or.inl
      ⟨hzero, hinputZero.mpr hzero, houtputZero.mpr hzero⟩)
  · exact Or.inr (Or.inr
      ⟨hpos, hordered.1.mpr hpos, hordered.2.2.1.mpr hpos⟩)

theorem determinantTensorBoundary_ordersLocalShiftAroundTwoComputation_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower)
    (theta_neg : data.thetaHullLogVolume < 0) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (cTheta = (-1 : Real) ∧
        twoComputation.inputPrimeStripLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.outputHullLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.inputPrimeStripLogVolume ∉
          (data.toThetaPilotTensorPowerLogVolume
            tensorPower tensor_power_ge_two).tensorPowerUpperRay ∧
        twoComputation.outputHullLogVolume ∉
          (data.toThetaPilotTensorPowerLogVolume
            tensorPower tensor_power_ge_two).tensorPowerUpperRay ∧
        (twoComputation.inputPrimeStripLogVolume <
          global.localData.shiftedLogVolume ↔
          0 < (localExponent : Real) * localPrimeStepLogVolume) ∧
        (global.localData.shiftedLogVolume <
          twoComputation.inputPrimeStripLogVolume ↔
          (localExponent : Real) * localPrimeStepLogVolume < 0) ∧
        (twoComputation.outputHullLogVolume <
          global.localData.shiftedLogVolume ↔
          0 < (localExponent : Real) * localPrimeStepLogVolume) ∧
        (global.localData.shiftedLogVolume <
          twoComputation.outputHullLogVolume ↔
          (localExponent : Real) * localPrimeStepLogVolume < 0)) ∨
      (-1 : Real) < cTheta := by
  intro twoComputation global
  rcases data.standardQLambdaCTheta_determinantTensorBoundary_or_strict
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
      tensorPower tensor_power_ge_two theta_neg with
    hboundary | hstrict
  · left
    have hordered :=
      data.boundaryCTheta_localShift_orderedAround_twoComputation
        localExponent localPrimeStepLogVolume q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ hboundary.1
    exact
      ⟨hboundary.1, hboundary.2.1, hboundary.2.2.1,
        hboundary.2.2.2.1, hboundary.2.2.2.2,
        hordered.1, hordered.2.1, hordered.2.2.1,
        hordered.2.2.2⟩
  · exact Or.inr hstrict

theorem determinantTensorBoundary_trichotomyAroundTwoComputation_or_strict
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (tensorPower : Nat)
    (tensor_power_ge_two : 2 ≤ tensorPower)
    (theta_neg : data.thetaHullLogVolume < 0) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (cTheta = (-1 : Real) ∧
        twoComputation.inputPrimeStripLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.outputHullLogVolume =
          data.determinant.determinantLogVolume ∧
        twoComputation.inputPrimeStripLogVolume ∉
          (data.toThetaPilotTensorPowerLogVolume
            tensorPower tensor_power_ge_two).tensorPowerUpperRay ∧
        twoComputation.outputHullLogVolume ∉
          (data.toThetaPilotTensorPowerLogVolume
            tensorPower tensor_power_ge_two).tensorPowerUpperRay ∧
        (((localExponent : Real) * localPrimeStepLogVolume < 0 ∧
            global.localData.shiftedLogVolume <
              twoComputation.inputPrimeStripLogVolume ∧
            global.localData.shiftedLogVolume <
              twoComputation.outputHullLogVolume) ∨
          ((localExponent : Real) * localPrimeStepLogVolume = 0 ∧
            global.localData.shiftedLogVolume =
              twoComputation.inputPrimeStripLogVolume ∧
            global.localData.shiftedLogVolume =
              twoComputation.outputHullLogVolume) ∨
          (0 < (localExponent : Real) * localPrimeStepLogVolume ∧
            twoComputation.inputPrimeStripLogVolume <
              global.localData.shiftedLogVolume ∧
            twoComputation.outputHullLogVolume <
              global.localData.shiftedLogVolume))) ∨
      (-1 : Real) < cTheta := by
  intro twoComputation global
  rcases data.standardQLambdaCTheta_determinantTensorBoundary_or_strict
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
      tensorPower tensor_power_ge_two theta_neg with
    hboundary | hstrict
  · left
    have htri :=
      data.boundaryCTheta_localShift_trichotomyAround_twoComputation
        localExponent localPrimeStepLogVolume q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ hboundary.1
    exact
      ⟨hboundary.1, hboundary.2.1, hboundary.2.2.1,
        hboundary.2.2.2.1, hboundary.2.2.2.2, htri⟩
  · exact Or.inr hstrict

theorem boundaryCTheta_localShift_eq_q_or_det_iff_exponent_zero_of_step_nonzero
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real))
    (hStep : localPrimeStepLogVolume ≠ 0) :
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (global.localData.shiftedLogVolume = data.qPilotLogVolume ↔
        localExponent = 0) ∧
      (global.localData.shiftedLogVolume =
          data.determinant.determinantLogVolume ↔
        localExponent = 0) := by
  intro global
  have hcollapse :=
    data.boundaryCTheta_localShift_eq_q_or_det_iff_trivial
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC
  exact
    ⟨by
      constructor
      · intro hshift
        rcases hcollapse.1.mp hshift with hExponent | hStepZero
        · exact hExponent
        · exact False.elim (hStep hStepZero)
      · intro hExponent
        exact hcollapse.1.mpr (Or.inl hExponent),
    by
      constructor
      · intro hshift
        rcases hcollapse.2.mp hshift with hExponent | hStepZero
        · exact hExponent
        · exact False.elim (hStep hStepZero)
      · intro hExponent
        exact hcollapse.2.mpr (Or.inl hExponent)⟩

theorem boundaryCTheta_localShift_eq_twoComputation_iff_exponent_zero_of_step_nonzero
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real))
    (hStep : localPrimeStepLogVolume ≠ 0) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    (global.localData.shiftedLogVolume =
        twoComputation.inputPrimeStripLogVolume ↔
        localExponent = 0) ∧
      (global.localData.shiftedLogVolume =
        twoComputation.outputHullLogVolume ↔
        localExponent = 0) := by
  intro twoComputation global
  have hcriterion :=
    data.boundaryCTheta_localShift_eq_q_or_det_iff_exponent_zero_of_step_nonzero
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC hStep
  exact
    ⟨by
      rw [twoComputation.input_eq_q]
      exact hcriterion.1,
    by
      rw [twoComputation.output_eq_q]
      exact hcriterion.1⟩

theorem boundaryCTheta_localShift_collapses_for_step_zero
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real))
    (hStep : localPrimeStepLogVolume = 0) :
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    global.localData.shiftedLogVolume = data.qPilotLogVolume ∧
      global.localData.shiftedLogVolume =
        data.determinant.determinantLogVolume := by
  intro global
  have hcollapse :=
    data.boundaryCTheta_localShift_eq_q_or_det_iff_trivial
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC
  exact
    ⟨hcollapse.1.mpr (Or.inr hStep),
      hcollapse.2.mpr (Or.inr hStep)⟩

theorem boundaryCTheta_localShift_collapses_to_twoComputation_for_step_zero
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real))
    (hStep : localPrimeStepLogVolume = 0) :
    let twoComputation := data.toQPilotTwoComputationLogVolume;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    global.localData.shiftedLogVolume =
        twoComputation.inputPrimeStripLogVolume ∧
      global.localData.shiftedLogVolume =
        twoComputation.outputHullLogVolume ∧
      global.localData.shiftedLogVolume =
        data.determinant.determinantLogVolume := by
  intro twoComputation global
  have hcollapse :=
    data.boundaryCTheta_localShift_collapses_for_step_zero
      localExponent localPrimeStepLogVolume q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ hC hStep
  exact
    ⟨by
      rw [twoComputation.input_eq_q]
      exact hcollapse.1,
    by
      rw [twoComputation.output_eq_q]
      exact hcollapse.1,
    hcollapse.2⟩

theorem cTheta_ge_neg_one
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (-1 : Real) <= cTheta :=
  (data.toQPilotTwoComputationCThetaEndpoint
    q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ).cTheta_ge_neg_one

theorem thetaFinite_globalFrobenioidCThetaEndpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    let finite := data.toThetaFiniteLogVolumeEndpoint;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    let endpoint :=
      data.toQPilotTwoComputationCThetaEndpoint
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ;
    global.calibratedLogVolume = finite.thetaRealLogVolume ∧
      global.calibratedLogVolume = data.thetaHullLogVolume ∧
      (-1 : Real) <= endpoint.cTheta ∧
      (global.calibratedLogVolume = global.localData.shiftedLogVolume ↔
        (global.localData.localExponent : Real) *
          global.localData.localPrimeStepLogVolume = 0) ∧
      (localExponent ≠ 0 →
        localPrimeStepLogVolume ≠ 0 →
          global.calibratedLogVolume ≠ global.localData.shiftedLogVolume) := by
  intro finite global endpoint
  exact
    ⟨global.calibratedLogVolume_eq_unshifted,
    by
      rw [global.calibratedLogVolume_eq_unshifted]
      exact finite.thetaRealLogVolume_eq_hull,
    endpoint.cTheta_ge_neg_one,
    global.calibratedLogVolume_eq_shifted_iff_shiftTerm_eq_zero,
    fun hExponent hStep =>
      global.calibratedLogVolume_ne_shifted_of_local_nonzero
        hExponent hStep⟩

theorem thetaFinite_globalFrobenioidCThetaEndpoint_eq_shifted_iff_exponent_zero_or_step_zero
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    let finite := data.toThetaFiniteLogVolumeEndpoint;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    let endpoint :=
      data.toQPilotTwoComputationCThetaEndpoint
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ;
    global.calibratedLogVolume = finite.thetaRealLogVolume ∧
      global.calibratedLogVolume = data.thetaHullLogVolume ∧
      (-1 : Real) <= endpoint.cTheta ∧
      (global.calibratedLogVolume = global.localData.shiftedLogVolume ↔
        localExponent = 0 ∨ localPrimeStepLogVolume = 0) := by
  intro finite global endpoint
  exact
    ⟨global.calibratedLogVolume_eq_unshifted,
      by
        rw [global.calibratedLogVolume_eq_unshifted]
        exact finite.thetaRealLogVolume_eq_hull,
      endpoint.cTheta_ge_neg_one,
      global.calibratedLogVolume_eq_shifted_iff_exponent_zero_or_step_zero⟩

theorem thetaFinite_globalFrobenioidCThetaEndpoint_orderedShift
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (localExponent : Int)
    (localPrimeStepLogVolume : Real)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    let finite := data.toThetaFiniteLogVolumeEndpoint;
    let global :=
      data.toGlobalFrobenioidLogVolumeCalibration
        localExponent localPrimeStepLogVolume;
    let endpoint :=
      data.toQPilotTwoComputationCThetaEndpoint
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ;
    global.calibratedLogVolume = finite.thetaRealLogVolume ∧
      global.calibratedLogVolume = data.thetaHullLogVolume ∧
      (-1 : Real) <= endpoint.cTheta ∧
      (global.calibratedLogVolume < global.localData.shiftedLogVolume ↔
        0 < (localExponent : Real) * localPrimeStepLogVolume) ∧
      (global.localData.shiftedLogVolume < global.calibratedLogVolume ↔
        (localExponent : Real) * localPrimeStepLogVolume < 0) := by
  intro finite global endpoint
  exact
    ⟨global.calibratedLogVolume_eq_unshifted,
      by
        rw [global.calibratedLogVolume_eq_unshifted]
        exact finite.thetaRealLogVolume_eq_hull,
      endpoint.cTheta_ge_neg_one,
      global.calibratedLogVolume_lt_shifted_iff_shiftTerm_pos,
      global.shiftedLogVolume_lt_calibrated_iff_shiftTerm_lt_zero⟩

theorem fixedQPilotCTheta_endpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    let endpoint :=
      data.toQPilotTwoComputationCThetaEndpoint
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ;
    -endpoint.absLogQ <= endpoint.cTheta * endpoint.absLogQ ∧
      (-1 : Real) <= endpoint.cTheta ∧
      ¬ (cTheta < (-1 : Real)) := by
  intro endpoint
  exact
    ⟨endpoint.fixed_qPilotLogVolume_le_cTheta_absLogQ,
      endpoint.cTheta_ge_neg_one_from_fixed_qPilot,
      endpoint.not_cTheta_lt_neg_one_from_fixed_qPilot⟩

theorem xiF_upperRayCTheta_endpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    data.qPilotLogVolume ∈
        data.toHullDetPilotUpperRayLogVolume.upperRay ∧
      data.qPilotLogVolume <= data.thetaHullLogVolume ∧
      data.thetaHullLogVolume <= cTheta * (-data.qPilotLogVolume) ∧
      data.qPilotLogVolume <= cTheta * (-data.qPilotLogVolume) ∧
      (-1 : Real) <= cTheta ∧
      ¬ cTheta < (-1 : Real) := by
  have hTheta :
      data.thetaHullLogVolume <= cTheta * (-data.qPilotLogVolume) := by
    rw [data.q_eq_beforeAverage]
    exact thetaHull_le_cTheta_absLogQ
  have hCTheta := data.cTheta_ge_neg_one
    q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
  exact
    ⟨data.toUpperRay_q_mem,
      data.qPilotLogVolume_le_thetaHullLogVolume,
      hTheta,
      le_trans data.qPilotLogVolume_le_thetaHullLogVolume hTheta,
      hCTheta,
      not_lt_of_ge hCTheta⟩

theorem xiF_upperRayCTheta_distinctIntertwining_endpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (transport : IUTStage1DistinctLabelIntertwiningTransport)
    (hq : transport.qIntertwining) :
    let endpoint :=
      data.toQPilotTwoComputationCThetaEndpoint
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ;
    data.qPilotLogVolume ∈
        data.toHullDetPilotUpperRayLogVolume.upperRay ∧
      data.qPilotLogVolume <= data.thetaHullLogVolume ∧
      data.thetaHullLogVolume <= endpoint.cTheta * (-data.qPilotLogVolume) ∧
      data.qPilotLogVolume <= endpoint.cTheta * (-data.qPilotLogVolume) ∧
      (-1 : Real) <= endpoint.cTheta ∧
      Corollary312Inequality
        endpoint.toSignedCThetaBound.comparison.thetaPilot
        endpoint.toSignedCThetaBound.comparison.qPilot ∧
      transport.qLabel ≠ transport.thetaLabel ∧
      transport.weakenedPrimeStripCannotDistinguishPilots ∧
      transport.qIntertwining ∧
      transport.thetaIntertwiningUpToIndeterminacy := by
  intro endpoint
  have hxi :=
    data.xiF_upperRayCTheta_endpoint
      q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
  exact
    ⟨hxi.1, hxi.2.1, hxi.2.2.1, hxi.2.2.2.1,
      hxi.2.2.2.2.1,
      endpoint.toSignedCThetaBound.comparison.corollary312,
      transport.labels_distinct,
      transport.weakenedPrimeStripCondition,
      hq, transport.theta_from_q hq⟩

theorem signedCThetaComparison_endpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    let endpoint :=
      data.toQPilotTwoComputationCThetaEndpoint
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ;
    endpoint.toSignedCThetaBound.comparison.qSigned =
        data.corridor.beforeIndeterminacy.averageLogVolume ∧
      endpoint.toSignedCThetaBound.comparison.thetaSigned =
        data.thetaHullLogVolume ∧
      endpoint.toSignedCThetaBound.comparison.qSigned <=
        endpoint.toSignedCThetaBound.comparison.thetaSigned ∧
      endpoint.toSignedCThetaBound.comparison.qSigned <=
        endpoint.toSignedCThetaBound.cTheta *
          (-endpoint.toSignedCThetaBound.comparison.qSigned) ∧
      (-1 : Real) <= endpoint.toSignedCThetaBound.cTheta := by
  intro endpoint
  exact
    ⟨rfl, rfl,
      endpoint.toSignedCThetaBound.comparison.qSigned_le_thetaSigned,
      endpoint.toSignedCThetaBound.qSigned_le_cTheta_absLogQ,
      endpoint.toSignedCThetaBound.cTheta_ge_neg_one⟩

theorem signedCThetaComparison_corollary312
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    let endpoint :=
      data.toQPilotTwoComputationCThetaEndpoint
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ;
    Corollary312Inequality
      endpoint.toSignedCThetaBound.comparison.thetaPilot
      endpoint.toSignedCThetaBound.comparison.qPilot := by
  intro endpoint
  exact endpoint.toSignedCThetaBound.comparison.corollary312

theorem signedCThetaComparison_corollary312_magnitudes
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    let endpoint :=
      data.toQPilotTwoComputationCThetaEndpoint
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ;
    endpoint.toSignedCThetaBound.comparison.qPilot.value =
        -data.corridor.beforeIndeterminacy.averageLogVolume ∧
      endpoint.toSignedCThetaBound.comparison.thetaPilot.value =
        -data.thetaHullLogVolume ∧
      Corollary312Inequality
        endpoint.toSignedCThetaBound.comparison.thetaPilot
        endpoint.toSignedCThetaBound.comparison.qPilot := by
  intro endpoint
  exact
    ⟨rfl, rfl,
      endpoint.toSignedCThetaBound.comparison.corollary312⟩

def toStatementEndpoint
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    IUTStage1Corollary312StatementEndpoint :=
  (data.toQPilotTwoComputationCThetaEndpoint
    q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ).toStatementEndpoint
      pilotBoundary

theorem statementEndpoint_thetaExtendedFinite
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).finiteEndpoint.thetaExtended.IsFinite :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ).thetaExtendedFinite

theorem statementEndpoint_thetaExtended_ne_plusInfinity
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).finiteEndpoint.thetaExtended ≠
      IUTStage1ExtendedSignedLogVolume.plusInfinity :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ).thetaExtended_ne_plusInfinity

theorem statementEndpoint_thetaFiniteValue_eq_ind3Upper
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    IUTStage1ExtendedSignedLogVolume.finiteValueOrZero
        (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
          thetaHull_le_cTheta_absLogQ).finiteEndpoint.thetaExtended =
      data.corridor.ind3UpperBound := by
  rw [(data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).finiteEndpoint.thetaFiniteValue_eq_hull]
  change data.thetaHullLogVolume = data.corridor.ind3UpperBound
  exact data.theta_eq_ind3Upper

theorem statementEndpoint_qPilotNotSubject
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).pilotBoundary.qStatus =
      IUTStage1Corollary312PilotIndeterminacyStatus.notSubjectToIndeterminacies :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ).qPilotNotSubject

theorem statementEndpoint_thetaPilotSubject
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).pilotBoundary.thetaStatus =
      IUTStage1Corollary312PilotIndeterminacyStatus.subjectToIndeterminacies :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ).thetaPilotSubject

theorem statementEndpoint_thetaStatus_ne_qStatus
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).pilotBoundary.thetaStatus ≠
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).pilotBoundary.qStatus :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ).pilotBoundary.thetaStatus_ne_qStatus

theorem statementEndpoint_qPilotLogVolume_eq_beforeAverage
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).finiteEndpoint.upperRayData.qPilotLogVolume =
      data.corridor.beforeIndeterminacy.averageLogVolume :=
  data.q_eq_beforeAverage

theorem statementEndpoint_absLogQ_eq_neg_beforeAverage
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    -((data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).finiteEndpoint.upperRayData.qPilotLogVolume) =
      -data.corridor.beforeIndeterminacy.averageLogVolume := by
  rw [data.statementEndpoint_qPilotLogVolume_eq_beforeAverage
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ]

theorem statementEndpoint_absLogQ_pos
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    0 < -((data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).finiteEndpoint.upperRayData.qPilotLogVolume) :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ).q_pilot_positive

theorem beforeAverage_neg_of_qPilotPositive
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume) :
    data.corridor.beforeIndeterminacy.averageLogVolume < 0 := by
  linarith

theorem afterInd1Average_neg_of_qPilotPositive
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume) :
    data.corridor.afterInd1.averageLogVolume < 0 := by
  rw [data.corridor.afterInd1_average_eq_before]
  exact data.beforeAverage_neg_of_qPilotPositive q_pilot_positive

theorem afterInd2Average_neg_of_qPilotPositive
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume) :
    data.corridor.afterInd2.averageLogVolume < 0 := by
  rw [data.corridor.afterInd2_average_eq_before]
  exact data.beforeAverage_neg_of_qPilotPositive q_pilot_positive

theorem statementEndpoint_qPilotLogVolume_eq_afterInd1Average
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).finiteEndpoint.upperRayData.qPilotLogVolume =
      data.corridor.afterInd1.averageLogVolume := by
  rw [data.statementEndpoint_qPilotLogVolume_eq_beforeAverage
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ,
    data.corridor.afterInd1_average_eq_before]

theorem statementEndpoint_qPilotLogVolume_eq_afterInd2Average
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).finiteEndpoint.upperRayData.qPilotLogVolume =
      data.corridor.afterInd2.averageLogVolume := by
  rw [data.statementEndpoint_qPilotLogVolume_eq_beforeAverage
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ,
    data.corridor.afterInd2_average_eq_before]

theorem statementEndpoint_thetaRealLogVolume_eq_hull
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).thetaRealLogVolume =
      data.thetaHullLogVolume :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ).thetaRealLogVolume_eq_hull

theorem statementEndpoint_thetaRealLogVolume_eq_ind3Upper
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).thetaRealLogVolume =
      data.corridor.ind3UpperBound := by
  rw [data.statementEndpoint_thetaRealLogVolume_eq_hull
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ,
    data.theta_eq_ind3Upper]

theorem statementEndpoint_qPilotLogVolume_mem_upperRay
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).finiteEndpoint.upperRayData.qPilotLogVolume ∈
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).finiteEndpoint.upperRayData.upperRay :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ).qPilotLogVolume_mem_upperRay

theorem ofZModCuspLabelLogVolumeCompatibilities_statementEndpoint
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -before.toLabelAveraged.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      thetaHullLogVolume <= cTheta * (-before.toLabelAveraged.averageLogVolume)) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant
    let endpoint :=
      data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ
    endpoint.finiteEndpoint.upperRayData.qPilotLogVolume =
        before.toLabelAveraged.averageLogVolume ∧
      endpoint.finiteEndpoint.upperRayData.qPilotLogVolume ∈
        endpoint.finiteEndpoint.upperRayData.upperRay ∧
      endpoint.thetaRealLogVolume = ind3UpperBound ∧
      endpoint.pilotBoundary.qStatus =
        IUTStage1Corollary312PilotIndeterminacyStatus.notSubjectToIndeterminacies ∧
      endpoint.pilotBoundary.thetaStatus =
        IUTStage1Corollary312PilotIndeterminacyStatus.subjectToIndeterminacies ∧
      endpoint.pilotBoundary.thetaStatus ≠ endpoint.pilotBoundary.qStatus := by
  intro data endpoint
  exact
    ⟨data.statementEndpoint_qPilotLogVolume_eq_beforeAverage
        pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ,
      data.statementEndpoint_qPilotLogVolume_mem_upperRay
        pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ,
      data.statementEndpoint_thetaRealLogVolume_eq_ind3Upper
        pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ,
      data.statementEndpoint_qPilotNotSubject
        pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ,
      data.statementEndpoint_thetaPilotSubject
        pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ,
      data.statementEndpoint_thetaStatus_ne_qStatus
        pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ⟩

theorem statementEndpoint_qPilotLogVolume_le_thetaRealLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).finiteEndpoint.upperRayData.qPilotLogVolume <=
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).thetaRealLogVolume :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ).qPilotLogVolume_le_thetaRealLogVolume

theorem statementEndpoint_qPilotLogVolume_lt_thetaRealLogVolume_of_theta_nonneg
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hTheta :
      0 <= (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).thetaRealLogVolume) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).finiteEndpoint.upperRayData.qPilotLogVolume <
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).thetaRealLogVolume :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ).qPilotLogVolume_lt_thetaRealLogVolume_of_theta_nonneg
      hTheta

theorem beforeAverage_lt_statementEndpoint_thetaRealLogVolume_of_theta_nonneg
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hTheta :
      0 <= (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).thetaRealLogVolume) :
    data.corridor.beforeIndeterminacy.averageLogVolume <
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).thetaRealLogVolume := by
  rw [← data.statementEndpoint_qPilotLogVolume_eq_beforeAverage
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ]
  exact data.statementEndpoint_qPilotLogVolume_lt_thetaRealLogVolume_of_theta_nonneg
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hTheta

theorem statementEndpoint_cTheta_nonnegative_of_thetaRealLogVolume_nonnegative
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hTheta :
      0 <= (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).thetaRealLogVolume) :
    0 <=
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).cTheta :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ).cTheta_nonnegative_of_thetaRealLogVolume_nonnegative
      hTheta

theorem ofZModCuspLabelLogVolumeCompatibilities_thetaNonnegativeBranch
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -before.toLabelAveraged.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      thetaHullLogVolume <= cTheta * (-before.toLabelAveraged.averageLogVolume))
    (theta_nonnegative : 0 <= ind3UpperBound) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant
    let endpoint :=
      data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ
    before.toLabelAveraged.averageLogVolume < ind3UpperBound ∧
      0 <= endpoint.cTheta := by
  intro data endpoint
  have hThetaEndpoint :
      0 <= endpoint.thetaRealLogVolume := by
    rw [data.statementEndpoint_thetaRealLogVolume_eq_ind3Upper
      pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ]
    exact theta_nonnegative
  have hlt :
      before.toLabelAveraged.averageLogVolume <
        endpoint.thetaRealLogVolume :=
    data.beforeAverage_lt_statementEndpoint_thetaRealLogVolume_of_theta_nonneg
      pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
      hThetaEndpoint
  rw [data.statementEndpoint_thetaRealLogVolume_eq_ind3Upper
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ] at hlt
  exact
    ⟨hlt,
      data.statementEndpoint_cTheta_nonnegative_of_thetaRealLogVolume_nonnegative
        pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
        hThetaEndpoint⟩

theorem ofZModCuspLabelLogVolumeCompatibilities_corollary312_of_thetaNonnegative
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -before.toLabelAveraged.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      thetaHullLogVolume <= cTheta * (-before.toLabelAveraged.averageLogVolume))
    (theta_nonnegative : 0 <= ind3UpperBound) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant
    let endpoint :=
      data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ
    ∃ hTheta : 0 <= endpoint.thetaRealLogVolume,
      Corollary312Inequality
        (endpoint.toThetaSignReduction.comparisonDataOfThetaNonnegative
          hTheta).thetaPilot
        (endpoint.toThetaSignReduction.comparisonDataOfThetaNonnegative
          hTheta).qPilot := by
  intro data endpoint
  have hThetaEndpoint :
      0 <= endpoint.thetaRealLogVolume := by
    rw [data.statementEndpoint_thetaRealLogVolume_eq_ind3Upper
      pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ]
    exact theta_nonnegative
  exact
    ⟨hThetaEndpoint,
      endpoint.corollary312_of_thetaRealLogVolume_nonnegative hThetaEndpoint⟩

theorem beforeAverage_le_statementEndpoint_ind3Upper
    (data : IUTStage1StepXToHullUpperRayLogVolume label) :
    data.corridor.beforeIndeterminacy.averageLogVolume <=
      data.corridor.ind3UpperBound :=
  data.corridor.before_average_le_ind3UpperBound

theorem beforeAverage_le_statementEndpoint_thetaRealLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    data.corridor.beforeIndeterminacy.averageLogVolume <=
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).thetaRealLogVolume := by
  rw [data.statementEndpoint_thetaRealLogVolume_eq_hull
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ]
  rw [← data.q_eq_beforeAverage]
  exact data.qPilotLogVolume_le_thetaHullLogVolume

theorem statementEndpoint_thetaRealLogVolume_le_cTheta_absLogQ
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).thetaRealLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume) := by
  have h :=
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).thetaRealLogVolume_le_cTheta_absLogQ
  simpa [data.statementEndpoint_qPilotLogVolume_eq_beforeAverage
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ] using h

theorem beforeAverage_le_cTheta_absLogQ
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    data.corridor.beforeIndeterminacy.averageLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume) :=
  le_trans
    (data.beforeAverage_le_statementEndpoint_thetaRealLogVolume
      pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ)
    (data.statementEndpoint_thetaRealLogVolume_le_cTheta_absLogQ
      pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ)

theorem afterInd1Average_le_statementEndpoint_thetaRealLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    data.corridor.afterInd1.averageLogVolume <=
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).thetaRealLogVolume := by
  rw [data.corridor.afterInd1_average_eq_before]
  exact data.beforeAverage_le_statementEndpoint_thetaRealLogVolume
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ

theorem afterInd2Average_le_statementEndpoint_thetaRealLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    data.corridor.afterInd2.averageLogVolume <=
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).thetaRealLogVolume := by
  rw [data.corridor.afterInd2_average_eq_before]
  exact data.beforeAverage_le_statementEndpoint_thetaRealLogVolume
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ

theorem statementEndpoint_cTheta_ge_neg_one
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    (-1 : Real) <=
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).cTheta :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ).cTheta_ge_neg_one

theorem statementEndpoint_cTheta_gt_neg_one_of_beforeAverage_lt_thetaRealLogVolume
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hstrict :
      data.corridor.beforeIndeterminacy.averageLogVolume <
        (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
          thetaHull_le_cTheta_absLogQ).thetaRealLogVolume) :
    (-1 : Real) <
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).cTheta := by
  apply
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).cTheta_gt_neg_one_of_qPilot_lt_thetaRealLogVolume
  rw [data.statementEndpoint_qPilotLogVolume_eq_beforeAverage
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ]
  exact hstrict

theorem statementEndpoint_cTheta_gt_neg_one_of_thetaRealLogVolume_nonnegative
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hTheta :
      0 <= (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).thetaRealLogVolume) :
    (-1 : Real) <
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).cTheta :=
  data.statementEndpoint_cTheta_gt_neg_one_of_beforeAverage_lt_thetaRealLogVolume
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
    (data.beforeAverage_lt_statementEndpoint_thetaRealLogVolume_of_theta_nonneg
      pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ
      hTheta)

theorem statementEndpoint_qPilotLogVolume_eq_thetaRealLogVolume_of_cTheta_eq_neg_one
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
      thetaHull_le_cTheta_absLogQ).finiteEndpoint.upperRayData.qPilotLogVolume =
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).thetaRealLogVolume :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ)
      |>.qPilotLogVolume_eq_thetaRealLogVolume_of_cTheta_eq_neg_one hC

theorem beforeAverage_eq_statementEndpoint_thetaRealLogVolume_of_cTheta_eq_neg_one
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    data.corridor.beforeIndeterminacy.averageLogVolume =
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).thetaRealLogVolume := by
  have h :=
    data.statementEndpoint_qPilotLogVolume_eq_thetaRealLogVolume_of_cTheta_eq_neg_one
      pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC
  rw [data.statementEndpoint_qPilotLogVolume_eq_beforeAverage
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ] at h
  exact h

theorem beforeAverage_eq_thetaHullLogVolume_of_cTheta_eq_neg_one
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    data.corridor.beforeIndeterminacy.averageLogVolume =
      data.thetaHullLogVolume := by
  have h :=
    data.beforeAverage_eq_statementEndpoint_thetaRealLogVolume_of_cTheta_eq_neg_one
      pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC
  rw [data.statementEndpoint_thetaRealLogVolume_eq_hull
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ] at h
  exact h

theorem not_beforeAverage_lt_statementEndpoint_thetaRealLogVolume_of_cTheta_eq_neg_one
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    ¬ data.corridor.beforeIndeterminacy.averageLogVolume <
      (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).thetaRealLogVolume := by
  rw [data.beforeAverage_eq_statementEndpoint_thetaRealLogVolume_of_cTheta_eq_neg_one
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC]
  exact lt_irrefl _

theorem thetaHullLogVolume_neg_of_cTheta_eq_neg_one
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    data.thetaHullLogVolume < 0 := by
  rw [← data.beforeAverage_eq_thetaHullLogVolume_of_cTheta_eq_neg_one
    pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC]
  linarith [q_pilot_positive]

theorem not_thetaHullLogVolume_nonnegative_of_cTheta_eq_neg_one
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume))
    (hC : cTheta = (-1 : Real)) :
    ¬ 0 <= data.thetaHullLogVolume :=
  not_le_of_gt
    (data.thetaHullLogVolume_neg_of_cTheta_eq_neg_one
      pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ hC)

theorem statementEndpoint_cTheta_eq_neg_one_or_gt_neg_one
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    cTheta = (-1 : Real) ∨ (-1 : Real) < cTheta :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ).cTheta_eq_neg_one_or_gt_neg_one

theorem statementEndpoint_not_cTheta_lt_neg_one
    (data : IUTStage1StepXToHullUpperRayLogVolume label)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -data.corridor.beforeIndeterminacy.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      data.thetaHullLogVolume <=
        cTheta * (-data.corridor.beforeIndeterminacy.averageLogVolume)) :
    ¬ (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ).cTheta < (-1 : Real) :=
  (data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
    thetaHull_le_cTheta_absLogQ).not_cTheta_lt_neg_one

theorem ofZModCuspLabelLogVolumeCompatibilities_cThetaLowerBound
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume)
    (pilotBoundary : IUTStage1Corollary312PilotIndeterminacyBoundary)
    (q_pilot_positive :
      0 < -before.toLabelAveraged.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      thetaHullLogVolume <= cTheta * (-before.toLabelAveraged.averageLogVolume)) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant
    let endpoint :=
      data.toStatementEndpoint pilotBoundary q_pilot_positive cTheta
        thetaHull_le_cTheta_absLogQ
    before.toLabelAveraged.averageLogVolume <=
        cTheta * (-before.toLabelAveraged.averageLogVolume) ∧
      (-1 : Real) <= endpoint.cTheta ∧
      ¬ endpoint.cTheta < (-1 : Real) := by
  intro data endpoint
  exact
    ⟨data.beforeAverage_le_cTheta_absLogQ
        pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ,
      data.statementEndpoint_cTheta_ge_neg_one
        pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ,
      data.statementEndpoint_not_cTheta_lt_neg_one
        pilotBoundary q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ⟩

theorem ofZModCuspLabelLogVolumeCompatibilities_fixedQPilotCThetaEndpoint
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume)
    (q_pilot_positive :
      0 < -before.toLabelAveraged.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      thetaHullLogVolume <= cTheta * (-before.toLabelAveraged.averageLogVolume)) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant;
    let endpoint :=
      data.toQPilotTwoComputationCThetaEndpoint
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ;
    -endpoint.absLogQ <= endpoint.cTheta * endpoint.absLogQ ∧
      (-1 : Real) <= endpoint.cTheta ∧
      ¬ (cTheta < (-1 : Real)) := by
  intro data endpoint
  exact data.fixedQPilotCTheta_endpoint
    q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ

theorem ofZModCuspLabelLogVolumeCompatibilities_signedCThetaComparison
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume)
    (q_pilot_positive :
      0 < -before.toLabelAveraged.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      thetaHullLogVolume <= cTheta * (-before.toLabelAveraged.averageLogVolume)) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant;
    let endpoint :=
      data.toQPilotTwoComputationCThetaEndpoint
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ;
    endpoint.toSignedCThetaBound.comparison.qSigned =
        before.toLabelAveraged.averageLogVolume ∧
      endpoint.toSignedCThetaBound.comparison.thetaSigned =
        thetaHullLogVolume ∧
      endpoint.toSignedCThetaBound.comparison.qSigned <=
        endpoint.toSignedCThetaBound.comparison.thetaSigned ∧
      endpoint.toSignedCThetaBound.comparison.qSigned <=
        endpoint.toSignedCThetaBound.cTheta *
          (-endpoint.toSignedCThetaBound.comparison.qSigned) ∧
      (-1 : Real) <= endpoint.toSignedCThetaBound.cTheta := by
  intro data endpoint
  exact data.signedCThetaComparison_endpoint
    q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ

theorem ofZModCuspLabelLogVolumeCompatibilities_signedCorollary312
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume)
    (q_pilot_positive :
      0 < -before.toLabelAveraged.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      thetaHullLogVolume <= cTheta * (-before.toLabelAveraged.averageLogVolume)) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant;
    let endpoint :=
      data.toQPilotTwoComputationCThetaEndpoint
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ;
    Corollary312Inequality
      endpoint.toSignedCThetaBound.comparison.thetaPilot
      endpoint.toSignedCThetaBound.comparison.qPilot := by
  intro data endpoint
  exact data.signedCThetaComparison_corollary312
    q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ

theorem ofZModCuspLabelLogVolumeCompatibilities_signedCorollary312_magnitudes
    {l : PrimeGeFive}
    (before afterInd1 afterInd2 :
      IUTStage1ZModCuspLabelLogVolumeCompatibility l)
    (ind3UpperBound : Real)
    (hind1 :
      ∀ j : ZMod l.value,
        before.normalizedLogVolume j =
          afterInd1.normalizedLogVolume j)
    (hind2 :
      ∀ j : ZMod l.value,
        afterInd1.normalizedLogVolume j =
          afterInd2.normalizedLogVolume j)
    (hzero : afterInd2.zeroLogVolume <= ind3UpperBound)
    (hcusp : ∀ label : (zmodSignAction l).SignLabelQuotient,
      afterInd2.cuspClassLogVolume label <= ind3UpperBound)
    (determinant :
      IUTStage1ArithmeticVectorBundleDeterminantLogVolume)
    (thetaHullLogVolume : Real)
    (theta_eq_ind3Upper :
      thetaHullLogVolume = ind3UpperBound)
    (theta_eq_normalized_determinant :
      thetaHullLogVolume = determinant.normalizedLogVolume)
    (q_pilot_positive :
      0 < -before.toLabelAveraged.averageLogVolume)
    (cTheta : Real)
    (thetaHull_le_cTheta_absLogQ :
      thetaHullLogVolume <= cTheta * (-before.toLabelAveraged.averageLogVolume)) :
    let data :=
      ofZModCuspLabelLogVolumeCompatibilities before afterInd1 afterInd2
        ind3UpperBound hind1 hind2 hzero hcusp determinant thetaHullLogVolume
        theta_eq_ind3Upper theta_eq_normalized_determinant;
    let endpoint :=
      data.toQPilotTwoComputationCThetaEndpoint
        q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ;
    endpoint.toSignedCThetaBound.comparison.qPilot.value =
        -before.toLabelAveraged.averageLogVolume ∧
      endpoint.toSignedCThetaBound.comparison.thetaPilot.value =
        -thetaHullLogVolume ∧
      Corollary312Inequality
        endpoint.toSignedCThetaBound.comparison.thetaPilot
        endpoint.toSignedCThetaBound.comparison.qPilot := by
  intro data endpoint
  exact data.signedCThetaComparison_corollary312_magnitudes
    q_pilot_positive cTheta thetaHull_le_cTheta_absLogQ

end IUTStage1StepXToHullUpperRayLogVolume
end Stage1
end Iut
