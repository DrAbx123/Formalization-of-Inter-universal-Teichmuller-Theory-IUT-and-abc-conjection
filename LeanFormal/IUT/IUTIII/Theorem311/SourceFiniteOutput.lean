import LeanFormal.IUT.IUTIII.Theorem311.ConcreteFiniteModelTransport
import LeanFormal.IUT.IUTII.Theta.ConcreteSourceHistoryLinkBridge
import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

local instance primeFactForSourceTheorem311 (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) := l.factPrime

namespace SourceFiniteTheorem311

open ConcreteSourceHistoryLinkBridge
open ConcreteFiniteTheorem311

structure Output (l : PrimeGeFive) where
  algebraic : ConcreteSourceEtaleThetaBridge.ConcreteSourceAlgebraicThetaOutput l
  history : ConcreteSourceHistoryLinkOutput l
  procession : ConcreteFiniteTheorem311.FiniteOutput l
  history_terminal_eq_procession_theater :
    history.terminal = procession.sourceTheater
  history_level_eq_algebraic_level :
    history.level = algebraic.level
  history_model_eq_algebraic_model :
    history.sourceModel = algebraic.sourceModel

noncomputable def output (l : PrimeGeFive) : Output l where
  algebraic := ConcreteSourceEtaleThetaBridge.concreteSourceAlgebraicThetaOutput l
  history := concreteSourceHistoryLinkOutput l
  procession := ConcreteFiniteTheorem311.finiteOutput l
  history_terminal_eq_procession_theater := by
    rfl
  history_level_eq_algebraic_level := by
    rfl
  history_model_eq_algebraic_model := by
    rfl

theorem output_history_terminal (l : PrimeGeFive) :
    (output l).history.terminal = (output l).procession.sourceTheater :=
  (output l).history_terminal_eq_procession_theater

theorem output_history_level (l : PrimeGeFive) :
    (output l).history.level =
      ConcreteSourceEtaleThetaBridge.algebraicFiniteThetaLevel l := by
  simp [output]

theorem output_algebraic_level (l : PrimeGeFive) :
    (output l).algebraic.level =
      ConcreteSourceEtaleThetaBridge.algebraicFiniteThetaLevel l := by
  simp [output]

theorem output_history_model (l : PrimeGeFive) :
    (output l).history.sourceModel = ConcreteSourceEtaleThetaBridge.sourceModel := by
  simp [output]

theorem output_algebraic_model (l : PrimeGeFive) :
    (output l).algebraic.sourceModel = ConcreteSourceEtaleThetaBridge.sourceModel := by
  simp [output]

theorem output_models_agree (l : PrimeGeFive) :
    (output l).history.sourceModel = (output l).algebraic.sourceModel :=
  (output l).history_model_eq_algebraic_model

theorem output_reduction_kernel (l : PrimeGeFive) :
    (ConcreteSourceEtaleThetaBridge.reduction l).ker =
      AddSubgroup.zmultiples (l.value : ℤ) :=
  ConcreteSourceEtaleThetaBridge.reduction_kernel l

theorem output_reduction_surjective (l : PrimeGeFive) :
    Function.Surjective (ConcreteSourceEtaleThetaBridge.reduction l) :=
  ConcreteSourceEtaleThetaBridge.reduction_surjective l

theorem output_generator_order (l : PrimeGeFive) :
    addOrderOf (ConcreteSourceEtaleThetaBridge.generator l) = l.value :=
  ConcreteSourceEtaleThetaBridge.generator_order l

theorem output_generator_ne_zero (l : PrimeGeFive) :
    ConcreteSourceEtaleThetaBridge.generator l ≠ 0 :=
  ConcreteSourceEtaleThetaBridge.generator_ne_zero l

theorem output_root_compatibility (l : PrimeGeFive) (n : ℤ) :
    (ConcreteSourceEtaleThetaBridge.packet l).integerRoot n =
      (ConcreteSourceEtaleThetaBridge.roots l).roots (n : ℚ) :=
  ConcreteSourceEtaleThetaBridge.integer_root_compatible l n

theorem output_level_quotient_apply (l : PrimeGeFive) (n : ℤ) :
    (ConcreteSourceEtaleThetaBridge.algebraicFiniteThetaLevel l).quotientEquiv
        (QuotientAddGroup.mk n) =
      ConcreteSourceEtaleThetaBridge.reduction l n :=
  ConcreteSourceEtaleThetaBridge.quotientEquiv_apply_mk l n

theorem output_level_quotient_bijective (l : PrimeGeFive) :
    Function.Bijective
      (ConcreteSourceEtaleThetaBridge.algebraicFiniteThetaLevel l).quotientEquiv := by
  constructor
  · exact (ConcreteSourceEtaleThetaBridge.algebraicFiniteThetaLevel l).quotientEquiv_injective
  · exact (ConcreteSourceEtaleThetaBridge.algebraicFiniteThetaLevel l).quotientEquiv_surjective

theorem output_history_to_terminal_q (l : PrimeGeFive) :
    (output l).history.terminal.thetaPacket.q =
      (output l).history.history.terminal.thetaPacket.q := by
  exact history_output_terminal_eq_history l ▸ rfl

theorem output_history_packet_volume (l : PrimeGeFive) :
    (output l).history.terminal.thetaPacket.logVolume =
      ConcreteSourceEtaleThetaBridge.thetaLogVolume l :=
  history_output_packet_volume l

theorem output_history_determinant_log (l : PrimeGeFive) :
    Real.log (sourceHistoryDeterminant l) = thetaLogVolume l :=
  sourceHistoryDeterminant_log l

theorem output_history_determinant_positive (l : PrimeGeFive) :
    0 < sourceHistoryDeterminant l :=
  sourceHistoryDeterminant_positive l

theorem output_history_determinant_exp (l : PrimeGeFive) :
    Real.exp (thetaLogVolume l) = sourceHistoryDeterminant l :=
  sourceHistoryDeterminant_exp l

theorem output_history_tensor_log (l : PrimeGeFive) :
    Real.log (packetDet (sourceTensorPacket l)) =
      (2 * (Fintype.card (sourceFiniteLabel l) : Real)) *
        ConcreteSourceEtaleThetaBridge.thetaLogVolume l :=
  sourceHistoryDeterminant_tensor_log l

theorem output_normalization_identity :
    sourceNormalizationPacket.weightedLogVolume =
      (sourceNormalizationPacket.commonTensorDegree : Real) *
        sourceNormalizationPacket.normalizedLogVolume :=
  sourceNormalizationPacket_weighted_identity

theorem output_normalization_degree :
    sourceNormalizationPacket.commonTensorDegree = 8 :=
  sourceNormalizationPacket_common_degree

theorem procession_ind1_invariant (l : PrimeGeFive)
    (t : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l) :
    (output l).procession.logVolume (ProcessionChoice.ind1Act t c) =
      (output l).procession.logVolume c := by
  exact (output l).procession.ind1_invariant t c

theorem procession_ind2_invariant (l : PrimeGeFive)
    (t : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l) :
    (output l).procession.logVolume (ProcessionChoice.ind2Act t c) =
      (output l).procession.logVolume c := by
  exact (output l).procession.ind2_invariant t c

theorem procession_ind3_upper (l : PrimeGeFive)
    (n : Nat) (c : ProcessionChoice l) :
    (output l).procession.logVolume c ≤
      (output l).procession.logVolume (ProcessionChoice.ind3Lift n c) := by
  exact (output l).procession.ind3_upper n c

theorem procession_possible_nonempty (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    ((output l).procession.possibleImage c).Nonempty := by
  exact (output l).procession.possibleImage_nonempty c

theorem procession_possible_ind1 (l : PrimeGeFive)
    (t : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l) :
    (output l).procession.possibleImage (ProcessionChoice.ind1Act t c) =
      (output l).procession.possibleImage c := by
  exact (output l).procession.possibleImage_ind1 t c

theorem procession_possible_ind2 (l : PrimeGeFive)
    (t : ConcreteFiniteTheorem311.finiteLabel l) (c : ProcessionChoice l) :
    (output l).procession.possibleImage (ProcessionChoice.ind2Act t c) =
      (output l).procession.possibleImage c := by
  exact (output l).procession.possibleImage_ind2 t c

theorem procession_possible_ind3_upper (l : PrimeGeFive)
    (n : Nat) (c : ProcessionChoice l) (z : Real)
    (hz : z ∈ (output l).procession.possibleImage c) :
    ∃ w, w ∈ (output l).procession.possibleImage
      (ProcessionChoice.ind3Lift n c) ∧ z ≤ w := by
  exact (output l).procession.possibleImage_ind3 n c z hz

theorem procession_base_log_volume (l : PrimeGeFive) :
    (output l).procession.logVolume (output l).procession.baseChoice =
      ConcreteSourceEtaleThetaBridge.thetaLogVolume l := by
  change normalizedLogVolume l ProcessionChoice.base = thetaLogVolume l
  exact normalizedLogVolume_base l

theorem procession_base_possible_nonempty (l : PrimeGeFive) :
    ((output l).procession.possibleImage
      (output l).procession.baseChoice).Nonempty := by
  exact procession_possible_nonempty l (output l).procession.baseChoice

theorem procession_generated_quotient_same_level
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    generatedQuotientMap l a = generatedQuotientMap l b :=
  generatedQuotient_same_level hlevel

theorem procession_generated_quotient_no_level_collapse
    {l : PrimeGeFive} {a b : ProcessionChoice l}
    (hlevel : a.upperSemiLevel ≠ b.upperSemiLevel) :
    generatedQuotientMap l a ≠ generatedQuotientMap l b :=
  generatedQuotient_no_level_collapse hlevel

theorem procession_quotient_image_nonempty (l : PrimeGeFive)
    (q : generatedQuotient l) :
    (quotientPossibleLogImage l q).Nonempty :=
  quotientPossibleLogImage_nonempty l q

theorem procession_quotient_ind3_upper
    {l : PrimeGeFive} (a : ProcessionChoice l) (n : Nat)
    (z : Real) (hz : z ∈ quotientPossibleLogImage l
      (generatedQuotientMap l a)) :
    ∃ w, w ∈ quotientPossibleLogImage l
      (generatedQuotientMap l (ProcessionChoice.ind3Lift n a)) ∧ z ≤ w :=
  quotientPossibleLogImage_level_ind3 a n z hz

theorem procession_log_volume_is_source_profile (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    (output l).procession.logVolume c =
      ConcreteSourceEtaleThetaBridge.thetaLogVolume l +
        (c.upperSemiLevel : Real) := by
  change normalizedLogVolume l c = _
  rfl

end SourceFiniteTheorem311

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteSourceTheorem311Output : Obligation :=
  { id := "IUT-III.concrete-source-theorem311-output"
    source := "IUT III, Theorem 3.11 (single concrete source carrier)"
    status := VerificationStatus.interface
    note :=
      "A source-facing Q(i)-at-5 carrier is assembled from the proved " ++
        "algebraic theta level, finite history link, and procession output. " ++
        "Its quotient, root, determinant, Ind1/Ind2, and Ind3 laws are proved. " ++
        "It is one explicit finite carrier and does not construct the arbitrary " ++
        "D-prime-strip multiradial output required by the paper."
    dependsOn :=
      [ "IUT-I-II.concrete-source-algebraic-theta-bridge",
        "IUT-I-II.concrete-source-history-link-volume-bridge",
        "IUT-III.concrete-finite-theorem311-model",
        "IUT-III.generic-quotient-transport",
        "IUT-III.orbit-quotient-transport",
        "IUT-III.Ind3.upper-semi-kernel" ] }

end LeanFormal.IUT.Audit
