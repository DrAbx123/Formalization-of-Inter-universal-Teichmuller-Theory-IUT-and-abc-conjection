/-
  Auditable C-layer boundary for the concrete input.

  The record contains exactly the constructions that are currently genuine:
  arithmetic, selected finite place, stable and split multiplicative
  reduction, finite prime-strip/theta carrier, and local Kummer packet.  It
  intentionally has no field for Tate point uniformization, anabelian
  reconstruction, or a theta-link to a distinct history.
-/

import LeanFormal.IUT.IUTI.InitialTheta.ConcreteInitialThetaFiniteArithmetic
import LeanFormal.IUT.IUTI.InitialTheta.SourceObligations
import LeanFormal.IUT.IUTII.Kummer.ConcreteEtaleKummerDirection

namespace LeanFormal.IUT

noncomputable section

local instance primeFactForConcreteC (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

local instance fivePrimeFactConcreteC : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

structure ConcreteCConstructedBoundary (l : PrimeGeFive) where
  finitePlaceInput : InitialThetaFinitePlaceInput l
  hodgeTheater : HodgeTheater l (FinitePrimePlace 2 7)
  localCarrier : ConcreteTateLocalCarrier l
  history : ConcreteInitialThetaHistory l
  selectedFiniteLabel : FinitePrimePlace 2 7
  selectedFiniteLabel_eq_five : selectedFiniteLabel = concreteInitialThetaLabel

noncomputable def concreteCConstructedBoundary (l : PrimeGeFive) :
    ConcreteCConstructedBoundary l where
  finitePlaceInput := concreteInitialThetaPlaceInput l
  hodgeTheater := concreteInitialThetaHodgeTheater l
  localCarrier := ConcreteTateLocalCarrier.canonical l
  history := concreteInitialThetaHistory l
  selectedFiniteLabel := concreteInitialThetaLabel
  selectedFiniteLabel_eq_five := rfl

@[simp] theorem concreteCConstructedBoundary_finitePlaceInput
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).finitePlaceInput =
      concreteInitialThetaPlaceInput l :=
  rfl

@[simp] theorem concreteCConstructedBoundary_hodgeTheater
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).hodgeTheater =
      concreteInitialThetaHodgeTheater l :=
  rfl

@[simp] theorem concreteCConstructedBoundary_localCarrier
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).localCarrier =
      ConcreteTateLocalCarrier.canonical l :=
  rfl

@[simp] theorem concreteCConstructedBoundary_history
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).history =
      concreteInitialThetaHistory l :=
  rfl

@[simp] theorem concreteCConstructedBoundary_selectedFiniteLabel
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).selectedFiniteLabel =
      concreteInitialThetaLabel :=
  (concreteCConstructedBoundary l).selectedFiniteLabel_eq_five

theorem concreteCConstructedBoundary_arithmetic_curve
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).finitePlaceInput.arithmetic.curve =
      (concreteGaussianInitialThetaArithmeticData l).curve := by
  change (concreteInitialThetaPlaceInput l).arithmetic.curve = _
  rfl

theorem concreteCConstructedBoundary_place
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).finitePlaceInput.place =
      concreteGaussianFivePlace := by
  change (concreteInitialThetaPlaceInput l).place = _
  rfl

theorem concreteCConstructedBoundary_place_stable
    (l : PrimeGeFive) :
    ((concreteCConstructedBoundary l).finitePlaceInput.arithmetic.curve).HasStableReductionAt
      (concreteCConstructedBoundary l).finitePlaceInput.place := by
  change ((concreteInitialThetaPlaceInput l).arithmetic.curve).HasStableReductionAt
    (concreteInitialThetaPlaceInput l).place
  exact concreteInitialThetaPlaceInput_stable l

theorem concreteCConstructedBoundary_place_multiplicative
    (l : PrimeGeFive) :
    let C := (concreteCConstructedBoundary l).finitePlaceInput.arithmetic.curve
    C.HasMultiplicativeReductionAt
      (concreteCConstructedBoundary l).finitePlaceInput.place := by
  dsimp
  change ((concreteInitialThetaPlaceInput l).arithmetic.curve).HasMultiplicativeReductionAt
    (concreteInitialThetaPlaceInput l).place
  exact concreteInitialThetaPlaceInput_multiplicative l

theorem concreteCConstructedBoundary_place_q_order_pos
    (l : PrimeGeFive) :
    0 < (concreteCConstructedBoundary l).finitePlaceInput.qCandidate.order := by
  change 0 < (concreteInitialThetaPlaceInput l).qCandidate.order
  exact concreteInitialThetaPlaceInput_q_order_pos l

theorem concreteCConstructedBoundary_place_q_ne_one
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).finitePlaceInput.qCandidate.q ≠ 1 := by
  change (concreteInitialThetaPlaceInput l).qCandidate.q ≠ 1
  exact concreteInitialThetaPlaceInput_q_ne_one l

theorem concreteCConstructedBoundary_local_q_prime
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).localCarrier.parameter.q =
      (l.value : ℚ_[l.value]) := by
  exact concreteInitialThetaCarrier_q_prime l

theorem concreteCConstructedBoundary_local_q_contracting
    (l : PrimeGeFive) :
    ‖(concreteCConstructedBoundary l).localCarrier.parameter.q‖ < 1 := by
  exact concreteInitialThetaCarrier_q_contracting l

theorem concreteCConstructedBoundary_local_q_ne_one
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).localCarrier.parameter.q ≠ 1 := by
  exact concreteInitialThetaCarrier_q_ne_one l

theorem concreteCConstructedBoundary_local_parameter_ne_one
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).localCarrier.kummer.localParameter ≠ 1 := by
  exact concreteInitialThetaCarrier_local_parameter_ne_one l

theorem concreteCConstructedBoundary_finite_kernel
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).localCarrier.kummer.finiteReduction.ker =
      AddSubgroup.zmultiples (l.value : ℤ) := by
  exact concreteInitialThetaCarrier_finite_kernel l

theorem concreteCConstructedBoundary_integer_root_add
    (l : PrimeGeFive) (m n : ℤ) :
    (concreteCConstructedBoundary l).localCarrier.kummer.integerRoot (m + n) =
      (concreteCConstructedBoundary l).localCarrier.kummer.integerRoot m +
        (concreteCConstructedBoundary l).localCarrier.kummer.integerRoot n := by
  exact concreteInitialThetaCarrier_integer_root_add l m n

theorem concreteCConstructedBoundary_integer_root_neg
    (l : PrimeGeFive) (n : ℤ) :
    (concreteCConstructedBoundary l).localCarrier.kummer.integerRoot (-n) =
      -(concreteCConstructedBoundary l).localCarrier.kummer.integerRoot n := by
  exact concreteInitialThetaCarrier_integer_root_neg l n

theorem concreteCConstructedBoundary_integer_root_one
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).localCarrier.kummer.integerRoot 1 =
      Additive.ofMul
        (LocalIntegralMonoid.qParameterGroupification l.value) := by
  exact concreteInitialThetaCarrier_integer_root_one l

theorem concreteCConstructedBoundary_zero_label_lift
    (l : PrimeGeFive) (n : ℤ)
    (h : (concreteCConstructedBoundary l).localCarrier.kummer.finiteReduction n = 0) :
    ∃ k : ℤ,
      (concreteCConstructedBoundary l).localCarrier.kummer.integerRoot n =
        (l.value : ℤ) •
          (concreteCConstructedBoundary l).localCarrier.kummer.integerRoot k := by
  exact concreteInitialThetaCarrier_zero_label_lift l n h

theorem concreteCConstructedBoundary_finite_level_mk
    (l : PrimeGeFive) (n : ℤ) :
    ConcreteTateKummerPacket.finiteLevelQuotientEquiv
        (concreteCConstructedBoundary l).localCarrier.kummer
        (QuotientAddGroup.mk n) =
      (concreteCConstructedBoundary l).localCarrier.kummer.finiteReduction n := by
  exact concreteInitialThetaCarrier_finite_level_mk l n

theorem concreteCConstructedBoundary_finite_level_zero_iff
    (l : PrimeGeFive) (n : ℤ) :
    (QuotientAddGroup.mk n :
      ℤ ⧸ (concreteCConstructedBoundary l).localCarrier.kummer.finiteReduction.ker) = 0 ↔
      n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact concreteInitialThetaCarrier_finite_level_zero_iff l n

theorem concreteCConstructedBoundary_theta_q
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).hodgeTheater.thetaPacket.q =
      gaussianFiveThetaQ := by
  exact concreteInitialThetaHodgeTheater_q l

theorem concreteCConstructedBoundary_theta_q_pos
    (l : PrimeGeFive) :
    0 < (concreteCConstructedBoundary l).hodgeTheater.thetaPacket.q := by
  exact concreteInitialThetaHodgeTheater_q_pos l

theorem concreteCConstructedBoundary_theta_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteCConstructedBoundary l).hodgeTheater.thetaPacket.scale j =
      realThetaValue gaussianFiveThetaQ j.1 := by
  exact concreteLabel_packet_scale_eq l j

theorem concreteCConstructedBoundary_theta_scale_pos
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    0 < (concreteCConstructedBoundary l).hodgeTheater.thetaPacket.scale j := by
  exact concreteLabel_packet_scale_pos l j

theorem concreteCConstructedBoundary_theta_log_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    Real.log ((concreteCConstructedBoundary l).hodgeTheater.thetaPacket.scale j) =
      (gaussExponent j.1).toNat *
        Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  exact concreteLabel_packet_log_scale_local_degree l j

theorem concreteCConstructedBoundary_theta_log_volume
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).hodgeTheater.thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat *
          Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  exact concreteLabel_packet_log_volume_local_degree l

theorem concreteCConstructedBoundary_history_q
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).history.source.theater.thetaPacket.q =
      (concreteCConstructedBoundary l).history.target.theater.thetaPacket.q := by
  exact concreteInitialThetaHistory_q_eq l

theorem concreteCConstructedBoundary_history_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteCConstructedBoundary l).history.source.theater.thetaPacket.scale j =
      (concreteCConstructedBoundary l).history.target.theater.thetaPacket.scale j := by
  exact concreteInitialThetaHistory_scale_eq l j

theorem concreteCConstructedBoundary_history_log_volume
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).history.source.theater.thetaPacket.logVolume =
      (concreteCConstructedBoundary l).history.target.theater.thetaPacket.logVolume := by
  exact concreteInitialThetaHistory_log_volume_eq l

theorem concreteCConstructedBoundary_history_product
    (l : PrimeGeFive) :
    (∏ j : SignedLabel l.value,
      (concreteCConstructedBoundary l).history.source.theater.thetaPacket.scale j) =
      ∏ j : SignedLabel l.value,
        (concreteCConstructedBoundary l).history.target.theater.thetaPacket.scale j := by
  exact concreteInitialThetaHistory_scale_product_eq l

theorem concreteCConstructedBoundary_selected_label_value
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).selectedFiniteLabel.1 = 5 := by
  rfl

theorem concreteCConstructedBoundary_selected_label_prime
    (l : PrimeGeFive) :
    Nat.Prime (concreteCConstructedBoundary l).selectedFiniteLabel.1 := by
  exact concreteInitialThetaLabel_prime

theorem concreteCConstructedBoundary_selected_label_mem_interval
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).selectedFiniteLabel.1 ∈
      (Finset.Icc 2 7 : Finset ℕ) := by
  exact concreteInitialThetaLabel_mem

theorem concreteCConstructedBoundary_selected_label_lower
    (l : PrimeGeFive) :
    2 ≤ (concreteCConstructedBoundary l).selectedFiniteLabel.1 := by
  exact concreteInitialThetaLabel_ge_lower

theorem concreteCConstructedBoundary_selected_label_upper
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).selectedFiniteLabel.1 ≤ 7 := by
  exact concreteInitialThetaLabel_le_upper

theorem concreteCConstructedBoundary_source_to_target_q
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).history.source.theater.thetaPacket.q =
      (concreteCConstructedBoundary l).history.target.theater.thetaPacket.q := by
  exact concreteCConstructedBoundary_history_q l

theorem concreteCConstructedBoundary_source_to_target_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteCConstructedBoundary l).history.source.theater.thetaPacket.scale j =
      (concreteCConstructedBoundary l).history.target.theater.thetaPacket.scale j := by
  exact concreteCConstructedBoundary_history_scale l j

theorem concreteCConstructedBoundary_source_to_target_log_volume
    (l : PrimeGeFive) :
    (concreteCConstructedBoundary l).history.source.theater.thetaPacket.logVolume =
      (concreteCConstructedBoundary l).history.target.theater.thetaPacket.logVolume := by
  exact concreteCConstructedBoundary_history_log_volume l

theorem concreteCConstructedBoundary_source_to_target_product
    (l : PrimeGeFive) :
    (∏ j : SignedLabel l.value,
      (concreteCConstructedBoundary l).history.source.theater.thetaPacket.scale j) =
      ∏ j : SignedLabel l.value,
        (concreteCConstructedBoundary l).history.target.theater.thetaPacket.scale j := by
  exact concreteCConstructedBoundary_history_product l

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteCConstructedBoundaryAudit : Obligation :=
  { id := "IUT-I-II.concrete-c-constructed-boundary"
    source := "IUT I-II concrete C-layer boundary"
    status := VerificationStatus.proved
    note :=
      "This is the exact proved boundary record: actual arithmetic/finite " ++
        "place, stable and multiplicative reduction, finite theta carrier, " ++
        "local q/Kummer packet, and reflexive history. Its projections include " ++
        "the finite kernel, root lifts, theta logarithms and volume transport. " ++
        "The missing CurveIndexedTateUniformization contract is intentionally " ++
        "not a field and remains an interface obligation."
    dependsOn := [ "IUT-I-II.concrete-initial-theta-finite-arithmetic",
      "IUT-I.concrete-initial-theta-finite-place-boundary" ] }

end LeanFormal.IUT.Audit
