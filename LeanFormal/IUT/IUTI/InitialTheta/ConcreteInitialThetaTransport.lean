/-
  Transport lemmas for the concrete initial-theta carrier.

  This file keeps three different carriers distinct: the actual number-field
  finite place, the finite prime-strip label, and the local q/Kummer packet.
  The record below only assembles already proved data.  Every projection is
  exposed by a theorem so later source-oriented code can depend on explicit
  equalities instead of unfolding a large dependent record.
-/

import LeanFormal.IUT.IUTI.InitialTheta.ConcreteFinitePlaceBoundary
import LeanFormal.IUT.IUTI.HodgeTheater.ConcreteIntegralHodgeTheaterExample
import LeanFormal.IUT.Foundations.Geometry.ConcreteTateLocalCarrier

namespace LeanFormal.IUT

noncomputable section

local instance fivePrimeFactTransport : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance primeFactForTransport (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

def concreteInitialThetaLabel : FinitePrimePlace 2 7 :=
  fiveFinitePrimePlace

@[simp] theorem concreteInitialThetaLabel_value :
    (concreteInitialThetaLabel : FinitePrimePlace 2 7).1 = 5 :=
  rfl

theorem concreteInitialThetaLabel_mem :
    (concreteInitialThetaLabel : FinitePrimePlace 2 7).1 ∈
      (Finset.Icc 2 7 : Finset ℕ) := by
  norm_num [concreteInitialThetaLabel, fiveFinitePrimePlace]

theorem concreteInitialThetaLabel_prime :
    Nat.Prime (concreteInitialThetaLabel : FinitePrimePlace 2 7).1 := by
  exact FinitePrimePlace.prime concreteInitialThetaLabel

theorem concreteInitialThetaLabel_ge_lower :
    2 ≤ (concreteInitialThetaLabel : FinitePrimePlace 2 7).1 := by
  exact (concreteInitialThetaLabel : FinitePrimePlace 2 7).2.1

theorem concreteInitialThetaLabel_le_upper :
    (concreteInitialThetaLabel : FinitePrimePlace 2 7).1 ≤ 7 := by
  exact (concreteInitialThetaLabel : FinitePrimePlace 2 7).2.2.1

def concreteInitialThetaHodgeTheater (l : PrimeGeFive) :
    HodgeTheater l (FinitePrimePlace 2 7) :=
  gaussianFiniteIntegralHodgeTheater l

@[simp] theorem concreteInitialThetaHodgeTheater_arithmetic
    (l : PrimeGeFive) :
    (concreteInitialThetaHodgeTheater l).arithmetic =
      gaussianInitialThetaArithmeticData l :=
  rfl

@[simp] theorem concreteInitialThetaHodgeTheater_primeStrip
    (l : PrimeGeFive) :
    (concreteInitialThetaHodgeTheater l).primeStrip =
      finiteLocalIntegralFPrimeStrip 2 7 :=
  rfl

@[simp] theorem concreteInitialThetaHodgeTheater_thetaPacket
    (l : PrimeGeFive) :
    (concreteInitialThetaHodgeTheater l).thetaPacket =
      FiniteThetaPacket.ofQ gaussianFiveThetaQ gaussianFiveThetaQ_pos :=
  rfl

theorem concreteInitialThetaHodgeTheater_q (l : PrimeGeFive) :
    (concreteInitialThetaHodgeTheater l).thetaPacket.q = gaussianFiveThetaQ := by
  rfl

theorem concreteInitialThetaHodgeTheater_q_pos (l : PrimeGeFive) :
    0 < (concreteInitialThetaHodgeTheater l).thetaPacket.q := by
  rw [concreteInitialThetaHodgeTheater_q]
  exact gaussianFiveThetaQ_pos

theorem concreteInitialThetaHodgeTheater_q_ne_zero (l : PrimeGeFive) :
    (concreteInitialThetaHodgeTheater l).thetaPacket.q ≠ 0 := by
  exact ne_of_gt (concreteInitialThetaHodgeTheater_q_pos l)

theorem concreteInitialThetaHodgeTheater_log_volume (l : PrimeGeFive) :
    (concreteInitialThetaHodgeTheater l).thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat *
          Multiplicative.toAdd
            (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  exact gaussianFiniteIntegralHodgeTheater_logVolume l

theorem concreteInitialThetaHodgeTheater_scale_pos
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    0 < (concreteInitialThetaHodgeTheater l).thetaPacket.scale j := by
  exact (concreteInitialThetaHodgeTheater l).thetaPacket.scale_pos j

theorem concreteInitialThetaHodgeTheater_scale_ne_zero
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaHodgeTheater l).thetaPacket.scale j ≠ 0 := by
  exact (concreteInitialThetaHodgeTheater l).thetaPacket.scale_ne_zero j

theorem concreteInitialThetaHodgeTheater_scale_neg
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaHodgeTheater l).thetaPacket.scale (SignedLabel.neg j) =
      (concreteInitialThetaHodgeTheater l).thetaPacket.scale j := by
  exact (concreteInitialThetaHodgeTheater l).thetaPacket.scale_neg j

theorem concreteInitialThetaHodgeTheater_log_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    Real.log ((concreteInitialThetaHodgeTheater l).thetaPacket.scale j) =
      (gaussExponent j.1).toNat * Real.log gaussianFiveThetaQ := by
  rw [(concreteInitialThetaHodgeTheater l).thetaPacket.log_scale,
    concreteInitialThetaHodgeTheater_q]

theorem concreteInitialThetaHodgeTheater_log_scale_local_degree
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    Real.log ((concreteInitialThetaHodgeTheater l).thetaPacket.scale j) =
      (gaussExponent j.1).toNat *
        Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  rw [concreteInitialThetaHodgeTheater_log_scale,
    gaussianFiveThetaQ_log_eq_local_degree]

theorem concreteInitialThetaHodgeTheater_log_volume_eq_sum
    (l : PrimeGeFive) :
    (concreteInitialThetaHodgeTheater l).thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        Real.log ((concreteInitialThetaHodgeTheater l).thetaPacket.scale j) := by
  exact (concreteInitialThetaHodgeTheater l).thetaPacket.logVolume_eq_sum

theorem concreteInitialThetaHodgeTheater_log_volume_neg_invariant
    (l : PrimeGeFive) :
    (∑ j : SignedLabel l.value,
      Real.log ((concreteInitialThetaHodgeTheater l).thetaPacket.scale
        (SignedLabel.neg j))) =
      (concreteInitialThetaHodgeTheater l).thetaPacket.logVolume := by
  exact (concreteInitialThetaHodgeTheater l).thetaPacket.logVolume_neg_invariant

theorem concreteInitialThetaHodgeTheater_primeStrip_totalDegree_mul
    (l : PrimeGeFive) (s : Finset (FinitePrimePlace 2 7))
    (x y : ∀ v, (concreteInitialThetaHodgeTheater l).primeStrip.Mon v) :
    (concreteInitialThetaHodgeTheater l).primeStrip.totalDegree s
        (fun v => x v * y v) =
      (concreteInitialThetaHodgeTheater l).primeStrip.totalDegree s x +
        (concreteInitialThetaHodgeTheater l).primeStrip.totalDegree s y := by
  exact (concreteInitialThetaHodgeTheater l).primeStrip.totalDegree_mul s x y

theorem concreteInitialThetaHodgeTheater_primeStrip_totalDegree_one
    (l : PrimeGeFive) (s : Finset (FinitePrimePlace 2 7)) :
    (concreteInitialThetaHodgeTheater l).primeStrip.totalDegree s
        (fun _ => 1) = 0 := by
  exact (concreteInitialThetaHodgeTheater l).primeStrip.totalDegree_one s

theorem concreteInitialThetaHodgeTheater_action_mul
    (l : PrimeGeFive) (v : FinitePrimePlace 2 7)
    (g h : (concreteInitialThetaHodgeTheater l).primeStrip.toDPrimeStrip.Pi v)
    (x : (concreteInitialThetaHodgeTheater l).primeStrip.Mon v) :
    (concreteInitialThetaHodgeTheater l).primeStrip.action v (g * h) x =
      (concreteInitialThetaHodgeTheater l).primeStrip.action v g
        ((concreteInitialThetaHodgeTheater l).primeStrip.action v h x) := by
  exact (concreteInitialThetaHodgeTheater l).primeStrip.action_mul v g h x

theorem concreteInitialThetaHodgeTheater_action_one
    (l : PrimeGeFive) (v : FinitePrimePlace 2 7)
    (x : (concreteInitialThetaHodgeTheater l).primeStrip.Mon v) :
    (concreteInitialThetaHodgeTheater l).primeStrip.action v 1 x = x := by
  exact (concreteInitialThetaHodgeTheater l).primeStrip.action_one v x

def concreteInitialThetaPlaceInput (l : PrimeGeFive) :
    InitialThetaFinitePlaceInput l :=
  concreteGaussianInitialThetaFinitePlaceInput l

@[simp] theorem concreteInitialThetaPlaceInput_arithmetic (l : PrimeGeFive) :
    (concreteInitialThetaPlaceInput l).arithmetic =
      concreteGaussianInitialThetaArithmeticData l :=
  rfl

@[simp] theorem concreteInitialThetaPlaceInput_place (l : PrimeGeFive) :
    (concreteInitialThetaPlaceInput l).place = concreteGaussianFivePlace :=
  rfl

theorem concreteInitialThetaPlaceInput_stable (l : PrimeGeFive) :
    (concreteInitialThetaPlaceInput l).arithmetic.curve.HasStableReductionAt
      (concreteInitialThetaPlaceInput l).place := by
  exact concreteGaussianInitialThetaFinitePlaceInput_stable l

theorem concreteInitialThetaPlaceInput_multiplicative (l : PrimeGeFive) :
    ((concreteInitialThetaPlaceInput l).arithmetic.curve).HasMultiplicativeReductionAt
      (concreteInitialThetaPlaceInput l).place := by
  exact concreteGaussianInitialThetaFinitePlaceInput_multiplicative l

theorem concreteInitialThetaPlaceInput_q_order_pos (l : PrimeGeFive) :
    0 < (concreteInitialThetaPlaceInput l).qCandidate.order := by
  exact concreteGaussianInitialThetaFinitePlaceInput_q_order_pos l

theorem concreteInitialThetaPlaceInput_q_ne_one (l : PrimeGeFive) :
    (concreteInitialThetaPlaceInput l).qCandidate.q ≠ 1 := by
  exact concreteGaussianInitialThetaFinitePlaceInput_q_ne_one l

structure ConcreteInitialThetaCarrier (l : PrimeGeFive) where
  placeInput : InitialThetaFinitePlaceInput l
  theater : HodgeTheater l (FinitePrimePlace 2 7)
  localCarrier : ConcreteTateLocalCarrier l
  selectedLabel : FinitePrimePlace 2 7
  selectedLabel_eq_five : selectedLabel = concreteInitialThetaLabel

noncomputable def concreteInitialThetaCarrier (l : PrimeGeFive) :
    ConcreteInitialThetaCarrier l where
  placeInput := concreteInitialThetaPlaceInput l
  theater := concreteInitialThetaHodgeTheater l
  localCarrier := ConcreteTateLocalCarrier.canonical l
  selectedLabel := concreteInitialThetaLabel
  selectedLabel_eq_five := rfl

@[simp] theorem concreteInitialThetaCarrier_placeInput
    (l : PrimeGeFive) :
    (concreteInitialThetaCarrier l).placeInput = concreteInitialThetaPlaceInput l :=
  rfl

@[simp] theorem concreteInitialThetaCarrier_theater
    (l : PrimeGeFive) :
    (concreteInitialThetaCarrier l).theater = concreteInitialThetaHodgeTheater l :=
  rfl

@[simp] theorem concreteInitialThetaCarrier_localCarrier
    (l : PrimeGeFive) :
    (concreteInitialThetaCarrier l).localCarrier =
      ConcreteTateLocalCarrier.canonical l :=
  rfl

@[simp] theorem concreteInitialThetaCarrier_selectedLabel
    (l : PrimeGeFive) :
    (concreteInitialThetaCarrier l).selectedLabel = concreteInitialThetaLabel :=
  (concreteInitialThetaCarrier l).selectedLabel_eq_five

theorem concreteInitialThetaCarrier_place_stable (l : PrimeGeFive) :
    (concreteInitialThetaCarrier l).placeInput.arithmetic.curve.HasStableReductionAt
      (concreteInitialThetaCarrier l).placeInput.place := by
  change (concreteInitialThetaPlaceInput l).arithmetic.curve.HasStableReductionAt
    (concreteInitialThetaPlaceInput l).place
  exact concreteInitialThetaPlaceInput_stable l

theorem concreteInitialThetaCarrier_place_multiplicative (l : PrimeGeFive) :
    ((concreteInitialThetaCarrier l).placeInput.arithmetic.curve).HasMultiplicativeReductionAt
      (concreteInitialThetaCarrier l).placeInput.place := by
  change ((concreteInitialThetaPlaceInput l).arithmetic.curve).HasMultiplicativeReductionAt
    (concreteInitialThetaPlaceInput l).place
  exact concreteInitialThetaPlaceInput_multiplicative l

theorem concreteInitialThetaCarrier_q_contracting (l : PrimeGeFive) :
    ‖(concreteInitialThetaCarrier l).localCarrier.parameter.q‖ < 1 := by
  exact (concreteInitialThetaCarrier l).localCarrier.q_is_contracting

theorem concreteInitialThetaCarrier_q_prime (l : PrimeGeFive) :
    (concreteInitialThetaCarrier l).localCarrier.parameter.q =
      (l.value : ℚ_[l.value]) := by
  exact (concreteInitialThetaCarrier l).localCarrier.q_is_prime

theorem concreteInitialThetaCarrier_q_ne_one (l : PrimeGeFive) :
    (concreteInitialThetaCarrier l).localCarrier.parameter.q ≠ 1 := by
  exact (concreteInitialThetaCarrier l).localCarrier.q_is_nontrivial

theorem concreteInitialThetaCarrier_local_parameter_ne_one (l : PrimeGeFive) :
    (concreteInitialThetaCarrier l).localCarrier.kummer.localParameter ≠ 1 := by
  exact (concreteInitialThetaCarrier l).localCarrier.local_parameter_is_nontrivial

theorem concreteInitialThetaCarrier_finite_kernel (l : PrimeGeFive) :
    (concreteInitialThetaCarrier l).localCarrier.kummer.finiteReduction.ker =
      AddSubgroup.zmultiples (l.value : ℤ) := by
  exact (concreteInitialThetaCarrier l).localCarrier.finite_kernel_is_exact

theorem concreteInitialThetaCarrier_integer_root_zero (l : PrimeGeFive) :
    (concreteInitialThetaCarrier l).localCarrier.kummer.integerRoot 0 = 0 := by
  exact ConcreteTateLocalCarrier.canonical_integer_root_zero l

theorem concreteInitialThetaCarrier_integer_root_add
    (l : PrimeGeFive) (m n : ℤ) :
    (concreteInitialThetaCarrier l).localCarrier.kummer.integerRoot (m + n) =
      (concreteInitialThetaCarrier l).localCarrier.kummer.integerRoot m +
        (concreteInitialThetaCarrier l).localCarrier.kummer.integerRoot n := by
  exact ConcreteTateLocalCarrier.canonical_integer_root_add l m n

theorem concreteInitialThetaCarrier_integer_root_neg
    (l : PrimeGeFive) (n : ℤ) :
    (concreteInitialThetaCarrier l).localCarrier.kummer.integerRoot (-n) =
      -(concreteInitialThetaCarrier l).localCarrier.kummer.integerRoot n := by
  exact ConcreteTateLocalCarrier.canonical_integer_root_neg l n

theorem concreteInitialThetaCarrier_integer_root_one (l : PrimeGeFive) :
    (concreteInitialThetaCarrier l).localCarrier.kummer.integerRoot 1 =
      Additive.ofMul
        (LocalIntegralMonoid.qParameterGroupification l.value) := by
  exact ConcreteTateLocalCarrier.canonical_integer_root_one l

theorem concreteInitialThetaCarrier_zero_label_lift
    (l : PrimeGeFive) (n : ℤ)
    (h : (concreteInitialThetaCarrier l).localCarrier.kummer.finiteReduction n = 0) :
    ∃ k : ℤ,
      (concreteInitialThetaCarrier l).localCarrier.kummer.integerRoot n =
        (l.value : ℤ) •
          (concreteInitialThetaCarrier l).localCarrier.kummer.integerRoot k := by
  exact ConcreteTateLocalCarrier.canonical_zero_label_has_lift l n h

theorem concreteInitialThetaCarrier_finite_level_mk
    (l : PrimeGeFive) (n : ℤ) :
    ConcreteTateKummerPacket.finiteLevelQuotientEquiv
        (concreteInitialThetaCarrier l).localCarrier.kummer
        (QuotientAddGroup.mk n) =
      (concreteInitialThetaCarrier l).localCarrier.kummer.finiteReduction n := by
  exact ConcreteTateLocalCarrier.canonical_finite_level_equiv_mk l n

theorem concreteInitialThetaCarrier_finite_level_zero_iff
    (l : PrimeGeFive) (n : ℤ) :
    (QuotientAddGroup.mk n :
      ℤ ⧸ (concreteInitialThetaCarrier l).localCarrier.kummer.finiteReduction.ker) = 0 ↔
      n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact ConcreteTateLocalCarrier.canonical_finite_level_zero_iff l n

theorem concreteInitialThetaCarrier_deck_qUnit_class_fixed
    (l : PrimeGeFive)
    (sigma : ConcreteTateParameter.LocalAbsoluteGalois l) :
    ConcreteTateParameter.qDeckQuotientEquiv
        (concreteInitialThetaCarrier l).localCarrier.parameter sigma
        (QuotientGroup.mk
          (concreteInitialThetaCarrier l).localCarrier.parameter.qUnit) =
      QuotientGroup.mk
        (concreteInitialThetaCarrier l).localCarrier.parameter.qUnit := by
  exact ConcreteTateLocalCarrier.canonical_deck_qUnit_class_fixed l sigma

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteInitialThetaTransport : Obligation :=
  { id := "IUT-I.concrete-initial-theta-carrier-transport"
    source := "IUT I, Definition 3.1; IUT II finite local carrier"
    status := VerificationStatus.testCarrier
    note :=
      "The actual Gaussian finite-place input, finite prime-strip label, " ++
        "finite theta packet, and q/Kummer carrier are assembled without " ++
        "identifying their distinct carriers. All q, reduction, kernel, root, " ++
        "deck, theta-scale, and log-volume projections are proved. This is a " ++
        "concrete carrier transport, not the source's etale theta-link or " ++
        "Hodge-Arakelov comparison theorem."
    dependsOn :=
      [ "IUT-I.concrete-initial-theta-finite-place-boundary",
        "IUT-I-II.concrete-finite-integral-hodge-carrier",
        "Foundations.Geometry.concrete-tate-local-carrier" ] }

end LeanFormal.IUT.Audit
