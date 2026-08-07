/-
  A compact C-stage certificate consumed by later algorithm experiments.

  The certificate is a named boundary between the proved local arithmetic and
  the still-missing source-faithful Tate/anabelian constructions.  Its fields
  are all populated by the preceding modules; no placeholder proposition is
  used as a proof field.
-/

import LeanFormal.IUT.IUTI.InitialTheta.ConcreteInitialThetaLocalArithmetic

namespace LeanFormal.IUT

noncomputable section

local instance primeFactForConcreteCStage (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

local instance fivePrimeFactConcreteCStage : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance gaussianPolynomialIrreducibleFactConcreteCStage :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

def concreteInitialThetaCStageTheater (l : PrimeGeFive) :
    HodgeTheater l (FinitePrimePlace 2 7) where
  arithmetic := concreteGaussianInitialThetaArithmeticData l
  primeStrip := finiteLocalIntegralFPrimeStrip 2 7
  thetaPacket :=
    FiniteThetaPacket.ofQ (l := l) gaussianFiveThetaQ gaussianFiveThetaQ_pos

theorem concreteInitialThetaCStageTheater_q (l : PrimeGeFive) :
    (concreteInitialThetaCStageTheater l).thetaPacket.q = gaussianFiveThetaQ :=
  rfl

theorem concreteInitialThetaCStageTheater_logVolume (l : PrimeGeFive) :
    (concreteInitialThetaCStageTheater l).thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat *
          Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  change (FiniteThetaPacket.ofQ (l := l) gaussianFiveThetaQ gaussianFiveThetaQ_pos).logVolume = _
  rw [FiniteThetaPacket.logVolume_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [FiniteThetaPacket.log_scale]
  simp only [FiniteThetaPacket.ofQ_q]
  rw [gaussianFiveThetaQ_log_eq_local_degree]

structure ConcreteInitialThetaCStage (l : PrimeGeFive) where
  input : InitialThetaFinitePlaceInput l
  curve : PuncturedEllipticCurve input.arithmetic.F
  curve_eq_input : curve = input.arithmetic.curve
  place : NumberField.FinitePlace input.arithmetic.F
  place_eq_input : place = input.place
  place_comap :
    NumberFieldFinitePlace.comap (k := ℚ) concreteGaussianFivePlace =
      concreteFivePlace
  stable : curve.HasStableReductionAt place
  multiplicative : curve.HasMultiplicativeReductionAt place
  theater : HodgeTheater l (FinitePrimePlace 2 7)
  theater_arithmetic : theater.arithmetic = input.arithmetic
  finite_label : FinitePrimePlace 2 7
  finite_label_eq_five : finite_label = concreteInitialThetaLabel
  theta_q : theater.thetaPacket.q = gaussianFiveThetaQ
  theta_log_volume : theater.thetaPacket.logVolume =
    ∑ j : SignedLabel l.value,
      (gaussExponent j.1).toNat *
        Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5))
  localCarrier : ConcreteTateLocalCarrier l
  finite_kernel : localCarrier.kummer.finiteReduction.ker =
    AddSubgroup.zmultiples (l.value : ℤ)
  history : ConcreteInitialThetaHistory l
  history_log_volume :
    history.source.theater.thetaPacket.logVolume =
      history.target.theater.thetaPacket.logVolume

noncomputable def concreteInitialThetaCStage (l : PrimeGeFive) :
    ConcreteInitialThetaCStage l where
  input := concreteInitialThetaPlaceInput l
  curve := (concreteInitialThetaPlaceInput l).arithmetic.curve
  curve_eq_input := rfl
  place := (concreteInitialThetaPlaceInput l).place
  place_eq_input := rfl
  place_comap := concreteGaussianFivePlace_comap
  stable := concreteInitialThetaPlaceInput_stable l
  multiplicative := concreteInitialThetaPlaceInput_multiplicative l
  theater := concreteInitialThetaCStageTheater l
  theater_arithmetic := by rfl
  finite_label := concreteInitialThetaLabel
  finite_label_eq_five := rfl
  theta_q := concreteInitialThetaCStageTheater_q l
  theta_log_volume := concreteInitialThetaCStageTheater_logVolume l
  localCarrier := ConcreteTateLocalCarrier.canonical l
  finite_kernel := (ConcreteTateKummerPacket.canonical l).finiteReduction_kernel
  history := concreteInitialThetaHistory l
  history_log_volume := concreteInitialThetaHistory_log_volume_eq l

@[simp] theorem concreteInitialThetaCStage_input (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).input = concreteInitialThetaPlaceInput l :=
  rfl

@[simp] theorem concreteInitialThetaCStage_curve (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).curve =
      (concreteInitialThetaPlaceInput l).arithmetic.curve :=
  rfl

@[simp] theorem concreteInitialThetaCStage_place (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).place =
      (concreteInitialThetaPlaceInput l).place :=
  rfl

@[simp] theorem concreteInitialThetaCStage_theater (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).theater =
      concreteInitialThetaCStageTheater l :=
  rfl

@[simp] theorem concreteInitialThetaCStage_finite_label (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).finite_label = concreteInitialThetaLabel :=
  rfl

@[simp] theorem concreteInitialThetaCStage_localCarrier (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).localCarrier =
      ConcreteTateLocalCarrier.canonical l :=
  rfl

@[simp] theorem concreteInitialThetaCStage_history (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).history = concreteInitialThetaHistory l :=
  rfl

theorem concreteInitialThetaCStage_curve_eq_arithmetic (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).curve =
      (concreteInitialThetaCStage l).input.arithmetic.curve :=
  (concreteInitialThetaCStage l).curve_eq_input

theorem concreteInitialThetaCStage_place_eq_input (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).place =
      (concreteInitialThetaCStage l).input.place :=
  (concreteInitialThetaCStage l).place_eq_input

theorem concreteInitialThetaCStage_comap (l : PrimeGeFive) :
    NumberFieldFinitePlace.comap (k := ℚ) concreteGaussianFivePlace =
      concreteFivePlace :=
  (concreteInitialThetaCStage l).place_comap

theorem concreteInitialThetaCStage_stable (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).curve.HasStableReductionAt
      (concreteInitialThetaCStage l).place :=
  (concreteInitialThetaCStage l).stable

theorem concreteInitialThetaCStage_multiplicative (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).curve.HasMultiplicativeReductionAt
      (concreteInitialThetaCStage l).place :=
  (concreteInitialThetaCStage l).multiplicative

theorem concreteInitialThetaCStage_theater_arithmetic (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).theater.arithmetic =
      (concreteInitialThetaCStage l).input.arithmetic :=
  (concreteInitialThetaCStage l).theater_arithmetic

theorem concreteInitialThetaCStage_label_value (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).finite_label.1 = 5 := by
  rfl

theorem concreteInitialThetaCStage_label_prime (l : PrimeGeFive) :
    Nat.Prime (concreteInitialThetaCStage l).finite_label.1 := by
  exact concreteInitialThetaLabel_prime

theorem concreteInitialThetaCStage_label_mem_interval (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).finite_label.1 ∈
      (Finset.Icc 2 7 : Finset ℕ) := by
  exact concreteInitialThetaLabel_mem

theorem concreteInitialThetaCStage_theta_q (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).theater.thetaPacket.q = gaussianFiveThetaQ :=
  (concreteInitialThetaCStage l).theta_q

theorem concreteInitialThetaCStage_theta_q_pos (l : PrimeGeFive) :
    0 < (concreteInitialThetaCStage l).theater.thetaPacket.q := by
  rw [concreteInitialThetaCStage_theta_q]
  exact gaussianFiveThetaQ_pos

theorem concreteInitialThetaCStage_theta_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaCStage l).theater.thetaPacket.scale j =
      realThetaValue gaussianFiveThetaQ j.1 := by
  change (concreteInitialThetaCStageTheater l).thetaPacket.scale j = _
  exact concreteLabel_packet_scale_eq l j

theorem concreteInitialThetaCStage_theta_scale_pos
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    0 < (concreteInitialThetaCStage l).theater.thetaPacket.scale j := by
  rw [concreteInitialThetaCStage_theta_scale]
  exact realThetaValue_pos gaussianFiveThetaQ_pos j.1

theorem concreteInitialThetaCStage_theta_log_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    Real.log ((concreteInitialThetaCStage l).theater.thetaPacket.scale j) =
      (gaussExponent j.1).toNat *
        Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  change Real.log ((concreteInitialThetaCStageTheater l).thetaPacket.scale j) = _
  exact concreteLabel_packet_log_scale_local_degree l j

theorem concreteInitialThetaCStage_theta_log_volume (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).theater.thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat *
          Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) :=
  (concreteInitialThetaCStage l).theta_log_volume

theorem concreteInitialThetaCStage_theta_log_volume_eq_sum (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).theater.thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        Real.log ((concreteInitialThetaCStage l).theater.thetaPacket.scale j) := by
  exact (concreteInitialThetaCStage l).theater.thetaPacket.logVolume_eq_sum

theorem concreteInitialThetaCStage_theta_log_volume_neg (l : PrimeGeFive) :
    (∑ j : SignedLabel l.value,
      Real.log ((concreteInitialThetaCStage l).theater.thetaPacket.scale
        (SignedLabel.neg j))) =
      (concreteInitialThetaCStage l).theater.thetaPacket.logVolume := by
  exact (concreteInitialThetaCStage l).theater.thetaPacket.logVolume_neg_invariant

theorem concreteInitialThetaCStage_local_q (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).localCarrier.parameter.q =
      (l.value : ℚ_[l.value]) := by
  exact concreteInitialThetaCarrier_q_prime l

theorem concreteInitialThetaCStage_local_q_contracting (l : PrimeGeFive) :
    ‖(concreteInitialThetaCStage l).localCarrier.parameter.q‖ < 1 := by
  exact concreteInitialThetaCarrier_q_contracting l

theorem concreteInitialThetaCStage_local_q_ne_one (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).localCarrier.parameter.q ≠ 1 := by
  exact concreteInitialThetaCarrier_q_ne_one l

theorem concreteInitialThetaCStage_local_finite_kernel (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).localCarrier.kummer.finiteReduction.ker =
      AddSubgroup.zmultiples (l.value : ℤ) :=
  (concreteInitialThetaCStage l).finite_kernel

theorem concreteInitialThetaCStage_place_q_order_pos (l : PrimeGeFive) :
    0 < (concreteInitialThetaCStage l).input.qCandidate.order := by
  exact concreteInitialThetaPlaceInput_q_order_pos l

theorem concreteInitialThetaCStage_place_q_ne_one (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).input.qCandidate.q ≠ 1 := by
  exact concreteInitialThetaPlaceInput_q_ne_one l

theorem concreteInitialThetaCStage_integer_root_zero (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).localCarrier.kummer.integerRoot 0 = 0 := by
  exact concreteInitialThetaCarrier_integer_root_zero l

theorem concreteInitialThetaCStage_integer_root_one (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).localCarrier.kummer.integerRoot 1 =
      Additive.ofMul
        (LocalIntegralMonoid.qParameterGroupification l.value) := by
  exact concreteInitialThetaCarrier_integer_root_one l

theorem concreteInitialThetaCStage_integer_root_add
    (l : PrimeGeFive) (m n : ℤ) :
    (concreteInitialThetaCStage l).localCarrier.kummer.integerRoot (m + n) =
      (concreteInitialThetaCStage l).localCarrier.kummer.integerRoot m +
        (concreteInitialThetaCStage l).localCarrier.kummer.integerRoot n := by
  exact concreteInitialThetaCarrier_integer_root_add l m n

theorem concreteInitialThetaCStage_integer_root_neg
    (l : PrimeGeFive) (n : ℤ) :
    (concreteInitialThetaCStage l).localCarrier.kummer.integerRoot (-n) =
      -(concreteInitialThetaCStage l).localCarrier.kummer.integerRoot n := by
  exact concreteInitialThetaCarrier_integer_root_neg l n

theorem concreteInitialThetaCStage_zero_label_lift
    (l : PrimeGeFive) (n : ℤ)
    (h : (concreteInitialThetaCStage l).localCarrier.kummer.finiteReduction n = 0) :
    ∃ k : ℤ,
      (concreteInitialThetaCStage l).localCarrier.kummer.integerRoot n =
        (l.value : ℤ) •
          (concreteInitialThetaCStage l).localCarrier.kummer.integerRoot k := by
  exact concreteInitialThetaCarrier_zero_label_lift l n h

theorem concreteInitialThetaCStage_finite_level_zero_iff
    (l : PrimeGeFive) (n : ℤ) :
    (QuotientAddGroup.mk n :
      ℤ ⧸ (concreteInitialThetaCStage l).localCarrier.kummer.finiteReduction.ker) = 0 ↔
      n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact concreteInitialThetaCarrier_finite_level_zero_iff l n

theorem concreteInitialThetaCStage_finite_level_mk
    (l : PrimeGeFive) (n : ℤ) :
    ConcreteTateKummerPacket.finiteLevelQuotientEquiv
        (concreteInitialThetaCStage l).localCarrier.kummer
        (QuotientAddGroup.mk n) =
      (concreteInitialThetaCStage l).localCarrier.kummer.finiteReduction n := by
  exact concreteInitialThetaCarrier_finite_level_mk l n

theorem concreteInitialThetaCStage_history_log_volume (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).history.source.theater.thetaPacket.logVolume =
      (concreteInitialThetaCStage l).history.target.theater.thetaPacket.logVolume :=
  (concreteInitialThetaCStage l).history_log_volume

theorem concreteInitialThetaCStage_history_q (l : PrimeGeFive) :
    (concreteInitialThetaCStage l).history.source.theater.thetaPacket.q =
      (concreteInitialThetaCStage l).history.target.theater.thetaPacket.q := by
  change (concreteInitialThetaHistory l).source.theater.thetaPacket.q = _
  exact concreteInitialThetaHistory_q_eq l

theorem concreteInitialThetaCStage_history_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaCStage l).history.source.theater.thetaPacket.scale j =
      (concreteInitialThetaCStage l).history.target.theater.thetaPacket.scale j := by
  change (concreteInitialThetaHistory l).source.theater.thetaPacket.scale j = _
  exact concreteInitialThetaHistory_scale_eq l j

theorem concreteInitialThetaCStage_history_product (l : PrimeGeFive) :
    (∏ j : SignedLabel l.value,
      (concreteInitialThetaCStage l).history.source.theater.thetaPacket.scale j) =
      ∏ j : SignedLabel l.value,
        (concreteInitialThetaCStage l).history.target.theater.thetaPacket.scale j := by
  change (∏ j : SignedLabel l.value,
      (concreteInitialThetaHistory l).source.theater.thetaPacket.scale j) = _
  exact concreteInitialThetaHistory_scale_product_eq l

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteInitialThetaCStageAudit : Obligation :=
  { id := "IUT-I-II.concrete-initial-theta-c-stage"
    source := "IUT I-II concrete C-stage certificate"
    status := VerificationStatus.proved
    note :=
      "A named C-stage certificate exposes the actual selected place, its " ++
        "base-change relation, stable/multiplicative reduction, finite label " ++
        "bounds, theta log-volume, q contraction, exact finite kernel, and " ++
        "history transport. It is the strongest currently built concrete " ++
        "boundary and still intentionally stops before curve-point Tate " ++
        "uniformization and source anabelian links."
    dependsOn := [ "IUT-I-II.concrete-c-local-arithmetic",
      "IUT-I-II.concrete-c-constructed-boundary" ] }

end LeanFormal.IUT.Audit
