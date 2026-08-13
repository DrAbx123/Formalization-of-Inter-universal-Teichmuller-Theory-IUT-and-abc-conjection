import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralFPrimeStrip
import LeanFormal.IUT.IUTII.Frobenioid.ConcreteLocalKummerExample

/-!
  A finite, integral local carrier assembled from the concrete arithmetic and
  Kummer units.

  The selected finite place is the ordinary prime `5` in `[2, 7]`.  The
  theater uses the actual nonzero integral-closure monoids at all selected
  places, while its selected local Kummer data is the nontrivial `q = 5`
  parameter and its coherent root realization.  This is a finite carrier
  model for later algorithm tests; it is not the paper's etale Hodge theater
  existence theorem.
-/

namespace LeanFormal.IUT

noncomputable section

local instance fivePrimeFact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

def fiveFinitePrimePlace : FinitePrimePlace 2 7 :=
  ⟨5, by norm_num [mem_primeStrip_iff, Nat.prime_five]⟩

noncomputable def gaussianFiveThetaQ : Real :=
  ‖(localQParameterFor 5 : AlgebraicClosure ℚ_[5])‖

theorem gaussianFiveThetaQ_pos : 0 < gaussianFiveThetaQ := by
  exact norm_pos_unit (AlgebraicClosure ℚ_[5]) (localQParameterFor 5)

theorem gaussianFiveThetaQ_eq_exp_local_degree :
    gaussianFiveThetaQ =
      Real.exp (Multiplicative.toAdd
        (localUnitNormDegreeFor 5 (localQParameterFor 5))) := by
  change ‖(localQParameterFor 5 : AlgebraicClosure ℚ_[5])‖ =
    Real.exp (Real.log ‖(localQParameterFor 5 : AlgebraicClosure ℚ_[5])‖)
  exact (Real.exp_log (gaussianFiveThetaQ_pos)).symm

theorem gaussianFiveThetaQ_log_eq_local_degree :
    Real.log gaussianFiveThetaQ =
      Multiplicative.toAdd
        (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  rw [gaussianFiveThetaQ_eq_exp_local_degree, Real.log_exp]

def gaussianFiniteIntegralHodgeTheater (l : PrimeGeFive) :
    HodgeTheater l (FinitePrimePlace 2 7) where
  arithmetic := gaussianInitialThetaArithmeticData l
  primeStrip := finiteLocalIntegralFPrimeStrip 2 7
  thetaPacket :=
    FiniteThetaPacket.ofQ (l := l) gaussianFiveThetaQ gaussianFiveThetaQ_pos

theorem gaussianFiniteIntegralHodgeTheater_q (l : PrimeGeFive) :
    (gaussianFiniteIntegralHodgeTheater l).thetaPacket.q = gaussianFiveThetaQ :=
  rfl

theorem gaussianFiniteIntegralHodgeTheater_logVolume (l : PrimeGeFive) :
    (gaussianFiniteIntegralHodgeTheater l).thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat *
          Multiplicative.toAdd
            (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  rw [FiniteThetaPacket.logVolume_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(gaussianFiniteIntegralHodgeTheater l).thetaPacket.log_scale j,
    gaussianFiniteIntegralHodgeTheater_q,
    gaussianFiveThetaQ_log_eq_local_degree]

def gaussianFiniteIntegralThreeTheaterSystem (l : PrimeGeFive) :
    ThreeTheaterSystem l (FinitePrimePlace 2 7) where
  source := gaussianFiniteIntegralHodgeTheater l
  middle := gaussianFiniteIntegralHodgeTheater l
  target := gaussianFiniteIntegralHodgeTheater l
  source_to_middle := HodgeTheaterLink.refl _
  middle_to_target := HodgeTheaterLink.refl _

structure ConcreteFiniteIntegralThetaInput (l : PrimeGeFive) where
  theater : HodgeTheater l (FinitePrimePlace 2 7)
  selectedPlace : FinitePrimePlace 2 7
  selectedPlace_isFive : selectedPlace = fiveFinitePrimePlace
  qRootRealization :
    LocalMLFModelTMPair.IntegralKummerRootRealization 5
      (LocalMLFModelTMPair.monoAnalytic 5)
      ((LocalMLFModelTMPair.monoAnalytic 5).openStabilizer 5
        (LocalIntegralMonoid.qParameter 5))
      (LocalIntegralMonoid.qParameter 5)

def gaussianConcreteFiniteIntegralThetaInput (l : PrimeGeFive) :
    ConcreteFiniteIntegralThetaInput l where
  theater := gaussianFiniteIntegralHodgeTheater l
  selectedPlace := fiveFinitePrimePlace
  selectedPlace_isFive := rfl
  qRootRealization := LocalIntegralMonoid.qParameterKummerRealization 5

theorem gaussianFiniteIntegralThreeTheaterSystem_q (l : PrimeGeFive) :
    (gaussianFiniteIntegralThreeTheaterSystem l).source.thetaPacket.q =
      (gaussianFiniteIntegralThreeTheaterSystem l).target.thetaPacket.q := by
  exact (gaussianFiniteIntegralThreeTheaterSystem l).sourceToTarget_q

theorem gaussianConcreteFiniteIntegralThetaInput_q_nontrivial :
    LocalIntegralMonoid.qParameterGroupification 5 ≠ 1 :=
  LocalIntegralMonoid.qParameterGroupification_ne_one 5

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteFiniteIntegralHodgeTheater : Obligation :=
  { id := "IUT-I-II.concrete-finite-integral-hodge-carrier"
    source := "IUT I-II, finite prime-strip and local Kummer carrier"
    status := VerificationStatus.testCarrier
    note :=
      "A finite interval [2,7], an actual integral F-prime-strip, the proved " ++
        "Q(i) arithmetic input, a reflexive three-theater carrier, and the " ++
        "nontrivial q=5 local Kummer realization are assembled in one explicit " ++
        "Lean object. This is a carrier/test model only: etale fundamental " ++
        "groups, source histories, theta-links, and Frobenioid recognition are " ++
        "not asserted."
    dependsOn :=
      [ "IUT-I.initial-theta-concrete-gaussian",
        "IUT-II.local-integral-f-prime-strip-carrier",
        "IUT-II.concrete-local-q-parameter-roots" ] }

end LeanFormal.IUT.Audit
