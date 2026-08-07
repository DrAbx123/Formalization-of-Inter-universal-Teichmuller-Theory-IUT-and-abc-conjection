import LeanFormal.IUT.IUTII.Frobenioid.ConcreteSourceFrobenioidBridge
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteInitialThetaLocalArithmetic
import LeanFormal.IUT.Foundations.Geometry.ConcreteTateFiniteLevel
import LeanFormal.IUT.Foundations.Geometry.ConcreteTateDeckQuotient
import LeanFormal.IUT.IUTII.Kummer.ConcreteEtaleKummerBridge

namespace LeanFormal.IUT

noncomputable section

open CategoryTheory

local instance gaussianPolynomialIrreducibleFactConcreteTheta :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance fivePrimeFactConcreteTheta : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance primeFactForConcreteTheta (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) :=
  l.factPrime

namespace ConcreteSourceEtaleThetaBridge

abbrev cStage (l : PrimeGeFive) := concreteInitialThetaCStage l

abbrev packet (l : PrimeGeFive) :=
  (cStage l).localCarrier.kummer

abbrev parameter (l : PrimeGeFive) :=
  (cStage l).localCarrier.parameter

abbrev quotient (l : PrimeGeFive) :=
  ℤ ⧸ (packet l).finiteReduction.ker

abbrev finiteLabel (l : PrimeGeFive) := ZMod l.value

abbrev roots (l : PrimeGeFive) := (packet l).compatibleRoots

abbrev theater (l : PrimeGeFive) := (cStage l).theater

abbrev sourceModel := ConcreteSourceFrobenioidBridge.concreteStageModel

def reduction (l : PrimeGeFive) : ℤ →+ finiteLabel l :=
  (packet l).finiteReduction

noncomputable def quotientEquiv (l : PrimeGeFive) :
    quotient l ≃+ finiteLabel l :=
  (packet l).finiteLevelQuotientEquiv

def generator (l : PrimeGeFive) : finiteLabel l :=
  canonicalTateGenerator l

def thetaScale (l : PrimeGeFive) (j : SignedLabel l.value) : Real :=
  (theater l).thetaPacket.scale j

def thetaLogScale (l : PrimeGeFive) (j : SignedLabel l.value) : Real :=
  Real.log (thetaScale l j)

def thetaLogVolume (l : PrimeGeFive) : Real :=
  (theater l).thetaPacket.logVolume

structure AlgebraicFiniteThetaLevel (l : PrimeGeFive) where
  cStage : ConcreteInitialThetaCStage l
  packet : ConcreteTateKummerPacket l
  packet_eq : packet = (cStage).localCarrier.kummer
  reduction : ℤ →+ ZMod l.value
  reduction_eq : reduction = packet.finiteReduction
  quotientEquiv : (ℤ ⧸ packet.finiteReduction.ker) ≃+ ZMod l.value
  quotientEquiv_apply_mk : ∀ n : ℤ,
    quotientEquiv (QuotientAddGroup.mk n) = reduction n
  quotientEquiv_injective : Function.Injective quotientEquiv
  quotientEquiv_surjective : Function.Surjective quotientEquiv
  generator : ZMod l.value
  generator_eq_reduction_one : generator = reduction 1
  generator_order : addOrderOf generator = l.value
  generator_ne_zero : generator ≠ 0
  roots : CompatibleRootSystem
    (Algebra.GrothendieckGroup (LocalIntegralMonoid l.value))
    (LocalIntegralMonoid.qParameterGroupification l.value)
  roots_eq_packet : roots = packet.compatibleRoots
  theater : HodgeTheater l (FinitePrimePlace 2 7)
  theater_eq : theater = cStage.theater
  sourceFrobenioid : Iut.FrobenioidPresentation
  sourceFrobenioid_eq : sourceFrobenioid = sourceModel

noncomputable def algebraicFiniteThetaLevel (l : PrimeGeFive) :
    AlgebraicFiniteThetaLevel l where
  cStage := cStage l
  packet := packet l
  packet_eq := rfl
  reduction := reduction l
  reduction_eq := rfl
  quotientEquiv := quotientEquiv l
  quotientEquiv_apply_mk := by
    intro n
    exact (packet l).finiteLevelQuotientEquiv_apply_mk n
  quotientEquiv_injective := (quotientEquiv l).injective
  quotientEquiv_surjective := (quotientEquiv l).surjective
  generator := generator l
  generator_eq_reduction_one := by
    simp [generator, reduction, packet, cStage, concreteInitialThetaCStage,
      ConcreteTateLocalCarrier.canonical, ConcreteTateKummerPacket.canonical,
      integralTateReduction, canonicalTateGenerator]
  generator_order := canonicalTateGenerator_order l
  generator_ne_zero := canonicalTateGenerator_ne_zero l
  roots := (packet l).compatibleRoots
  roots_eq_packet := rfl
  theater := theater l
  theater_eq := rfl
  sourceFrobenioid := sourceModel
  sourceFrobenioid_eq := rfl

@[simp] theorem level_cStage (l : PrimeGeFive) :
    (algebraicFiniteThetaLevel l).cStage = cStage l :=
  rfl

@[simp] theorem level_packet (l : PrimeGeFive) :
    (algebraicFiniteThetaLevel l).packet = packet l :=
  rfl

@[simp] theorem level_reduction (l : PrimeGeFive) :
    (algebraicFiniteThetaLevel l).reduction = reduction l :=
  rfl

@[simp] theorem level_generator (l : PrimeGeFive) :
    (algebraicFiniteThetaLevel l).generator = generator l :=
  rfl

@[simp] theorem level_theater (l : PrimeGeFive) :
    (algebraicFiniteThetaLevel l).theater = theater l :=
  rfl

@[simp] theorem level_sourceFrobenioid (l : PrimeGeFive) :
    (algebraicFiniteThetaLevel l).sourceFrobenioid = sourceModel :=
  rfl

theorem level_packet_eq_stage (l : PrimeGeFive) :
    (algebraicFiniteThetaLevel l).packet =
      (algebraicFiniteThetaLevel l).cStage.localCarrier.kummer :=
  (algebraicFiniteThetaLevel l).packet_eq

theorem level_reduction_eq_packet (l : PrimeGeFive) :
    (algebraicFiniteThetaLevel l).reduction =
      (algebraicFiniteThetaLevel l).packet.finiteReduction :=
  (algebraicFiniteThetaLevel l).reduction_eq

theorem level_theater_eq_stage (l : PrimeGeFive) :
    (algebraicFiniteThetaLevel l).theater =
      (algebraicFiniteThetaLevel l).cStage.theater :=
  (algebraicFiniteThetaLevel l).theater_eq

theorem level_sourceFrobenioid_eq_model (l : PrimeGeFive) :
    (algebraicFiniteThetaLevel l).sourceFrobenioid = sourceModel :=
  (algebraicFiniteThetaLevel l).sourceFrobenioid_eq

theorem reduction_apply (l : PrimeGeFive) (n : ℤ) :
    reduction l n = (packet l).finiteReduction n :=
  rfl

theorem reduction_zero (l : PrimeGeFive) :
    reduction l 0 = 0 := by
  exact map_zero (reduction l)

theorem reduction_add (l : PrimeGeFive) (m n : ℤ) :
    reduction l (m + n) = reduction l m + reduction l n := by
  exact map_add (reduction l) m n

theorem reduction_neg (l : PrimeGeFive) (n : ℤ) :
    reduction l (-n) = -reduction l n := by
  exact map_neg (reduction l) n

theorem reduction_sub (l : PrimeGeFive) (m n : ℤ) :
    reduction l (m - n) = reduction l m - reduction l n := by
  exact map_sub (reduction l) m n

theorem reduction_zsmul (l : PrimeGeFive) (a n : ℤ) :
    reduction l (a • n) = a • reduction l n := by
  exact map_zsmul (reduction l) a n

theorem reduction_surjective (l : PrimeGeFive) :
    Function.Surjective (reduction l) := by
  exact (packet l).finiteReduction_surjective

theorem reduction_kernel (l : PrimeGeFive) :
    (reduction l).ker = AddSubgroup.zmultiples (l.value : ℤ) := by
  exact (packet l).finiteReduction_kernel

theorem reduction_zero_iff_multiple (l : PrimeGeFive) (n : ℤ) :
    reduction l n = 0 ↔ n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact ConcreteTateKummerPacket.finiteReduction_zero_iff_multiple l (packet l) n

theorem reduction_eq_iff_multiple (l : PrimeGeFive) (m n : ℤ) :
    reduction l m = reduction l n ↔
      m - n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact ConcreteTateKummerPacket.finiteReduction_eq_iff_multiple l (packet l) m n

theorem reduction_add_multiple (l : PrimeGeFive) (n k : ℤ) :
    reduction l (n + (l.value : ℤ) * k) = reduction l n := by
  exact (packet l).finiteLevel_label_add_multiple n k

theorem reduction_sub_multiple (l : PrimeGeFive) (n k : ℤ) :
    reduction l (n - (l.value : ℤ) * k) = reduction l n := by
  exact (packet l).finiteLevel_label_sub_multiple n k

theorem quotientEquiv_apply_mk (l : PrimeGeFive) (n : ℤ) :
    quotientEquiv l (QuotientAddGroup.mk n) = reduction l n := by
  exact (packet l).finiteLevelQuotientEquiv_apply_mk n

theorem quotientEquiv_zero (l : PrimeGeFive) :
    quotientEquiv l (0 : quotient l) = 0 := by
  exact map_zero (quotientEquiv l)

theorem quotientEquiv_add (l : PrimeGeFive)
    (x y : quotient l) :
    quotientEquiv l (x + y) = quotientEquiv l x + quotientEquiv l y := by
  exact map_add (quotientEquiv l) x y

theorem quotientEquiv_neg (l : PrimeGeFive) (x : quotient l) :
    quotientEquiv l (-x) = -quotientEquiv l x := by
  exact map_neg (quotientEquiv l) x

theorem quotientEquiv_zsmul (l : PrimeGeFive) (a : ℤ) (x : quotient l) :
    quotientEquiv l (a • x) = a • quotientEquiv l x := by
  exact map_zsmul (quotientEquiv l) a x

theorem quotientEquiv_injective (l : PrimeGeFive) :
    Function.Injective (quotientEquiv l) := by
  exact (quotientEquiv l).injective

theorem quotientEquiv_surjective (l : PrimeGeFive) :
    Function.Surjective (quotientEquiv l) := by
  exact (quotientEquiv l).surjective

theorem quotientEquiv_bijective (l : PrimeGeFive) :
    Function.Bijective (quotientEquiv l) := by
  exact (quotientEquiv l).bijective

theorem quotient_mk_add (l : PrimeGeFive) (m n : ℤ) :
    (QuotientAddGroup.mk (m + n) : quotient l) =
      QuotientAddGroup.mk m + QuotientAddGroup.mk n := by
  rfl

theorem quotient_mk_neg (l : PrimeGeFive) (n : ℤ) :
    (QuotientAddGroup.mk (-n) : quotient l) =
      -(QuotientAddGroup.mk n) := by
  rfl

theorem quotient_mk_sub (l : PrimeGeFive) (m n : ℤ) :
    (QuotientAddGroup.mk (m - n) : quotient l) =
      QuotientAddGroup.mk m - QuotientAddGroup.mk n := by
  rfl

theorem quotient_mk_zsmul (l : PrimeGeFive) (a n : ℤ) :
    (QuotientAddGroup.mk (a • n) : quotient l) =
      a • QuotientAddGroup.mk n := by
  rfl

theorem quotient_mk_surjective (l : PrimeGeFive) :
    Function.Surjective (fun n : ℤ =>
      (QuotientAddGroup.mk n : quotient l)) := by
  exact QuotientAddGroup.mk_surjective

theorem quotient_eq_iff (l : PrimeGeFive) (m n : ℤ) :
    (QuotientAddGroup.mk m : quotient l) = QuotientAddGroup.mk n ↔
      m - n ∈ (packet l).finiteReduction.ker := by
  exact QuotientAddGroup.eq_iff_sub_mem

theorem quotient_eq_iff_multiple (l : PrimeGeFive) (m n : ℤ) :
    (QuotientAddGroup.mk m : quotient l) = QuotientAddGroup.mk n ↔
      m - n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact (packet l).finiteLevel_quotient_eq_iff_multiple m n

theorem quotient_zero_iff_multiple (l : PrimeGeFive) (n : ℤ) :
    (QuotientAddGroup.mk n : quotient l) = 0 ↔
      n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact (packet l).finiteLevel_quotient_mk_zero_iff n

theorem quotient_mk_add_multiple (l : PrimeGeFive) (n k : ℤ) :
    (QuotientAddGroup.mk (n + (l.value : ℤ) * k) : quotient l) =
      QuotientAddGroup.mk n := by
  exact (packet l).finiteLevel_quotient_mk_add_multiple n k

theorem quotient_mk_sub_multiple (l : PrimeGeFive) (n k : ℤ) :
    (QuotientAddGroup.mk (n - (l.value : ℤ) * k) : quotient l) =
      QuotientAddGroup.mk n := by
  exact (packet l).finiteLevel_quotient_mk_sub_multiple n k

theorem generator_eq_reduction_one (l : PrimeGeFive) :
    generator l = reduction l 1 := by
  simp [generator, reduction, packet, cStage, concreteInitialThetaCStage,
    ConcreteTateLocalCarrier.canonical, ConcreteTateKummerPacket.canonical,
    integralTateReduction, canonicalTateGenerator]

theorem generator_order (l : PrimeGeFive) :
    addOrderOf (generator l) = l.value := by
  exact canonicalTateGenerator_order l

theorem generator_ne_zero (l : PrimeGeFive) :
    generator l ≠ 0 := by
  exact canonicalTateGenerator_ne_zero l

theorem generator_not_small_order (l : PrimeGeFive) (h : addOrderOf (generator l) = 1) :
    False := by
  rw [generator_order l] at h
  have hge := l.ge_five
  omega

theorem generator_not_two_order (l : PrimeGeFive) (h : addOrderOf (generator l) = 2) :
    False := by
  rw [generator_order l] at h
  have hge := l.ge_five
  omega

theorem generator_is_unit_level (l : PrimeGeFive) :
    IsUnit (generator l) := by
  exact isUnit_iff_ne_zero.mpr (generator_ne_zero l)

theorem root_zero (l : PrimeGeFive) :
    (roots l).roots 0 = 0 := by
  exact map_zero (roots l).roots

theorem root_add (l : PrimeGeFive) (a b : ℚ) :
    (roots l).roots (a + b) = (roots l).roots a + (roots l).roots b := by
  exact map_add (roots l).roots a b

theorem root_neg (l : PrimeGeFive) (a : ℚ) :
    (roots l).roots (-a) = -(roots l).roots a := by
  exact map_neg (roots l).roots a

theorem root_sub (l : PrimeGeFive) (a b : ℚ) :
    (roots l).roots (a - b) = (roots l).roots a - (roots l).roots b := by
  exact map_sub (roots l).roots a b

theorem root_zsmul (l : PrimeGeFive) (a : ℤ) (b : ℚ) :
    (roots l).roots (a • b) = a • (roots l).roots b := by
  exact (roots l).roots.map_zsmul a b

theorem integer_root_zero (l : PrimeGeFive) :
    (packet l).integerRoot 0 = 0 := by
  exact ConcreteTateKummerPacket.integerRoot_zero l (packet l)

theorem integer_root_add (l : PrimeGeFive) (m n : ℤ) :
    (packet l).integerRoot (m + n) =
      (packet l).integerRoot m + (packet l).integerRoot n := by
  exact ConcreteTateKummerPacket.integerRoot_add l (packet l) m n

theorem integer_root_neg (l : PrimeGeFive) (n : ℤ) :
    (packet l).integerRoot (-n) = -(packet l).integerRoot n := by
  exact ConcreteTateKummerPacket.integerRoot_neg l (packet l) n

theorem integer_root_sub (l : PrimeGeFive) (m n : ℤ) :
    (packet l).integerRoot (m - n) =
      (packet l).integerRoot m - (packet l).integerRoot n := by
  exact ConcreteTateKummerPacket.integerRoot_sub l (packet l) m n

theorem integer_root_mul (l : PrimeGeFive) (m n : ℤ) :
    (packet l).integerRoot (m * n) =
      m • (packet l).integerRoot n := by
  exact ConcreteTateKummerPacket.integerRoot_mul l (packet l) m n

theorem integer_root_one (l : PrimeGeFive) :
    (packet l).integerRoot 1 =
      Additive.ofMul (LocalIntegralMonoid.qParameterGroupification l.value) := by
  exact ConcreteTateKummerPacket.integerRoot_one l (packet l)

theorem integer_root_compatible (l : PrimeGeFive) (n : ℤ) :
    (packet l).integerRoot n = (roots l).roots (n : ℚ) := by
  exact ConcreteTateKummerPacket.integerRoot_eq_compatible_roots l (packet l) n

theorem integer_root_zero_label_lift (l : PrimeGeFive) (n : ℤ)
    (h : reduction l n = 0) :
    ∃ k : ℤ,
      (packet l).integerRoot n = (l.value : ℤ) • (packet l).integerRoot k := by
  exact ConcreteTateKummerPacket.integerRoot_zero_label_multiple l (packet l) n h

theorem root_zero_label_lift (l : PrimeGeFive) (n : ℤ)
    (h : reduction l n = 0) :
    ∃ k : ℤ,
      (roots l).roots (n : ℚ) =
        (l.value : ℤ) • (roots l).roots (k : ℚ) := by
  obtain ⟨k, hk⟩ := integer_root_zero_label_lift l n h
  refine ⟨k, ?_⟩
  rw [← integer_root_compatible l n, ← integer_root_compatible l k]
  exact hk

theorem root_label_eq_of_reduction_eq (l : PrimeGeFive) (m n : ℤ)
    (_h : reduction l m = reduction l n) :
    (roots l).roots (m : ℚ) - (roots l).roots (n : ℚ) =
    (roots l).roots ((m - n : ℤ) : ℚ) := by
  rw [show ((m - n : ℤ) : ℚ) = (m : ℚ) - (n : ℚ) by norm_num]
  exact (map_sub (roots l).roots (m : ℚ) (n : ℚ)).symm

theorem root_label_sub_multiple (l : PrimeGeFive) (n k : ℤ) :
    (roots l).roots ((n + (l.value : ℤ) * k : ℤ) : ℚ) =
      (roots l).roots (n : ℚ) +
        (l.value : ℤ) • (roots l).roots (k : ℚ) := by
  rw [show ((n + (l.value : ℤ) * k : ℤ) : ℚ) =
      (n : ℚ) + (l.value : ℤ) • (k : ℚ) by norm_num]
  rw [map_add, map_zsmul]

abbrev qDeckQuotient (l : PrimeGeFive) :=
  (AlgebraicClosure ℚ_[l.value])ˣ ⧸ (parameter l).qDeckSubgroup

def qDeckAction (l : PrimeGeFive)
    (sigma : ConcreteTateParameter.LocalAbsoluteGalois l) :
    qDeckQuotient l ≃* qDeckQuotient l :=
  (parameter l).qDeckQuotientEquiv sigma

theorem q_power_nonzero (l : PrimeGeFive) (n : ℕ) :
    (parameter l).q ^ n ≠ 0 := by
  exact ConcreteTateParameter.q_power_ne_zero l (parameter l) n

theorem q_power_not_one (l : PrimeGeFive) (n : ℕ) (hn : 0 < n) :
    (parameter l).q ^ n ≠ 1 := by
  exact ConcreteTateParameter.q_power_ne_one l (parameter l) n hn

theorem q_unit_nontrivial (l : PrimeGeFive) :
    (parameter l).qUnit ≠ 1 := by
  exact ConcreteTateParameter.qUnit_ne_one l (parameter l)

theorem q_unit_pow (l : PrimeGeFive) (n : ℕ) :
    (parameter l).qUnit ^ n =
      Units.map
        (algebraMap (ℚ_[l.value])
          (AlgebraicClosure ℚ_[l.value])).toMonoidHom
        (Units.mk0 ((parameter l).q ^ n) (q_power_nonzero l n)) := by
  exact ConcreteTateParameter.qUnit_pow l (parameter l) n

theorem q_deck_action_mk (l : PrimeGeFive)
    (sigma : ConcreteTateParameter.LocalAbsoluteGalois l)
    (x : (AlgebraicClosure ℚ_[l.value])ˣ) :
    qDeckAction l sigma (QuotientGroup.mk x) =
      (QuotientGroup.mk ((parameter l).unitsGaloisEquiv sigma x) :
        qDeckQuotient l) := by
  exact (parameter l).qDeckQuotientEquiv_mk sigma x

theorem q_deck_action_refl (l : PrimeGeFive) :
    qDeckAction l (AlgEquiv.refl) = MulEquiv.refl _ := by
  exact ConcreteTateParameter.qDeckQuotientEquiv_refl (parameter l)

theorem q_deck_action_trans (l : PrimeGeFive)
    (sigma tau : ConcreteTateParameter.LocalAbsoluteGalois l) :
    qDeckAction l (sigma.trans tau) =
      (qDeckAction l sigma).trans (qDeckAction l tau) := by
  exact ConcreteTateParameter.qDeckQuotientEquiv_trans (parameter l) sigma tau

theorem q_deck_action_preserves_power (l : PrimeGeFive)
    (sigma : ConcreteTateParameter.LocalAbsoluteGalois l)
    (x : (AlgebraicClosure ℚ_[l.value])ˣ) (n : ℤ) :
    qDeckAction l sigma (QuotientGroup.mk (x ^ n)) =
      (QuotientGroup.mk ((parameter l).unitsGaloisEquiv sigma x ^ n) :
        qDeckQuotient l) := by
  exact (parameter l).qDeckQuotientEquiv_preserves_power_class sigma x n

theorem q_deck_action_fixes_generator (l : PrimeGeFive)
    (sigma : ConcreteTateParameter.LocalAbsoluteGalois l) :
    qDeckAction l sigma (QuotientGroup.mk (parameter l).qUnit) =
      (QuotientGroup.mk (parameter l).qUnit : qDeckQuotient l) := by
  exact (parameter l).qDeckQuotientEquiv_qUnit_class sigma

theorem q_deck_quotient_eq_iff (l : PrimeGeFive)
    (x y : (AlgebraicClosure ℚ_[l.value])ˣ) :
    (QuotientGroup.mk x : qDeckQuotient l) = QuotientGroup.mk y ↔
      x / y ∈ (parameter l).qDeckSubgroup := by
  exact ConcreteTateParameter.qDeckQuotient_eq_iff (parameter l) x y

theorem q_deck_quotient_eq_iff_power_ratio (l : PrimeGeFive)
    (x y : (AlgebraicClosure ℚ_[l.value])ˣ) :
    (QuotientGroup.mk x : qDeckQuotient l) = QuotientGroup.mk y ↔
      ∃ n : ℤ, x / y = (parameter l).qUnit ^ n := by
  exact ConcreteTateParameter.qDeckQuotient_eq_iff_power_ratio
    (parameter l) x y

theorem q_deck_quotient_mul_power (l : PrimeGeFive)
    (x : (AlgebraicClosure ℚ_[l.value])ˣ) (n : ℤ) :
    (QuotientGroup.mk (x * (parameter l).qUnit ^ n) : qDeckQuotient l) =
      QuotientGroup.mk x := by
  exact ConcreteTateParameter.qDeckQuotient_mk_mul_qUnit (parameter l) x n

theorem q_deck_action_preserves_equality (l : PrimeGeFive)
    (sigma : ConcreteTateParameter.LocalAbsoluteGalois l)
    (x y : (AlgebraicClosure ℚ_[l.value])ˣ)
    (h : (QuotientGroup.mk x : qDeckQuotient l) = QuotientGroup.mk y) :
    qDeckAction l sigma (QuotientGroup.mk x) =
      qDeckAction l sigma (QuotientGroup.mk y) := by
  exact congrArg (qDeckAction l sigma) h

theorem theta_q_pos (l : PrimeGeFive) :
    0 < thetaScale l (⟨0, by
      have hstar : 0 ≤ (lStar l.value : Int) := by
        exact_mod_cast Nat.zero_le (lStar l.value)
      constructor <;> omega⟩ : SignedLabel l.value) := by
  exact (theater l).thetaPacket.scale_pos _

theorem theta_scale_eq_real_value (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    thetaScale l j = realThetaValue gaussianFiveThetaQ j.1 := by
  exact concreteInitialThetaCStage_theta_scale l j

theorem theta_scale_pos (l : PrimeGeFive) (j : SignedLabel l.value) :
    0 < thetaScale l j := by
  exact (theater l).thetaPacket.scale_pos j

theorem theta_scale_ne_zero (l : PrimeGeFive) (j : SignedLabel l.value) :
    thetaScale l j ≠ 0 := by
  exact ne_of_gt (theta_scale_pos l j)

theorem theta_scale_neg (l : PrimeGeFive) (j : SignedLabel l.value) :
    thetaScale l (SignedLabel.neg j) = thetaScale l j := by
  exact (theater l).thetaPacket.scale_neg j

theorem theta_log_scale_eq (l : PrimeGeFive) (j : SignedLabel l.value) :
    thetaLogScale l j = Real.log gaussianFiveThetaQ *
      (gaussExponent j.1).toNat := by
  change Real.log (thetaScale l j) = _
  rw [theta_scale_eq_real_value]
  simpa [mul_comm] using
    (log_realThetaValue (q := gaussianFiveThetaQ) j.1)

theorem theta_log_scale_local_degree (l : PrimeGeFive) (j : SignedLabel l.value) :
    thetaLogScale l j =
      (gaussExponent j.1).toNat *
        Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  exact concreteInitialThetaCStage_theta_log_scale l j

theorem theta_log_volume_eq_sum (l : PrimeGeFive) :
    thetaLogVolume l = ∑ j : SignedLabel l.value, thetaLogScale l j := by
  rfl

theorem theta_log_volume_eq_local_degree_sum (l : PrimeGeFive) :
    thetaLogVolume l =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat *
          Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  exact concreteInitialThetaCStage_theta_log_volume l

theorem theta_log_volume_neg_invariant (l : PrimeGeFive) :
    (∑ j : SignedLabel l.value, thetaLogScale l (SignedLabel.neg j)) =
      thetaLogVolume l := by
  exact (theater l).thetaPacket.logVolume_neg_invariant

theorem theta_scale_product_eq_exp_log_volume (l : PrimeGeFive) :
    Real.exp (thetaLogVolume l) =
      ∏ j : SignedLabel l.value, thetaScale l j := by
  rw [theta_log_volume_eq_sum]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro j hj
  change Real.exp (Real.log (thetaScale l j)) = thetaScale l j
  exact Real.exp_log (theta_scale_pos l j)

theorem theta_scale_product_positive (l : PrimeGeFive) :
    0 < ∏ j : SignedLabel l.value, thetaScale l j := by
  apply Finset.prod_pos
  intro j hj
  exact theta_scale_pos l j

theorem theta_scale_product_ne_zero (l : PrimeGeFive) :
    (∏ j : SignedLabel l.value, thetaScale l j) ≠ 0 := by
  exact ne_of_gt (theta_scale_product_positive l)

theorem theta_scale_product_log (l : PrimeGeFive) :
    Real.log (∏ j : SignedLabel l.value, thetaScale l j) =
      thetaLogVolume l := by
  rw [Real.log_prod (fun j _ => theta_scale_ne_zero l j)]
  exact theta_log_volume_eq_sum l

theorem theta_packet_q (l : PrimeGeFive) :
    (theater l).thetaPacket.q = gaussianFiveThetaQ := by
  exact concreteInitialThetaCStage_theta_q l

theorem theta_packet_q_positive (l : PrimeGeFive) :
    0 < (theater l).thetaPacket.q := by
  rw [theta_packet_q]
  exact gaussianFiveThetaQ_pos

theorem theta_packet_q_ne_zero (l : PrimeGeFive) :
    (theater l).thetaPacket.q ≠ 0 := by
  exact ne_of_gt (theta_packet_q_positive l)

theorem theta_packet_scale_eq (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    (theater l).thetaPacket.scale j = thetaScale l j := by
  rfl

theorem theta_packet_log_volume_eq (l : PrimeGeFive) :
    (theater l).thetaPacket.logVolume = thetaLogVolume l := by
  rfl

theorem theater_arithmetic_eq_input (l : PrimeGeFive) :
    (theater l).arithmetic = (cStage l).input.arithmetic := by
  exact concreteInitialThetaCStage_theater_arithmetic l

theorem source_model_is_connected :
    CategoryTheory.IsConnected ConcreteSourceFrobenioidBridge.concreteStageBase := by
  exact ConcreteSourceFrobenioidBridge.source_stage_model_base_is_connected

theorem source_model_arrow_epi
    {source target : ConcreteSourceFrobenioidBridge.concreteStageBase}
    (arrow : source ⟶ target) :
    Epi arrow := by
  exact ConcreteSourceFrobenioidBridge.source_stage_model_base_arrow_epi arrow

theorem source_model_zero_object_base
    (stage : ConcreteSourceFrobenioidBridge.concreteStageBase) :
    Iut.SourceModelFrobenioid.Object.base
      (Iut.SourceModelFrobenioid.Carrier.zeroObject
        ConcreteSourceFrobenioidBridge.concreteStageModelDivisorialMonoid
        ConcreteSourceFrobenioidBridge.concreteStageModelInput stage) = stage := by
  exact ConcreteSourceFrobenioidBridge.source_stage_model_zero_object_base stage

structure ConcreteSourceAlgebraicThetaOutput (l : PrimeGeFive) where
  level : AlgebraicFiniteThetaLevel l
  sourceModel : Iut.FrobenioidPresentation
  sourceModel_eq : sourceModel = ConcreteSourceEtaleThetaBridge.sourceModel
  finiteQuotient : Type
  finiteQuotient_equiv : finiteQuotient = quotient l
  thetaVolume : Real
  thetaVolume_eq : thetaVolume = thetaLogVolume l

noncomputable def concreteSourceAlgebraicThetaOutput (l : PrimeGeFive) :
    ConcreteSourceAlgebraicThetaOutput l where
  level := algebraicFiniteThetaLevel l
  sourceModel := ConcreteSourceEtaleThetaBridge.sourceModel
  sourceModel_eq := rfl
  finiteQuotient := quotient l
  finiteQuotient_equiv := rfl
  thetaVolume := thetaLogVolume l
  thetaVolume_eq := rfl

@[simp] theorem algebraic_output_level (l : PrimeGeFive) :
    (concreteSourceAlgebraicThetaOutput l).level = algebraicFiniteThetaLevel l :=
  rfl

@[simp] theorem algebraic_output_source_model (l : PrimeGeFive) :
    (concreteSourceAlgebraicThetaOutput l).sourceModel = sourceModel :=
  rfl

@[simp] theorem algebraic_output_finite_quotient (l : PrimeGeFive) :
    (concreteSourceAlgebraicThetaOutput l).finiteQuotient = quotient l :=
  rfl

@[simp] theorem algebraic_output_theta_volume (l : PrimeGeFive) :
    (concreteSourceAlgebraicThetaOutput l).thetaVolume = thetaLogVolume l :=
  rfl

theorem algebraic_output_generator_order (l : PrimeGeFive) :
    addOrderOf (generator l) = l.value :=
  generator_order l

theorem algebraic_output_reduction_kernel (l : PrimeGeFive) :
    (reduction l).ker = AddSubgroup.zmultiples (l.value : ℤ) :=
  reduction_kernel l

theorem algebraic_output_root_compatibility (l : PrimeGeFive) (n : ℤ) :
    (packet l).integerRoot n = (roots l).roots (n : ℚ) :=
  integer_root_compatible l n

theorem algebraic_output_source_model_connection (l : PrimeGeFive) :
    (algebraicFiniteThetaLevel l).sourceFrobenioid = sourceModel :=
  level_sourceFrobenioid_eq_model l

end ConcreteSourceEtaleThetaBridge

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteSourceEtaleThetaBridge : Obligation :=
  { id := "IUT-I-II.concrete-source-algebraic-theta-bridge"
    source := "IUT II, finite etale theta direction and Kummer/Frobenioid carrier"
    status := VerificationStatus.proved
    note :=
      "The actual finite reduction quotient, exact kernel, generator order, " ++
        "compatible integer/rational roots, q-deck quotient action, theta " ++
        "scale symmetry and log-volume, and the concrete source Frobenioid " ++
        "presentation are packaged in an algebraic finite-theta output. The " ++
        "record does not assert a geometric etale fundamental-group " ++
        "identification; that boundary is recorded in this audit note."
    dependsOn :=
      [ "IUT-I-II.concrete-source-frobenioid-bridge",
        "Foundations.Geometry.concrete-tate-finite-level",
        "Foundations.Geometry.concrete-tate-deck-quotient",
        "IUT-II.concrete-etale-kummer-bridge" ] }

end LeanFormal.IUT.Audit
