/-
  Local arithmetic projections for the concrete C boundary.

  This is the algebraic part of the finite Tate direction: powers of q, deck
  classes, finite reductions, exact quotient classes, and coherent integer
  roots.  It records no analytic point map and no Tate uniformization.
-/

import LeanFormal.IUT.IUTI.InitialTheta.ConcreteInitialThetaCObligations
import LeanFormal.IUT.Foundations.Geometry.ConcreteTateFiniteLevel
import LeanFormal.IUT.Foundations.Geometry.ConcreteTateDeckQuotient

namespace LeanFormal.IUT

noncomputable section

local instance primeFactForConcreteLocalArithmetic
    (l : PrimeGeFive) : Fact (Nat.Prime l.value) := l.factPrime

namespace ConcreteInitialThetaLocalArithmetic

variable {l : PrimeGeFive} [Fact (Nat.Prime l.value)]

def parameter (l : PrimeGeFive) : ConcreteTateParameter l :=
  (concreteCConstructedBoundary l).localCarrier.parameter

def packet (l : PrimeGeFive) : ConcreteTateKummerPacket l :=
  (concreteCConstructedBoundary l).localCarrier.kummer

@[simp] theorem parameter_eq_canonical (l : PrimeGeFive) :
    parameter l = ConcreteTateParameter.canonical l :=
  rfl

@[simp] theorem packet_eq_canonical (l : PrimeGeFive) :
    packet l = ConcreteTateKummerPacket.canonical l :=
  rfl

theorem q_eq_prime (l : PrimeGeFive) :
    (parameter l).q = (l.value : ℚ_[l.value]) := by
  exact (parameter l).q_eq_prime

theorem q_norm_lt_one (l : PrimeGeFive) :
    ‖(parameter l).q‖ < 1 := by
  exact (parameter l).q_norm_lt_one

theorem q_ne_zero (l : PrimeGeFive) :
    (parameter l).q ≠ 0 := by
  exact (parameter l).q_ne_zero

theorem q_ne_one (l : PrimeGeFive) :
    (parameter l).q ≠ 1 := by
  exact ConcreteTateParameter.q_ne_one l (parameter l)

theorem q_power_norm_lt_one (l : PrimeGeFive) (n : Nat) (hn : 0 < n) :
    ‖(parameter l).q ^ n‖ < 1 := by
  exact ConcreteTateParameter.q_power_norm_lt_one l (parameter l) n hn

theorem q_power_ne_zero (l : PrimeGeFive) (n : Nat) :
    (parameter l).q ^ n ≠ 0 := by
  exact ConcreteTateParameter.q_power_ne_zero l (parameter l) n

theorem q_power_ne_one (l : PrimeGeFive) (n : Nat) (hn : 0 < n) :
    (parameter l).q ^ n ≠ 1 := by
  exact ConcreteTateParameter.q_power_ne_one l (parameter l) n hn

theorem q_unit_ne_one (l : PrimeGeFive) :
    (parameter l).qUnit ≠ 1 := by
  exact ConcreteTateParameter.qUnit_ne_one l (parameter l)

theorem q_unit_power (l : PrimeGeFive) (n : Nat) :
    (parameter l).qUnit ^ n =
      Units.map
        (algebraMap (ℚ_[l.value]) (AlgebraicClosure ℚ_[l.value])).toMonoidHom
        (Units.mk0 ((parameter l).q ^ n)
          (ConcreteTateParameter.q_power_ne_zero l (parameter l) n)) := by
  exact ConcreteTateParameter.qUnit_pow l (parameter l) n

theorem q_unit_galois_fixed
    (l : PrimeGeFive) (sigma : ConcreteTateParameter.LocalAbsoluteGalois l) :
    (parameter l).unitsGaloisEquiv sigma (parameter l).qUnit =
      (parameter l).qUnit := by
  exact (parameter l).unitsGaloisEquiv_qUnit sigma

theorem deck_subgroup_map
    (l : PrimeGeFive) (sigma : ConcreteTateParameter.LocalAbsoluteGalois l) :
    Subgroup.map ((parameter l).unitsGaloisEquiv sigma).toMonoidHom
        (parameter l).qDeckSubgroup =
      (parameter l).qDeckSubgroup := by
  exact (parameter l).qDeckSubgroup_map sigma

theorem deck_quotient_mk
    (l : PrimeGeFive) (sigma : ConcreteTateParameter.LocalAbsoluteGalois l)
    (x : (AlgebraicClosure ℚ_[l.value])ˣ) :
    (parameter l).qDeckQuotientEquiv sigma (QuotientGroup.mk x) =
      QuotientGroup.mk ((parameter l).unitsGaloisEquiv sigma x) := by
  exact (parameter l).qDeckQuotientEquiv_mk sigma x

theorem deck_quotient_q_unit_class
    (l : PrimeGeFive) (sigma : ConcreteTateParameter.LocalAbsoluteGalois l) :
    (parameter l).qDeckQuotientEquiv sigma
        (QuotientGroup.mk (parameter l).qUnit) =
      QuotientGroup.mk (parameter l).qUnit := by
  exact (parameter l).qDeckQuotientEquiv_qUnit_class sigma

theorem deck_quotient_power_class
    (l : PrimeGeFive) (sigma : ConcreteTateParameter.LocalAbsoluteGalois l)
    (x : (AlgebraicClosure ℚ_[l.value])ˣ) (n : ℤ) :
    (parameter l).qDeckQuotientEquiv sigma
        (QuotientGroup.mk (x ^ n)) =
      QuotientGroup.mk (((parameter l).unitsGaloisEquiv sigma x) ^ n) := by
  exact (parameter l).qDeckQuotientEquiv_preserves_power_class sigma x n

theorem deck_quotient_eq_iff
    (l : PrimeGeFive) (x y : (AlgebraicClosure ℚ_[l.value])ˣ) :
    (QuotientGroup.mk x :
      (AlgebraicClosure ℚ_[l.value])ˣ ⧸ (parameter l).qDeckSubgroup) =
        QuotientGroup.mk y ↔
      x / y ∈ (parameter l).qDeckSubgroup := by
  exact (parameter l).qDeckQuotient_eq_iff x y

theorem deck_quotient_eq_iff_power_ratio
    (l : PrimeGeFive) (x y : (AlgebraicClosure ℚ_[l.value])ˣ) :
    (QuotientGroup.mk x :
      (AlgebraicClosure ℚ_[l.value])ˣ ⧸ (parameter l).qDeckSubgroup) =
        QuotientGroup.mk y ↔
      ∃ n : ℤ, x / y = (parameter l).qUnit ^ n := by
  exact (parameter l).qDeckQuotient_eq_iff_power_ratio x y

theorem deck_quotient_mul_q_power
    (l : PrimeGeFive) (x : (AlgebraicClosure ℚ_[l.value])ˣ) (n : ℤ) :
    (QuotientGroup.mk (x * (parameter l).qUnit ^ n) :
      (AlgebraicClosure ℚ_[l.value])ˣ ⧸ (parameter l).qDeckSubgroup) =
        QuotientGroup.mk x := by
  exact (parameter l).qDeckQuotient_mk_mul_qUnit x n

theorem finite_reduction_zero (l : PrimeGeFive) :
    (packet l).finiteReduction 0 = 0 := by
  exact ConcreteTateKummerPacket.finiteReduction_zero l (packet l)

theorem finite_reduction_add (l : PrimeGeFive) (m n : ℤ) :
    (packet l).finiteReduction (m + n) =
      (packet l).finiteReduction m + (packet l).finiteReduction n := by
  exact ConcreteTateKummerPacket.finiteReduction_add l (packet l) m n

theorem finite_reduction_neg (l : PrimeGeFive) (n : ℤ) :
    (packet l).finiteReduction (-n) = -(packet l).finiteReduction n := by
  exact ConcreteTateKummerPacket.finiteReduction_neg l (packet l) n

theorem finite_reduction_sub (l : PrimeGeFive) (m n : ℤ) :
    (packet l).finiteReduction (m - n) =
      (packet l).finiteReduction m - (packet l).finiteReduction n := by
  exact ConcreteTateKummerPacket.finiteReduction_sub l (packet l) m n

theorem finite_reduction_zsmul (l : PrimeGeFive) (a n : ℤ) :
    (packet l).finiteReduction (a • n) =
      a • (packet l).finiteReduction n := by
  exact ConcreteTateKummerPacket.finiteReduction_zsmul l (packet l) a n

theorem finite_reduction_kernel (l : PrimeGeFive) :
    (packet l).finiteReduction.ker =
      AddSubgroup.zmultiples (l.value : ℤ) := by
  exact (packet l).finiteReduction_kernel

theorem finite_reduction_zero_iff_multiple (l : PrimeGeFive) (n : ℤ) :
    (packet l).finiteReduction n = 0 ↔
      n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact ConcreteTateKummerPacket.finiteReduction_zero_iff_multiple l (packet l) n

theorem finite_reduction_eq_iff_multiple (l : PrimeGeFive) (m n : ℤ) :
    (packet l).finiteReduction m = (packet l).finiteReduction n ↔
      m - n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact ConcreteTateKummerPacket.finiteReduction_eq_iff_multiple l (packet l) m n

theorem finite_reduction_add_multiple (l : PrimeGeFive) (n k : ℤ) :
    (packet l).finiteReduction (n + (l.value : ℤ) * k) =
      (packet l).finiteReduction n := by
  exact (packet l).finiteLevel_label_add_multiple n k

theorem finite_reduction_sub_multiple (l : PrimeGeFive) (n k : ℤ) :
    (packet l).finiteReduction (n - (l.value : ℤ) * k) =
      (packet l).finiteReduction n := by
  exact (packet l).finiteLevel_label_sub_multiple n k

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
    (packet l).integerRoot (m * n) = m • (packet l).integerRoot n := by
  exact ConcreteTateKummerPacket.integerRoot_mul l (packet l) m n

theorem integer_root_one (l : PrimeGeFive) :
    (packet l).integerRoot 1 =
      Additive.ofMul (LocalIntegralMonoid.qParameterGroupification l.value) := by
  exact ConcreteTateKummerPacket.integerRoot_one l (packet l)

theorem integer_root_zero_label_multiple
    (l : PrimeGeFive) (n : ℤ) (h : (packet l).finiteReduction n = 0) :
    ∃ k : ℤ, (packet l).integerRoot n =
      (l.value : ℤ) • (packet l).integerRoot k := by
  exact ConcreteTateKummerPacket.integerRoot_zero_label_multiple l (packet l) n h

theorem compatible_root_zero (l : PrimeGeFive) :
    (packet l).compatibleRoots.roots 0 = 0 := by
  exact ConcreteTateKummerPacket.compatibleRoot_zero l (packet l)

theorem compatible_root_add (l : PrimeGeFive) (a b : ℚ) :
    (packet l).compatibleRoots.roots (a + b) =
      (packet l).compatibleRoots.roots a + (packet l).compatibleRoots.roots b := by
  exact ConcreteTateKummerPacket.compatibleRoot_add l (packet l) a b

theorem compatible_root_neg (l : PrimeGeFive) (a : ℚ) :
    (packet l).compatibleRoots.roots (-a) =
      -(packet l).compatibleRoots.roots a := by
  exact ConcreteTateKummerPacket.compatibleRoot_neg l (packet l) a

theorem compatible_root_zsmul (l : PrimeGeFive) (a : ℤ) (b : ℚ) :
    (packet l).compatibleRoots.roots (a • b) =
      a • (packet l).compatibleRoots.roots b := by
  exact ConcreteTateKummerPacket.compatibleRoot_zsmul l (packet l) a b

theorem integer_root_eq_compatible (l : PrimeGeFive) (n : ℤ) :
    (packet l).integerRoot n = (packet l).compatibleRoots.roots (n : ℚ) := by
  exact ConcreteTateKummerPacket.integerRoot_eq_compatible_roots l (packet l) n

theorem finite_level_equiv_mk (l : PrimeGeFive) (n : ℤ) :
    ConcreteTateKummerPacket.finiteLevelQuotientEquiv (packet l)
        (QuotientAddGroup.mk n) = (packet l).finiteReduction n := by
  exact (packet l).finiteLevelQuotientEquiv_apply_mk n

theorem finite_level_quotient_zero_iff (l : PrimeGeFive) (n : ℤ) :
    (QuotientAddGroup.mk n : ℤ ⧸ (packet l).finiteReduction.ker) = 0 ↔
      n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact (packet l).finiteLevel_quotient_mk_zero_iff n

theorem finite_level_quotient_eq_iff_multiple
    (l : PrimeGeFive) (m n : ℤ) :
    (QuotientAddGroup.mk m : ℤ ⧸ (packet l).finiteReduction.ker) =
      QuotientAddGroup.mk n ↔
      m - n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact (packet l).finiteLevel_quotient_eq_iff_multiple m n

theorem finite_level_quotient_add_multiple
    (l : PrimeGeFive) (n k : ℤ) :
    (QuotientAddGroup.mk (n + (l.value : ℤ) * k) :
      ℤ ⧸ (packet l).finiteReduction.ker) = QuotientAddGroup.mk n := by
  exact (packet l).finiteLevel_quotient_mk_add_multiple n k

theorem finite_level_quotient_sub_multiple
    (l : PrimeGeFive) (n k : ℤ) :
    (QuotientAddGroup.mk (n - (l.value : ℤ) * k) :
      ℤ ⧸ (packet l).finiteReduction.ker) = QuotientAddGroup.mk n := by
  exact (packet l).finiteLevel_quotient_mk_sub_multiple n k

theorem finite_level_label_surjective (l : PrimeGeFive) :
    Function.Surjective (packet l).finiteReduction := by
  exact (packet l).finiteReduction_surjective

theorem finite_level_equiv_injective (l : PrimeGeFive) :
    Function.Injective
      (ConcreteTateKummerPacket.finiteLevelQuotientEquiv (packet l)) := by
  exact (packet l).finiteLevelQuotientEquiv.injective

theorem finite_level_equiv_surjective (l : PrimeGeFive) :
    Function.Surjective
      (ConcreteTateKummerPacket.finiteLevelQuotientEquiv (packet l)) := by
  exact (packet l).finiteLevelQuotientEquiv.surjective

end ConcreteInitialThetaLocalArithmetic

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteInitialThetaLocalArithmetic : Obligation :=
  { id := "IUT-II.concrete-initial-theta-local-arithmetic"
    source := "IUT II finite Tate/Kummer direction"
    status := VerificationStatus.proved
    note :=
      "The concrete C boundary exposes q powers, Galois-fixed deck classes, " ++
        "exact finite reduction kernels, quotient representatives, coherent " ++
        "integer roots, and compatible rational roots through named local " ++
        "theorems. These are genuine algebraic consequences and do not claim " ++
        "an etale fundamental-group or point-uniformization identification."
    dependsOn := [ "IUT-I-II.concrete-c-constructed-boundary",
      "Foundations.Geometry.concrete-tate-finite-level",
      "Foundations.Geometry.concrete-tate-deck-quotient" ] }

end LeanFormal.IUT.Audit
