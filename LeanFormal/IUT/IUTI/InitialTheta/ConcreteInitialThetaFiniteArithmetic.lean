/-
  Arithmetic consequences used by the concrete initial-theta carrier.

  These lemmas expose the finite label bounds, sign quotient, Gaussian
  exponents, and volume normalization at the exact prime-label type used by
  the carrier.  They are ordinary finite arithmetic; no geometric theorem is
  hidden behind a numerical equality.
-/

import LeanFormal.IUT.IUTI.InitialTheta.ConcreteInitialThetaLinks
import LeanFormal.IUT.Foundations.Theta.GaussianSquareSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace LeanFormal.IUT

noncomputable section

local instance primeFactForConcreteFiniteArithmetic
    (l : PrimeGeFive) : Fact (Nat.Prime l.value) := l.factPrime

local instance fivePrimeFactConcreteFiniteArithmetic : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

theorem concreteLabel_odd (l : PrimeGeFive) : Odd l.value :=
  l.odd

theorem concreteLabel_star_positive (l : PrimeGeFive) : 0 < lStar l.value := by
  obtain ⟨k, hk⟩ := l.odd
  have hge : 5 ≤ 2 * k + 1 := by
    rw [← hk]
    exact l.ge_five
  have hkpos : 0 < k := by omega
  simpa [lStar, hk] using hkpos

theorem concreteLabel_star_ne_zero (l : PrimeGeFive) : lStar l.value ≠ 0 := by
  exact ne_of_gt (concreteLabel_star_positive l)

theorem concreteLabel_two_star_add_one (l : PrimeGeFive) :
    2 * lStar l.value + 1 = l.value :=
  two_mul_lStar_add_one l.value l.odd

theorem concreteLabel_star_lt (l : PrimeGeFive) : lStar l.value < l.value := by
  have h := concreteLabel_two_star_add_one l
  omega

theorem concreteLabel_card_Fl (l : PrimeGeFive) :
    Fintype.card (Fl l.value) = l.value := by
  letI := l.factPrime
  exact card_Fl l.value

theorem concreteLabel_card_nonzero_Fl (l : PrimeGeFive) :
    Fintype.card {x : Fl l.value // x ≠ 0} = 2 * lStar l.value := by
  letI := l.factPrime
  exact card_compl_zero l.value l.odd

theorem concreteLabel_card_cusp (l : PrimeGeFive) :
    Nat.card (LabCusp l.value) = lStar l.value := by
  letI := l.factPrime
  exact card_LabCusp l.value l.ge_five

theorem concreteLabel_two_ne_zero (l : PrimeGeFive) :
    (2 : Fl l.value) ≠ 0 := by
  letI := l.factPrime
  exact two_ne_zero_Fl l.value l.ge_five

theorem concreteLabel_neg_eq_self_iff (l : PrimeGeFive) (x : Fl l.value) :
    -x = x ↔ x = 0 := by
  letI := l.factPrime
  exact neg_eq_self_iff l.value l.ge_five x

theorem concreteLabel_signed_label_neg_involutive
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    SignedLabel.neg (SignedLabel.neg j) = j :=
  SignedLabel.neg_involutive j

theorem concreteLabel_signed_label_neg_value
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (SignedLabel.neg j).1 = -j.1 :=
  rfl

theorem concreteLabel_signed_label_theta_neg
    (l : PrimeGeFive) (q : Real) (j : SignedLabel l.value) :
    realThetaValue q (SignedLabel.neg j).1 = realThetaValue q j.1 := by
  exact SignedLabel.theta_neg q j

theorem concreteLabel_gaussExponent_neg (l : PrimeGeFive) (j : SignedLabel l.value) :
    gaussExponent (SignedLabel.neg j).1 = gaussExponent j.1 := by
  simp

theorem concreteLabel_gaussExponent_nonneg
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    0 ≤ gaussExponent j.1 := by
  exact gaussExponent_nonneg j.1

theorem concreteLabel_gaussExponent_toNat_nonneg
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    0 ≤ (gaussExponent j.1).toNat := by
  exact Nat.zero_le _

theorem concreteLabel_gaussExponent_zero :
    gaussExponent (0 : Int) = 0 :=
  gaussExponent_zero

theorem concreteLabel_gaussExponent_succ_sub (j : Int) :
    gaussExponent (j + 1) - gaussExponent j = 2 * j + 1 :=
  gaussExponent_succ_sub j

theorem concreteLabel_gaussian_square_sum_formula (l : PrimeGeFive) :
    gaussianSquareSum (lStar l.value) =
      (lStar l.value : Real) * (lStar l.value + 1) *
        (2 * lStar l.value + 1) / 6 := by
  exact gaussianSquareSum_formula (lStar l.value)

theorem concreteLabel_normalized_gaussian_degree (l : PrimeGeFive) :
    normalizedGaussianDegree l.value =
      (l.value : Real) * (l.value + 1) / 12 := by
  exact normalizedGaussianDegree_eq_factor l.value l.odd l.ge_five

theorem concreteLabel_normalized_gaussian_degree_pos (l : PrimeGeFive) :
    0 < normalizedGaussianDegree l.value := by
  rw [concreteLabel_normalized_gaussian_degree]
  have hl : (0 : Real) < l.value := by exact_mod_cast l.prime.pos
  have hl1 : (0 : Real) < l.value + 1 := by linarith
  positivity

theorem concreteLabel_gaussian_q_pos (_l : PrimeGeFive) :
    0 < gaussianFiveThetaQ :=
  gaussianFiveThetaQ_pos

theorem concreteLabel_gaussian_q_ne_zero (_l : PrimeGeFive) :
    gaussianFiveThetaQ ≠ 0 := by
  exact ne_of_gt (concreteLabel_gaussian_q_pos _l)

theorem concreteLabel_gaussian_q_log_local_degree (_l : PrimeGeFive) :
    Real.log gaussianFiveThetaQ =
      Multiplicative.toAdd
        (localUnitNormDegreeFor 5 (localQParameterFor 5)) :=
  gaussianFiveThetaQ_log_eq_local_degree

theorem concreteLabel_gaussian_q_exp_local_degree (_l : PrimeGeFive) :
    gaussianFiveThetaQ =
      Real.exp (Multiplicative.toAdd
        (localUnitNormDegreeFor 5 (localQParameterFor 5))) :=
  gaussianFiveThetaQ_eq_exp_local_degree

theorem concreteLabel_theta_value_pos
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    0 < realThetaValue gaussianFiveThetaQ j.1 := by
  exact realThetaValue_pos (concreteLabel_gaussian_q_pos l) j.1

theorem concreteLabel_theta_value_neg
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    realThetaValue gaussianFiveThetaQ (SignedLabel.neg j).1 =
      realThetaValue gaussianFiveThetaQ j.1 := by
  exact concreteLabel_signed_label_theta_neg l gaussianFiveThetaQ j

theorem concreteLabel_theta_value_zero (_l : PrimeGeFive) :
    realThetaValue gaussianFiveThetaQ 0 = 1 := by
  exact realThetaValue_zero _

theorem concreteLabel_theta_value_log
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    Real.log (realThetaValue gaussianFiveThetaQ j.1) =
      (gaussExponent j.1).toNat * Real.log gaussianFiveThetaQ := by
  exact log_realThetaValue j.1

theorem concreteLabel_theta_value_log_local_degree
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    Real.log (realThetaValue gaussianFiveThetaQ j.1) =
      (gaussExponent j.1).toNat *
        Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  rw [concreteLabel_theta_value_log,
    concreteLabel_gaussian_q_log_local_degree l]

theorem concreteLabel_packet_q (l : PrimeGeFive) :
    (concreteInitialThetaHodgeTheater l).thetaPacket.q = gaussianFiveThetaQ := by
  exact concreteInitialThetaHodgeTheater_q l

theorem concreteLabel_packet_q_pos (l : PrimeGeFive) :
    0 < (concreteInitialThetaHodgeTheater l).thetaPacket.q := by
  exact concreteInitialThetaHodgeTheater_q_pos l

theorem concreteLabel_packet_scale_eq
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaHodgeTheater l).thetaPacket.scale j =
      realThetaValue gaussianFiveThetaQ j.1 := by
  rw [(concreteInitialThetaHodgeTheater l).thetaPacket.scale_eq,
    concreteLabel_packet_q]

theorem concreteLabel_packet_scale_pos
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    0 < (concreteInitialThetaHodgeTheater l).thetaPacket.scale j := by
  exact concreteInitialThetaHodgeTheater_scale_pos l j

theorem concreteLabel_packet_scale_neg
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaHodgeTheater l).thetaPacket.scale (SignedLabel.neg j) =
      (concreteInitialThetaHodgeTheater l).thetaPacket.scale j := by
  exact concreteInitialThetaHodgeTheater_scale_neg l j

theorem concreteLabel_packet_log_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    Real.log ((concreteInitialThetaHodgeTheater l).thetaPacket.scale j) =
      (gaussExponent j.1).toNat * Real.log gaussianFiveThetaQ := by
  exact concreteInitialThetaHodgeTheater_log_scale l j

theorem concreteLabel_packet_log_scale_local_degree
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    Real.log ((concreteInitialThetaHodgeTheater l).thetaPacket.scale j) =
      (gaussExponent j.1).toNat *
        Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  exact concreteInitialThetaHodgeTheater_log_scale_local_degree l j

theorem concreteLabel_packet_log_volume_eq_sum
    (l : PrimeGeFive) :
    (concreteInitialThetaHodgeTheater l).thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        Real.log ((concreteInitialThetaHodgeTheater l).thetaPacket.scale j) := by
  exact concreteInitialThetaHodgeTheater_log_volume_eq_sum l

theorem concreteLabel_packet_log_volume_local_degree
    (l : PrimeGeFive) :
    (concreteInitialThetaHodgeTheater l).thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat *
          Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  exact concreteInitialThetaHodgeTheater_log_volume l

theorem concreteLabel_packet_log_volume_neg_invariant
    (l : PrimeGeFive) :
    (∑ j : SignedLabel l.value,
      Real.log ((concreteInitialThetaHodgeTheater l).thetaPacket.scale
        (SignedLabel.neg j))) =
      (concreteInitialThetaHodgeTheater l).thetaPacket.logVolume := by
  exact concreteInitialThetaHodgeTheater_log_volume_neg_invariant l

theorem concreteLabel_packet_scale_product_positive
    (l : PrimeGeFive) :
    0 < ∏ j : SignedLabel l.value,
      (concreteInitialThetaHodgeTheater l).thetaPacket.scale j := by
  classical
  apply Finset.prod_pos
  intro j hj
  exact concreteInitialThetaHodgeTheater_scale_pos l j

theorem concreteLabel_packet_scale_product_ne_zero
    (l : PrimeGeFive) :
    (∏ j : SignedLabel l.value,
      (concreteInitialThetaHodgeTheater l).thetaPacket.scale j) ≠ 0 := by
  exact ne_of_gt (concreteLabel_packet_scale_product_positive l)

theorem concreteLabel_packet_scale_product_neg_invariant
    (l : PrimeGeFive) :
    (∏ j : SignedLabel l.value,
      (concreteInitialThetaHodgeTheater l).thetaPacket.scale (SignedLabel.neg j)) =
      ∏ j : SignedLabel l.value,
        (concreteInitialThetaHodgeTheater l).thetaPacket.scale j := by
  classical
  let e : SignedLabel l.value ≃ SignedLabel l.value :=
    { toFun := SignedLabel.neg
      invFun := SignedLabel.neg
      left_inv := SignedLabel.neg_involutive
      right_inv := SignedLabel.neg_involutive }
  simpa [e] using
    (e.prod_comp (fun j : SignedLabel l.value =>
      (concreteInitialThetaHodgeTheater l).thetaPacket.scale j))

theorem concreteLabel_packet_scale_product_log
    (l : PrimeGeFive) :
    Real.log (∏ j : SignedLabel l.value,
      (concreteInitialThetaHodgeTheater l).thetaPacket.scale j) =
      (concreteInitialThetaHodgeTheater l).thetaPacket.logVolume := by
  rw [Real.log_prod]
  · exact concreteInitialThetaHodgeTheater_log_volume_eq_sum l
  · intro j hj
    exact concreteInitialThetaHodgeTheater_scale_ne_zero l j

theorem concreteLabel_packet_scale_product_log_local_degree
    (l : PrimeGeFive) :
    Real.log (∏ j : SignedLabel l.value,
      (concreteInitialThetaHodgeTheater l).thetaPacket.scale j) =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat *
          Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  rw [concreteLabel_packet_scale_product_log l]
  exact concreteLabel_packet_log_volume_local_degree l

theorem concreteLabel_packet_log_volume_zero_if_q_one
    (l : PrimeGeFive) (hq : gaussianFiveThetaQ = 1) :
    (concreteInitialThetaHodgeTheater l).thetaPacket.logVolume = 0 := by
  rw [concreteInitialThetaHodgeTheater_log_volume_eq_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [concreteInitialThetaHodgeTheater_log_scale,
    hq, Real.log_one, mul_zero]

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteInitialThetaFiniteArithmetic : Obligation :=
  { id := "IUT-I-II.concrete-initial-theta-finite-arithmetic"
    source := "IUT II theta labels and finite volume normalization"
    status := VerificationStatus.testCarrier
    note :=
      "The exact prime-at-least-five label, sign quotient, Gaussian square " ++
        "exponents, positive theta scales, local-degree log formula, finite " ++
        "log-volume, product, and sign invariance are specialized to the " ++
        "concrete carrier and proved from the lower arithmetic kernel. No " ++
        "etale theta or Hodge-Arakelov interpretation is inferred."
    dependsOn := [ "IUT-I.concrete-initial-theta-links",
      "IUT-III.arithmetic-gaussian-square-sum-normalization" ] }

end LeanFormal.IUT.Audit
