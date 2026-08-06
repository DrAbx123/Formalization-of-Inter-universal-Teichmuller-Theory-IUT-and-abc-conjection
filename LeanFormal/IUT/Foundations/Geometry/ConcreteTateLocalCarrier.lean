/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Foundations.Geometry.ConcreteTateParameter
import LeanFormal.IUT.Foundations.Geometry.ConcreteTateKummerPacket
import LeanFormal.IUT.Foundations.Geometry.ConcreteTateFiniteLevel
import LeanFormal.IUT.Foundations.Geometry.ConcreteTateDeckQuotient

/-!
  The final module of the concrete Tate prerequisite batch.

  This is a carrier assembly point only.  Its two components are the
  separately proved local q-series and Kummer packets.  The structure is
  intentionally not a `CurveIndexedTateUniformization`: stable reduction,
  point uniformization, and Galois equivariance remain outside this batch.
-/

namespace LeanFormal.IUT

noncomputable section

structure ConcreteTateLocalCarrier (l : PrimeGeFive)
    [Fact (Nat.Prime l.value)] where
  parameter : ConcreteTateParameter l
  kummer : ConcreteTateKummerPacket l
  q_is_prime : parameter.q = (l.value : ℚ_[l.value])
  q_is_contracting : ‖parameter.q‖ < 1
  q_is_nontrivial : parameter.q ≠ 1
  local_parameter_is_nontrivial :
    kummer.localParameter ≠ 1
  finite_kernel_is_exact :
    kummer.finiteReduction.ker =
      AddSubgroup.zmultiples (l.value : ℤ)

namespace ConcreteTateLocalCarrier

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

noncomputable def canonical : ConcreteTateLocalCarrier l where
  parameter := ConcreteTateParameter.canonical l
  kummer := ConcreteTateKummerPacket.canonical l
  q_is_prime := ConcreteTateParameter.canonical_q l
  q_is_contracting := (ConcreteTateParameter.canonical l).q_norm_lt_one
  q_is_nontrivial := ConcreteTateParameter.canonical_q_ne_one l
  local_parameter_is_nontrivial :=
    (ConcreteTateKummerPacket.canonical l).localParameter_nontrivial
  finite_kernel_is_exact :=
    (ConcreteTateKummerPacket.canonical l).finiteReduction_kernel

theorem canonical_integer_root_one :
    (canonical l).kummer.integerRoot 1 = Additive.ofMul
      (LocalIntegralMonoid.qParameterGroupification l.value) := by
  exact ConcreteTateKummerPacket.canonical_integerRoot_one l

theorem canonical_zero_label_has_lift (n : ℤ)
    (h : (canonical l).kummer.finiteReduction n = 0) :
    ∃ k : ℤ,
      (canonical l).kummer.integerRoot n = (l.value : ℤ) •
        (canonical l).kummer.integerRoot k := by
  exact ConcreteTateKummerPacket.canonical_zero_label_has_lift l n h

theorem canonical_q_eq_prime :
    (canonical l).parameter.q = (l.value : ℚ_[l.value]) :=
  (canonical l).q_is_prime

theorem canonical_q_contracting :
    ‖(canonical l).parameter.q‖ < 1 :=
  (canonical l).q_is_contracting

theorem canonical_q_nontrivial :
    (canonical l).parameter.q ≠ 1 :=
  (canonical l).q_is_nontrivial

theorem canonical_qUnit_eq_local_parameter :
    (canonical l).parameter.qUnit = localQParameterFor l.value := by
  exact ConcreteTateParameter.canonical_qUnit_eq_localParameter l

theorem canonical_groupification_maps_to_q :
    LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits l.value
        (LocalIntegralMonoid.qParameterGroupification l.value) =
      localQParameterFor l.value := by
  exact (canonical l).kummer.groupificationMapsToQ

theorem canonical_integer_root_zero :
    (canonical l).kummer.integerRoot 0 = 0 := by
  exact ConcreteTateKummerPacket.integerRoot_zero l
    (canonical l).kummer

theorem canonical_integer_root_add (m n : ℤ) :
    (canonical l).kummer.integerRoot (m + n) =
      (canonical l).kummer.integerRoot m +
        (canonical l).kummer.integerRoot n := by
  exact ConcreteTateKummerPacket.integerRoot_add l
    (canonical l).kummer m n

theorem canonical_integer_root_neg (n : ℤ) :
    (canonical l).kummer.integerRoot (-n) =
      -(canonical l).kummer.integerRoot n := by
  exact ConcreteTateKummerPacket.integerRoot_neg l
    (canonical l).kummer n

theorem canonical_finite_level_equiv_mk (n : ℤ) :
    ConcreteTateKummerPacket.finiteLevelQuotientEquiv
        (canonical l).kummer
        (QuotientAddGroup.mk n) =
      (canonical l).kummer.finiteReduction n := by
  exact ConcreteTateKummerPacket.finiteLevelQuotientEquiv_apply_mk
    (canonical l).kummer n

theorem canonical_finite_level_zero_iff (n : ℤ) :
    (QuotientAddGroup.mk n :
      ℤ ⧸ (canonical l).kummer.finiteReduction.ker) = 0 ↔
      n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  exact ConcreteTateKummerPacket.finiteLevel_quotient_mk_zero_iff
    (canonical l).kummer n

theorem canonical_deck_qUnit_class_fixed
    (sigma : ConcreteTateParameter.LocalAbsoluteGalois l) :
    ConcreteTateParameter.qDeckQuotientEquiv
        (canonical l).parameter sigma
        (QuotientGroup.mk (canonical l).parameter.qUnit) =
      QuotientGroup.mk (canonical l).parameter.qUnit := by
  exact ConcreteTateParameter.qDeckQuotientEquiv_qUnit_class
    (canonical l).parameter sigma

end ConcreteTateLocalCarrier

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteTateLocalCarrier : Obligation :=
  { id := "Foundations.Geometry.concrete-tate-local-carrier"
    source := "IUT I-II local q/Kummer prerequisite carrier"
    status := VerificationStatus.proved
    note :=
      "A single concrete carrier combines the independently proved q-series " ++
        "parameter and Kummer/finite-kernel packets. Its projections prove " ++
        "the q identity, contraction, nontriviality, exact finite kernel, and " ++
        "integer-root lift. It is explicitly not the paper's stable-reduction " ++
        "or Tate-uniformization theorem."
    dependsOn :=
      [ "Foundations.Geometry.concrete-tate-parameter",
        "Foundations.Geometry.concrete-tate-kummer-packet" ] }

end LeanFormal.IUT.Audit
