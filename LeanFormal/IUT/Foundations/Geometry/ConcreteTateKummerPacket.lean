/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Foundations.Geometry.ConcreteTateParameter
import LeanFormal.IUT.IUTII.Frobenioid.ConcreteLocalKummerExample
import LeanFormal.IUT.IUTII.Kummer.ConcreteEtaleKummerBridge

/-!
  The second module of the concrete Tate prerequisite batch.

  This module connects the actual q=p local integral monoid to its coherent
  rational-root system and to the exact finite Z/lZ quotient.  It remains
  algebraic: no etale fundamental group or curve-point interpretation is
  inferred from the packet.
-/

namespace LeanFormal.IUT

noncomputable section

structure ConcreteTateKummerPacket (l : PrimeGeFive)
    [Fact (Nat.Prime l.value)] where
  localParameter : LocalIntegralMonoid l.value
  localParameter_nontrivial : localParameter ≠ 1
  groupificationMapsToQ :
    LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits l.value
        (LocalIntegralMonoid.qParameterGroupification l.value) =
      localQParameterFor l.value
  compatibleRoots :
    CompatibleRootSystem
      (Algebra.GrothendieckGroup (LocalIntegralMonoid l.value))
      (LocalIntegralMonoid.qParameterGroupification l.value)
  integerRoot : ℤ → Additive
    (Algebra.GrothendieckGroup (LocalIntegralMonoid l.value))
  integerRoot_eq_zsmul : ∀ n : ℤ,
    integerRoot n = n • Additive.ofMul
      (LocalIntegralMonoid.qParameterGroupification l.value)
  integerRoot_eq_compatible : ∀ n : ℤ,
    integerRoot n = compatibleRoots.roots (n : ℚ)
  finiteReduction : ℤ →+ ZMod l.value
  finiteReduction_surjective : Function.Surjective finiteReduction
  finiteReduction_kernel :
    finiteReduction.ker = AddSubgroup.zmultiples (l.value : ℤ)

namespace ConcreteTateKummerPacket

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

noncomputable def canonical : ConcreteTateKummerPacket l where
  localParameter := LocalIntegralMonoid.qParameter l.value
  localParameter_nontrivial := LocalIntegralMonoid.qParameter_ne_one l.value
  groupificationMapsToQ :=
    LocalIntegralMonoid.qParameterGroupification_maps_to_q l.value
  compatibleRoots := LocalIntegralMonoid.qParameterCompatibleRoots l.value
  integerRoot := LocalIntegralMonoid.qIntegerRoot l.value
  integerRoot_eq_zsmul := fun n =>
    LocalIntegralMonoid.qIntegerRoot_eq_zsmul l.value n
  integerRoot_eq_compatible := by
    intro n
    rfl
  finiteReduction := integralTateReduction l
  finiteReduction_surjective := integralTateReduction_surjective l
  finiteReduction_kernel := integralTateReduction_kernel l

theorem canonical_integerRoot_one :
    (canonical l).integerRoot 1 = Additive.ofMul
      (LocalIntegralMonoid.qParameterGroupification l.value) := by
  rw [(canonical l).integerRoot_eq_zsmul]
  simp

theorem canonical_zero_label_has_lift (n : ℤ)
    (h : (canonical l).finiteReduction n = 0) :
    ∃ k : ℤ,
      (canonical l).integerRoot n = (l.value : ℤ) •
        (canonical l).integerRoot k := by
  obtain ⟨k, hk⟩ :=
    LocalIntegralMonoid.qIntegerRoot_of_etale_kernel l n (by
      simpa [canonical] using h)
  refine ⟨k, ?_⟩
  simpa [canonical] using hk

theorem canonical_zero_label_iff (n : ℤ) :
    (canonical l).finiteReduction n = 0 ↔
      n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  constructor
  · intro h
    have hm : n ∈ (canonical l).finiteReduction.ker := h
    rw [(canonical l).finiteReduction_kernel] at hm
    exact hm
  · intro h
    have hm : n ∈ (canonical l).finiteReduction.ker := by
      rw [(canonical l).finiteReduction_kernel]
      exact h
    exact hm

theorem integerRoot_zero
    (P : ConcreteTateKummerPacket l) : P.integerRoot 0 = 0 := by
  rw [P.integerRoot_eq_zsmul]
  simp

theorem integerRoot_add
    (P : ConcreteTateKummerPacket l) (m n : ℤ) :
    P.integerRoot (m + n) = P.integerRoot m + P.integerRoot n := by
  rw [P.integerRoot_eq_zsmul, P.integerRoot_eq_zsmul,
    P.integerRoot_eq_zsmul]
  simp [add_zsmul]

theorem integerRoot_sub
    (P : ConcreteTateKummerPacket l) (m n : ℤ) :
    P.integerRoot (m - n) = P.integerRoot m - P.integerRoot n := by
  rw [P.integerRoot_eq_zsmul, P.integerRoot_eq_zsmul,
    P.integerRoot_eq_zsmul]
  simp [sub_eq_add_neg, add_zsmul]

theorem integerRoot_neg
    (P : ConcreteTateKummerPacket l) (n : ℤ) :
    P.integerRoot (-n) = -P.integerRoot n := by
  rw [P.integerRoot_eq_zsmul, P.integerRoot_eq_zsmul]
  simp

theorem integerRoot_mul
    (P : ConcreteTateKummerPacket l) (m n : ℤ) :
    P.integerRoot (m * n) = m • P.integerRoot n := by
  rw [P.integerRoot_eq_zsmul, P.integerRoot_eq_zsmul]
  simp [mul_zsmul]

theorem integerRoot_one
    (P : ConcreteTateKummerPacket l) :
    P.integerRoot 1 = Additive.ofMul
      (LocalIntegralMonoid.qParameterGroupification l.value) := by
  rw [P.integerRoot_eq_zsmul]
  simp

theorem compatibleRoot_zero
    (P : ConcreteTateKummerPacket l) :
    P.compatibleRoots.roots 0 = 0 :=
  map_zero P.compatibleRoots.roots

theorem compatibleRoot_add
    (P : ConcreteTateKummerPacket l) (a b : ℚ) :
    P.compatibleRoots.roots (a + b) =
      P.compatibleRoots.roots a + P.compatibleRoots.roots b :=
  map_add P.compatibleRoots.roots a b

theorem compatibleRoot_neg
    (P : ConcreteTateKummerPacket l) (a : ℚ) :
    P.compatibleRoots.roots (-a) = -P.compatibleRoots.roots a :=
  map_neg P.compatibleRoots.roots a

theorem compatibleRoot_sub
    (P : ConcreteTateKummerPacket l) (a b : ℚ) :
    P.compatibleRoots.roots (a - b) =
      P.compatibleRoots.roots a - P.compatibleRoots.roots b :=
  map_sub P.compatibleRoots.roots a b

theorem compatibleRoot_zsmul
    (P : ConcreteTateKummerPacket l) (a : ℤ) (b : ℚ) :
    P.compatibleRoots.roots (a • b) =
      a • P.compatibleRoots.roots b := by
  exact P.compatibleRoots.roots.map_zsmul a b

theorem integerRoot_eq_compatible_roots
    (P : ConcreteTateKummerPacket l) (n : ℤ) :
    P.integerRoot n = P.compatibleRoots.roots (n : ℚ) :=
  P.integerRoot_eq_compatible n

theorem integerRoot_add_via_roots
    (P : ConcreteTateKummerPacket l) (m n : ℤ) :
    P.integerRoot (m + n) = P.compatibleRoots.roots ((m + n : ℤ) : ℚ) := by
  exact P.integerRoot_eq_compatible (m + n)

theorem integerRoot_one_via_root_one
    (P : ConcreteTateKummerPacket l) :
    P.integerRoot 1 = P.compatibleRoots.roots 1 := by
  exact P.integerRoot_eq_compatible 1

theorem finiteReduction_zero
    (P : ConcreteTateKummerPacket l) : P.finiteReduction 0 = 0 :=
  map_zero P.finiteReduction

theorem finiteReduction_add
    (P : ConcreteTateKummerPacket l) (m n : ℤ) :
    P.finiteReduction (m + n) =
      P.finiteReduction m + P.finiteReduction n :=
  map_add P.finiteReduction m n

theorem finiteReduction_sub
    (P : ConcreteTateKummerPacket l) (m n : ℤ) :
    P.finiteReduction (m - n) =
      P.finiteReduction m - P.finiteReduction n := by
  exact map_sub P.finiteReduction m n

theorem finiteReduction_neg
    (P : ConcreteTateKummerPacket l) (n : ℤ) :
    P.finiteReduction (-n) = -P.finiteReduction n := by
  exact map_neg P.finiteReduction n

theorem finiteReduction_zsmul
    (P : ConcreteTateKummerPacket l) (a n : ℤ) :
    P.finiteReduction (a • n) = a • P.finiteReduction n := by
  exact map_zsmul P.finiteReduction a n

theorem finiteReduction_eq_iff_sub_mem_kernel
    (P : ConcreteTateKummerPacket l) (m n : ℤ) :
    P.finiteReduction m = P.finiteReduction n ↔
      m - n ∈ P.finiteReduction.ker := by
  constructor
  · intro h
    have hz : P.finiteReduction (m - n) = 0 := by
      rw [P.finiteReduction_sub, h, sub_self]
    exact hz
  · intro h
    have hz : P.finiteReduction (m - n) = 0 := h
    rw [P.finiteReduction_sub] at hz
    exact sub_eq_zero.mp hz

theorem finiteReduction_eq_iff_multiple
    (P : ConcreteTateKummerPacket l) (m n : ℤ) :
    P.finiteReduction m = P.finiteReduction n ↔
      m - n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  rw [finiteReduction_eq_iff_sub_mem_kernel l P m n,
    P.finiteReduction_kernel]

theorem finiteReduction_zero_iff_multiple
    (P : ConcreteTateKummerPacket l) (n : ℤ) :
    P.finiteReduction n = 0 ↔
      n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  simpa using finiteReduction_eq_iff_multiple l P n 0

theorem integerRoot_zero_label_multiple
    (P : ConcreteTateKummerPacket l) (n : ℤ)
    (h : P.finiteReduction n = 0) :
    ∃ k : ℤ, P.integerRoot n = (l.value : ℤ) • P.integerRoot k := by
  have hm : n ∈ P.finiteReduction.ker := h
  rw [P.finiteReduction_kernel] at hm
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  refine ⟨k, ?_⟩
  rw [P.integerRoot_eq_zsmul, P.integerRoot_eq_zsmul, ← hk]
  rw [zsmul_eq_mul, smul_smul]
  congr 1
  exact mul_comm _ _

theorem finiteReduction_surjective_exists
    (P : ConcreteTateKummerPacket l) (z : ZMod l.value) :
    ∃ n : ℤ, P.finiteReduction n = z :=
  P.finiteReduction_surjective z

end ConcreteTateKummerPacket

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteTateKummerPacket : Obligation :=
  { id := "Foundations.Geometry.concrete-tate-kummer-packet"
    source := "IUT II, local Kummer system and finite etale Tate direction"
    status := VerificationStatus.proved
    note :=
      "The actual q=p integral carrier, its nontriviality, groupification " ++
        "map, compatible rational roots, integer exponent law, surjective " ++
        "Z/lZ reduction, and exact kernel are assembled in one dependent " ++
        "packet. The zero-label lift is proved from the concrete Kummer bridge. " ++
        "No geometric etale or curve-point claim is added."
    dependsOn :=
      [ "IUT-II.concrete-local-q-parameter-roots",
        "IUT-II.concrete-integer-kummer-direction",
        "IUT-II.concrete-etale-kummer-bridge",
        "IUT-II.etale-finite-tate-direction" ] }

end LeanFormal.IUT.Audit
