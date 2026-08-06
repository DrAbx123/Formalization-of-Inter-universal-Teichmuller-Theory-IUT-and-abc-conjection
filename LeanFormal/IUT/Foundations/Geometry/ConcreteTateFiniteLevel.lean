/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Foundations.Geometry.ConcreteTateKummerPacket
import Mathlib.Data.ZMod.QuotientGroup

/-!
  The finite-level quotient of the concrete integer Tate direction.

  The quotient is formed from the actual kernel of the packet's reduction
  homomorphism, then identified with `ZMod l` by the first isomorphism
  theorem.  This is a genuine algebraic quotient statement; it is not an
  etale-cover or fundamental-group identification.
-/

namespace LeanFormal.IUT

noncomputable section

namespace ConcreteTateKummerPacket

variable {l : PrimeGeFive} [Fact (Nat.Prime l.value)]

noncomputable def finiteLevelQuotientEquiv
    (P : ConcreteTateKummerPacket l) :
    (ℤ ⧸ P.finiteReduction.ker) ≃+ ZMod l.value :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    P.finiteReduction P.finiteReduction_surjective

theorem finiteLevelQuotientEquiv_apply_mk
    (P : ConcreteTateKummerPacket l) (n : ℤ) :
    P.finiteLevelQuotientEquiv (QuotientAddGroup.mk n) =
      P.finiteReduction n := by
  change (QuotientAddGroup.kerLift P.finiteReduction) n =
    P.finiteReduction n
  exact QuotientAddGroup.kerLift_mk P.finiteReduction n

theorem finiteLevelQuotientEquiv_zero
    (P : ConcreteTateKummerPacket l) :
    P.finiteLevelQuotientEquiv (0 : ℤ ⧸ P.finiteReduction.ker) = 0 := by
  exact map_zero P.finiteLevelQuotientEquiv

theorem finiteLevelQuotientEquiv_add
    (P : ConcreteTateKummerPacket l)
    (x y : ℤ ⧸ P.finiteReduction.ker) :
    P.finiteLevelQuotientEquiv (x + y) =
      P.finiteLevelQuotientEquiv x + P.finiteLevelQuotientEquiv y :=
  map_add P.finiteLevelQuotientEquiv x y

theorem finiteLevelQuotientEquiv_neg
    (P : ConcreteTateKummerPacket l) (x : ℤ ⧸ P.finiteReduction.ker) :
    P.finiteLevelQuotientEquiv (-x) =
      -P.finiteLevelQuotientEquiv x :=
  map_neg P.finiteLevelQuotientEquiv x

theorem finiteLevelQuotientEquiv_zsmul
    (P : ConcreteTateKummerPacket l)
    (a : ℤ) (x : ℤ ⧸ P.finiteReduction.ker) :
    P.finiteLevelQuotientEquiv (a • x) =
      a • P.finiteLevelQuotientEquiv x := by
  exact map_zsmul P.finiteLevelQuotientEquiv a x

theorem finiteLevel_quotient_mk_add
    (P : ConcreteTateKummerPacket l) (m n : ℤ) :
    (QuotientAddGroup.mk (m + n) :
      ℤ ⧸ P.finiteReduction.ker) =
        QuotientAddGroup.mk m + QuotientAddGroup.mk n := by
  rfl

theorem finiteLevel_quotient_mk_neg
    (P : ConcreteTateKummerPacket l) (n : ℤ) :
    (QuotientAddGroup.mk (-n) :
      ℤ ⧸ P.finiteReduction.ker) =
        -(QuotientAddGroup.mk n) := by
  rfl

theorem finiteLevel_quotient_mk_zsmul
    (P : ConcreteTateKummerPacket l) (a n : ℤ) :
    (QuotientAddGroup.mk (a • n) :
      ℤ ⧸ P.finiteReduction.ker) =
        a • QuotientAddGroup.mk n := by
  rfl

theorem finiteLevel_quotient_mk_surjective
    (P : ConcreteTateKummerPacket l) :
    Function.Surjective
      (fun n : ℤ =>
        (QuotientAddGroup.mk n : ℤ ⧸ P.finiteReduction.ker)) := by
  exact QuotientAddGroup.mk_surjective

theorem finiteLevel_label_class_eq_iff
    (P : ConcreteTateKummerPacket l) (x : ℤ ⧸ P.finiteReduction.ker)
    (n : ℤ) :
    x = QuotientAddGroup.mk n ↔
      P.finiteLevelQuotientEquiv x = P.finiteReduction n := by
  constructor
  · intro h
    rw [h, P.finiteLevelQuotientEquiv_apply_mk]
  · intro h
    apply P.finiteLevelQuotientEquiv.injective
    simpa [P.finiteLevelQuotientEquiv_apply_mk] using h

theorem finiteLevelQuotientEquiv_surjective
    (P : ConcreteTateKummerPacket l) :
    Function.Surjective P.finiteLevelQuotientEquiv :=
  P.finiteLevelQuotientEquiv.surjective

theorem finiteLevelQuotientEquiv_injective
    (P : ConcreteTateKummerPacket l) :
    Function.Injective P.finiteLevelQuotientEquiv :=
  P.finiteLevelQuotientEquiv.injective

theorem finiteLevel_quotient_eq_iff
    (P : ConcreteTateKummerPacket l) (m n : ℤ) :
    (QuotientAddGroup.mk m : ℤ ⧸ P.finiteReduction.ker) =
        QuotientAddGroup.mk n ↔
      m - n ∈ P.finiteReduction.ker := by
  exact QuotientAddGroup.eq_iff_sub_mem

theorem finiteLevel_quotient_eq_iff_multiple
    (P : ConcreteTateKummerPacket l) (m n : ℤ) :
    (QuotientAddGroup.mk m : ℤ ⧸ P.finiteReduction.ker) =
        QuotientAddGroup.mk n ↔
      m - n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  rw [P.finiteLevel_quotient_eq_iff,
    P.finiteReduction_kernel]

theorem finiteLevel_quotient_mk_zero_iff
    (P : ConcreteTateKummerPacket l) (n : ℤ) :
    (QuotientAddGroup.mk n : ℤ ⧸ P.finiteReduction.ker) = 0 ↔
      n ∈ AddSubgroup.zmultiples (l.value : ℤ) := by
  simpa using P.finiteLevel_quotient_eq_iff_multiple n 0

theorem finiteLevel_quotient_mk_eq_of_label_eq
    (P : ConcreteTateKummerPacket l) (m n : ℤ)
    (h : P.finiteReduction m = P.finiteReduction n) :
    (QuotientAddGroup.mk m : ℤ ⧸ P.finiteReduction.ker) =
      QuotientAddGroup.mk n := by
  apply P.finiteLevelQuotientEquiv.injective
  simpa [P.finiteLevelQuotientEquiv_apply_mk] using h

theorem finiteLevel_quotient_mk_eq_iff_label_eq
    (P : ConcreteTateKummerPacket l) (m n : ℤ) :
    (QuotientAddGroup.mk m : ℤ ⧸ P.finiteReduction.ker) =
        QuotientAddGroup.mk n ↔
      P.finiteReduction m = P.finiteReduction n := by
  constructor
  · intro h
    simpa [P.finiteLevelQuotientEquiv_apply_mk] using
      congrArg P.finiteLevelQuotientEquiv h
  · exact P.finiteLevel_quotient_mk_eq_of_label_eq m n

theorem finiteLevel_quotient_mk_add_multiple
    (P : ConcreteTateKummerPacket l) (n k : ℤ) :
    (QuotientAddGroup.mk (n + (l.value : ℤ) * k) :
      ℤ ⧸ P.finiteReduction.ker) = QuotientAddGroup.mk n := by
  apply (P.finiteLevel_quotient_eq_iff_multiple _ _).mpr
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨k, ?_⟩
  ring

theorem finiteLevel_label_add_multiple
    (P : ConcreteTateKummerPacket l) (n k : ℤ) :
    P.finiteReduction (n + (l.value : ℤ) * k) =
      P.finiteReduction n := by
  apply (P.finiteLevel_quotient_mk_eq_iff_label_eq _ _).mp
  exact P.finiteLevel_quotient_mk_add_multiple n k

theorem finiteLevel_quotient_mk_sub_multiple
    (P : ConcreteTateKummerPacket l) (n k : ℤ) :
    (QuotientAddGroup.mk (n - (l.value : ℤ) * k) :
      ℤ ⧸ P.finiteReduction.ker) = QuotientAddGroup.mk n := by
  apply (P.finiteLevel_quotient_eq_iff_multiple _ _).mpr
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨-k, ?_⟩
  ring

theorem finiteLevel_label_sub_multiple
    (P : ConcreteTateKummerPacket l) (n k : ℤ) :
    P.finiteReduction (n - (l.value : ℤ) * k) =
      P.finiteReduction n := by
  apply (P.finiteLevel_quotient_mk_eq_iff_label_eq _ _).mp
  exact P.finiteLevel_quotient_mk_sub_multiple n k

end ConcreteTateKummerPacket

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteTateFiniteLevel : Obligation :=
  { id := "Foundations.Geometry.concrete-tate-finite-level"
    source := "IUT II finite Tate direction and Kummer quotient"
    status := VerificationStatus.proved
    note :=
      "The quotient of the actual integer direction by the actual finite " ++
        "reduction kernel is constructed as an additive equivalence with " ++
        "ZMod l. Representatives, equality, zero class, injectivity and " ++
        "surjectivity are proved. This is an algebraic quotient only, with no " ++
        "geometric etale interpretation."
    dependsOn := [ "Foundations.Geometry.concrete-tate-kummer-packet" ] }

end LeanFormal.IUT.Audit
