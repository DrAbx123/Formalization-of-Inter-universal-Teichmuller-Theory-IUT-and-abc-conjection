import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.Arithmetic.Radical
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
  The standard primitive additive triple layer beneath ABC.

  This is ordinary natural-number arithmetic: positivity, `a + b = c`, and
  coprimality.  The global epsilon estimate is intentionally absent.
-/

namespace LeanFormal.IUT

def PrimitiveAdditiveTriple (a b c : Nat) : Prop :=
  0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b

theorem PrimitiveAdditiveTriple.c_pos {a b c : Nat}
    (h : PrimitiveAdditiveTriple a b c) : 0 < c := by
  rcases h with ⟨ha, hb, hsum, _⟩
  omega

theorem PrimitiveAdditiveTriple.coprime_left_right {a b c : Nat}
    (h : PrimitiveAdditiveTriple a b c) : Nat.Coprime a c := by
  rcases h with ⟨_ha, _hb, hsum, hab⟩
  simpa [hsum] using (Nat.coprime_self_add_right.mpr hab)

theorem PrimitiveAdditiveTriple.coprime_right_left {a b c : Nat}
    (h : PrimitiveAdditiveTriple a b c) : Nat.Coprime b c := by
  rcases h with ⟨_ha, _hb, hsum, hab⟩
  simpa [hsum] using (Nat.coprime_add_self_left.mpr hab).symm

theorem PrimitiveAdditiveTriple.radical_product_eq {a b c : Nat}
    (h : PrimitiveAdditiveTriple a b c) :
    natRadical (a * b * c) = natRadical a * natRadical b * natRadical c := by
  exact natRadical_mul_three_of_pairwise_coprime
    h.2.2.2 h.coprime_left_right h.coprime_right_left

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def primitiveAdditiveArithmetic : Obligation :=
  { id := "Foundations.Arithmetic.primitive-additive"
    source := "Standard primitive ABC triple arithmetic"
    status := VerificationStatus.proved
    note :=
      "Positivity of c, pairwise coprimality, and radical factorization for " ++
        "primitive additive triples are proved. The ABC epsilon bound is not " ++
        "claimed."
    dependsOn := [ "Foundations.Arithmetic.radical" ] }

end LeanFormal.IUT.Audit
