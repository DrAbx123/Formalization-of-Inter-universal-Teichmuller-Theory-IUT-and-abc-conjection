import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import LeanFormal.IUT.ABCBridge.Statement
import LeanFormal.IUT.Foundations.Arithmetic.Radical

/-!
  Elementary arithmetic beneath the ABC target.

  An ABC triple is primitive by definition (`Nat.Coprime a b`).  The
  equalities below record the standard consequence that all three pairs are
  coprime.  This is ordinary natural-number arithmetic, not an IUT object and
  not a replacement for the missing IUT-to-ABC bridge.
-/

namespace LeanFormal.IUT

def ABCPairwiseCoprime (a b c : Nat) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c

theorem IsABCTriple.coprime_left_right {a b c : Nat}
    (h : IsABCTriple a b c) : Nat.Coprime a c := by
  rcases h with ⟨_ha, _hb, hsum, hab⟩
  have hleft : Nat.Coprime a (a + b) :=
    Nat.coprime_self_add_right.mpr hab
  simpa [hsum] using hleft

theorem IsABCTriple.coprime_right_left {a b c : Nat}
    (h : IsABCTriple a b c) : Nat.Coprime b c := by
  rcases h with ⟨_ha, _hb, hsum, hab⟩
  have hright : Nat.Coprime (a + b) b :=
    Nat.coprime_add_self_left.mpr hab
  simpa [hsum] using hright.symm

theorem IsABCTriple.pairwise_coprime {a b c : Nat}
    (h : IsABCTriple a b c) : ABCPairwiseCoprime a b c := by
  exact ⟨h.2.2.2, h.coprime_left_right, h.coprime_right_left⟩

theorem IsABCTriple.radical_product_eq {a b c : Nat}
    (h : IsABCTriple a b c) :
    radical (a * b * c) = radical a * radical b * radical c := by
  have hab : IsRelPrime a b := Nat.coprime_iff_isRelPrime.mp h.2.2.2
  have hac : IsRelPrime a c :=
    Nat.coprime_iff_isRelPrime.mp h.coprime_left_right
  have hbc : IsRelPrime b c :=
    Nat.coprime_iff_isRelPrime.mp h.coprime_right_left
  have habc : IsRelPrime (a * b) c := hac.mul_left hbc
  exact natRadical_mul_three_of_pairwise_coprime
    h.2.2.2 h.coprime_left_right h.coprime_right_left


end LeanFormal.IUT
