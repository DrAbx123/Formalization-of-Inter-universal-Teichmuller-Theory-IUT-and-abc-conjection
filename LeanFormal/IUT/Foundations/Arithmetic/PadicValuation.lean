import LeanFormal.IUT.Audit.Status
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
  Standard natural-number p-adic valuation facts.

  The statements are thin, named wrappers around Mathlib's `padicValNat`
  API.  Keeping them in the foundation layer makes the valuation conventions
  explicit before any local-field or Frobenioid object is introduced.
-/

namespace LeanFormal.IUT

theorem padicValNat_prime_self {p : Nat} [Fact p.Prime] :
    padicValNat p p = 1 := by
  exact padicValNat_self

theorem padicValNat_mul_of_nonzero {p a b : Nat} [Fact p.Prime]
    (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (a * b) = padicValNat p a + padicValNat p b := by
  exact padicValNat.mul ha hb

theorem padicValNat_pow_nat {p a k : Nat} [Fact p.Prime] :
    padicValNat p (a ^ k) = k * padicValNat p a := by
  exact padicValNat.pow a k

theorem prime_dvd_iff_padicValNat_ne_zero {p n : Nat} [Fact p.Prime]
    (hn : n ≠ 0) :
    p ∣ n ↔ padicValNat p n ≠ 0 := by
  exact dvd_iff_padicValNat_ne_zero hn

theorem prime_pow_dvd_iff_padicValNat_le {p n k : Nat} [Fact p.Prime]
    (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ padicValNat p n := by
  exact padicValNat_dvd_iff_le hn

theorem padicValNat_prime_pow {p k : Nat} [Fact p.Prime] :
    padicValNat p (p ^ k) = k := by
  exact padicValNat.prime_pow k

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def padicValuationArithmetic : Obligation :=
  { id := "Foundations.Arithmetic.padic-valuation"
    source := "Standard natural-number p-adic valuation and divisibility"
    status := VerificationStatus.proved
    note :=
      "Prime self-value, multiplicativity, power law, prime support, and " ++
        "the power-divisibility characterization are proved by Mathlib's " ++
        "padicValNat API. No local field, Frobenioid, or ABC estimate is " ++
        "assumed."
    dependsOn := [] }

end LeanFormal.IUT.Audit
