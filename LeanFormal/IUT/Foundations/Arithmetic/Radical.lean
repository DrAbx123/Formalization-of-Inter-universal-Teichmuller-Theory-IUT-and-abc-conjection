import LeanFormal.IUT.Audit.Status
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic

/-!
  Standard radical arithmetic used by the eventual ABC bridge.

  This module deliberately contains only the ordinary unique-factorization
  facts supplied by Mathlib.  It does not mention IUT data or assert the ABC
  conjecture.  The alias is shared by the ABC statement so that the project
  has one radical definition rather than parallel local notions.
-/

namespace LeanFormal.IUT

noncomputable abbrev natRadical (n : Nat) : Nat :=
  UniqueFactorizationMonoid.radical n

theorem natRadical_zero : natRadical 0 = 1 := by
  simp [natRadical]

theorem natRadical_pos (n : Nat) : 0 < natRadical n := by
  exact Nat.radical_pos n

theorem natRadical_dvd_self {n : Nat} : natRadical n ∣ n := by
  exact UniqueFactorizationMonoid.radical_dvd_self

theorem natRadical_eq_one_iff {n : Nat} : natRadical n = 1 ↔ n ≤ 1 := by
  exact Nat.radical_eq_one_iff

theorem natRadical_eq_prod_primeFactors (n : Nat) :
    natRadical n = ∏ p ∈ n.primeFactors, p := by
  exact Nat.radical_eq_prod_primeFactors

theorem natRadical_pow {n k : Nat} (hk : k ≠ 0) :
    natRadical (n ^ k) = natRadical n := by
  exact UniqueFactorizationMonoid.radical_pow n hk

theorem natRadical_dvd_radical_of_dvd {a b : Nat}
    (hab : a ∣ b) (hb : b ≠ 0) :
    natRadical a ∣ natRadical b := by
  exact UniqueFactorizationMonoid.radical_dvd_radical hab hb

theorem natRadical_mul_of_coprime {a b : Nat} (h : Nat.Coprime a b) :
    natRadical (a * b) = natRadical a * natRadical b := by
  have hr : IsRelPrime a b := Nat.coprime_iff_isRelPrime.mp h
  exact UniqueFactorizationMonoid.radical_mul hr

theorem natRadical_mul_three_of_pairwise_coprime
    {a b c : Nat} (hab : Nat.Coprime a b)
    (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    natRadical (a * b * c) = natRadical a * natRadical b * natRadical c := by
  have habr : IsRelPrime a b := Nat.coprime_iff_isRelPrime.mp hab
  have hacr : IsRelPrime a c := Nat.coprime_iff_isRelPrime.mp hac
  have hbcr : IsRelPrime b c := Nat.coprime_iff_isRelPrime.mp hbc
  have habc : IsRelPrime (a * b) c := hacr.mul_left hbcr
  change UniqueFactorizationMonoid.radical (a * b * c) =
    UniqueFactorizationMonoid.radical a *
      UniqueFactorizationMonoid.radical b *
        UniqueFactorizationMonoid.radical c
  rw [UniqueFactorizationMonoid.radical_mul habc,
    UniqueFactorizationMonoid.radical_mul habr]

theorem coprime_add_left {a b : Nat} (h : Nat.Coprime a b) :
    Nat.Coprime a (a + b) :=
  Nat.coprime_self_add_right.mpr h

theorem coprime_add_right {a b : Nat} (h : Nat.Coprime a b) :
    Nat.Coprime b (a + b) := by
  exact (Nat.coprime_add_self_left.mpr h).symm

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def radicalArithmetic : Obligation :=
  { id := "Foundations.Arithmetic.radical"
    source := "Standard unique-factorization arithmetic; ABC radical convention"
    status := VerificationStatus.proved
    note :=
      "Mathlib's natural-number radical, positivity, divisibility, the one " ++
        "case, coprime multiplication, pairwise-coprime triple factorization, " ++
        "and elementary additive coprimality are proved. No ABC estimate is " ++
        "included."
    dependsOn := [] }

end LeanFormal.IUT.Audit
