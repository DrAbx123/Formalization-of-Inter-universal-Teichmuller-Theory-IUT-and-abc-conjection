/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.CompatibleRoots
import Mathlib.GroupTheory.Divisible

/-!
  The natural-power root-system layer of IUT Kummer theory.

  This follows the source-oriented `RootSystem` construction: a compatible
  family of n-th roots is recorded in units, then built in an algebraically
  closed field by a factorial chain.  The source's Galois Kummer class and its
  cocycle are a later layer; this file only proves the root-system identities.
-/

namespace LeanFormal.IUT

structure NatRootSystem {M : Type*} [CommMonoid M] (value : Mˣ) where
  root : Nat → Mˣ
  root_one : root 1 = value
  compat : ∀ n k : Nat, k ≠ 0 → root (n * k) ^ k = root n

namespace NatRootSystem

variable {M : Type*} [CommMonoid M] {value : Mˣ}
variable (r : NatRootSystem value)

theorem pow_self (n : Nat) (hn : n ≠ 0) : r.root n ^ n = value := by
  have h := r.compat 1 n hn
  rwa [Nat.one_mul, r.root_one] at h

def pow (e : Nat) : NatRootSystem (value ^ e) where
  root n := r.root n ^ e
  root_one := by rw [r.root_one]
  compat n k hk := by
    rw [pow_right_comm, r.compat n k hk]

end NatRootSystem

namespace AlgebraicClosureRootSystem

variable {K : Type*} [Field K] [IsAlgClosed K]

theorem exists_pow_root (u : Kˣ) (n : Nat) (hn : n ≠ 0) :
    ∃ v : Kˣ, v ^ n = u := by
  obtain ⟨z, hz⟩ :=
    IsAlgClosed.exists_pow_nat_eq (u : K) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow hn] at hz
    exact (Units.ne_zero u) hz.symm
  refine ⟨Units.mk0 z hz0, ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz]

noncomputable def chainRoot (value : Kˣ) : Nat → Kˣ
  | 0 => value
  | k + 1 =>
      (exists_pow_root (chainRoot value k) (k + 1) (Nat.succ_ne_zero k)).choose

theorem chainRoot_spec (value : Kˣ) (k : Nat) :
    chainRoot value (k + 1) ^ (k + 1) = chainRoot value k :=
  (exists_pow_root (chainRoot value k) (k + 1) (Nat.succ_ne_zero k)).choose_spec

theorem chainRoot_telescope (value : Kˣ) {j i : Nat} (hji : j ≤ i) :
    chainRoot value i ^ (i.factorial / j.factorial) = chainRoot value j := by
  induction i, hji using Nat.le_induction with
  | base => rw [Nat.div_self j.factorial_pos, pow_one]
  | succ i hji ih =>
      have hdvd : j.factorial ∣ i.factorial := Nat.factorial_dvd_factorial hji
      have hexp : (i + 1).factorial / j.factorial =
          (i + 1) * (i.factorial / j.factorial) := by
        rw [Nat.factorial_succ, Nat.mul_div_assoc _ hdvd]
      rw [hexp, pow_mul, chainRoot_spec, ih]

noncomputable def rootSystemOfAlgClosed (value : Kˣ) :
    NatRootSystem value where
  root n := if n = 0 then 1 else chainRoot value n ^ (n.factorial / n)
  root_one := by
    rw [if_neg one_ne_zero, Nat.factorial_one, Nat.div_one, pow_one]
    have h := chainRoot_spec value 0
    rwa [pow_one] at h
  compat n k hk := by
    rcases eq_or_ne n 0 with rfl | hn
    · rw [Nat.zero_mul, if_pos rfl, one_pow]
    · have hnk : n * k ≠ 0 := Nat.mul_ne_zero hn hk
      rw [if_neg hnk, if_neg hn]
      have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      have hk0 : 0 < k := Nat.pos_of_ne_zero hk
      have hnk0 : 0 < n * k := Nat.mul_pos hn0 hk0
      have hle : n ≤ n * k := Nat.le_mul_of_pos_right n hk0
      have hd1 : n * k ∣ (n * k).factorial :=
        Nat.dvd_factorial hnk0 le_rfl
      have hd2 : n ∣ (n * k).factorial :=
        dvd_trans (Dvd.intro k rfl) hd1
      have hd3 : n ∣ n.factorial := Nat.dvd_factorial hn0 le_rfl
      have hd4 : n.factorial ∣ (n * k).factorial :=
        Nat.factorial_dvd_factorial hle
      have hexp1 : (n * k).factorial / (n * k) * k =
          (n * k).factorial / n := by
        apply Nat.eq_of_mul_eq_mul_right hn0
        rw [Nat.div_mul_cancel hd2, mul_assoc, mul_comm k n,
          Nat.div_mul_cancel hd1]
      have hexp2 : (n * k).factorial / n.factorial *
          (n.factorial / n) = (n * k).factorial / n := by
        apply Nat.eq_of_mul_eq_mul_right hn0
        rw [Nat.div_mul_cancel hd2, mul_assoc, Nat.div_mul_cancel hd3,
          Nat.div_mul_cancel hd4]
      rw [← pow_mul, hexp1, ← hexp2, pow_mul,
        chainRoot_telescope value hle]

end AlgebraicClosureRootSystem

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def naturalRootSystem : Obligation :=
  { id := "IUT-II.natural-compatible-root-system"
    source := "IUT II, Kummer root layer; IUT III, Proposition 3.5"
    status := VerificationStatus.proved
    note :=
      "The natural-power compatible root-system laws, algebraically closed " ++
        "n-th-root existence, factorial-chain telescope, and the resulting " ++
        "root system are proved in units using Mathlib's standard algebraic " ++
        "closedness API. The rational-root packaging, Galois root ratios, and " ++
        "Kummer cocycle remain separate obligations."
    dependsOn := [ "IUT-II.compatible-rational-root-system" ] }

end LeanFormal.IUT.Audit
