import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import Mathlib.FieldTheory.KummerPolynomial

/-!
  The polynomial/root layer used before a vertical log-Kummer correspondence.

  `AdjoinRoot` is Mathlib's quotient construction for `X^n - C a`.  The
  root relation and non-vanishing are proved from the official Kummer API.
  Irreducibility, a field realization, local valuation data, and the
  correspondence between different levels are intentionally not inferred.
-/

namespace LeanFormal.IUT

structure KummerPolynomialData (K : Type*) [Field K] where
  exponent : Nat
  exponent_pos : 0 < exponent
  parameter : K
  parameter_ne_zero : parameter ≠ 0

namespace KummerPolynomialData

variable {K : Type*} [Field K] (D : KummerPolynomialData K)

noncomputable def polynomial : Polynomial K :=
  Polynomial.X ^ D.exponent - Polynomial.C D.parameter

abbrev Adjoined : Type _ := AdjoinRoot D.polynomial

noncomputable def root : D.Adjoined :=
  AdjoinRoot.root D.polynomial

theorem root_pow_eq :
    D.root ^ D.exponent = AdjoinRoot.of D.polynomial D.parameter := by
  exact root_X_pow_sub_C_pow D.exponent D.parameter

theorem root_ne_zero : D.root ≠ 0 := by
  exact root_X_pow_sub_C_ne_zero' D.exponent_pos D.parameter_ne_zero

end KummerPolynomialData

noncomputable def localKummerPolynomialFor
    (p n : Nat) [Fact (Nat.Prime p)] (hn : 0 < n) :
    KummerPolynomialData ℚ_[p] where
  exponent := n
  exponent_pos := hn
  parameter := (p : ℚ_[p])
  parameter_ne_zero := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))

noncomputable def localKummerPolynomial
    (v : RationalPrimePlace) (n : Nat) (hn : 0 < n) := by
  letI := Fact.mk v.2
  exact localKummerPolynomialFor v.1 n hn

theorem localKummerPolynomialFor_root_pow_eq
    (p n : Nat) [Fact (Nat.Prime p)] (hn : 0 < n) :
    (localKummerPolynomialFor p n hn).root ^ n =
      AdjoinRoot.of (localKummerPolynomialFor p n hn).polynomial (p : ℚ_[p]) := by
  exact (localKummerPolynomialFor p n hn).root_pow_eq

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def kummerPolynomialKernel : Obligation :=
  { id := "IUT-II.kummer-polynomial-kernel"
    source := "IUT II, Kummer-theoretic polynomial/root prerequisites"
    status := VerificationStatus.proved
    note :=
      "Mathlib AdjoinRoot objects for X^n-C(a), their root-power relation, " ++
        "non-vanishing, and the local p-adic parameter specialization are proved. " ++
        "Irreducibility, valuation/log structures, and the vertical correspondence " ++
        "remain pending."
    dependsOn := [ "IUT-I-II.local-prime-place-carrier" ] }

end LeanFormal.IUT.Audit
