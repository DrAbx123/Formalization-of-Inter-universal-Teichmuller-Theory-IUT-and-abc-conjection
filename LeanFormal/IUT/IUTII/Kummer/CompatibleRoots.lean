/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.KummerPolynomial

/-!
  Source-facing compatible rational root systems.

  This is the root-system object used in the Kummer layer of the public
  source-oriented developments.  It is deliberately stated for a genuine
  commutative group, so the additive homomorphism records compatibility for
  every rational exponent.  Existence for the arithmetic monoids of IUT is a
  later obligation; it is not obtained from this record alone.
-/

namespace LeanFormal.IUT

structure CompatibleRootSystem (M : Type*) [CommGroup M] (value : M) where
  roots : ℚ →+ Additive M
  root_one : roots 1 = Additive.ofMul value

namespace CompatibleRootSystem

variable {M : Type*} [CommGroup M] {value : M}

theorem quotient_pow_den
    (first second : CompatibleRootSystem M value) (q : ℚ) :
    ((second.roots q).toMul / (first.roots q).toMul) ^ q.den = 1 := by
  have first_nsmul := first.roots.map_nsmul q.den q
  have second_nsmul := second.roots.map_nsmul q.den q
  have denominator_smul : q.den • q = (q.num : ℚ) := by
    simp [nsmul_eq_mul, q.den_mul_eq_num]
  have first_integer := first.roots.map_zsmul q.num 1
  have second_integer := second.roots.map_zsmul q.num 1
  have first_integer' :
      first.roots (q.num : ℚ) = q.num • first.roots 1 := by
    simpa using first_integer
  have second_integer' :
      second.roots (q.num : ℚ) = q.num • second.roots 1 := by
    simpa using second_integer
  have roots_integer_equal :
      first.roots (q.num : ℚ) = second.roots (q.num : ℚ) := by
    rw [first_integer', second_integer', first.root_one, second.root_one]
  have roots_power_equal :
      (first.roots q).toMul ^ q.den =
        (second.roots q).toMul ^ q.den := by
    apply Additive.ofMul.injective
    change q.den • first.roots q = q.den • second.roots q
    rw [← first_nsmul, ← second_nsmul, denominator_smul, roots_integer_equal]
  rw [div_pow, roots_power_equal]
  simp

end CompatibleRootSystem

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def compatibleRootSystem : Obligation :=
  { id := "IUT-II.compatible-rational-root-system"
    source := "IUT II, Kummer-theoretic root systems; public source implementations"
    status := VerificationStatus.interface
    note :=
      "The compatible rational-root record and the denominator-torsion " ++
        "identity are stated for a genuine commutative group. Existence in " ++
        "the IUT arithmetic monoid, integral root ratios, and Galois descent " ++
        "remain pending."
    dependsOn := [ "IUT-II.kummer-polynomial-kernel" ] }

end LeanFormal.IUT.Audit
