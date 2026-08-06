import LeanFormal.IUT.IUTII.Frobenioid.ConcreteLocalKummerExample
import LeanFormal.IUT.IUTII.Theta.EtaleTateDirection

/-!
  The integer part of the concrete compatible Kummer root system.

  Integer exponents are the algebraic Tate direction, while the roots are
  taken from the already proved rational root system of the actual local
  integral q-parameter.  The equality below is an additive-homomorphism law;
  no geometric etale or Galois descent claim is added.
-/

namespace LeanFormal.IUT

noncomputable section

namespace LocalIntegralMonoid

variable (p : Nat) [Fact (Nat.Prime p)]

def qIntegerRoot (n : ℤ) :
    Additive (Algebra.GrothendieckGroup (LocalIntegralMonoid p)) :=
  (qParameterCompatibleRoots p).roots (n : ℚ)

theorem qIntegerRoot_eq_zsmul (n : ℤ) :
    qIntegerRoot p n =
      n • Additive.ofMul (qParameterGroupification p) := by
  have h := (qParameterCompatibleRoots p).roots.map_zsmul n 1
  simpa [qIntegerRoot, (qParameterCompatibleRoots p).root_one] using h

theorem qIntegerRoot_one :
    qIntegerRoot p 1 = Additive.ofMul (qParameterGroupification p) := by
  simpa using qIntegerRoot_eq_zsmul p 1

end LocalIntegralMonoid

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteIntegerKummerDirection : Obligation :=
  { id := "IUT-II.concrete-integer-kummer-direction"
    source := "IUT II, Kummer system over the local q-parameter"
    status := VerificationStatus.proved
    note :=
      "The integer exponent slice of the actual compatible rational-root " ++
        "system is defined and its zsmul law is proved. This connects the " ++
        "algebraic Tate direction to the concrete q= p Kummer carrier, while " ++
        "geometric etale descent remains a separate obligation."
    dependsOn :=
      [ "IUT-II.concrete-local-q-parameter-roots",
        "IUT-II.etale-finite-tate-direction" ] }

end LeanFormal.IUT.Audit
