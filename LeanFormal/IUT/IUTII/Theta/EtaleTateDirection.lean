import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import Mathlib.Data.ZMod.Basic

/-!
  The finite cyclic quotient of the integral Tate direction.

  This is the exact algebraic kernel used by finite etale theta levels: the
  integer direction is reduced modulo the prime label, with its kernel and
  generator order proved from `ZMod`.  It is not a construction of an etale
  fundamental group or of the source's geometric cover.
-/

namespace LeanFormal.IUT

noncomputable section

def integralTateReduction (l : PrimeGeFive) : ℤ →+ ZMod l.value :=
  Int.castAddHom (ZMod l.value)

theorem integralTateReduction_apply (l : PrimeGeFive) (n : ℤ) :
    integralTateReduction l n = (n : ZMod l.value) :=
  rfl

theorem integralTateReduction_surjective (l : PrimeGeFive) :
    Function.Surjective (integralTateReduction l) := by
  exact ZMod.intCast_surjective

theorem integralTateReduction_kernel (l : PrimeGeFive) :
    (integralTateReduction l).ker = AddSubgroup.zmultiples (l.value : ℤ) := by
  exact ZMod.ker_intCastAddHom l.value

def canonicalTateGenerator (l : PrimeGeFive) : ZMod l.value :=
  1

theorem canonicalTateGenerator_order (l : PrimeGeFive) :
    addOrderOf (canonicalTateGenerator l) = l.value := by
  exact ZMod.addOrderOf_one l.value

theorem canonicalTateGenerator_ne_zero (l : PrimeGeFive) :
    canonicalTateGenerator l ≠ 0 := by
  intro h
  have hzero : l.value = 1 := by
    calc
      l.value = addOrderOf (canonicalTateGenerator l) :=
        (canonicalTateGenerator_order l).symm
      _ = addOrderOf (0 : ZMod l.value) := by rw [h]
      _ = 1 := addOrderOf_zero
  have hge : 5 ≤ l.value := l.ge_five
  omega

def canonicalTateLevel (l : PrimeGeFive) : AddSubgroup (ZMod l.value) :=
  ⊤

theorem canonicalTateLevel_eq_top (l : PrimeGeFive) :
    canonicalTateLevel l = ⊤ :=
  rfl

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def finiteEtaleTateDirection : Obligation :=
  { id := "IUT-II.etale-finite-tate-direction"
    source := "IUT II, finite etale theta direction"
    status := VerificationStatus.proved
    note :=
      "The exact cyclic Z/lZ quotient of the integer Tate direction is " ++
        "constructed with its surjectivity, kernel, generator, and generator " ++
        "order. Geometric etale-cover representability and fundamental-group " ++
        "identification remain pending."
    dependsOn := ["Foundations.Arithmetic.prime-label-ge-five"] }

end LeanFormal.IUT.Audit
