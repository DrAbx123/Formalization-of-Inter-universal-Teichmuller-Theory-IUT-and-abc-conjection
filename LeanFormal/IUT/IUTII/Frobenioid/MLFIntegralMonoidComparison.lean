import Iut.Foundations.SourceMLFIntegralMonoid
import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralMonoid

/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

namespace LeanFormal.IUT

namespace LocalIntegralMonoid

variable (p : Nat) [Fact (Nat.Prime p)]

noncomputable def equivSourceMLF :
    LocalIntegralMonoid p ≃*
      Iut.SourceMLFIntegralMonoid ℚ_[p] :=
  MulEquiv.refl _

@[simp]
theorem equivSourceMLF_apply
    (value : LocalIntegralMonoid p) :
    equivSourceMLF p value = value :=
  rfl

theorem sourceMLF_toAlgebraicClosureUnits_eq :
    Iut.SourceMLFIntegralMonoid.toAlgebraicClosureUnits ℚ_[p] =
      toAlgebraicClosureUnits p :=
  rfl

theorem sourceMLF_groupificationToAlgebraicClosureUnits_eq :
    Iut.SourceMLFIntegralMonoid.groupificationToAlgebraicClosureUnits ℚ_[p] =
      groupificationToAlgebraicClosureUnits p :=
  rfl

theorem sourceMLF_galoisAction_apply
    (sigma : LocalAbsoluteGalois p)
    (value : LocalIntegralMonoid p) :
    Iut.SourceMLFIntegralMonoid.galoisAction ℚ_[p] sigma
        (equivSourceMLF p value) =
      equivSourceMLF p (galoisAction p sigma value) :=
  rfl

end LocalIntegralMonoid

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def mlfIntegralMonoidComparison : Obligation :=
  { id := "IUT-II.MLF-integral-monoid-comparison"
    source := "IUT II, Definition 4.9(i); O-triangle of an MLF universal cover"
    status := VerificationStatus.proved
    note :=
      "The Q_p local integral monoid is definitionally identified with the " ++
        "generic characteristic-zero MLF integral-closure monoid. The " ++
        "inclusion into algebraic-closure units, the groupification map, and " ++
        "the absolute-Galois action are proved compatible. The finite-etale " ++
        "Frobenioid evaluation equivalence remains separate."
    dependsOn :=
      [ "IUT-II.local-integral-monoid-carrier" ] }

end LeanFormal.IUT.Audit
