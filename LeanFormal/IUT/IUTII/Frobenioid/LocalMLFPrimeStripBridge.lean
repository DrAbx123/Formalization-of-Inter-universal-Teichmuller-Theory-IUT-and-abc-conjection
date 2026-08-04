import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralFPrimeStrip
import LeanFormal.IUT.IUTII.Frobenioid.LocalMLFTMPair

/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

/-!
  Definitional compatibility between the literal local MLF `TM` model and the
  integral F-prime-strip carrier.

  Both constructions use the same nonzero integral-closure monoid and the same
  absolute-Galois action.  The theorems below make this identity explicit at
  the monoid, unit, and `times-mu` levels.  They do not construct the global
  Frobenioid evaluation functor or an etale theta-link.
-/

namespace LeanFormal.IUT

local instance rationalPrimePlaceFact (v : RationalPrimePlace) :
    Fact (Nat.Prime v.1) :=
  Fact.mk v.2

theorem localIntegralFPrimeStrip_action_eq_modelAction
    (v : RationalPrimePlace)
    (g : localIntegralFPrimeStrip.toDPrimeStrip.Pi v)
    (value : localIntegralFPrimeStrip.Mon v) :
    localIntegralFPrimeStrip.action v g value =
      (LocalMLFModelTMPair.monoAnalytic v.1).action v.1 g value := by
  letI := Fact.mk v.2
  rfl

theorem localIntegralFPrimeStrip_unitsAction_eq_modelUnitAction
    (v : RationalPrimePlace)
    (g : localIntegralFPrimeStrip.toDPrimeStrip.Pi v)
    (value : (localIntegralFPrimeStrip.Mon v)ˣ) :
    localIntegralFPrimeStrip.unitsAction v g value =
      (LocalMLFModelTMPair.monoAnalytic v.1).unitAction v.1 g value := by
  letI := Fact.mk v.2
  rfl

theorem localIntegralFPrimeStrip_timesMuAction_eq_modelTimesMuAction
    (v : RationalPrimePlace) :
    localIntegralFPrimeStrip.timesMuAction v =
      (LocalMLFModelTMPair.monoAnalytic v.1).timesMuAction v.1 := by
  letI := Fact.mk v.2
  rfl

@[simp]
theorem localIntegralFPrimeStrip_timesMuAction_quotientMap
    (v : RationalPrimePlace)
    (g : localIntegralFPrimeStrip.toDPrimeStrip.Pi v)
    (value : (localIntegralFPrimeStrip.Mon v)ˣ) :
    localIntegralFPrimeStrip.timesMuAction v g
        (TimesMuQuotient.quotientMap value) =
      TimesMuQuotient.quotientMap
        ((LocalMLFModelTMPair.monoAnalytic v.1).unitAction v.1 g value) := by
  letI := Fact.mk v.2
  rfl

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localMLFPrimeStripBridge : Obligation :=
  { id := "IUT-II.local-MLF-prime-strip-bridge"
    source := "IUT II, Definition 4.9(i); local MLF TM/F-prime-strip compatibility"
    status := VerificationStatus.proved
    note :=
      "After representing the F-prime-strip value object by the actual local " ++
        "integral monoid, its monoid, unit, and times-mu Galois actions are " ++
        "proved definitionally identical to those of the canonical local MLF " ++
        "TM pair. This removes a double-units mismatch. The categorical " ++
        "Frobenioid evaluation and the group/Frobenioid Kummer comparison " ++
        "remain pending."
    dependsOn :=
      [ "IUT-II.local-integral-f-prime-strip-carrier",
        "IUT-II.local-MLF-TM-pair" ] }

end LeanFormal.IUT.Audit
