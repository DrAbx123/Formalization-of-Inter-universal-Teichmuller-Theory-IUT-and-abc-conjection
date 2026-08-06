import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralFPrimeStrip

/-!
  Restriction facts for the finite integral prime-strip carrier.

  The finite interval carrier is definitionally the same local integral
  monoid, Galois action, and norm degree as the unrestricted carrier at each
  selected prime.  These equalities are useful when a finite source strip is
  fed into a Hodge theater, but they do not construct an etale or global
  Frobenioid.
-/

namespace LeanFormal.IUT

noncomputable section

local instance rationalPrimePlaceFact (v : RationalPrimePlace) :
    Fact (Nat.Prime v.1) := Fact.mk v.2

theorem finiteIntegralFPrimeStrip_monoid_eq
    (lower upper : Nat) (v : FinitePrimePlace lower upper) :
    (finiteLocalIntegralFPrimeStrip lower upper).Mon v =
      @LocalIntegralMonoid v.1 (Fact.mk v.prime) := by
  rfl

theorem finiteIntegralFPrimeStrip_degree_eq
    (lower upper : Nat) (v : FinitePrimePlace lower upper)
    (u : (finiteLocalIntegralFPrimeStrip lower upper).Mon v) :
    (finiteLocalIntegralFPrimeStrip lower upper).degree v u =
      @localIntegralNormDegreeFor v.1 (Fact.mk v.prime) u := by
  rfl

theorem finiteIntegralFPrimeStrip_action_eq
    (lower upper : Nat) (v : FinitePrimePlace lower upper)
    (g : (finiteLocalIntegralFPrimeStrip lower upper).Pi v)
    (u : (finiteLocalIntegralFPrimeStrip lower upper).Mon v) :
    (finiteLocalIntegralFPrimeStrip lower upper).action v g u =
      @LocalIntegralMonoid.galoisAction v.1 (Fact.mk v.prime) g u := by
  rfl

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def finitePrimeStripRestriction : Obligation :=
  { id := "IUT-II.finite-integral-prime-strip-restriction"
    source := "IUT II, finite prime strips and Definition 4.9(i)"
    status := VerificationStatus.proved
    note :=
      "At every selected finite prime, the interval integral F-prime-strip " ++
        "has exactly the local integral monoid, Galois action, and norm " ++
        "degree used by the unrestricted carrier."
    dependsOn := ["IUT-II.local-integral-f-prime-strip-carrier"] }

end LeanFormal.IUT.Audit
