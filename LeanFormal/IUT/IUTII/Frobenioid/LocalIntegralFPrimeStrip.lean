import LeanFormal.IUT.IUTII.Frobenioid.LocalTimesMuEvaluation
import LeanFormal.IUT.IUTII.Frobenioid.LocalPrimeStrip

/-!
  A concrete local `FPrimeStrip` whose value monoids are the nonzero local
  integral-closure monoids themselves.  The degree is transported from the
  ambient algebraic-closure units along the proved monoid inclusion.  Keeping
  the monoid here is essential: the generic `FPrimeStrip` Kummer layer takes
  its unit group exactly once.  This is a local carrier instance, not yet the
  paper's global Frobenioid or its etale link.
-/

namespace LeanFormal.IUT

noncomputable abbrev localIntegralNormDegreeFor
    (p : Nat) [Fact (Nat.Prime p)] :
    LocalIntegralMonoid p →* Multiplicative Real :=
  (localUnitNormDegreeFor p).comp
    (LocalIntegralMonoid.toAlgebraicClosureUnits p)

theorem localIntegralNormDegreeFor_apply_mul
    (p : Nat) [Fact (Nat.Prime p)]
    (u v : LocalIntegralMonoid p) :
    localIntegralNormDegreeFor p (u * v) =
      localIntegralNormDegreeFor p u *
        localIntegralNormDegreeFor p v := by
  exact (localIntegralNormDegreeFor p).map_mul u v

noncomputable def localIntegralFPrimeStrip :
    FPrimeStrip RationalPrimePlace where
  Pi := localDPrimeStrip.Pi
  groupPi := localDPrimeStrip.groupPi
  G := localDPrimeStrip.G
  groupG := localDPrimeStrip.groupG
  proj := localDPrimeStrip.proj
  proj_surjective := localDPrimeStrip.proj_surjective
  Mon := fun v => letI := Fact.mk v.2; LocalIntegralMonoid v.1
  commMonoidMon := fun v => by
    letI := Fact.mk v.2
    infer_instance
  action := fun v => by
    letI := Fact.mk v.2
    exact LocalIntegralMonoid.galoisAction v.1
  degree := fun v => by
    letI := Fact.mk v.2
    exact localIntegralNormDegreeFor v.1

theorem localIntegralFPrimeStrip_degree_mul
    (v : RationalPrimePlace)
    (u w : localIntegralFPrimeStrip.Mon v) :
    localIntegralFPrimeStrip.degree v (u * w) =
      localIntegralFPrimeStrip.degree v u *
        localIntegralFPrimeStrip.degree v w := by
  letI := Fact.mk v.2
  exact (localIntegralNormDegreeFor v.1).map_mul u w

noncomputable def finiteLocalIntegralFPrimeStrip
    (lower upper : Nat) :
    FPrimeStrip (FinitePrimePlace lower upper) where
  Pi := (finiteLocalFPrimeStrip lower upper).Pi
  groupPi := (finiteLocalFPrimeStrip lower upper).groupPi
  G := (finiteLocalFPrimeStrip lower upper).G
  groupG := (finiteLocalFPrimeStrip lower upper).groupG
  proj := (finiteLocalFPrimeStrip lower upper).proj
  proj_surjective := (finiteLocalFPrimeStrip lower upper).proj_surjective
  Mon := fun v => letI := Fact.mk v.prime; LocalIntegralMonoid v.1
  commMonoidMon := fun v => by
    letI := Fact.mk v.prime
    infer_instance
  action := fun v => by
    letI := Fact.mk v.prime
    exact LocalIntegralMonoid.galoisAction v.1
  degree := fun v => by
    letI := Fact.mk v.prime
    exact localIntegralNormDegreeFor v.1

theorem finiteLocalIntegralFPrimeStrip_degree_mul
    (lower upper : Nat)
    (v : FinitePrimePlace lower upper)
    (u w : (finiteLocalIntegralFPrimeStrip lower upper).Mon v) :
    (finiteLocalIntegralFPrimeStrip lower upper).degree v (u * w) =
      (finiteLocalIntegralFPrimeStrip lower upper).degree v u *
        (finiteLocalIntegralFPrimeStrip lower upper).degree v w := by
  letI := Fact.mk v.prime
  exact (localIntegralNormDegreeFor v.1).map_mul u w

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localIntegralFPrimeStripCarrier : Obligation :=
  { id := "IUT-II.local-integral-f-prime-strip-carrier"
    source := "IUT II, Definition 4.9(i); local integral Frobenioid carrier"
    status := VerificationStatus.proved
    note :=
      "A concrete F-prime-strip instance is built from the nonzero local " ++
        "integral-closure monoids, the proved local Galois action, and the norm " ++
        "degree transported through the monoid inclusion, both on all rational prime places " ++
        "and on finite prime intervals. The global Frobenioid, etale realization, " ++
        "and arithmetic Frobenius links remain pending."
    dependsOn :=
      [ "IUT-II.local-integral-monoid-carrier",
        "IUT-II.local-times-mu-evaluation",
        "IUT-I-II.prime-strip-core" ] }

end LeanFormal.IUT.Audit
