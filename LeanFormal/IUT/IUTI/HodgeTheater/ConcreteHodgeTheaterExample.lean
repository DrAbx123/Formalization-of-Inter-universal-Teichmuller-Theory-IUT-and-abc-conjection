/-
  A concrete Hodge-theater carrier assembled from the proved lower layers.

  This example deliberately exposes the boundary of the construction.  The
  arithmetic input, local F-prime strip, and finite theta packet are genuine
  Lean objects, while the source's etale, Frobenioid, and Hodge-Arakelov
  compatibility conditions remain obligations of later modules.
-/

import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTII.Frobenioid.LocalPrimeStrip

namespace LeanFormal.IUT

noncomputable section

def gaussianHodgeTheater (l : PrimeGeFive) :
    HodgeTheater l RationalPrimePlace where
  arithmetic := gaussianInitialThetaArithmeticData l
  primeStrip := localFPrimeStrip
  thetaPacket := FiniteThetaPacket.ofQ (l := l) (1 / 2 : Real) (by norm_num)

theorem gaussianHodgeTheater_q (l : PrimeGeFive) :
    (gaussianHodgeTheater l).thetaPacket.q = (1 / 2 : Real) := by
  rfl

def gaussianThreeTheaterSystem (l : PrimeGeFive) :
    ThreeTheaterSystem l RationalPrimePlace where
  source := gaussianHodgeTheater l
  middle := gaussianHodgeTheater l
  target := gaussianHodgeTheater l
  source_to_middle := HodgeTheaterLink.refl _
  middle_to_target := HodgeTheaterLink.refl _

theorem gaussianThreeTheaterSystem_q (l : PrimeGeFive) :
    (gaussianThreeTheaterSystem l).source.thetaPacket.q =
      (gaussianThreeTheaterSystem l).target.thetaPacket.q := by
  exact (gaussianThreeTheaterSystem l).sourceToTarget_q

end
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteHodgeTheaterExample : Obligation :=
  { id := "IUT-I.concrete-hodge-theater-carrier"
    source := "IUT I, Sections 4-5 (one explicit carrier instance)"
    status := VerificationStatus.proved
    note :=
      "A concrete theater and a reflexive three-theater system are assembled " ++
        "from the proved Q(i) arithmetic input, local F-prime strip, and " ++
        "finite theta packet. The construction does not assert the source's " ++
        "etale/Frobenioid/Hodge-Arakelov compatibility or distinct-history " ++
        "existence theorem."
    dependsOn :=
      [ "IUT-I.initial-theta-concrete-gaussian",
        "IUT-I-II.local-f-prime-strip-carrier",
        "IUT-II.finite-theta-packet" ] }

end LeanFormal.IUT.Audit
