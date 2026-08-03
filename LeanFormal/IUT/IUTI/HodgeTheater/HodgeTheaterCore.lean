/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket

/-!
  Source-facing Hodge-theater carriers and links.

  A Hodge theater in IUT I is not merely a label for a type: it contains the
  arithmetic input, a prime-strip realization, and theta data.  This module
  records those three pieces using the lower-layer Mathlib carriers.  A link
  records both the prime-strip equivalence and the theta-packet alignment;
  composition and symmetry are proved from the official equivalence API.

  The remaining arithmetic/geometric compatibility conditions of Mochizuki's
  Hodge theaters are intentionally fields of later source constructions, not
  silently inferred here.  Thus this module is an auditable carrier/interface
  layer, while its link algebra is fully proved.

  Source correspondence: IUT I, Sections 3--5 (initial theta data, Hodge
  theaters, and histories); compare the public `IUT_LEAN` Hodge-theater and
  prime-strip structures.
-/

namespace LeanFormal.IUT

universe ua uv upi umon

set_option linter.checkUnivs false in
structure HodgeTheater (l : PrimeGeFive) (V : Type uv) where
  arithmetic : InitialThetaArithmeticData.{ua} l
  primeStrip : FPrimeStrip.{umon, uv, upi} V
  thetaPacket : FiniteThetaPacket l

structure HodgeTheaterLink
    {l : PrimeGeFive} {V : Type uv}
    (source target : HodgeTheater.{ua, uv, upi, umon} l V) where
  primeStripEquiv : FPrimeStripEquiv source.primeStrip target.primeStrip
  theta_q_eq : source.thetaPacket.q = target.thetaPacket.q
  theta_scale_eq : ∀ j,
    source.thetaPacket.scale j = target.thetaPacket.scale j

namespace HodgeTheaterLink

variable {l : PrimeGeFive} {V : Type uv}
variable {S T U : HodgeTheater.{ua, uv, upi, umon} l V}

def refl (S : HodgeTheater.{ua, uv, upi, umon} l V) : HodgeTheaterLink S S where
  primeStripEquiv := FPrimeStripEquiv.refl S.primeStrip
  theta_q_eq := rfl
  theta_scale_eq := by intro j; rfl

def symm (link : HodgeTheaterLink S T) : HodgeTheaterLink T S where
  primeStripEquiv := FPrimeStripEquiv.symm link.primeStripEquiv
  theta_q_eq := link.theta_q_eq.symm
  theta_scale_eq := by intro j; exact (link.theta_scale_eq j).symm

def trans (first : HodgeTheaterLink S T)
    (second : HodgeTheaterLink T U) : HodgeTheaterLink S U where
  primeStripEquiv := FPrimeStripEquiv.trans first.primeStripEquiv second.primeStripEquiv
  theta_q_eq := first.theta_q_eq.trans second.theta_q_eq
  theta_scale_eq := by
    intro j
    exact (first.theta_scale_eq j).trans (second.theta_scale_eq j)

theorem symm_symm (link : HodgeTheaterLink S T) :
    (link.symm).symm = link := by
  cases link
  rfl

theorem refl_trans (first : HodgeTheaterLink S T) :
    trans (refl S) first = first := by
  cases first
  rfl

theorem trans_refl (first : HodgeTheaterLink S T) :
    trans first (refl T) = first := by
  cases first
  rfl

end HodgeTheaterLink

set_option linter.checkUnivs false in
structure ThreeTheaterSystem (l : PrimeGeFive) (V : Type uv) where
  source : HodgeTheater.{ua, uv, upi, umon} l V
  middle : HodgeTheater.{ua, uv, upi, umon} l V
  target : HodgeTheater.{ua, uv, upi, umon} l V
  source_to_middle : HodgeTheaterLink source middle
  middle_to_target : HodgeTheaterLink middle target

namespace ThreeTheaterSystem

variable {l : PrimeGeFive} {V : Type uv}

def sourceToTarget (system : ThreeTheaterSystem l V) :
    HodgeTheaterLink system.source system.target :=
  HodgeTheaterLink.trans system.source_to_middle system.middle_to_target

theorem sourceToTarget_q (system : ThreeTheaterSystem l V) :
    system.source.thetaPacket.q = system.target.thetaPacket.q :=
  system.sourceToTarget.theta_q_eq

theorem sourceToTarget_scale (system : ThreeTheaterSystem l V)
    (j : SignedLabel l.value) :
    system.source.thetaPacket.scale j = system.target.thetaPacket.scale j :=
  system.sourceToTarget.theta_scale_eq j

end ThreeTheaterSystem

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def hodgeTheaterCore : Obligation :=
  { id := "IUT-I.hodge-theater-carrier-and-links"
    source := "IUT I, Sections 3-5"
    status := VerificationStatus.interface
    note :=
      "A theater records explicit InitialTheta arithmetic data, a concrete " ++
        "prime-strip carrier, and a finite theta packet. Links carry both " ++
        "prime-strip equivalences and theta alignment; link symmetry, " ++
        "composition, and the three-theater source-to-target transport are " ++
        "proved. The paper's existence and full anabelian/Hodge-Arakelov " ++
        "compatibility conditions remain pending fields of later modules."
    dependsOn :=
      [ "IUT-I.initial-theta-arithmetic-data",
        "IUT-I-II.prime-strip-core",
        "IUT-II.finite-theta-packet" ] }

end LeanFormal.IUT.Audit
