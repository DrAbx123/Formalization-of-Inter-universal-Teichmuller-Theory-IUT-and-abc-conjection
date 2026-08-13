import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
  Determinant and log-volume transport along a proved Hodge-theater link.

  The equalities are derived from the link's scale equality and finite
  products.  They do not assert a holomorphic hull or identify the packet
  with the source's etale theta function.
-/

namespace LeanFormal.IUT

namespace HodgeTheaterLink

variable {l : PrimeGeFive} {V : Type*}
  {source target : HodgeTheater l V}

theorem log_scale_eq (link : HodgeTheaterLink source target)
    (j : SignedLabel l.value) :
    Real.log (source.thetaPacket.scale j) =
      Real.log (target.thetaPacket.scale j) := by
  rw [link.theta_scale_eq j]

theorem scale_product_eq (link : HodgeTheaterLink source target) :
    (∏ j : SignedLabel l.value, source.thetaPacket.scale j) =
      ∏ j : SignedLabel l.value, target.thetaPacket.scale j := by
  apply Finset.prod_congr rfl
  intro j hj
  exact link.theta_scale_eq j

theorem log_volume_eq (link : HodgeTheaterLink source target) :
    source.thetaPacket.logVolume = target.thetaPacket.logVolume := by
  rw [source.thetaPacket.logVolume_eq_sum,
    target.thetaPacket.logVolume_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact link.log_scale_eq j

end HodgeTheaterLink

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def hodgeTheaterLinkVolumeTransport : Obligation :=
  { id := "IUT-I.hodge-theater-link-log-volume-transport"
    source := "IUT I, Sections 4--5; theta-link scale transport"
    status := VerificationStatus.provedKernel
    note :=
      "A proved Hodge-theater link transports every logarithmic scale, the " ++
        "finite scale product, and the finite packet log-volume. The result " ++
        "uses no hull, determinant line, or etale-theta identification."
    dependsOn := ["IUT-I.hodge-theater-carrier-and-links"] }

end LeanFormal.IUT.Audit
