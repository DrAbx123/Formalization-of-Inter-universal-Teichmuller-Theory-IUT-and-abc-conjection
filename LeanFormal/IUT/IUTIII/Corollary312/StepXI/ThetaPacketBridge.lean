/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
  The concrete finite theta packet entering the Step-XI arithmetic kernel.

  `FiniteThetaPacket` is the lower-layer source object.  The Step-XI volume
  file deliberately works with a positive finite packet so that determinant,
  tensor, rescaling, and logarithm identities can be stated using Mathlib's
  official finite products.  This file is the explicit bridge between those
  two carriers.  It proves only transport of the already-established data;
  it does not assert the paper's holomorphic-hull or Hodge-theater
  construction.
-/

namespace LeanFormal.IUT

namespace FiniteThetaPacket

variable {l : PrimeGeFive} (packet : FiniteThetaPacket l)

def toPositivePacket : PositivePacket (SignedLabel l.value) where
  scale := packet.scale
  positive := packet.scale_pos

@[simp] theorem toPositivePacket_scale (j : SignedLabel l.value) :
    packet.toPositivePacket.scale j = packet.scale j := rfl

theorem toPositivePacket_positive (j : SignedLabel l.value) :
    0 < packet.toPositivePacket.scale j :=
  packet.scale_pos j

theorem toPositivePacket_det_eq_prod :
    packetDet packet.toPositivePacket =
      ∏ j : SignedLabel l.value, packet.scale j := by
  rw [packetDet_eq_prod]
  rfl

theorem toPositivePacket_logVolume_eq_log_det :
    packetLogVolume packet.toPositivePacket =
      Real.log (packetDet packet.toPositivePacket) :=
  packetLogVolume_eq_log_det packet.toPositivePacket

theorem toPositivePacket_logVolume_eq_sum :
    packetLogVolume packet.toPositivePacket =
      ∑ j : SignedLabel l.value, Real.log (packet.scale j) := by
  rfl

theorem toPositivePacket_neg_invariant :
    (∑ j : SignedLabel l.value,
        Real.log (packet.toPositivePacket.scale (SignedLabel.neg j))) =
      packetLogVolume packet.toPositivePacket := by
  change (∑ j : SignedLabel l.value,
      Real.log (packet.scale (SignedLabel.neg j))) =
    ∑ j : SignedLabel l.value, Real.log (packet.scale j)
  exact packet.logVolume_neg_invariant

theorem toPositivePacket_det_rescale (c : Real) (hc : 0 < c) :
    packetDet (rescalePacket c hc packet.toPositivePacket) =
      c ^ Fintype.card (SignedLabel l.value) *
        packetDet packet.toPositivePacket :=
  packetDet_rescale c hc packet.toPositivePacket

theorem toPositivePacket_logVolume_rescale (c : Real) (hc : 0 < c) :
    packetLogVolume (rescalePacket c hc packet.toPositivePacket) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log c +
        packetLogVolume packet.toPositivePacket :=
  packetLogVolume_rescale c hc packet.toPositivePacket

end FiniteThetaPacket

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def finiteThetaPacketBridge : Obligation :=
  { id := "IUT-III.StepXI.finite-theta-packet-bridge"
    source := "IUT II theta special values; IUT III Corollary 3.12 Steps (xi-d)-(xi-g)"
    status := VerificationStatus.proved
    note :=
      "The concrete lower-layer Gaussian theta packet is transported into " ++
        "the positive finite-packet carrier used by the determinant and " ++
        "log-volume kernel. Product, log-determinant, sign-invariance, and " ++
        "rescaling identities are inherited from Mathlib-backed proofs. " ++
        "The source holomorphic hull and its volume bound remain pending."
    dependsOn :=
      [ "IUT-II.finite-theta-packet",
        "IUT-III.holomorphic-hull-determinant-log-volume" ] }

end LeanFormal.IUT.Audit
