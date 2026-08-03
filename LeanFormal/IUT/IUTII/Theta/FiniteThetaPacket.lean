/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Foundations.Theta.GaussianKernel
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
  Finite theta packets on the bounded integer representatives of `F_l`.

  The source labels in IUT II are represented by bounded integers, with the
  involution `j ↦ -j` accounting for the `±1` quotient.  This file makes the
  finite carrier and the real special-value packet explicit.  It uses the
  standard Gaussian value `q^(j^2)` already proved in the lower theta kernel;
  it does not identify this packet with an etale theta function or assert the
  Hodge-Arakelov comparison.  Those identifications remain separate audited
  obligations.

  Source correspondence: IUT II, theta special values and the `F_l`/cusp
  labels; compare Takkun-kohinata/IUT_LEAN `Theta/ThetaValues.lean` and
  `Combinatorics/Fl.lean`.
-/

namespace LeanFormal.IUT

structure FiniteThetaPacket (l : PrimeGeFive) where
  q : Real
  q_pos : 0 < q
  scale : SignedLabel l.value → Real
  scale_eq : ∀ j, scale j = realThetaValue q j.1

namespace FiniteThetaPacket

variable {l : PrimeGeFive} (packet : FiniteThetaPacket l)

noncomputable def ofQ (q : Real) (hq : 0 < q) : FiniteThetaPacket l where
  q := q
  q_pos := hq
  scale := fun j => realThetaValue q j.1
  scale_eq := by intro j; rfl

@[simp] theorem ofQ_q (q : Real) (hq : 0 < q) :
    (ofQ (l := l) q hq).q = q := rfl

theorem scale_pos (j : SignedLabel l.value) : 0 < packet.scale j := by
  rw [packet.scale_eq]
  exact realThetaValue_pos packet.q_pos j.1

theorem scale_ne_zero (j : SignedLabel l.value) : packet.scale j ≠ 0 :=
  ne_of_gt (packet.scale_pos j)

theorem scale_neg (j : SignedLabel l.value) :
    packet.scale (SignedLabel.neg j) = packet.scale j := by
  rw [packet.scale_eq, packet.scale_eq, SignedLabel.theta_neg]

theorem log_scale (j : SignedLabel l.value) :
    Real.log (packet.scale j) =
      (gaussExponent j.1).toNat * Real.log packet.q := by
  rw [packet.scale_eq, log_realThetaValue]

noncomputable def logVolume : Real :=
  ∑ j : SignedLabel l.value, Real.log (packet.scale j)

theorem logVolume_eq_sum :
    packet.logVolume = ∑ j : SignedLabel l.value, Real.log (packet.scale j) :=
  rfl

theorem logVolume_ofQ (q : Real) (hq : 0 < q) :
    (ofQ (l := l) q hq).logVolume =
      ∑ j : SignedLabel l.value, Real.log (realThetaValue q j.1) := by
  rfl

theorem logVolume_neg_invariant :
    (∑ j : SignedLabel l.value, Real.log (packet.scale (SignedLabel.neg j))) =
      packet.logVolume := by
  classical
  let e : SignedLabel l.value ≃ SignedLabel l.value :=
    { toFun := SignedLabel.neg
      invFun := SignedLabel.neg
      left_inv := SignedLabel.neg_involutive
      right_inv := SignedLabel.neg_involutive }
  simpa [logVolume, e] using
    (e.sum_comp (fun j : SignedLabel l.value => Real.log (packet.scale j)))

end FiniteThetaPacket

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def finiteThetaPacket : Obligation :=
  { id := "IUT-II.finite-theta-packet"
    source := "IUT II, theta special values and finite F_l/cusp labels"
    status := VerificationStatus.proved
    note :=
      "Bounded integer representatives have a standard finite carrier. A " ++
        "positive real q produces an explicit Gaussian theta packet; Lean " ++
        "proves positivity, nonvanishing, logarithmic special-value formulas, " ++
        "and invariance under j ↦ -j. Etale theta evaluation, Hodge-Arakelov " ++
        "comparison, and the Step-XI hull construction remain pending."
    dependsOn :=
      [ "IUT-I.initial-theta-arithmetic-data",
        "Foundations.Theta.GaussianKernel" ] }

end LeanFormal.IUT.Audit
