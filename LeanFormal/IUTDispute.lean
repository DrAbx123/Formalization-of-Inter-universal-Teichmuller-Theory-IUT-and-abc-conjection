import Mathlib

/-!
  A small audit model for the disputed IUT III, Corollary 3.12 step.

  The declarations mirror two public Lean experiments:

  * Takkun-kohinata/IUT_LEAN separates a one-sided `PilotVolumeData`
    from a two-sided `ThetaLinkComparison`;
  * promachina/iut-lean packages the missing source construction as explicit
    obligations (`SourceObligationLedger`).

  This file proves only the order-theoretic consequences.  It does not model
  Hodge theaters, Frobenioids, Kummer maps, or the arithmetic construction of
  the obligations.
-/

namespace LeanFormal.IUTDispute

/-! ## Same-space identification: the inequality becomes tautological -/

structure SameSpaceData where
  Ω : Type
  [ord : Preorder Ω]
  vol : Ω → ℝ
  vol_mono : Monotone vol
  thetaPilot qPilot hull : Ω
  hull_contains_theta : thetaPilot ≤ hull
  q_is_theta : qPilot = thetaPilot

attribute [instance] SameSpaceData.ord

theorem same_space_inequality_is_vacuous (D : SameSpaceData) :
    D.vol D.qPilot ≤ D.vol D.hull := by
  rw [D.q_is_theta]
  exact D.vol_mono D.hull_contains_theta

/-! ## Arithmetic normalization: the two pilot readings cannot be equal -/

theorem link_not_isometric
    (q theta factor : ℝ)
    (hq : q < 0)
    (hfactor : 1 < factor)
    (htheta : theta = factor * q) :
    q ≠ theta := by
  intro h
  nlinarith [mul_pos (sub_pos.mpr hfactor) (neg_pos.mpr hq)]

/-! ## If the tight-hull simplification is added, the data collapse -/

theorem strict_collapse
    (q theta hull factor : ℝ)
    (hq : q < 0)
    (hfactor : 1 < factor)
    (htheta : theta = factor * q)
    (hq_hull : q ≤ hull)
    (hhull_theta : hull ≤ theta) :
    False := by
  nlinarith [mul_pos (sub_pos.mpr hfactor) (neg_pos.mpr hq)]

/-! ## Receiver-side common-container route -/

structure ReceiverBound where
  q hull cTheta : ℝ
  q_negative : q < 0
  q_in_hull : q ≤ hull
  hull_upper_bound : hull ≤ cTheta * (-q)

theorem receiver_bound_implies_cTheta_ge_neg_one (D : ReceiverBound) :
    -1 ≤ D.cTheta := by
  nlinarith [D.q_in_hull, D.hull_upper_bound]

/-!
  A concrete slack witness.  It satisfies the useful receiver-side inequality
  while violating the tight-hull assumption.  Thus the contradiction above is
  caused by the extra identification/tightness premise, not by the abstract
  common-container shape itself.
-/
theorem slack_witness :
    let q : ℝ := -1
    let theta : ℝ := -2
    let hull : ℝ := -1
    q < 0 ∧ 1 < 2 ∧ theta = 2 * q ∧ q ≤ hull ∧ ¬ hull ≤ theta := by
  norm_num

end LeanFormal.IUTDispute
