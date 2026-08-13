/-
  Link algebra for the concrete initial-theta carrier.

  The source/target objects are intentionally the same checked carrier.  This
  proves the complete identity, symmetry, composition, scale-product, and
  log-volume laws in the actual dependent types.  It is a finite test history,
  not a claim that the paper's anabelian histories have been constructed.
-/

import LeanFormal.IUT.IUTI.InitialTheta.ConcreteInitialThetaTransport
import LeanFormal.IUT.IUTI.HodgeTheater.LinkVolumeTransport

namespace LeanFormal.IUT

noncomputable section

local instance primeFactForConcreteLinks (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

def concreteInitialThetaLink (l : PrimeGeFive) :
    HodgeTheaterLink
      (concreteInitialThetaCarrier l).theater
      (concreteInitialThetaCarrier l).theater :=
  HodgeTheaterLink.refl _

@[simp] theorem concreteInitialThetaLink_primeStrip
    (l : PrimeGeFive) :
    (concreteInitialThetaLink l).primeStripEquiv =
      FPrimeStripEquiv.refl (concreteInitialThetaCarrier l).theater.primeStrip :=
  rfl

@[simp] theorem concreteInitialThetaLink_q (l : PrimeGeFive) :
    (concreteInitialThetaLink l).theta_q_eq =
      Eq.refl (concreteInitialThetaCarrier l).theater.thetaPacket.q :=
  rfl

theorem concreteInitialThetaLink_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaLink l).theta_scale_eq j =
      Eq.refl ((concreteInitialThetaCarrier l).theater.thetaPacket.scale j) :=
  rfl

theorem concreteInitialThetaLink_symm (l : PrimeGeFive) :
    (concreteInitialThetaLink l).symm = concreteInitialThetaLink l := by
  rfl

theorem concreteInitialThetaLink_trans (l : PrimeGeFive) :
    (concreteInitialThetaLink l).trans (concreteInitialThetaLink l) =
      concreteInitialThetaLink l := by
  exact HodgeTheaterLink.refl_trans (concreteInitialThetaLink l)

def concreteInitialThetaThreeTheaterSystem (l : PrimeGeFive) :
    ThreeTheaterSystem l (FinitePrimePlace 2 7) where
  source := (concreteInitialThetaCarrier l).theater
  middle := (concreteInitialThetaCarrier l).theater
  target := (concreteInitialThetaCarrier l).theater
  source_to_middle := concreteInitialThetaLink l
  middle_to_target := concreteInitialThetaLink l

@[simp] theorem concreteInitialThetaThreeTheaterSystem_source
    (l : PrimeGeFive) :
    (concreteInitialThetaThreeTheaterSystem l).source =
      (concreteInitialThetaCarrier l).theater :=
  rfl

@[simp] theorem concreteInitialThetaThreeTheaterSystem_middle
    (l : PrimeGeFive) :
    (concreteInitialThetaThreeTheaterSystem l).middle =
      (concreteInitialThetaCarrier l).theater :=
  rfl

@[simp] theorem concreteInitialThetaThreeTheaterSystem_target
    (l : PrimeGeFive) :
    (concreteInitialThetaThreeTheaterSystem l).target =
      (concreteInitialThetaCarrier l).theater :=
  rfl

theorem concreteInitialThetaThreeTheaterSystem_sourceToTarget
    (l : PrimeGeFive) :
    (concreteInitialThetaThreeTheaterSystem l).sourceToTarget =
      concreteInitialThetaLink l := by
  exact HodgeTheaterLink.refl_trans (concreteInitialThetaLink l)

theorem concreteInitialThetaThreeTheaterSystem_q
    (l : PrimeGeFive) :
    (concreteInitialThetaThreeTheaterSystem l).source.thetaPacket.q =
      (concreteInitialThetaThreeTheaterSystem l).target.thetaPacket.q := by
  exact (concreteInitialThetaThreeTheaterSystem l).sourceToTarget_q

theorem concreteInitialThetaThreeTheaterSystem_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaThreeTheaterSystem l).source.thetaPacket.scale j =
      (concreteInitialThetaThreeTheaterSystem l).target.thetaPacket.scale j := by
  exact (concreteInitialThetaThreeTheaterSystem l).sourceToTarget_scale j

theorem concreteInitialThetaThreeTheaterSystem_log_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    Real.log ((concreteInitialThetaThreeTheaterSystem l).source.thetaPacket.scale j) =
      Real.log ((concreteInitialThetaThreeTheaterSystem l).target.thetaPacket.scale j) := by
  exact (concreteInitialThetaThreeTheaterSystem l).sourceToTarget.log_scale_eq j

theorem concreteInitialThetaThreeTheaterSystem_log_volume
    (l : PrimeGeFive) :
    (concreteInitialThetaThreeTheaterSystem l).source.thetaPacket.logVolume =
      (concreteInitialThetaThreeTheaterSystem l).target.thetaPacket.logVolume := by
  exact (concreteInitialThetaThreeTheaterSystem l).sourceToTarget.log_volume_eq

theorem concreteInitialThetaThreeTheaterSystem_scale_product
    (l : PrimeGeFive) :
    (∏ j : SignedLabel l.value,
      (concreteInitialThetaThreeTheaterSystem l).source.thetaPacket.scale j) =
      ∏ j : SignedLabel l.value,
        (concreteInitialThetaThreeTheaterSystem l).target.thetaPacket.scale j := by
  exact (concreteInitialThetaThreeTheaterSystem l).sourceToTarget.scale_product_eq

structure ConcreteInitialThetaHistory (l : PrimeGeFive) where
  source : ConcreteInitialThetaCarrier l
  middle : ConcreteInitialThetaCarrier l
  target : ConcreteInitialThetaCarrier l
  source_to_middle : source.theater.primeStrip = middle.theater.primeStrip
  middle_to_target : middle.theater.primeStrip = target.theater.primeStrip
  source_q_eq_middle : source.theater.thetaPacket.q = middle.theater.thetaPacket.q
  middle_q_eq_target : middle.theater.thetaPacket.q = target.theater.thetaPacket.q
  source_scale_eq_middle : ∀ j,
    source.theater.thetaPacket.scale j = middle.theater.thetaPacket.scale j
  middle_scale_eq_target : ∀ j,
    middle.theater.thetaPacket.scale j = target.theater.thetaPacket.scale j

def concreteInitialThetaHistory (l : PrimeGeFive) :
    ConcreteInitialThetaHistory l where
  source := concreteInitialThetaCarrier l
  middle := concreteInitialThetaCarrier l
  target := concreteInitialThetaCarrier l
  source_to_middle := rfl
  middle_to_target := rfl
  source_q_eq_middle := rfl
  middle_q_eq_target := rfl
  source_scale_eq_middle := fun _ => rfl
  middle_scale_eq_target := fun _ => rfl

theorem concreteInitialThetaHistory_primeStrip_eq
    (l : PrimeGeFive) :
    (concreteInitialThetaHistory l).source.theater.primeStrip =
      (concreteInitialThetaHistory l).target.theater.primeStrip := by
  exact (concreteInitialThetaHistory l).source_to_middle.trans
    (concreteInitialThetaHistory l).middle_to_target

theorem concreteInitialThetaHistory_q_eq
    (l : PrimeGeFive) :
    (concreteInitialThetaHistory l).source.theater.thetaPacket.q =
      (concreteInitialThetaHistory l).target.theater.thetaPacket.q := by
  exact (concreteInitialThetaHistory l).source_q_eq_middle.trans
    (concreteInitialThetaHistory l).middle_q_eq_target

theorem concreteInitialThetaHistory_scale_eq
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaHistory l).source.theater.thetaPacket.scale j =
      (concreteInitialThetaHistory l).target.theater.thetaPacket.scale j := by
  exact (concreteInitialThetaHistory l).source_scale_eq_middle j |>.trans
    ((concreteInitialThetaHistory l).middle_scale_eq_target j)

theorem concreteInitialThetaHistory_log_scale_eq
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    Real.log ((concreteInitialThetaHistory l).source.theater.thetaPacket.scale j) =
      Real.log ((concreteInitialThetaHistory l).target.theater.thetaPacket.scale j) := by
  rw [concreteInitialThetaHistory_scale_eq]

theorem concreteInitialThetaHistory_log_volume_eq
    (l : PrimeGeFive) :
    (concreteInitialThetaHistory l).source.theater.thetaPacket.logVolume =
      (concreteInitialThetaHistory l).target.theater.thetaPacket.logVolume := by
  rw [(concreteInitialThetaHistory l).source.theater.thetaPacket.logVolume_eq_sum,
    (concreteInitialThetaHistory l).target.theater.thetaPacket.logVolume_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact concreteInitialThetaHistory_log_scale_eq l j

theorem concreteInitialThetaHistory_scale_product_eq
    (l : PrimeGeFive) :
    (∏ j : SignedLabel l.value,
      (concreteInitialThetaHistory l).source.theater.thetaPacket.scale j) =
      ∏ j : SignedLabel l.value,
        (concreteInitialThetaHistory l).target.theater.thetaPacket.scale j := by
  apply Finset.prod_congr rfl
  intro j hj
  exact concreteInitialThetaHistory_scale_eq l j

theorem concreteInitialThetaHistory_source_q_pos
    (l : PrimeGeFive) :
    0 < (concreteInitialThetaHistory l).source.theater.thetaPacket.q := by
  exact (concreteInitialThetaHistory l).source.theater.thetaPacket.q_pos

theorem concreteInitialThetaHistory_target_q_pos
    (l : PrimeGeFive) :
    0 < (concreteInitialThetaHistory l).target.theater.thetaPacket.q := by
  exact (concreteInitialThetaHistory l).target.theater.thetaPacket.q_pos

theorem concreteInitialThetaHistory_source_scale_pos
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    0 < (concreteInitialThetaHistory l).source.theater.thetaPacket.scale j := by
  exact (concreteInitialThetaHistory l).source.theater.thetaPacket.scale_pos j

theorem concreteInitialThetaHistory_target_scale_pos
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    0 < (concreteInitialThetaHistory l).target.theater.thetaPacket.scale j := by
  exact (concreteInitialThetaHistory l).target.theater.thetaPacket.scale_pos j

theorem concreteInitialThetaHistory_source_scale_ne_zero
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaHistory l).source.theater.thetaPacket.scale j ≠ 0 := by
  exact (concreteInitialThetaHistory l).source.theater.thetaPacket.scale_ne_zero j

theorem concreteInitialThetaHistory_target_scale_ne_zero
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaHistory l).target.theater.thetaPacket.scale j ≠ 0 := by
  exact (concreteInitialThetaHistory l).target.theater.thetaPacket.scale_ne_zero j

theorem concreteInitialThetaHistory_source_scale_neg
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaHistory l).source.theater.thetaPacket.scale
        (SignedLabel.neg j) =
      (concreteInitialThetaHistory l).source.theater.thetaPacket.scale j := by
  exact (concreteInitialThetaHistory l).source.theater.thetaPacket.scale_neg j

theorem concreteInitialThetaHistory_target_scale_neg
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaHistory l).target.theater.thetaPacket.scale
        (SignedLabel.neg j) =
      (concreteInitialThetaHistory l).target.theater.thetaPacket.scale j := by
  exact (concreteInitialThetaHistory l).target.theater.thetaPacket.scale_neg j

theorem concreteInitialThetaHistory_source_to_target_q
    (l : PrimeGeFive) :
    (concreteInitialThetaHistory l).source.theater.thetaPacket.q =
      (concreteInitialThetaHistory l).target.theater.thetaPacket.q := by
  exact concreteInitialThetaHistory_q_eq l

theorem concreteInitialThetaHistory_source_to_target_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaHistory l).source.theater.thetaPacket.scale j =
      (concreteInitialThetaHistory l).target.theater.thetaPacket.scale j := by
  exact concreteInitialThetaHistory_scale_eq l j

theorem concreteInitialThetaHistory_source_to_target_log_volume
    (l : PrimeGeFive) :
    (concreteInitialThetaHistory l).source.theater.thetaPacket.logVolume =
      (concreteInitialThetaHistory l).target.theater.thetaPacket.logVolume := by
  exact concreteInitialThetaHistory_log_volume_eq l

theorem concreteInitialThetaHistory_source_to_target_scale_product
    (l : PrimeGeFive) :
    (∏ j : SignedLabel l.value,
      (concreteInitialThetaHistory l).source.theater.thetaPacket.scale j) =
      ∏ j : SignedLabel l.value,
        (concreteInitialThetaHistory l).target.theater.thetaPacket.scale j := by
  exact concreteInitialThetaHistory_scale_product_eq l

def concreteInitialThetaHistoryLink (l : PrimeGeFive) :
    HodgeTheaterLink
      (concreteInitialThetaHistory l).source.theater
      (concreteInitialThetaHistory l).target.theater where
  primeStripEquiv := by
    cases (concreteInitialThetaHistory l).source_to_middle
    cases (concreteInitialThetaHistory l).middle_to_target
    exact FPrimeStripEquiv.refl _
  theta_q_eq := concreteInitialThetaHistory_q_eq l
  theta_scale_eq := concreteInitialThetaHistory_scale_eq l

theorem concreteInitialThetaHistoryLink_log_volume (l : PrimeGeFive) :
    (concreteInitialThetaHistory l).source.theater.thetaPacket.logVolume =
      (concreteInitialThetaHistory l).target.theater.thetaPacket.logVolume := by
  exact (concreteInitialThetaHistoryLink l).log_volume_eq

theorem concreteInitialThetaHistoryLink_scale_product (l : PrimeGeFive) :
    (∏ j : SignedLabel l.value,
      (concreteInitialThetaHistory l).source.theater.thetaPacket.scale j) =
      ∏ j : SignedLabel l.value,
        (concreteInitialThetaHistory l).target.theater.thetaPacket.scale j := by
  exact (concreteInitialThetaHistoryLink l).scale_product_eq

theorem concreteInitialThetaHistoryLink_q (l : PrimeGeFive) :
    (concreteInitialThetaHistory l).source.theater.thetaPacket.q =
      (concreteInitialThetaHistory l).target.theater.thetaPacket.q := by
  exact (concreteInitialThetaHistoryLink l).theta_q_eq

theorem concreteInitialThetaHistoryLink_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (concreteInitialThetaHistory l).source.theater.thetaPacket.scale j =
      (concreteInitialThetaHistory l).target.theater.thetaPacket.scale j := by
  exact (concreteInitialThetaHistoryLink l).theta_scale_eq j

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteInitialThetaLinks : Obligation :=
  { id := "IUT-I.concrete-initial-theta-links"
    source := "IUT I, Sections 4-5; finite carrier history"
    status := VerificationStatus.testCarrier
    note :=
      "The concrete carrier has a reflexive three-theater system and an " ++
        "explicit finite history. Prime-strip equality, theta-q equality, " ++
        "scale equality, finite scale products, logarithmic scales, and " ++
        "log-volume transport are all proved in the dependent types. The " ++
        "history is deliberately not presented as the paper's anabelian " ++
        "theta-link construction."
    dependsOn := [ "IUT-I.concrete-initial-theta-carrier-transport",
      "IUT-I.hodge-theater-link-log-volume-transport" ] }

end LeanFormal.IUT.Audit
