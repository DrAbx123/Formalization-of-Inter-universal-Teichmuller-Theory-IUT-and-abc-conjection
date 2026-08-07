import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteMultiradial
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ThetaPacketBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ConcreteFiniteRouteColumns
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

local instance primeFactForSourceRouteArithmetic (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) := l.factPrime

namespace SourceFiniteRouteArithmetic

open ConcreteFiniteTheorem311
open ConcreteFiniteStepXI
open MultiradialKernel
open SourceFiniteMultiradial

abbrev Label (l : PrimeGeFive) := ConcreteFiniteTheorem311.finiteLabel l
abbrev Choice (l : PrimeGeFive) := ConcreteFiniteTheorem311.ProcessionChoice l
abbrev Step (l : PrimeGeFive) := RouteStep (Label l)

def target (l : PrimeGeFive) (route : List (Step l)) (c : Choice l) :
    Choice l :=
  applyRoute (SourceFiniteMultiradial.core l) route c

def packet (l : PrimeGeFive) (route : List (Step l)) (c : Choice l) :
    PositivePacket (SignedLabel l.value) :=
  ConcreteFiniteTheorem311.choicePacket l (target l route c)

def tensorPacket (l : PrimeGeFive) (route : List (Step l)) (c : Choice l) :
    PositivePacket (SignedLabel l.value × SignedLabel l.value) :=
  ConcreteFiniteTheorem311.choiceTensorPacket l (target l route c)

@[simp] theorem target_nil (l : PrimeGeFive) (c : Choice l) :
    target l [] c = c :=
  rfl

@[simp] theorem target_cons (l : PrimeGeFive)
    (step : Step l) (route : List (Step l)) (c : Choice l) :
    target l (step :: route) c =
      target l route (applyStep (SourceFiniteMultiradial.core l) step c) :=
  rfl

theorem target_append (l : PrimeGeFive)
    (r₁ r₂ : List (Step l)) (c : Choice l) :
    target l (r₁ ++ r₂) c = target l r₂ (target l r₁ c) :=
  applyRoute_append (SourceFiniteMultiradial.core l) r₁ r₂ c

theorem packet_scale (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) (j : SignedLabel l.value) :
    (packet l route c).scale j =
      ConcreteFiniteTheorem311.thetaScale l
        (SignedLabel.translate l (target l route c).processionLabel j) :=
  rfl

theorem packet_positive (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) (j : SignedLabel l.value) :
    0 < (packet l route c).scale j := by
  exact ConcreteFiniteTheorem311.choicePacket_positive l (target l route c) j

theorem packet_nonzero (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) (j : SignedLabel l.value) :
    (packet l route c).scale j ≠ 0 := by
  exact ne_of_gt (packet_positive l route c j)

theorem packet_logVolume (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    packetLogVolume (packet l route c) =
      ConcreteFiniteTheorem311.thetaLogVolume l :=
  ConcreteFiniteTheorem311.choicePacket_logVolume l (target l route c)

theorem packet_det (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    packetDet (packet l route c) =
      packetDet (ConcreteFiniteTheorem311.thetaPacket l) :=
  ConcreteFiniteTheorem311.choicePacket_det l (target l route c)

theorem packet_det_positive (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    0 < packetDet (packet l route c) := by
  rw [packet_det]
  exact ConcreteFiniteTheorem311.finiteOutput_theta_det_positive l

theorem packet_det_nonzero (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    packetDet (packet l route c) ≠ 0 :=
  ne_of_gt (packet_det_positive l route c)

theorem packet_log_det (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    packetLogVolume (packet l route c) =
      Real.log (packetDet (packet l route c)) :=
  packetLogVolume_eq_log_det _

theorem packet_log_det_eq_theta (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    Real.log (packetDet (packet l route c)) =
      ConcreteFiniteTheorem311.thetaLogVolume l := by
  rw [← packet_logVolume l route c]
  exact (packet_log_det l route c).symm

theorem packet_exp_log_det (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    Real.exp (ConcreteFiniteTheorem311.thetaLogVolume l) =
      packetDet (packet l route c) := by
  rw [← packet_log_det_eq_theta l route c]
  exact Real.exp_log (packet_det_positive l route c)

theorem tensorPacket_scale (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l)
    (i : SignedLabel l.value × SignedLabel l.value) :
    (tensorPacket l route c).scale i =
      (packet l route c).scale i.1 *
        (ConcreteFiniteTheorem311.translatedPacket l
          (target l route c).tensorLabel).scale i.2 :=
  rfl

theorem tensorPacket_positive (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l)
    (i : SignedLabel l.value × SignedLabel l.value) :
    0 < (tensorPacket l route c).scale i := by
  exact ConcreteFiniteTheorem311.choiceTensorPacket_positive l
    (target l route c) i

theorem tensorPacket_det (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    packetDet (tensorPacket l route c) =
      packetDet (ConcreteFiniteTheorem311.thetaPacket l) ^
          Fintype.card (SignedLabel l.value) *
        packetDet (ConcreteFiniteTheorem311.thetaPacket l) ^
          Fintype.card (SignedLabel l.value) :=
  ConcreteFiniteTheorem311.choiceTensorPacket_det l (target l route c)

theorem tensorPacket_logVolume (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    packetLogVolume (tensorPacket l route c) =
      (2 * (Fintype.card (SignedLabel l.value) : Real)) *
        ConcreteFiniteTheorem311.thetaLogVolume l :=
  ConcreteFiniteTheorem311.choiceTensorPacket_logVolume l (target l route c)

theorem tensorPacket_log_det (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    packetLogVolume (tensorPacket l route c) =
      Real.log (packetDet (tensorPacket l route c)) :=
  packetLogVolume_eq_log_det _

def rescaledPacket (l : PrimeGeFive) (route : List (Step l))
    (c : Choice l) (scale : Real) (hscale : 0 < scale) :
    PositivePacket (SignedLabel l.value) :=
  ConcreteFiniteTheorem311.rescaledChoicePacket l (target l route c)
    scale hscale

@[simp] theorem rescaledPacket_scale (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) (scale : Real) (hscale : 0 < scale)
    (j : SignedLabel l.value) :
    (rescaledPacket l route c scale hscale).scale j =
      scale * (packet l route c).scale j :=
  rfl

theorem rescaledPacket_positive (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) (scale : Real) (hscale : 0 < scale)
    (j : SignedLabel l.value) :
    0 < (rescaledPacket l route c scale hscale).scale j := by
  exact (rescaledPacket l route c scale hscale).positive j

theorem rescaledPacket_det (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) (scale : Real) (hscale : 0 < scale) :
    packetDet (rescaledPacket l route c scale hscale) =
      scale ^ Fintype.card (SignedLabel l.value) *
        packetDet (packet l route c) := by
  change packetDet (ConcreteFiniteTheorem311.rescaledChoicePacket l
    (target l route c) scale hscale) = _
  rw [ConcreteFiniteTheorem311.rescaledChoicePacket_det,
    packet_det]

theorem rescaledPacket_logVolume (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) (scale : Real) (hscale : 0 < scale) :
    packetLogVolume (rescaledPacket l route c scale hscale) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log scale +
        ConcreteFiniteTheorem311.thetaLogVolume l := by
  change packetLogVolume (ConcreteFiniteTheorem311.rescaledChoicePacket l
    (target l route c) scale hscale) = _
  exact ConcreteFiniteTheorem311.rescaledChoicePacket_logVolume l
    (target l route c) scale hscale

theorem rescaledPacket_log_det (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) (scale : Real) (hscale : 0 < scale) :
    packetLogVolume (rescaledPacket l route c scale hscale) =
      Real.log (packetDet (rescaledPacket l route c scale hscale)) :=
  packetLogVolume_eq_log_det _

def horizontalRoute (l : PrimeGeFive)
    (route : List (Step l)) : Prop :=
  ∀ step ∈ route, MultiradialKernel.horizontal step

theorem level_target_horizontal
    (l : PrimeGeFive) (route : List (Step l)) (c : Choice l)
    (hroute : horizontalRoute l route) :
    (target l route c).upperSemiLevel = c.upperSemiLevel := by
  induction route generalizing c with
  | nil => rfl
  | cons step rest ih =>
      have hs : horizontal step := hroute step (by simp)
      have hr : horizontalRoute l rest := by
        intro s hs'
        exact hroute s (by simp [hs'])
      cases step with
      | ind1 g =>
          rw [target_cons, applyStep_ind1,
            SourceFiniteMultiradial.core_ind1]
          exact ih (ProcessionChoice.ind1Act g c) hr
      | ind2 g =>
          rw [target_cons, applyStep_ind2,
            SourceFiniteMultiradial.core_ind2]
          exact ih (ProcessionChoice.ind2Act g c) hr
      | ind3 n => exact False.elim hs

theorem profile_target_horizontal
    (l : PrimeGeFive) (route : List (Step l)) (c : Choice l)
    (hroute : horizontalRoute l route) :
    (profile l).logVolume (target l route c) =
      (profile l).logVolume c := by
  exact logVolume_applyRoute_horizontal (profile l) route hroute c

theorem packet_logVolume_horizontal
    (l : PrimeGeFive) (route : List (Step l)) (c : Choice l)
    (_hroute : horizontalRoute l route) :
    packetLogVolume (packet l route c) =
      packetLogVolume (packet l [] c) := by
  rw [packet_logVolume, packet_logVolume]

theorem packet_det_horizontal
    (l : PrimeGeFive) (route : List (Step l)) (c : Choice l)
    (_hroute : horizontalRoute l route) :
    packetDet (packet l route c) = packetDet (packet l [] c) := by
  rw [packet_det, packet_det]

theorem packet_logVolume_vertical
    (l : PrimeGeFive) (n : Nat) (route : List (Step l)) (c : Choice l) :
    packetLogVolume (packet l (route ++ [.ind3 n]) c) =
      packetLogVolume (packet l route c) := by
  unfold packet
  rw [target_append, ConcreteFiniteTheorem311.choicePacket_logVolume,
    ConcreteFiniteTheorem311.choicePacket_logVolume]

theorem packet_det_vertical
    (l : PrimeGeFive) (n : Nat) (route : List (Step l)) (c : Choice l) :
    packetDet (packet l (route ++ [.ind3 n]) c) =
      packetDet (packet l route c) := by
  unfold packet
  rw [target_append, ConcreteFiniteTheorem311.choicePacket_det,
    ConcreteFiniteTheorem311.choicePacket_det]

def profilePacketGap (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) : Real :=
  (profile l).logVolume (target l route c) -
    packetLogVolume (packet l route c)

theorem profilePacketGap_eq_level (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    profilePacketGap l route c =
      ((target l route c).upperSemiLevel : Real) := by
  unfold profilePacketGap
  rw [profile_logVolume_formula, packet_logVolume]
  ring

theorem profilePacketGap_nonnegative (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    0 ≤ profilePacketGap l route c := by
  rw [profilePacketGap_eq_level]
  exact_mod_cast Nat.zero_le (target l route c).upperSemiLevel

theorem profilePacketGap_horizontal (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l)
    (hroute : horizontalRoute l route) :
    profilePacketGap l route c = (c.upperSemiLevel : Real) := by
  rw [profilePacketGap_eq_level, level_target_horizontal l route c hroute]

theorem profilePacketGap_vertical (l : PrimeGeFive)
    (n : Nat) (route : List (Step l)) (c : Choice l) :
    profilePacketGap l (route ++ [.ind3 n]) c =
      profilePacketGap l route c + n := by
  rw [profilePacketGap_eq_level, profilePacketGap_eq_level,
    target_append, target_cons, target_nil, applyStep_ind3,
    SourceFiniteMultiradial.core_ind3,
    ProcessionChoice.ind3_upperSemiLevel]
  push_cast
  ring

def routeArithmeticCertificate (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    StepXIFiniteCertificate (FiniteColumnIndex l
      (route.length + c.upperSemiLevel)) :=
  finiteColumnCertificate l (route.length + c.upperSemiLevel)

theorem routeCertificate_hull_bound (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (routeArithmeticCertificate l route c).weighted.average ≤
      (routeArithmeticCertificate l route c).hull.hullVolume := by
  exact FiniteHull.average_le
    (routeArithmeticCertificate l route c).hull
    (routeArithmeticCertificate l route c).weighted
    (routeArithmeticCertificate l route c).weighted_matches_hull
    (routeArithmeticCertificate l route c).weights_nonnegative

theorem routeCertificate_q_bound (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (routeArithmeticCertificate l route c).qSigned ≤
      (routeArithmeticCertificate l route c).hull.hullVolume := by
  exact (routeArithmeticCertificate l route c).q_le_hull

theorem routeCertificate_theta_bound (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (routeArithmeticCertificate l route c).hull.hullVolume ≤
      (routeArithmeticCertificate l route c).thetaSigned := by
  exact (routeArithmeticCertificate l route c).hull_le_theta

theorem routeCertificate_q_theta_bound (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (routeArithmeticCertificate l route c).qSigned ≤
      (routeArithmeticCertificate l route c).thetaSigned := by
  exact le_trans (routeCertificate_q_bound l route c)
    (routeCertificate_theta_bound l route c)

theorem routeCertificate_q_negative (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (routeArithmeticCertificate l route c).qSigned < 0 := by
  exact (routeArithmeticCertificate l route c).q_negative

theorem routeCertificate_q_positive (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    0 < -(routeArithmeticCertificate l route c).qSigned := by
  exact neg_pos.mpr (routeCertificate_q_negative l route c)

theorem route_profile_packet_bound (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (profile l).logVolume c ≤
      (profile l).logVolume (target l route c) := by
  exact logVolume_applyRoute_le (SourceFiniteMultiradial.core l)
    (profile l) route c

theorem route_profile_packet_horizontal (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l)
    (hroute : horizontalRoute l route) :
    (profile l).logVolume (target l route c) =
      (profile l).logVolume c :=
  profile_target_horizontal l route c hroute

theorem route_profile_packet_vertical (l : PrimeGeFive)
    (n : Nat) (route : List (Step l)) (c : Choice l) :
    (profile l).logVolume (target l (route ++ [.ind3 n]) c) =
      (profile l).logVolume (target l route c) + n := by
  rw [profile_logVolume_formula, profile_logVolume_formula, target_append,
    target_cons, target_nil, applyStep_ind3,
    SourceFiniteMultiradial.core_ind3,
    ProcessionChoice.ind3_upperSemiLevel]
  push_cast
  ring

structure RouteCertificate (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) where
  target : Choice l
  target_eq : target = SourceFiniteRouteArithmetic.target l route c
  packet_det_positive : 0 < packetDet (packet l route c)
  packet_log_det_eq_theta :
    Real.log (packetDet (packet l route c)) =
      ConcreteFiniteTheorem311.thetaLogVolume l
  profile_gap : profilePacketGap l route c = (target.upperSemiLevel : Real)
  profile_upper : (profile l).logVolume c ≤
    (profile l).logVolume target

def routeCertificate (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    RouteCertificate l route c where
  target := target l route c
  target_eq := rfl
  packet_det_positive := packet_det_positive l route c
  packet_log_det_eq_theta := packet_log_det_eq_theta l route c
  profile_gap := by
    rw [profilePacketGap_eq_level]
  profile_upper := route_profile_packet_bound l route c

theorem routeCertificate_target (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (routeCertificate l route c).target = target l route c :=
  rfl

theorem routeCertificate_packet_positive (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    0 < packetDet (packet l route c) :=
  (routeCertificate l route c).packet_det_positive

theorem routeCertificate_packet_log_det (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    Real.log (packetDet (packet l route c)) =
      ConcreteFiniteTheorem311.thetaLogVolume l :=
  (routeCertificate l route c).packet_log_det_eq_theta

theorem routeCertificate_gap (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    profilePacketGap l route c =
      ((routeCertificate l route c).target.upperSemiLevel : Real) := by
  rw [routeCertificate_target]
  exact profilePacketGap_eq_level l route c

theorem routeCertificate_profile_upper (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (profile l).logVolume c ≤
      (profile l).logVolume (routeCertificate l route c).target :=
  (routeCertificate l route c).profile_upper

end SourceFiniteRouteArithmetic

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteSourceRouteArithmetic : Obligation :=
  { id := "IUT-III.concrete-source-route-arithmetic"
    source := "IUT III, Theorem 3.11 and Step XI arithmetic boundary"
    status := VerificationStatus.interface
    note :=
      "Every finite route is connected to the concrete positive theta packet, " ++
        "tensor packet, determinant, logarithmic volume, rescaling, and the " ++
        "finite hull certificate. The profile minus packet volume is exactly the " ++
        "upper-semi level. This is a finite arithmetic certificate, not the " ++
        "source-faithful arbitrary Hodge-theater conclusion."
    dependsOn :=
      [ "IUT-III.concrete-source-multiradial-kernel",
        "IUT-III.finite-certificate-to-contract",
        "IUT-III.holomorphic-hull-determinant-log-volume" ] }

end LeanFormal.IUT.Audit
