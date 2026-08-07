import LeanFormal.IUT.IUTIII.Theorem311.ConcreteRouteNormalForm
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteRouteArithmetic
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceProcessionStepXI
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

namespace SourceRouteDeterminantNormalization

open ConcreteFiniteTheorem311
open ConcreteFiniteStepXI
open ConcreteRouteNormalForm
open SourceFiniteRouteArithmetic
open SourceFiniteRouteNaturality
open SourceFiniteMultiradial
open MultiradialKernel
open MultiradialKernel.Core

local instance primeFactForNormalization (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) := l.factPrime

abbrev Label (l : PrimeGeFive) := ConcreteFiniteTheorem311.finiteLabel l
abbrev Choice (l : PrimeGeFive) := ConcreteFiniteTheorem311.ProcessionChoice l
abbrev Step (l : PrimeGeFive) := RouteStep (Label l)

def normalizedRoute (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) : List (Step l) :=
  ConcreteRouteNormalForm.normalizedRoute route c

theorem normalizedRoute_eq (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    normalizedRoute l route c =
      sameLevelRoute c
        (ConcreteRouteNormalForm.horizontalTarget route c) ++
        [.ind3 (ParametricTheorem311.verticalBudget route)] :=
  rfl

theorem normalizedRoute_budget (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    ParametricTheorem311.verticalBudget (normalizedRoute l route c) =
      ParametricTheorem311.verticalBudget route :=
  ConcreteRouteNormalForm.normalizedRoute_budget route c

theorem normalizedRoute_target (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    target l (normalizedRoute l route c) c = target l route c :=
  ConcreteRouteNormalForm.normalizedRoute_target route c

theorem normalizedRoute_level (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (target l (normalizedRoute l route c) c).upperSemiLevel =
      c.upperSemiLevel + ParametricTheorem311.verticalBudget route := by
  rw [normalizedRoute_target]
  exact ConcreteRouteNormalForm.normalized_target_level route c

theorem normalizedRoute_packet_logVolume (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    packetLogVolume (packet l (normalizedRoute l route c) c) =
      packetLogVolume (packet l route c) := by
  calc
    packetLogVolume (packet l (normalizedRoute l route c) c) =
        ConcreteFiniteTheorem311.thetaLogVolume l :=
      packet_logVolume l (normalizedRoute l route c) c
    _ = packetLogVolume (packet l route c) :=
      (packet_logVolume l route c).symm

theorem normalizedRoute_packet_det (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    packetDet (packet l (normalizedRoute l route c) c) =
      packetDet (packet l route c) := by
  calc
    packetDet (packet l (normalizedRoute l route c) c) =
        packetDet (ConcreteFiniteTheorem311.thetaPacket l) :=
      packet_det l (normalizedRoute l route c) c
    _ = packetDet (packet l route c) :=
      (packet_det l route c).symm

theorem normalizedRoute_profilePacketGap (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    profilePacketGap l (normalizedRoute l route c) c =
      profilePacketGap l route c := by
  rw [profilePacketGap_eq_level, profilePacketGap_eq_level,
    normalizedRoute_target]

theorem normalizedRoute_profile_upper (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (profile l).logVolume c ≤
      (profile l).logVolume (target l (normalizedRoute l route c) c) := by
  rw [normalizedRoute_target]
  exact route_profile_packet_bound l route c

theorem normalizedRoute_packet_positive (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    0 < packetDet (packet l (normalizedRoute l route c) c) := by
  rw [normalizedRoute_packet_det]
  exact packet_det_positive l route c

theorem normalizedRoute_log_det (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    Real.log (packetDet (packet l (normalizedRoute l route c) c)) =
      ConcreteFiniteTheorem311.thetaLogVolume l := by
  rw [normalizedRoute_packet_det]
  exact packet_log_det_eq_theta l route c

def normalizedTensorPacket (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
  PositivePacket (SignedLabel l.value × SignedLabel l.value) :=
  SourceFiniteRouteArithmetic.tensorPacket l (normalizedRoute l route c) c

theorem normalizedTensorPacket_det (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    packetDet (normalizedTensorPacket l route c) =
      packetDet (ConcreteFiniteTheorem311.thetaPacket l) ^
          Fintype.card (SignedLabel l.value) *
      packetDet (ConcreteFiniteTheorem311.thetaPacket l) ^
          Fintype.card (SignedLabel l.value) := by
  simpa [normalizedTensorPacket] using
    (SourceFiniteRouteArithmetic.tensorPacket_det l
      (normalizedRoute l route c) c)

theorem normalizedTensorPacket_logVolume (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    packetLogVolume (normalizedTensorPacket l route c) =
      (2 * (Fintype.card (SignedLabel l.value) : Real)) *
        ConcreteFiniteTheorem311.thetaLogVolume l := by
  simpa [normalizedTensorPacket] using
    (SourceFiniteRouteArithmetic.tensorPacket_logVolume l
      (normalizedRoute l route c) c)

theorem normalizedTensorPacket_log_det (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    packetLogVolume (normalizedTensorPacket l route c) =
      Real.log (packetDet (normalizedTensorPacket l route c)) := by
  simpa [normalizedTensorPacket] using
    (SourceFiniteRouteArithmetic.tensorPacket_log_det l
      (normalizedRoute l route c) c)

def normalizedRescaledPacket (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) (scale : Real) (hscale : 0 < scale) :
    PositivePacket (SignedLabel l.value) :=
  rescaledPacket l (normalizedRoute l route c) c scale hscale

theorem normalizedRescaledPacket_scale (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) (scale : Real) (hscale : 0 < scale)
    (j : SignedLabel l.value) :
    (normalizedRescaledPacket l route c scale hscale).scale j =
      scale * (packet l (normalizedRoute l route c) c).scale j :=
  rescaledPacket_scale l (normalizedRoute l route c) c scale hscale j

theorem normalizedRescaledPacket_det (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) (scale : Real) (hscale : 0 < scale) :
    packetDet (normalizedRescaledPacket l route c scale hscale) =
      scale ^ Fintype.card (SignedLabel l.value) *
        packetDet (packet l route c) := by
  rw [normalizedRescaledPacket, rescaledPacket_det,
    normalizedRoute_packet_det]

theorem normalizedRescaledPacket_logVolume (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) (scale : Real) (hscale : 0 < scale) :
    packetLogVolume (normalizedRescaledPacket l route c scale hscale) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log scale +
        ConcreteFiniteTheorem311.thetaLogVolume l := by
  exact rescaledPacket_logVolume l (normalizedRoute l route c) c scale hscale

theorem normalizedRescaledPacket_log_det (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) (scale : Real) (hscale : 0 < scale) :
    packetLogVolume (normalizedRescaledPacket l route c scale hscale) =
      Real.log (packetDet (normalizedRescaledPacket l route c scale hscale)) :=
  rescaledPacket_log_det l (normalizedRoute l route c) c scale hscale

def finiteHullCertificate (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    StepXIFiniteCertificate (FiniteColumnIndex l
      (route.length + c.upperSemiLevel)) :=
  routeArithmeticCertificate l route c

theorem finiteHullCertificate_average_le (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (finiteHullCertificate l route c).weighted.average ≤
      (finiteHullCertificate l route c).hull.hullVolume :=
  routeCertificate_hull_bound l route c

theorem finiteHullCertificate_q_le (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (finiteHullCertificate l route c).qSigned ≤
      (finiteHullCertificate l route c).hull.hullVolume :=
  routeCertificate_q_bound l route c

theorem finiteHullCertificate_hull_le_theta (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (finiteHullCertificate l route c).hull.hullVolume ≤
      (finiteHullCertificate l route c).thetaSigned :=
  routeCertificate_theta_bound l route c

theorem finiteHullCertificate_q_le_theta (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (finiteHullCertificate l route c).qSigned ≤
      (finiteHullCertificate l route c).thetaSigned :=
  routeCertificate_q_theta_bound l route c

theorem finiteHullCertificate_q_negative (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (finiteHullCertificate l route c).qSigned < 0 :=
  routeCertificate_q_negative l route c

theorem finiteHullCertificate_q_positive (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    0 < -(finiteHullCertificate l route c).qSigned :=
  routeCertificate_q_positive l route c

structure NormalizedArithmeticCertificate (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) where
  routeCertificate : RouteCertificate l route c
  normalForm : ConcreteRouteNormalForm.NormalFormCertificate l route c
  tensorDet : packetDet (normalizedTensorPacket l route c) =
      packetDet (ConcreteFiniteTheorem311.thetaPacket l) ^
          Fintype.card (SignedLabel l.value) *
        packetDet (ConcreteFiniteTheorem311.thetaPacket l) ^
          Fintype.card (SignedLabel l.value)
  packetLogDet : Real.log
      (packetDet (packet l (normalizedRoute l route c) c)) =
      ConcreteFiniteTheorem311.thetaLogVolume l
  hullBound : (finiteHullCertificate l route c).qSigned ≤
      (finiteHullCertificate l route c).thetaSigned

def normalizedArithmeticCertificate (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    NormalizedArithmeticCertificate l route c where
  routeCertificate := routeCertificate l route c
  normalForm := ConcreteRouteNormalForm.normalFormCertificate route c
  tensorDet := normalizedTensorPacket_det l route c
  packetLogDet := normalizedRoute_log_det l route c
  hullBound := finiteHullCertificate_q_le_theta l route c

theorem normalizedArithmeticCertificate_route (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (normalizedArithmeticCertificate l route c).routeCertificate.target =
      target l route c :=
  routeCertificate_target l route c

theorem normalizedArithmeticCertificate_normalForm (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    target l route c =
      ProcessionChoice.ind3Lift (ParametricTheorem311.verticalBudget route)
        (ConcreteRouteNormalForm.horizontalTarget route c) := by
  exact ConcreteRouteNormalForm.normalFormCertificate_target route c

theorem normalizedArithmeticCertificate_tensor (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (normalizedArithmeticCertificate l route c).tensorDet =
      (normalizedTensorPacket_det l route c) := rfl

theorem normalizedArithmeticCertificate_log (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (normalizedArithmeticCertificate l route c).packetLogDet =
      normalizedRoute_log_det l route c := rfl

theorem normalizedArithmeticCertificate_hull (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (finiteHullCertificate l route c).qSigned ≤
      (finiteHullCertificate l route c).thetaSigned := by
  exact finiteHullCertificate_q_le_theta l route c

theorem normalizedArithmeticCertificate_zero (l : PrimeGeFive) :
    (normalizedArithmeticCertificate l [] ProcessionChoice.base).normalForm.budget = 0 := by
  simp [normalizedArithmeticCertificate, ConcreteRouteNormalForm.normalFormCertificate,
    ConcreteRouteNormalForm.normalizedRoute]

end SourceRouteDeterminantNormalization

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def sourceRouteDeterminantNormalization : Obligation :=
  { id := "IUT-III.StepXI.source-route-determinant-normalization"
    source := "IUT III, Steps XI-(d)-(g)"
    status := VerificationStatus.proved
    note :=
      "For every finite route, the normalized horizontal-plus-vertical route " ++
        "has the same target, packet determinant, log-volume, tensor determinant, " ++
        "rescaling law, and finite holomorphic-hull bounds. The finite arithmetic " ++
        "certificate is explicit and has no extra axiom; it does not assert the " ++
        "arbitrary source Hodge-theater Step-XI construction."
    dependsOn :=
      [ "IUT-III.concrete-route-normal-form",
        "IUT-III.concrete-source-route-arithmetic",
        "IUT-III.source-procession-stepXI-boundary" ] }

end LeanFormal.IUT.Audit
