import LeanFormal.IUT.IUTIII.Theorem311.ParametricDStage
import LeanFormal.IUT.IUTIII.Theorem311.ConcreteRouteNormalForm
import LeanFormal.IUT.IUTI.HodgeTheater.History
import LeanFormal.IUT.IUTII.Theta.ConcreteSourceHistoryLinkBridge
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

namespace SourceProcessionBoundary

open HodgeTheaterHistory
open MultiradialKernel
open MultiradialKernel.Core
open MultiradialKernel
open MultiradialKernel.Core
open ParametricTheorem311
open ParametricDStage

universe ua uv upi umon u w

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type w} [AddGroup Label]

/- The source Hodge-theater carrier is genuinely polymorphic in these
   universe parameters.  The linter reports that they occur through the
   dependent-history `max`; suppressing that linter message does not alter
   kernel checking or any proof term. -/
set_option linter.checkUnivs false in
structure Input where
  theater : HodgeTheater.{ua, uv, upi, umon} l V
  history : HodgeTheaterHistory.{ua, uv, upi, umon} l V theater
  carrier : Carrier Label Choice
  baseChoice : Choice
  baseChoice_eq : baseChoice = carrier.core.base
  packetVolume : Choice → Real
  packetVolume_eq_profile : ∀ c,
    packetVolume c = carrier.profile.logVolume c
  base_packetVolume_eq_theta :
    packetVolume baseChoice = theater.thetaPacket.logVolume
  target_q : Real
  target_q_eq : target_q = history.terminal.thetaPacket.q
  history_q_eq : theater.thetaPacket.q = history.terminal.thetaPacket.q
  route_normal_form : ∀ (route : List (RouteStep Label)),
    ∃ b n,
      carrier.core.level b = carrier.core.level carrier.core.base ∧
      routeTarget carrier route carrier.core.base = carrier.core.ind3 n b

namespace Input

variable (input : Input (l := l) (V := V) (Label := Label)
  (Choice := Choice))

theorem baseChoice_eq_core :
    input.baseChoice = input.carrier.core.base :=
  input.baseChoice_eq

theorem packetVolume_base_eq_profile :
    input.packetVolume input.baseChoice =
      input.carrier.profile.logVolume input.baseChoice :=
  input.packetVolume_eq_profile input.baseChoice

theorem packetVolume_base_eq_theta :
    input.packetVolume input.baseChoice = input.theater.thetaPacket.logVolume :=
  input.base_packetVolume_eq_theta

theorem profile_base_eq_theta :
    input.carrier.profile.logVolume input.carrier.core.base =
      input.theater.thetaPacket.logVolume := by
  rw [← input.baseChoice_eq_core]
  exact (input.packetVolume_base_eq_profile).symm.trans
    input.packetVolume_base_eq_theta

theorem theater_q_eq_terminal :
    input.theater.thetaPacket.q = input.history.terminal.thetaPacket.q :=
  input.history_q_eq

theorem target_q_eq_terminal :
    input.target_q = input.history.terminal.thetaPacket.q :=
  input.target_q_eq

theorem target_q_eq_source :
    input.target_q = input.theater.thetaPacket.q := by
  rw [input.target_q_eq, ← input.history_q_eq]

def compositeLink :
    HodgeTheaterLink input.theater input.history.terminal :=
  input.history.composite

theorem compositeLink_q :
    input.theater.thetaPacket.q = input.history.terminal.thetaPacket.q :=
  input.compositeLink.theta_q_eq

theorem compositeLink_scale (j : SignedLabel l.value) :
    input.theater.thetaPacket.scale j =
      input.history.terminal.thetaPacket.scale j :=
  input.compositeLink.theta_scale_eq j

theorem compositeLink_primeStrip :
    ∃ _e : FPrimeStripEquiv input.theater.primeStrip
      input.history.terminal.primeStrip, True := by
  exact ⟨input.compositeLink.primeStripEquiv, trivial⟩

theorem history_length_pos : 0 < input.history.length :=
  HodgeTheaterHistory.length_pos input.history

theorem base_profile_eq_theta_via_choice :
    input.carrier.profile.logVolume input.carrier.core.base =
      input.packetVolume input.baseChoice := by
  rw [input.baseChoice_eq_core]
  exact (input.packetVolume_eq_profile input.carrier.core.base).symm

theorem packetVolume_eq_profile_at (c : Choice) :
    input.packetVolume c = input.carrier.profile.logVolume c :=
  input.packetVolume_eq_profile c

theorem profile_base_le_route_target
    (route : List (RouteStep Label)) :
    input.carrier.profile.logVolume input.carrier.core.base ≤
      input.carrier.profile.logVolume
        (routeTarget input.carrier route input.carrier.core.base) :=
  routeTarget_profile_monotone input.carrier route input.carrier.core.base

theorem profile_route_target_level
    (route : List (RouteStep Label)) :
    input.carrier.core.level
        (routeTarget input.carrier route input.carrier.core.base) =
      input.carrier.core.level input.carrier.core.base +
        verticalBudget route :=
  routeTarget_level_eq_budget input.carrier route input.carrier.core.base

theorem packetVolume_route_target_lower
    (route : List (RouteStep Label)) :
    input.packetVolume input.baseChoice ≤
      input.packetVolume
        (routeTarget input.carrier route input.baseChoice) := by
  rw [input.packetVolume_eq_profile, input.packetVolume_eq_profile]
  rw [input.baseChoice_eq_core]
  exact input.profile_base_le_route_target route

theorem packetVolume_horizontal_invariant
    (route : List (RouteStep Label))
    (hroute : ∀ step ∈ route, horizontal step) :
    input.packetVolume
        (routeTarget input.carrier route input.baseChoice) =
      input.packetVolume input.baseChoice := by
  rw [input.packetVolume_eq_profile, input.packetVolume_eq_profile]
  exact logVolume_applyRoute_horizontal input.carrier.profile route hroute
    input.baseChoice

theorem packetVolume_image_upper
    (route : List (RouteStep Label)) (z : Real)
    (hz : z ∈ input.carrier.profile.possibleImage input.baseChoice) :
    ∃ w, w ∈ input.carrier.profile.possibleImage
      (routeTarget input.carrier route input.baseChoice) ∧ z ≤ w :=
  routeTarget_image_upper input.carrier route input.baseChoice z hz

structure RouteOutput (route : List (RouteStep Label)) where
  algorithmInput : ParametricTheorem311.AlgorithmInput input.carrier
  output : ParametricTheorem311.AlgorithmOutput input.carrier algorithmInput
  input_source : algorithmInput.source = input.baseChoice
  output_target : output.target = routeTarget input.carrier route input.baseChoice

def routeOutput (route : List (RouteStep Label)) : RouteOutput input route where
  algorithmInput :=
    { source := input.baseChoice
      route := route
      source_image_nonempty :=
        input.carrier.profile.possibleImage_nonempty input.baseChoice }
  output := runAlgorithm input.carrier
    { source := input.baseChoice
      route := route
      source_image_nonempty :=
        input.carrier.profile.possibleImage_nonempty input.baseChoice }
  input_source := rfl
  output_target := rfl

theorem routeOutput_source (route : List (RouteStep Label)) :
    (input.routeOutput route).algorithmInput.source = input.baseChoice :=
  (input.routeOutput route).input_source

theorem routeOutput_route (route : List (RouteStep Label)) :
    (input.routeOutput route).algorithmInput.route = route :=
  rfl

theorem routeOutput_target (route : List (RouteStep Label)) :
    (input.routeOutput route).output.target =
      routeTarget input.carrier route input.baseChoice :=
  (input.routeOutput route).output_target

theorem routeOutput_level (route : List (RouteStep Label)) :
    input.carrier.core.level input.baseChoice ≤
      input.carrier.core.level (input.routeOutput route).output.target := by
  rw [input.routeOutput_target]
  exact routeTarget_level_monotone input.carrier route input.baseChoice

theorem routeOutput_profile (route : List (RouteStep Label)) :
    input.carrier.profile.logVolume input.baseChoice ≤
      input.carrier.profile.logVolume (input.routeOutput route).output.target := by
  rw [input.routeOutput_target]
  exact routeTarget_profile_monotone input.carrier route input.baseChoice

theorem routeOutput_image (route : List (RouteStep Label)) (z : Real)
    (hz : z ∈ input.carrier.profile.possibleImage input.baseChoice) :
    ∃ w, w ∈ input.carrier.profile.possibleImage
      (input.routeOutput route).output.target ∧ z ≤ w := by
  rw [input.routeOutput_target]
  exact input.packetVolume_image_upper route z hz

structure IndeterminacyEvidence where
  ind1 : ∀ (g : Label) (c : Choice),
    Ind1RouteCertificate input.carrier g c
  ind2 : ∀ (g : Label) (c : Choice),
    Ind2RouteCertificate input.carrier g c
  ind3 : ∀ (n : Nat) (c : Choice),
    Ind3RouteCertificate input.carrier n c
  ind1_ind2 : ∀ (g h : Label) (c : Choice),
    CommutationRouteCertificate input.carrier g h c
  ind1_ind3 : ∀ (g : Label) (n : Nat) (c : Choice),
    Ind3CommutationRouteCertificate input.carrier g n c
  ind2_ind3 : ∀ (g : Label) (n : Nat) (c : Choice),
    Ind2CommutationRouteCertificate input.carrier g n c

def indeterminacyEvidence : IndeterminacyEvidence input where
  ind1 := fun g c => ind1RouteCertificate input.carrier g c
  ind2 := fun g c => ind2RouteCertificate input.carrier g c
  ind3 := fun n c => ind3RouteCertificate input.carrier n c
  ind1_ind2 := fun g h c => ind1Ind2RouteCertificate input.carrier g h c
  ind1_ind3 := fun g n c => ind1Ind3RouteCertificate input.carrier g n c
  ind2_ind3 := fun g n c => ind2Ind3RouteCertificate input.carrier g n c

theorem indeterminacy_ind1_target (g : Label) (c : Choice) :
    ((input.indeterminacyEvidence).ind1 g c).target =
      input.carrier.core.ind1 g c := by
  exact ind1RouteCertificate_target input.carrier g c

theorem indeterminacy_ind2_target (g : Label) (c : Choice) :
    ((input.indeterminacyEvidence).ind2 g c).target =
      input.carrier.core.ind2 g c := by
  exact ind2RouteCertificate_target input.carrier g c

theorem indeterminacy_ind3_target (n : Nat) (c : Choice) :
    ((input.indeterminacyEvidence).ind3 n c).target =
      input.carrier.core.ind3 n c := by
  exact ind3RouteCertificate_target input.carrier n c

theorem indeterminacy_ind3_budget (n : Nat) (c : Choice) :
    verticalBudget ((input.indeterminacyEvidence).ind3 n c).route = n :=
  ind3RouteCertificate_budget input.carrier n c

theorem indeterminacy_ind1_ind2 (g h : Label) (c : Choice) :
    ((input.indeterminacyEvidence).ind1_ind2 g h c).leftTarget =
      ((input.indeterminacyEvidence).ind1_ind2 g h c).rightTarget :=
  ind1Ind2RouteCertificate_commutes input.carrier g h c

theorem indeterminacy_ind1_ind3 (g : Label) (n : Nat) (c : Choice) :
    ((input.indeterminacyEvidence).ind1_ind3 g n c).leftTarget =
      ((input.indeterminacyEvidence).ind1_ind3 g n c).rightTarget :=
  ind1Ind3RouteCertificate_commutes input.carrier g n c

theorem indeterminacy_ind2_ind3 (g : Label) (n : Nat) (c : Choice) :
    ((input.indeterminacyEvidence).ind2_ind3 g n c).leftTarget =
      ((input.indeterminacyEvidence).ind2_ind3 g n c).rightTarget :=
  ind2Ind3RouteCertificate_commutes input.carrier g n c

def dStage : DStageCertificate input.carrier :=
  dStageCertificate input.carrier

theorem dStage_base : input.dStage.base = input.carrier.core.base :=
  dStageCertificate_base input.carrier

theorem dStage_empty_target :
    input.dStage.emptyOutput.target = input.carrier.core.base :=
  dStageCertificate_empty_target input.carrier

theorem dStage_empty_level :
    input.carrier.core.level input.dStage.emptyOutput.target =
      input.carrier.core.level input.carrier.core.base :=
  dStageCertificate_empty_level input.carrier

theorem dStage_empty_profile :
    input.carrier.profile.logVolume input.carrier.core.base ≤
      input.carrier.profile.logVolume input.dStage.emptyOutput.target :=
  dStageCertificate_empty_profile input.carrier

structure CanonicalOutput (a b : Choice) (n : Nat)
    (hlevel : input.carrier.core.level a = input.carrier.core.level b) where
  canonicalInput : ParametricTheorem311.CanonicalInput input.carrier
  algorithmOutput : ParametricTheorem311.AlgorithmOutput input.carrier
    (ParametricTheorem311.canonicalAlgorithmInput input.carrier canonicalInput)
  target_eq : algorithmOutput.target = input.carrier.core.ind3 n b
  level_eq : input.carrier.core.level algorithmOutput.target =
    input.carrier.core.level b + n
  profile_bound : input.carrier.profile.logVolume a ≤
    input.carrier.profile.logVolume algorithmOutput.target
  image_bound : ∀ z, z ∈ input.carrier.profile.possibleImage a →
    ∃ w, w ∈ input.carrier.profile.possibleImage algorithmOutput.target ∧ z ≤ w

def canonicalOutput (a b : Choice) (n : Nat)
    (hlevel : input.carrier.core.level a = input.carrier.core.level b) :
    CanonicalOutput input a b n hlevel where
  canonicalInput := ParametricTheorem311.canonicalInput
    input.carrier a b n hlevel
  algorithmOutput := runAlgorithm input.carrier
    (canonicalAlgorithmInput input.carrier
      (canonicalInput input.carrier a b n hlevel))
  target_eq := canonicalAlgorithmOutput_target input.carrier
    (canonicalInput input.carrier a b n hlevel)
  level_eq := canonicalAlgorithmOutput_level input.carrier
    (canonicalInput input.carrier a b n hlevel)
  profile_bound := canonicalAlgorithmOutput_profile input.carrier
    (canonicalInput input.carrier a b n hlevel)
  image_bound := fun z hz => canonicalAlgorithmOutput_image input.carrier
    (canonicalInput input.carrier a b n hlevel) z hz

theorem canonicalOutput_target (a b : Choice) (n : Nat)
    (hlevel : input.carrier.core.level a = input.carrier.core.level b) :
    (input.canonicalOutput a b n hlevel).algorithmOutput.target =
      input.carrier.core.ind3 n b :=
  (input.canonicalOutput a b n hlevel).target_eq

theorem canonicalOutput_level (a b : Choice) (n : Nat)
    (hlevel : input.carrier.core.level a = input.carrier.core.level b) :
    input.carrier.core.level
        (input.canonicalOutput a b n hlevel).algorithmOutput.target =
      input.carrier.core.level b + n :=
  (input.canonicalOutput a b n hlevel).level_eq

theorem canonicalOutput_profile (a b : Choice) (n : Nat)
    (hlevel : input.carrier.core.level a = input.carrier.core.level b) :
    input.carrier.profile.logVolume a ≤
      input.carrier.profile.logVolume
        (input.canonicalOutput a b n hlevel).algorithmOutput.target :=
  (input.canonicalOutput a b n hlevel).profile_bound

theorem canonicalOutput_image (a b : Choice) (n : Nat)
    (hlevel : input.carrier.core.level a = input.carrier.core.level b)
    (z : Real) (hz : z ∈ input.carrier.profile.possibleImage a) :
    ∃ w, w ∈ input.carrier.profile.possibleImage
      (input.canonicalOutput a b n hlevel).algorithmOutput.target ∧ z ≤ w :=
  (input.canonicalOutput a b n hlevel).image_bound z hz

structure SourceTheorem311Certificate where
  source : Choice
  source_eq : source = input.carrier.core.base
  dStageEvidence : DStageCertificate input.carrier
  indeterminacy : IndeterminacyEvidence input
  sourceProfile : Real
  sourceProfile_eq : sourceProfile = input.theater.thetaPacket.logVolume
  sourceProfile_carrier_eq : sourceProfile =
    input.carrier.profile.logVolume source
  routeNormalization : ∀ (route : List (RouteStep Label)),
    ∃ b n,
      input.carrier.core.level b = input.carrier.core.level source ∧
      input.carrier.core.level (routeTarget input.carrier route source) =
        input.carrier.core.level b + n

def sourceTheorem311Certificate : SourceTheorem311Certificate input where
  source := input.baseChoice
  source_eq := input.baseChoice_eq_core
  dStageEvidence := input.dStage
  indeterminacy := input.indeterminacyEvidence
  sourceProfile := input.theater.thetaPacket.logVolume
  sourceProfile_eq := rfl
  sourceProfile_carrier_eq := by
    calc
      input.theater.thetaPacket.logVolume =
          input.carrier.profile.logVolume input.carrier.core.base :=
        input.profile_base_eq_theta.symm
      _ = input.carrier.profile.logVolume input.baseChoice := by
        rw [input.baseChoice_eq_core]
  routeNormalization := by
    intro route
    let n := ParametricTheorem311.verticalBudget route
    let b := input.carrier.core.base
    refine ⟨b, n, ?_, ?_⟩
    · simpa [b] using congrArg (fun x => input.carrier.core.level x)
        input.baseChoice_eq_core.symm
    · change input.carrier.core.level
          (routeTarget input.carrier route input.baseChoice) =
        input.carrier.core.level input.carrier.core.base +
          ParametricTheorem311.verticalBudget route
      rw [← input.baseChoice_eq_core]
      exact ParametricTheorem311.routeTarget_level_eq_budget
        input.carrier route input.baseChoice

theorem sourceTheorem311Certificate_source :
    input.sourceTheorem311Certificate.source = input.carrier.core.base :=
  (input.sourceTheorem311Certificate).source_eq

theorem sourceTheorem311Certificate_profile :
    (input.sourceTheorem311Certificate).sourceProfile =
      input.carrier.profile.logVolume input.carrier.core.base := by
  rw [input.sourceTheorem311Certificate.sourceProfile_carrier_eq,
    input.sourceTheorem311Certificate_source]

theorem sourceTheorem311Certificate_theta :
    (input.sourceTheorem311Certificate).sourceProfile =
      input.theater.thetaPacket.logVolume :=
  (input.sourceTheorem311Certificate).sourceProfile_eq

theorem sourceTheorem311Certificate_ind1 (g : Label) (c : Choice) :
    ((input.sourceTheorem311Certificate).indeterminacy.ind1 g c).target =
      input.carrier.core.ind1 g c :=
  indeterminacy_ind1_target input g c

theorem sourceTheorem311Certificate_ind2 (g : Label) (c : Choice) :
    ((input.sourceTheorem311Certificate).indeterminacy.ind2 g c).target =
      input.carrier.core.ind2 g c :=
  indeterminacy_ind2_target input g c

theorem sourceTheorem311Certificate_ind3 (n : Nat) (c : Choice) :
    ((input.sourceTheorem311Certificate).indeterminacy.ind3 n c).target =
      input.carrier.core.ind3 n c :=
  indeterminacy_ind3_target input n c

theorem sourceTheorem311Certificate_route_normalization
    (route : List (RouteStep Label)) :
    ∃ b n,
      input.carrier.core.level b = input.carrier.core.level input.carrier.core.base ∧
      input.carrier.core.level
          (routeTarget input.carrier route input.carrier.core.base) =
        input.carrier.core.level b + n :=
  by
    simpa [sourceTheorem311Certificate_source] using
      (input.sourceTheorem311Certificate).routeNormalization route

def concreteInput (l : PrimeGeFive) :
    Input (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l) where
  theater := ConcreteSourceHistoryLinkBridge.sourceTheater l
  history := ConcreteSourceHistoryLinkBridge.sourceHistory l
  carrier := SourceFiniteParameterized.carrier l
  baseChoice := ConcreteFiniteTheorem311.ProcessionChoice.base
  baseChoice_eq := rfl
  packetVolume := fun c =>
    (SourceFiniteParameterized.carrier l).profile.logVolume c
  packetVolume_eq_profile := by intro c; rfl
  base_packetVolume_eq_theta := by
    exact SourceFiniteMultiradial.emptyRouteOutput_log_volume l
  target_q := (ConcreteSourceHistoryLinkBridge.sourceHistory l).terminal.thetaPacket.q
  target_q_eq := rfl
  history_q_eq := ConcreteSourceHistoryLinkBridge.sourceHistory_source_to_terminal_q l
  route_normal_form := by
    intro route
    refine ⟨ConcreteRouteNormalForm.horizontalTarget route
        ConcreteFiniteTheorem311.ProcessionChoice.base,
      ParametricTheorem311.verticalBudget route, ?_, ?_⟩
    · exact ConcreteRouteNormalForm.horizontalTarget_level route
        ConcreteFiniteTheorem311.ProcessionChoice.base
    · change SourceFiniteRouteArithmetic.target l route
          ConcreteFiniteTheorem311.ProcessionChoice.base =
        ConcreteFiniteTheorem311.ProcessionChoice.ind3Lift
          (ParametricTheorem311.verticalBudget route)
          (SourceFiniteRouteArithmetic.target l
            (ConcreteRouteNormalForm.horizontalPart route)
            ConcreteFiniteTheorem311.ProcessionChoice.base)
      exact ConcreteRouteNormalForm.normalized_target_eq route
        ConcreteFiniteTheorem311.ProcessionChoice.base

theorem concreteInput_profile_base (l : PrimeGeFive) :
    (concreteInput l).carrier.profile.logVolume
        (concreteInput l).carrier.core.base =
      (concreteInput l).theater.thetaPacket.logVolume := by
  exact (concreteInput l).profile_base_eq_theta

theorem concreteInput_theater_q (l : PrimeGeFive) :
    (concreteInput l).target_q =
      (concreteInput l).theater.thetaPacket.q := by
  exact (concreteInput l).target_q_eq_source

theorem concreteInput_history_length (l : PrimeGeFive) :
    0 < (concreteInput l).history.length := by
  exact (concreteInput l).history_length_pos

theorem concreteInput_ind1 (l : PrimeGeFive)
    (g : ConcreteFiniteTheorem311.finiteLabel l)
    (c : ConcreteFiniteTheorem311.ProcessionChoice l) :
    (((concreteInput l).indeterminacyEvidence).ind1 g c).target =
      (concreteInput l).carrier.core.ind1 g c := by
  exact (concreteInput l).indeterminacy_ind1_target g c

theorem concreteInput_ind2 (l : PrimeGeFive)
    (g : ConcreteFiniteTheorem311.finiteLabel l)
    (c : ConcreteFiniteTheorem311.ProcessionChoice l) :
    (((concreteInput l).indeterminacyEvidence).ind2 g c).target =
      (concreteInput l).carrier.core.ind2 g c := by
  exact (concreteInput l).indeterminacy_ind2_target g c

theorem concreteInput_ind3 (l : PrimeGeFive)
    (n : Nat) (c : ConcreteFiniteTheorem311.ProcessionChoice l) :
    (((concreteInput l).indeterminacyEvidence).ind3 n c).target =
      (concreteInput l).carrier.core.ind3 n c := by
  exact (concreteInput l).indeterminacy_ind3_target n c

theorem concreteInput_dStage (l : PrimeGeFive) :
    (concreteInput l).dStage.emptyOutput.target =
      (concreteInput l).carrier.core.base := by
  exact (concreteInput l).dStage_empty_target

end Input

end SourceProcessionBoundary

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def sourceProcessionBoundary : Obligation :=
  { id := "IUT-III.source-procession-boundary"
    source := "IUT III, Theorem 3.11; Hodge theater/procession input"
    status := VerificationStatus.interface
    note :=
      "This record ties a concrete Hodge theater and its dependent history to " ++
        "a parameterized carrier, packet-volume bridge, and exact Ind1/Ind2/Ind3 " ++
        "route evidence. All projections are proved. The record's existence for " ++
        "an arbitrary source Hodge theater remains an explicit source-facing " ++
        "obligation; the Q(i)-at-5 instance is constructed without sorry."
    dependsOn :=
      [ "IUT-I.hodge-theater-history-composition",
        "IUT-III.parametric-d-stage",
        "IUT-III.concrete-route-normal-form" ] }

end LeanFormal.IUT.Audit
