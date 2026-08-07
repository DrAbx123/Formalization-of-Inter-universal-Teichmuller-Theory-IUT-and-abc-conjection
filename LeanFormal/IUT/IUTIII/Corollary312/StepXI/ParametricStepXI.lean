import LeanFormal.IUT.IUTIII.Theorem311.ParametricDStage
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

namespace ParametricStepXI

open MultiradialKernel
open ParametricTheorem311
open ParametricDStage

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-!
  The Step-XI boundary is parameterized by a Theorem-3.11 output.  The
  arithmetic quantities and the three comparison propositions are fields so
  that this file cannot manufacture the source-facing comparison.  It only
  proves the assembly once those fields are supplied.
-/
structure StepXIInput (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) where
  output : AlgorithmOutput carrier input
  output_is_run : output = runAlgorithm carrier input
  qSigned : Real
  targetSigned : Real
  thetaSigned : Real
  q_negative : qSigned < 0
  ipl : Prop
  she : Prop
  apt : Prop
  ipl_evidence : ipl
  she_evidence : she
  apt_evidence : apt
  q_le_target : qSigned ≤ targetSigned
  target_le_theta : targetSigned ≤ thetaSigned

def stepXIInput (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier)
    (qSigned targetSigned thetaSigned : Real)
    (q_negative : qSigned < 0)
    (ipl she apt : Prop)
    (ipl_evidence : ipl) (she_evidence : she) (apt_evidence : apt)
    (q_le_target : qSigned ≤ targetSigned)
    (target_le_theta : targetSigned ≤ thetaSigned) :
    StepXIInput carrier input where
  output := runAlgorithm carrier input
  output_is_run := rfl
  qSigned := qSigned
  targetSigned := targetSigned
  thetaSigned := thetaSigned
  q_negative := q_negative
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := ipl_evidence
  she_evidence := she_evidence
  apt_evidence := apt_evidence
  q_le_target := q_le_target
  target_le_theta := target_le_theta

def StepXIInput.toContract {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) : StepXIContract :=
  { qSigned := data.qSigned
    thetaSigned := data.thetaSigned
    targetSigned := data.targetSigned
    q_negative := data.q_negative
    ipl := data.ipl
    she := data.she
    apt := data.apt
    ipl_evidence := data.ipl_evidence
    she_evidence := data.she_evidence
    apt_evidence := data.apt_evidence
    q_le_target := data.q_le_target
    target_le_theta := data.target_le_theta }

theorem StepXIInput.output_eq_run {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) :
    data.output = runAlgorithm carrier input :=
  data.output_is_run

theorem StepXIInput.q_negative_field {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) :
    data.qSigned < 0 :=
  data.q_negative

theorem StepXIInput.q_le_target_field {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) :
    data.qSigned ≤ data.targetSigned :=
  data.q_le_target

theorem StepXIInput.target_le_theta_field {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) :
    data.targetSigned ≤ data.thetaSigned :=
  data.target_le_theta

theorem StepXIInput.ipl_evidence_field {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) : data.ipl :=
  data.ipl_evidence

theorem StepXIInput.she_evidence_field {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) : data.she :=
  data.she_evidence

theorem StepXIInput.apt_evidence_field {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) : data.apt :=
  data.apt_evidence

theorem StepXIInput.toContract_q {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) :
    (data.toContract).qSigned = data.qSigned :=
  rfl

theorem StepXIInput.toContract_theta {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) :
    (data.toContract).thetaSigned = data.thetaSigned :=
  rfl

theorem StepXIInput.toContract_target {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) :
    (data.toContract).targetSigned = data.targetSigned :=
  rfl

theorem StepXIInput.toContract_q_negative {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) :
    (data.toContract).qSigned < 0 :=
  data.q_negative

theorem StepXIInput.toContract_ipl {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) :
    (data.toContract).ipl :=
  data.ipl_evidence

theorem StepXIInput.toContract_she {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) :
    (data.toContract).she :=
  data.she_evidence

theorem StepXIInput.toContract_apt {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) :
    (data.toContract).apt :=
  data.apt_evidence

theorem StepXIInput.conclusion {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) :
    Cor312Conclusion data.toContract := by
  exact cor312_of_constructed_stepXI data.toContract

theorem StepXIInput.q_positive {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) :
    0 < -data.qSigned := by
  exact neg_pos.mpr data.q_negative

theorem StepXIInput.toContract_q_positive {carrier : Carrier Label Choice}
    {input : AlgorithmInput carrier}
    (data : StepXIInput carrier input) :
    0 < -(data.toContract).qSigned := by
  exact q_positive_of_constructed_stepXI data.toContract

structure StepXIWallCertificate (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) where
  theorem311 : AlgorithmOutput carrier input
  ind1_route : ∀ g c, Ind1RouteCertificate carrier g c
  ind2_route : ∀ g c, Ind2RouteCertificate carrier g c
  ind3_route : ∀ n c, Ind3RouteCertificate carrier n c
  commutation12 : ∀ g h c, CommutationRouteCertificate carrier g h c
  commutation13 : ∀ g n c, Ind3CommutationRouteCertificate carrier g n c
  commutation23 : ∀ g n c, Ind2CommutationRouteCertificate carrier g n c
  output_is_run : theorem311 = runAlgorithm carrier input

def stepXIWallCertificate (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) :
    StepXIWallCertificate carrier input where
  theorem311 := runAlgorithm carrier input
  ind1_route := ind1RouteCertificate carrier
  ind2_route := ind2RouteCertificate carrier
  ind3_route := ind3RouteCertificate carrier
  commutation12 := ind1Ind2RouteCertificate carrier
  commutation13 := ind1Ind3RouteCertificate carrier
  commutation23 := ind2Ind3RouteCertificate carrier
  output_is_run := rfl

theorem stepXIWallCertificate_output (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) :
    (stepXIWallCertificate carrier input).theorem311 =
      runAlgorithm carrier input :=
  rfl

theorem stepXIWallCertificate_ind1 (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) (g : Label) (c : Choice) :
    (stepXIWallCertificate carrier input).ind1_route g c =
      ind1RouteCertificate carrier g c :=
  rfl

theorem stepXIWallCertificate_ind2 (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) (g : Label) (c : Choice) :
    (stepXIWallCertificate carrier input).ind2_route g c =
      ind2RouteCertificate carrier g c :=
  rfl

theorem stepXIWallCertificate_ind3 (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) (n : Nat) (c : Choice) :
    (stepXIWallCertificate carrier input).ind3_route n c =
      ind3RouteCertificate carrier n c :=
  rfl

theorem stepXIWallCertificate_commutation12
    (carrier : Carrier Label Choice) (input : AlgorithmInput carrier)
    (g h : Label) (c : Choice) :
    (stepXIWallCertificate carrier input).commutation12 g h c =
      ind1Ind2RouteCertificate carrier g h c :=
  rfl

theorem stepXIWallCertificate_commutation13
    (carrier : Carrier Label Choice) (input : AlgorithmInput carrier)
    (g : Label) (n : Nat) (c : Choice) :
    (stepXIWallCertificate carrier input).commutation13 g n c =
      ind1Ind3RouteCertificate carrier g n c :=
  rfl

theorem stepXIWallCertificate_commutation23
    (carrier : Carrier Label Choice) (input : AlgorithmInput carrier)
    (g : Label) (n : Nat) (c : Choice) :
    (stepXIWallCertificate carrier input).commutation23 g n c =
      ind2Ind3RouteCertificate carrier g n c :=
  rfl

structure SourceStepXIAssembly (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) where
  wall : StepXIWallCertificate carrier input
  arithmetic : StepXIInput carrier input
  wall_input_agrees : wall.theorem311 = arithmetic.output

def sourceStepXIAssembly (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier)
    (arithmetic : StepXIInput carrier input) :
    SourceStepXIAssembly carrier input where
  wall := stepXIWallCertificate carrier input
  arithmetic := arithmetic
  wall_input_agrees := by
    rw [stepXIWallCertificate_output, arithmetic.output_eq_run]

theorem sourceStepXIAssembly_wall (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier)
    (arithmetic : StepXIInput carrier input) :
    (sourceStepXIAssembly carrier input arithmetic).wall =
      stepXIWallCertificate carrier input :=
  rfl

theorem sourceStepXIAssembly_arithmetic (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier)
    (arithmetic : StepXIInput carrier input) :
    (sourceStepXIAssembly carrier input arithmetic).arithmetic = arithmetic :=
  rfl

theorem sourceStepXIAssembly_conclusion (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier)
    (arithmetic : StepXIInput carrier input) :
    Cor312Conclusion arithmetic.toContract :=
  arithmetic.conclusion

theorem sourceStepXIAssembly_q_positive (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier)
    (arithmetic : StepXIInput carrier input) :
    0 < -arithmetic.qSigned :=
  arithmetic.q_positive

structure FiniteSourceStepXIAssembly (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) where
  wall : StepXIWallCertificate carrier input
  link : StepXIInput carrier input
  q_bound : link.qSigned ≤ link.targetSigned
  theta_bound : link.targetSigned ≤ link.thetaSigned

def finiteSourceStepXIAssembly (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier)
    (link : StepXIInput carrier input) :
    FiniteSourceStepXIAssembly carrier input where
  wall := stepXIWallCertificate carrier input
  link := link
  q_bound := link.q_le_target
  theta_bound := link.target_le_theta

theorem finiteSourceStepXIAssembly_q_bound
    (carrier : Carrier Label Choice) (input : AlgorithmInput carrier)
    (link : StepXIInput carrier input) :
    (finiteSourceStepXIAssembly carrier input link).link.qSigned ≤
      (finiteSourceStepXIAssembly carrier input link).link.targetSigned :=
  (finiteSourceStepXIAssembly carrier input link).q_bound

theorem finiteSourceStepXIAssembly_theta_bound
    (carrier : Carrier Label Choice) (input : AlgorithmInput carrier)
    (link : StepXIInput carrier input) :
    (finiteSourceStepXIAssembly carrier input link).link.targetSigned ≤
      (finiteSourceStepXIAssembly carrier input link).link.thetaSigned :=
  (finiteSourceStepXIAssembly carrier input link).theta_bound

theorem finiteSourceStepXIAssembly_conclusion
    (carrier : Carrier Label Choice) (input : AlgorithmInput carrier)
    (link : StepXIInput carrier input) :
    Cor312Conclusion
      (finiteSourceStepXIAssembly carrier input link).link.toContract := by
  exact link.conclusion

theorem finiteSourceStepXIAssembly_wall_output
    (carrier : Carrier Label Choice) (input : AlgorithmInput carrier)
    (link : StepXIInput carrier input) :
    (finiteSourceStepXIAssembly carrier input link).wall.theorem311 =
      runAlgorithm carrier input :=
  stepXIWallCertificate_output carrier input

end ParametricStepXI

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def parametricTheorem311Carrier : Obligation :=
  { id := "IUT-III.parametric-carrier-route-kernel"
    source := "IUT III, Theorem 3.11, Ind1-Ind3 and multiradial route"
    status := VerificationStatus.interface
    note :=
      "A parameterized carrier with explicit core, profile, horizontal " ++
        "connector, and exact Ind3 level formula yields proved route, quotient, " ++
        "profile, and possible-image invariants. The connector and exact level " ++
        "formula remain source-facing fields for arbitrary Hodge theaters."
    dependsOn :=
      [ "IUT-III.generic-quotient-transport",
        "IUT-III.Ind1",
        "IUT-III.Ind2",
        "IUT-III.Ind3" ] }

def parametricTheorem311DStage : Obligation :=
  { id := "IUT-III.parametric-D-stage-certificates"
    source := "IUT III, Theorem 3.11, Ind1/Ind2/Ind3 naturality"
    status := VerificationStatus.interface
    note :=
      "Single-step certificates, commutation route certificates, vertical " ++
        "budget, and algorithm output are proved for any supplied carrier. " ++
        "This does not construct the paper's multiradial algorithm from the " ++
        "source Hodge theaters."
    dependsOn := [ "IUT-III.parametric-carrier-route-kernel" ] }

def parametricStepXIAssembly : Obligation :=
  { id := "IUT-III.parametric-StepXI-assembly"
    source := "IUT III, Theorem 3.11 -> Corollary 3.12, Steps (xi-a)-(xi-g)"
    status := VerificationStatus.interface
    note :=
      "The Step-XI arithmetic, IPL, SHE, APT, and comparison fields are " ++
        "assembled into the existing contract only when supplied explicitly. " ++
        "No source-facing existence claim is made."
    dependsOn :=
      [ "IUT-III.parametric-D-stage-certificates",
        "IUT-III.StepXI.contract-construction" ] }

end LeanFormal.IUT.Audit
