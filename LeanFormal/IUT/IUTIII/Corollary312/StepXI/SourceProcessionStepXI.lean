import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ParametricStepXI
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

namespace SourceProcessionStepXI

open SourceProcessionBoundary
open MultiradialKernel
open MultiradialKernel.Core
open ParametricTheorem311
open ParametricDStage
open ParametricStepXI

universe u v w

variable {l : PrimeGeFive} {V : Type v}
variable {Label : Type u} {Choice : Type w} [AddGroup Label]

variable (input : SourceProcessionBoundary.Input
  (l := l) (V := V) (Label := Label) (Choice := Choice))

def ProcessionTheorem311Target (carrier : Carrier Label Choice)
    (b : Choice) (n : Nat) : Choice :=
  carrier.core.ind3 n b

structure Wall (route : List (RouteStep Label)) where
  dStage : DStageCertificate input.carrier
  routeOutput : input.RouteOutput route
  wall : StepXIWallCertificate input.carrier routeOutput.algorithmInput
  source_eq : routeOutput.algorithmInput.source = input.carrier.core.base
  target_eq : wall.theorem311.target =
    routeTarget input.carrier route input.carrier.core.base
  output_eq : wall.theorem311 = routeOutput.output

theorem ProcessionTheorem311Target_eq (carrier : Carrier Label Choice)
    (b : Choice) (n : Nat) :
    ProcessionTheorem311Target carrier b n = carrier.core.ind3 n b := rfl

def routeWall (route : List (RouteStep Label)) : Wall input route where
  dStage := input.dStage
  routeOutput := input.routeOutput route
  wall := stepXIWallCertificate input.carrier
    (input.routeOutput route).algorithmInput
  source_eq := (input.routeOutput_source route).trans input.baseChoice_eq_core
  target_eq := by
    rw [stepXIWallCertificate_output]
    calc
      (input.routeOutput route).output.target =
          routeTarget input.carrier route input.baseChoice :=
        input.routeOutput_target route
      _ = routeTarget input.carrier route input.carrier.core.base := by
        rw [input.baseChoice_eq_core]
  output_eq := rfl

theorem wall_dStage (route : List (RouteStep Label)) :
    (routeWall input route).dStage = input.dStage := rfl

theorem wall_source (route : List (RouteStep Label)) :
    (routeWall input route).routeOutput.algorithmInput.source =
      input.carrier.core.base :=
  (routeWall input route).source_eq

theorem wall_target (route : List (RouteStep Label)) :
    (routeWall input route).wall.theorem311.target =
      routeTarget input.carrier route input.carrier.core.base :=
  (routeWall input route).target_eq

theorem wall_output (route : List (RouteStep Label)) :
    (routeWall input route).wall.theorem311 =
      (routeWall input route).routeOutput.output :=
  (routeWall input route).output_eq

theorem wall_output_is_run (route : List (RouteStep Label)) :
    (routeWall input route).wall.theorem311 =
      runAlgorithm input.carrier (routeWall input route).routeOutput.algorithmInput :=
  stepXIWallCertificate_output input.carrier
    (routeWall input route).routeOutput.algorithmInput

theorem wall_ind1 (route : List (RouteStep Label))
    (g : Label) (c : Choice) :
    (routeWall input route).wall.ind1_route g c =
      ind1RouteCertificate input.carrier g c := rfl

theorem wall_ind2 (route : List (RouteStep Label))
    (g : Label) (c : Choice) :
    (routeWall input route).wall.ind2_route g c =
      ind2RouteCertificate input.carrier g c := rfl

theorem wall_ind3 (route : List (RouteStep Label))
    (n : Nat) (c : Choice) :
    (routeWall input route).wall.ind3_route n c =
      ind3RouteCertificate input.carrier n c := rfl

theorem wall_commutation12 (route : List (RouteStep Label))
    (g h : Label) (c : Choice) :
    (routeWall input route).wall.commutation12 g h c =
      ind1Ind2RouteCertificate input.carrier g h c := rfl

theorem wall_commutation13 (route : List (RouteStep Label))
    (g : Label) (n : Nat) (c : Choice) :
    (routeWall input route).wall.commutation13 g n c =
      ind1Ind3RouteCertificate input.carrier g n c := rfl

theorem wall_commutation23 (route : List (RouteStep Label))
    (g : Label) (n : Nat) (c : Choice) :
    (routeWall input route).wall.commutation23 g n c =
      ind2Ind3RouteCertificate input.carrier g n c := rfl

theorem wall_ind1_target (route : List (RouteStep Label))
    (g : Label) (c : Choice) :
    ((routeWall input route).wall.ind1_route g c).target =
      input.carrier.core.ind1 g c :=
  ind1RouteCertificate_target input.carrier g c

theorem wall_ind2_target (route : List (RouteStep Label))
    (g : Label) (c : Choice) :
    ((routeWall input route).wall.ind2_route g c).target =
      input.carrier.core.ind2 g c :=
  ind2RouteCertificate_target input.carrier g c

theorem wall_ind3_target (route : List (RouteStep Label))
    (n : Nat) (c : Choice) :
    ((routeWall input route).wall.ind3_route n c).target =
      input.carrier.core.ind3 n c :=
  ind3RouteCertificate_target input.carrier n c

theorem wall_ind1_profile (route : List (RouteStep Label))
    (g : Label) (c : Choice) :
    input.carrier.profile.logVolume
        ((routeWall input route).wall.ind1_route g c).target =
      input.carrier.profile.logVolume c :=
  ind1RouteCertificate_profile input.carrier g c

theorem wall_ind2_profile (route : List (RouteStep Label))
    (g : Label) (c : Choice) :
    input.carrier.profile.logVolume
        ((routeWall input route).wall.ind2_route g c).target =
      input.carrier.profile.logVolume c :=
  ind2RouteCertificate_profile input.carrier g c

theorem wall_ind3_profile (route : List (RouteStep Label))
    (n : Nat) (c : Choice) :
    input.carrier.profile.logVolume c ≤
      input.carrier.profile.logVolume
        ((routeWall input route).wall.ind3_route n c).target :=
  ind3RouteCertificate_profile input.carrier n c

theorem wall_route_level (route : List (RouteStep Label)) :
    input.carrier.core.level
        (routeTarget input.carrier route input.carrier.core.base) =
      input.carrier.core.level input.carrier.core.base + verticalBudget route :=
  routeTarget_level_eq_budget input.carrier route input.carrier.core.base

theorem wall_route_profile (route : List (RouteStep Label)) :
    input.carrier.profile.logVolume input.carrier.core.base ≤
      input.carrier.profile.logVolume
        (routeTarget input.carrier route input.carrier.core.base) :=
  routeTarget_profile_monotone input.carrier route input.carrier.core.base

theorem wall_route_image (route : List (RouteStep Label)) (z : Real)
    (hz : z ∈ input.carrier.profile.possibleImage input.carrier.core.base) :
    ∃ w, w ∈ input.carrier.profile.possibleImage
      (routeTarget input.carrier route input.carrier.core.base) ∧ z ≤ w :=
  routeTarget_image_upper input.carrier route input.carrier.core.base z hz

noncomputable def normalFormHorizontal (route : List (RouteStep Label)) : Choice :=
  Classical.choose (input.route_normal_form route)

noncomputable def normalFormBudget (route : List (RouteStep Label)) : Nat :=
  Classical.choose (Classical.choose_spec (input.route_normal_form route))

theorem normalFormHorizontal_level (route : List (RouteStep Label)) :
    input.carrier.core.level (normalFormHorizontal input route) =
      input.carrier.core.level input.carrier.core.base := by
  have hs := Classical.choose_spec (input.route_normal_form route)
  exact (Classical.choose_spec hs).1

theorem normalForm_target (route : List (RouteStep Label)) :
    routeTarget input.carrier route input.carrier.core.base =
      input.carrier.core.ind3 (normalFormBudget input route)
        (normalFormHorizontal input route) := by
  have hs := Classical.choose_spec (input.route_normal_form route)
  exact (Classical.choose_spec hs).2

theorem normalFormHorizontal_profile (route : List (RouteStep Label)) :
    input.carrier.profile.logVolume (normalFormHorizontal input route) =
      input.carrier.profile.logVolume input.carrier.core.base := by
  rw [← input.carrier.connector_target_same_level
    (normalFormHorizontal_level input route).symm]
  exact ParametricTheorem311.routeTarget_profile_horizontal
    input.carrier (input.carrier.connector input.carrier.core.base
      (normalFormHorizontal input route)) input.carrier.core.base
      (by
        intro step hstep
        exact input.carrier.connector_horizontal _ _ step hstep)

theorem normalFormHorizontal_image (route : List (RouteStep Label)) :
    input.carrier.profile.possibleImage (normalFormHorizontal input route) =
      input.carrier.profile.possibleImage input.carrier.core.base := by
  rw [← input.carrier.connector_target_same_level
    (normalFormHorizontal_level input route).symm]
  exact possibleImage_applyRoute_horizontal input.carrier.profile
    (input.carrier.connector input.carrier.core.base
      (normalFormHorizontal input route))
    (by
      intro step hstep
      exact input.carrier.connector_horizontal _ _ step hstep)
    input.carrier.core.base

structure NormalizedWall (route : List (RouteStep Label)) where
  wall : Wall input route
  horizontal : Choice
  budget : Nat
  horizontal_eq : horizontal = normalFormHorizontal input route
  budget_eq : budget = normalFormBudget input route
  horizontal_level : input.carrier.core.level horizontal =
    input.carrier.core.level input.carrier.core.base
  normalized_target :
    routeTarget input.carrier route input.carrier.core.base =
      input.carrier.core.ind3 budget horizontal

def normalizedWall (route : List (RouteStep Label)) :
    NormalizedWall input route where
  wall := routeWall input route
  horizontal := normalFormHorizontal input route
  budget := normalFormBudget input route
  horizontal_eq := rfl
  budget_eq := rfl
  horizontal_level := normalFormHorizontal_level input route
  normalized_target := normalForm_target input route

theorem normalizedWall_horizontal (route : List (RouteStep Label)) :
    (normalizedWall input route).horizontal =
      normalFormHorizontal input route :=
  (normalizedWall input route).horizontal_eq

theorem normalizedWall_budget (route : List (RouteStep Label)) :
    (normalizedWall input route).budget = normalFormBudget input route :=
  (normalizedWall input route).budget_eq

theorem normalizedWall_level (route : List (RouteStep Label)) :
    input.carrier.core.level (normalizedWall input route).horizontal =
      input.carrier.core.level input.carrier.core.base :=
  (normalizedWall input route).horizontal_level

theorem normalizedWall_target (route : List (RouteStep Label)) :
    routeTarget input.carrier route input.carrier.core.base =
      input.carrier.core.ind3 (normalizedWall input route).budget
        (normalizedWall input route).horizontal := by
  exact (normalizedWall input route).normalized_target

theorem normalizedWall_profile (route : List (RouteStep Label)) :
    input.carrier.profile.logVolume
        (normalizedWall input route).horizontal =
      input.carrier.profile.logVolume input.carrier.core.base := by
  rw [normalizedWall_horizontal]
  exact normalFormHorizontal_profile input route

theorem normalizedWall_image (route : List (RouteStep Label)) :
    input.carrier.profile.possibleImage
        (normalizedWall input route).horizontal =
      input.carrier.profile.possibleImage input.carrier.core.base := by
  rw [normalizedWall_horizontal]
  exact normalFormHorizontal_image input route

structure ArithmeticLink (route : List (RouteStep Label)) where
  arithmetic : StepXIInput input.carrier
    (routeWall input route).routeOutput.algorithmInput
  arithmetic_source : arithmetic.output = (routeWall input route).wall.theorem311
  q_negative : arithmetic.qSigned < 0
  q_le_target : arithmetic.qSigned ≤ arithmetic.targetSigned
  target_le_theta : arithmetic.targetSigned ≤ arithmetic.thetaSigned

def arithmeticLink (route : List (RouteStep Label))
    (arithmetic : StepXIInput input.carrier
      (routeWall input route).routeOutput.algorithmInput)
    (hagrees : arithmetic.output = (routeWall input route).wall.theorem311) :
    ArithmeticLink input route where
  arithmetic := arithmetic
  arithmetic_source := hagrees
  q_negative := arithmetic.q_negative
  q_le_target := arithmetic.q_le_target
  target_le_theta := arithmetic.target_le_theta

theorem arithmeticLink_source (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    link.arithmetic.output = (routeWall input route).wall.theorem311 :=
  link.arithmetic_source

theorem arithmeticLink_q_negative (route : List (RouteStep Label))
    (link : ArithmeticLink input route) : link.arithmetic.qSigned < 0 :=
  link.q_negative

theorem arithmeticLink_q_bound (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    link.arithmetic.qSigned ≤ link.arithmetic.targetSigned :=
  link.q_le_target

theorem arithmeticLink_theta_bound (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    link.arithmetic.targetSigned ≤ link.arithmetic.thetaSigned :=
  link.target_le_theta

def assembly (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    SourceStepXIAssembly input.carrier
      (routeWall input route).routeOutput.algorithmInput :=
  sourceStepXIAssembly input.carrier
    (routeWall input route).routeOutput.algorithmInput
    link.arithmetic

theorem assembly_wall (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    (assembly input route link).wall =
      (routeWall input route).wall := by
  rfl

theorem assembly_arithmetic (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    (assembly input route link).arithmetic = link.arithmetic := by
  rfl

theorem assembly_output (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    (assembly input route link).wall.theorem311 =
      (assembly input route link).arithmetic.output := by
  exact (assembly input route link).wall_input_agrees

theorem assembly_contract (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    Cor312Conclusion
      (assembly input route link).arithmetic.toContract :=
  sourceStepXIAssembly_conclusion input.carrier
    (routeWall input route).routeOutput.algorithmInput link.arithmetic

theorem assembly_q_positive (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    0 < -(assembly input route link).arithmetic.qSigned :=
  sourceStepXIAssembly_q_positive input.carrier
    (routeWall input route).routeOutput.algorithmInput link.arithmetic

structure SourceStepXIBoundary (route : List (RouteStep Label)) where
  wall : Wall input route
  normalized : NormalizedWall input route
  link : ArithmeticLink input route
  assembly : SourceStepXIAssembly input.carrier
    (routeWall input route).routeOutput.algorithmInput
  assembly_wall_eq : assembly.wall = (routeWall input route).wall
  assembly_link_eq : assembly.arithmetic = link.arithmetic

def sourceStepXIBoundary (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    SourceStepXIBoundary input route where
  wall := routeWall input route
  normalized := normalizedWall input route
  link := link
  assembly := assembly input route link
  assembly_wall_eq := rfl
  assembly_link_eq := rfl

theorem sourceStepXIBoundary_wall (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    (sourceStepXIBoundary input route link).wall = routeWall input route := rfl

theorem sourceStepXIBoundary_normalized (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    (sourceStepXIBoundary input route link).normalized =
      normalizedWall input route := rfl

theorem sourceStepXIBoundary_link (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    (sourceStepXIBoundary input route link).link = link := rfl

theorem sourceStepXIBoundary_contract (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    Cor312Conclusion
      (sourceStepXIBoundary input route link).assembly.arithmetic.toContract :=
  assembly_contract input route link

theorem sourceStepXIBoundary_output (route : List (RouteStep Label))
    (link : ArithmeticLink input route) :
    (sourceStepXIBoundary input route link).assembly.wall.theorem311 =
      (sourceStepXIBoundary input route link).assembly.arithmetic.output :=
  (sourceStepXIBoundary input route link).assembly.wall_input_agrees

end SourceProcessionStepXI

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def sourceProcessionStepXI : Obligation :=
  { id := "IUT-III.source-procession-stepXI-boundary"
    source := "IUT III, Theorem 3.11 -> Corollary 3.12"
    status := VerificationStatus.interface
    note :=
      "The source procession boundary now supplies a fully proved D-stage wall, " ++
        "route normalization, and Step-XI assembly. IPL/SHE/APT and the two real " ++
        "comparison inequalities remain explicit arithmetic link fields; no " ++
        "source-facing existence is manufactured."
    dependsOn :=
      [ "IUT-III.source-procession-boundary",
        "IUT-III.parametric-StepXI-assembly" ] }

end LeanFormal.IUT.Audit
