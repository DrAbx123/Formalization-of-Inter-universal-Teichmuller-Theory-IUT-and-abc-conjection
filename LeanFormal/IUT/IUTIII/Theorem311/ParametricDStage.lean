import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteParameterized
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.FiniteCertificateBridge
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

namespace ParametricDStage

open MultiradialKernel
open MultiradialKernel.Core
open ParametricTheorem311

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

structure Ind1RouteCertificate (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) where
  route : List (RouteStep Label)
  horizontal : horizontalRoute carrier route
  target : Choice
  target_eq : target = carrier.core.ind1 g c
  level_eq : carrier.core.level target = carrier.core.level c
  profile_eq : carrier.profile.logVolume target = carrier.profile.logVolume c

def ind1RouteCertificate (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) : Ind1RouteCertificate carrier g c where
  route := [.ind1 g]
  horizontal := by
    intro step hstep
    simp only [List.mem_singleton] at hstep
    subst step
    exact horizontal_of_ind1 g
  target := routeTarget carrier [.ind1 g] c
  target_eq := by
    rfl
  level_eq := by
    simp [routeTarget, applyRoute, applyStep, carrier.core.ind1_level]
  profile_eq := by
    exact carrier.profile.ind1_invariant g c

theorem ind1RouteCertificate_route (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    (ind1RouteCertificate carrier g c).route = [.ind1 g] :=
  rfl

theorem ind1RouteCertificate_horizontal (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    horizontalRoute carrier (ind1RouteCertificate carrier g c).route :=
  (ind1RouteCertificate carrier g c).horizontal

theorem ind1RouteCertificate_target (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    (ind1RouteCertificate carrier g c).target = carrier.core.ind1 g c :=
  (ind1RouteCertificate carrier g c).target_eq

theorem ind1RouteCertificate_level (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    carrier.core.level (ind1RouteCertificate carrier g c).target =
      carrier.core.level c :=
  (ind1RouteCertificate carrier g c).level_eq

theorem ind1RouteCertificate_profile (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    carrier.profile.logVolume (ind1RouteCertificate carrier g c).target =
      carrier.profile.logVolume c :=
  (ind1RouteCertificate carrier g c).profile_eq

structure Ind2RouteCertificate (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) where
  route : List (RouteStep Label)
  horizontal : horizontalRoute carrier route
  target : Choice
  target_eq : target = carrier.core.ind2 g c
  level_eq : carrier.core.level target = carrier.core.level c
  profile_eq : carrier.profile.logVolume target = carrier.profile.logVolume c

def ind2RouteCertificate (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) : Ind2RouteCertificate carrier g c where
  route := [.ind2 g]
  horizontal := by
    intro step hstep
    simp only [List.mem_singleton] at hstep
    subst step
    exact horizontal_of_ind2 g
  target := routeTarget carrier [.ind2 g] c
  target_eq := by
    rfl
  level_eq := by
    simp [routeTarget, applyRoute, applyStep, carrier.core.ind2_level]
  profile_eq := by
    exact carrier.profile.ind2_invariant g c

theorem ind2RouteCertificate_route (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    (ind2RouteCertificate carrier g c).route = [.ind2 g] :=
  rfl

theorem ind2RouteCertificate_horizontal (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    horizontalRoute carrier (ind2RouteCertificate carrier g c).route :=
  (ind2RouteCertificate carrier g c).horizontal

theorem ind2RouteCertificate_target (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    (ind2RouteCertificate carrier g c).target = carrier.core.ind2 g c :=
  (ind2RouteCertificate carrier g c).target_eq

theorem ind2RouteCertificate_level (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    carrier.core.level (ind2RouteCertificate carrier g c).target =
      carrier.core.level c :=
  (ind2RouteCertificate carrier g c).level_eq

theorem ind2RouteCertificate_profile (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    carrier.profile.logVolume (ind2RouteCertificate carrier g c).target =
      carrier.profile.logVolume c :=
  (ind2RouteCertificate carrier g c).profile_eq

structure Ind3RouteCertificate (carrier : Carrier Label Choice)
    (n : Nat) (c : Choice) where
  route : List (RouteStep Label)
  vertical_budget : verticalBudget route = n
  target : Choice
  target_eq : target = carrier.core.ind3 n c
  level_eq : carrier.core.level target = carrier.core.level c + n
  profile_le : carrier.profile.logVolume c ≤ carrier.profile.logVolume target

def ind3RouteCertificate (carrier : Carrier Label Choice)
    (n : Nat) (c : Choice) : Ind3RouteCertificate carrier n c where
  route := [.ind3 n]
  vertical_budget := by rfl
  target := routeTarget carrier [.ind3 n] c
  target_eq := by rfl
  level_eq := by
    rw [routeTarget, applyRoute_one, applyStep_ind3,
      carrier.ind3_level_eq]
  profile_le := carrier.profile.ind3_upper n c

theorem ind3RouteCertificate_route (carrier : Carrier Label Choice)
    (n : Nat) (c : Choice) :
    (ind3RouteCertificate carrier n c).route = [.ind3 n] :=
  rfl

theorem ind3RouteCertificate_budget (carrier : Carrier Label Choice)
    (n : Nat) (c : Choice) :
    verticalBudget (ind3RouteCertificate carrier n c).route = n :=
  (ind3RouteCertificate carrier n c).vertical_budget

theorem ind3RouteCertificate_target (carrier : Carrier Label Choice)
    (n : Nat) (c : Choice) :
    (ind3RouteCertificate carrier n c).target = carrier.core.ind3 n c :=
  (ind3RouteCertificate carrier n c).target_eq

theorem ind3RouteCertificate_level (carrier : Carrier Label Choice)
    (n : Nat) (c : Choice) :
    carrier.core.level (ind3RouteCertificate carrier n c).target =
      carrier.core.level c + n :=
  (ind3RouteCertificate carrier n c).level_eq

theorem ind3RouteCertificate_profile (carrier : Carrier Label Choice)
    (n : Nat) (c : Choice) :
    carrier.profile.logVolume c ≤
      carrier.profile.logVolume (ind3RouteCertificate carrier n c).target :=
  (ind3RouteCertificate carrier n c).profile_le

structure CommutationRouteCertificate (carrier : Carrier Label Choice)
    (g h : Label) (c : Choice) where
  leftRoute : List (RouteStep Label)
  rightRoute : List (RouteStep Label)
  leftTarget : Choice
  rightTarget : Choice
  left_eq : leftTarget = carrier.core.ind1 g (carrier.core.ind2 h c)
  right_eq : rightTarget = carrier.core.ind2 h (carrier.core.ind1 g c)
  target_eq : leftTarget = rightTarget

def ind1Ind2RouteCertificate (carrier : Carrier Label Choice)
    (g h : Label) (c : Choice) :
    CommutationRouteCertificate carrier g h c where
  leftRoute := [.ind2 h, .ind1 g]
  rightRoute := [.ind1 g, .ind2 h]
  leftTarget := routeTarget carrier [.ind2 h, .ind1 g] c
  rightTarget := routeTarget carrier [.ind1 g, .ind2 h] c
  left_eq := by rfl
  right_eq := by rfl
  target_eq := by
    change carrier.core.ind1 g (carrier.core.ind2 h c) =
      carrier.core.ind2 h (carrier.core.ind1 g c)
    exact carrier.core.ind1_ind2_commute g h c

theorem ind1Ind2RouteCertificate_left (carrier : Carrier Label Choice)
    (g h : Label) (c : Choice) :
    (ind1Ind2RouteCertificate carrier g h c).leftTarget =
      carrier.core.ind1 g (carrier.core.ind2 h c) :=
  (ind1Ind2RouteCertificate carrier g h c).left_eq

theorem ind1Ind2RouteCertificate_right (carrier : Carrier Label Choice)
    (g h : Label) (c : Choice) :
    (ind1Ind2RouteCertificate carrier g h c).rightTarget =
      carrier.core.ind2 h (carrier.core.ind1 g c) :=
  (ind1Ind2RouteCertificate carrier g h c).right_eq

theorem ind1Ind2RouteCertificate_commutes (carrier : Carrier Label Choice)
    (g h : Label) (c : Choice) :
    (ind1Ind2RouteCertificate carrier g h c).leftTarget =
      (ind1Ind2RouteCertificate carrier g h c).rightTarget :=
  (ind1Ind2RouteCertificate carrier g h c).target_eq

structure Ind3CommutationRouteCertificate (carrier : Carrier Label Choice)
    (g : Label) (n : Nat) (c : Choice) where
  leftTarget : Choice
  rightTarget : Choice
  left_eq : leftTarget = carrier.core.ind1 g (carrier.core.ind3 n c)
  right_eq : rightTarget = carrier.core.ind3 n (carrier.core.ind1 g c)
  target_eq : leftTarget = rightTarget

def ind1Ind3RouteCertificate (carrier : Carrier Label Choice)
    (g : Label) (n : Nat) (c : Choice) :
    Ind3CommutationRouteCertificate carrier g n c where
  leftTarget := routeTarget carrier [.ind3 n, .ind1 g] c
  rightTarget := routeTarget carrier [.ind1 g, .ind3 n] c
  left_eq := by rfl
  right_eq := by rfl
  target_eq := by
    change carrier.core.ind1 g (carrier.core.ind3 n c) =
      carrier.core.ind3 n (carrier.core.ind1 g c)
    exact carrier.core.ind1_ind3_commute g n c

theorem ind1Ind3RouteCertificate_commutes (carrier : Carrier Label Choice)
    (g : Label) (n : Nat) (c : Choice) :
    (ind1Ind3RouteCertificate carrier g n c).leftTarget =
      (ind1Ind3RouteCertificate carrier g n c).rightTarget :=
  (ind1Ind3RouteCertificate carrier g n c).target_eq

structure Ind2CommutationRouteCertificate (carrier : Carrier Label Choice)
    (g : Label) (n : Nat) (c : Choice) where
  leftTarget : Choice
  rightTarget : Choice
  left_eq : leftTarget = carrier.core.ind2 g (carrier.core.ind3 n c)
  right_eq : rightTarget = carrier.core.ind3 n (carrier.core.ind2 g c)
  target_eq : leftTarget = rightTarget

def ind2Ind3RouteCertificate (carrier : Carrier Label Choice)
    (g : Label) (n : Nat) (c : Choice) :
    Ind2CommutationRouteCertificate carrier g n c where
  leftTarget := routeTarget carrier [.ind3 n, .ind2 g] c
  rightTarget := routeTarget carrier [.ind2 g, .ind3 n] c
  left_eq := by rfl
  right_eq := by rfl
  target_eq := by
    change carrier.core.ind2 g (carrier.core.ind3 n c) =
      carrier.core.ind3 n (carrier.core.ind2 g c)
    exact carrier.core.ind2_ind3_commute g n c

theorem ind2Ind3RouteCertificate_commutes (carrier : Carrier Label Choice)
    (g : Label) (n : Nat) (c : Choice) :
    (ind2Ind3RouteCertificate carrier g n c).leftTarget =
      (ind2Ind3RouteCertificate carrier g n c).rightTarget :=
  (ind2Ind3RouteCertificate carrier g n c).target_eq

structure RouteNaturalityCertificate (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) where
  source : Choice
  source_eq : source = c
  target : Choice
  target_eq : target = routeTarget carrier route c
  level_eq : carrier.core.level target =
    carrier.core.level c + verticalBudget route
  profile_bound : carrier.profile.logVolume c ≤ carrier.profile.logVolume target
  image_bound : ∀ z, z ∈ carrier.profile.possibleImage c →
    ∃ w, w ∈ carrier.profile.possibleImage target ∧ z ≤ w

def routeNaturalityCertificate (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    RouteNaturalityCertificate carrier route c where
  source := c
  source_eq := rfl
  target := routeTarget carrier route c
  target_eq := rfl
  level_eq := routeTarget_level_eq_budget carrier route c
  profile_bound := routeTarget_profile_monotone carrier route c
  image_bound := routeTarget_image_upper carrier route c

theorem routeNaturalityCertificate_source (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    (routeNaturalityCertificate carrier route c).source = c :=
  rfl

theorem routeNaturalityCertificate_target (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    (routeNaturalityCertificate carrier route c).target =
      routeTarget carrier route c :=
  rfl

theorem routeNaturalityCertificate_level (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    carrier.core.level (routeNaturalityCertificate carrier route c).target =
      carrier.core.level c + verticalBudget route :=
  (routeNaturalityCertificate carrier route c).level_eq

theorem routeNaturalityCertificate_profile (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    carrier.profile.logVolume c ≤
      carrier.profile.logVolume (routeNaturalityCertificate carrier route c).target :=
  (routeNaturalityCertificate carrier route c).profile_bound

theorem routeNaturalityCertificate_image (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) (z : Real)
    (hz : z ∈ carrier.profile.possibleImage c) :
    ∃ w, w ∈ carrier.profile.possibleImage
      (routeNaturalityCertificate carrier route c).target ∧ z ≤ w :=
  (routeNaturalityCertificate carrier route c).image_bound z hz

structure DStageCertificate (carrier : Carrier Label Choice) where
  base : Choice
  base_eq : base = carrier.core.base
  independence : IndependenceBundle carrier
  emptyInput : AlgorithmInput carrier
  emptyInput_source : emptyInput.source = base
  emptyOutput : AlgorithmOutput carrier emptyInput
  emptyOutput_target : emptyOutput.target = base

def dStageCertificate (carrier : Carrier Label Choice) :
    DStageCertificate carrier where
  base := carrier.core.base
  base_eq := rfl
  independence := independenceBundle carrier
  emptyInput := AlgorithmInput.empty carrier
  emptyInput_source := rfl
  emptyOutput := runAlgorithm carrier (AlgorithmInput.empty carrier)
  emptyOutput_target := rfl

theorem dStageCertificate_base (carrier : Carrier Label Choice) :
    (dStageCertificate carrier).base = carrier.core.base :=
  rfl

theorem dStageCertificate_independence (carrier : Carrier Label Choice) :
    (dStageCertificate carrier).independence = independenceBundle carrier :=
  rfl

theorem dStageCertificate_empty_source (carrier : Carrier Label Choice) :
    (dStageCertificate carrier).emptyInput.source = carrier.core.base :=
  rfl

theorem dStageCertificate_empty_target (carrier : Carrier Label Choice) :
    (dStageCertificate carrier).emptyOutput.target = carrier.core.base :=
  rfl

theorem dStageCertificate_empty_level (carrier : Carrier Label Choice) :
    carrier.core.level (dStageCertificate carrier).emptyOutput.target =
      carrier.core.level carrier.core.base := by
  rw [dStageCertificate_empty_target]

theorem dStageCertificate_empty_profile (carrier : Carrier Label Choice) :
    carrier.profile.logVolume carrier.core.base ≤
      carrier.profile.logVolume (dStageCertificate carrier).emptyOutput.target := by
  rw [dStageCertificate_empty_target]

end ParametricDStage

end

end LeanFormal.IUT
