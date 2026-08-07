import LeanFormal.IUT.IUTIII.Theorem311.ParametricDStage
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

namespace ParametricRouteAlgebra

open MultiradialKernel
open MultiradialKernel.Core
open ParametricTheorem311

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

theorem horizontal_generated (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice)
    (hroute : horizontalRoute carrier route) :
    GeneratedEqualityRelation carrier.core c (routeTarget carrier route c) :=
  generated_of_horizontal_route carrier.core route hroute c

theorem horizontal_quotient_eq (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice)
    (hroute : horizontalRoute carrier route) :
    Core.generatedQuotientMap carrier.core c =
      Core.generatedQuotientMap carrier.core (routeTarget carrier route c) :=
  Core.generatedQuotientMap_eq_of_generated carrier.core
    (horizontal_generated carrier route c hroute)

theorem horizontal_profile_eq (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice)
    (hroute : horizontalRoute carrier route) :
    carrier.profile.logVolume (routeTarget carrier route c) =
      carrier.profile.logVolume c :=
  routeTarget_profile_horizontal carrier route c hroute

theorem horizontal_image_eq (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice)
    (hroute : horizontalRoute carrier route) :
    carrier.profile.possibleImage (routeTarget carrier route c) =
      carrier.profile.possibleImage c := by
  exact possibleImage_applyRoute_horizontal carrier.profile route hroute c

theorem connector_generated (carrier : Carrier Label Choice)
    {a b : Choice}
    (hlevel : carrier.core.level a = carrier.core.level b) :
    GeneratedEqualityRelation carrier.core a b := by
  rw [← carrier.connector_target_same_level hlevel]
  exact horizontal_generated carrier (carrier.connector a b) a
    (horizontalRoute_connector carrier a b)

theorem connector_quotient_eq (carrier : Carrier Label Choice)
    {a b : Choice}
    (hlevel : carrier.core.level a = carrier.core.level b) :
    Core.generatedQuotientMap carrier.core a =
      Core.generatedQuotientMap carrier.core b :=
  Core.generatedQuotientMap_eq_of_generated carrier.core
    (connector_generated carrier hlevel)

theorem connector_profile_eq (carrier : Carrier Label Choice)
    {a b : Choice}
    (hlevel : carrier.core.level a = carrier.core.level b) :
    carrier.profile.logVolume a = carrier.profile.logVolume b := by
  rw [← carrier.connector_target_same_level hlevel]
  exact (horizontal_profile_eq carrier (carrier.connector a b) a
    (horizontalRoute_connector carrier a b)).symm

theorem connector_image_eq (carrier : Carrier Label Choice)
    {a b : Choice}
    (hlevel : carrier.core.level a = carrier.core.level b) :
    carrier.profile.possibleImage a = carrier.profile.possibleImage b := by
  rw [← carrier.connector_target_same_level hlevel]
  exact (horizontal_image_eq carrier (carrier.connector a b) a
    (horizontalRoute_connector carrier a b)).symm

theorem route_budget_append (_carrier : Carrier Label Choice)
    (r₁ r₂ : List (RouteStep Label)) :
    verticalBudget (r₁ ++ r₂) = verticalBudget r₁ + verticalBudget r₂ :=
  verticalBudget_append r₁ r₂

theorem route_level_append (carrier : Carrier Label Choice)
    (r₁ r₂ : List (RouteStep Label)) (c : Choice) :
    carrier.core.level (routeTarget carrier (r₁ ++ r₂) c) =
      carrier.core.level c + verticalBudget r₁ + verticalBudget r₂ := by
  rw [routeTarget_append, routeTarget_level_eq_budget,
    routeTarget_level_eq_budget]

theorem route_profile_append_bound (carrier : Carrier Label Choice)
    (r₁ r₂ : List (RouteStep Label)) (c : Choice) :
    carrier.profile.logVolume c ≤
      carrier.profile.logVolume (routeTarget carrier (r₁ ++ r₂) c) :=
  routeTarget_profile_monotone carrier (r₁ ++ r₂) c

theorem route_image_append_upper (carrier : Carrier Label Choice)
    (r₁ r₂ : List (RouteStep Label)) (c : Choice) (z : Real)
    (hz : z ∈ carrier.profile.possibleImage c) :
    ∃ w, w ∈ carrier.profile.possibleImage
      (routeTarget carrier (r₁ ++ r₂) c) ∧ z ≤ w :=
  routeTarget_image_upper carrier (r₁ ++ r₂) c z hz

structure HorizontalRouteCertificate (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) where
  target : Choice
  target_eq : target = routeTarget carrier route c
  horizontal : horizontalRoute carrier route
  quotient_eq : Core.generatedQuotientMap carrier.core c =
    Core.generatedQuotientMap carrier.core target
  profile_eq : carrier.profile.logVolume target =
    carrier.profile.logVolume c
  image_eq : carrier.profile.possibleImage target =
    carrier.profile.possibleImage c

def horizontalRouteCertificate (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice)
    (hroute : horizontalRoute carrier route) :
    HorizontalRouteCertificate carrier route c where
  target := routeTarget carrier route c
  target_eq := rfl
  horizontal := hroute
  quotient_eq := horizontal_quotient_eq carrier route c hroute
  profile_eq := horizontal_profile_eq carrier route c hroute
  image_eq := horizontal_image_eq carrier route c hroute

theorem horizontalRouteCertificate_target (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice)
    (hroute : horizontalRoute carrier route) :
    (horizontalRouteCertificate carrier route c hroute).target =
      routeTarget carrier route c :=
  rfl

theorem horizontalRouteCertificate_quotient (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice)
    (hroute : horizontalRoute carrier route) :
    Core.generatedQuotientMap carrier.core c =
      Core.generatedQuotientMap carrier.core
        (horizontalRouteCertificate carrier route c hroute).target :=
  (horizontalRouteCertificate carrier route c hroute).quotient_eq

theorem horizontalRouteCertificate_profile (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice)
    (hroute : horizontalRoute carrier route) :
    carrier.profile.logVolume
        (horizontalRouteCertificate carrier route c hroute).target =
      carrier.profile.logVolume c :=
  (horizontalRouteCertificate carrier route c hroute).profile_eq

theorem horizontalRouteCertificate_image (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice)
    (hroute : horizontalRoute carrier route) :
    carrier.profile.possibleImage
        (horizontalRouteCertificate carrier route c hroute).target =
      carrier.profile.possibleImage c :=
  (horizontalRouteCertificate carrier route c hroute).image_eq

structure RouteCompositionCertificate (carrier : Carrier Label Choice)
    (r₁ r₂ : List (RouteStep Label)) (c : Choice) where
  first : Choice
  first_eq : first = routeTarget carrier r₁ c
  final : Choice
  final_eq : final = routeTarget carrier r₂ first
  append_eq : final = routeTarget carrier (r₁ ++ r₂) c
  budget_eq : carrier.core.level final =
    carrier.core.level c + verticalBudget r₁ + verticalBudget r₂
  profile_bound : carrier.profile.logVolume c ≤ carrier.profile.logVolume final

def routeCompositionCertificate (carrier : Carrier Label Choice)
    (r₁ r₂ : List (RouteStep Label)) (c : Choice) :
    RouteCompositionCertificate carrier r₁ r₂ c where
  first := routeTarget carrier r₁ c
  first_eq := rfl
  final := routeTarget carrier r₂ (routeTarget carrier r₁ c)
  final_eq := rfl
  append_eq := (routeTarget_append carrier r₁ r₂ c).symm
  budget_eq := by
    rw [← routeTarget_append]
    exact route_level_append carrier r₁ r₂ c
  profile_bound := by
    exact (routeTarget_profile_monotone carrier r₁ c).trans
      (routeTarget_profile_monotone carrier r₂
        (routeTarget carrier r₁ c))

theorem routeCompositionCertificate_first (carrier : Carrier Label Choice)
    (r₁ r₂ : List (RouteStep Label)) (c : Choice) :
    (routeCompositionCertificate carrier r₁ r₂ c).first =
      routeTarget carrier r₁ c :=
  rfl

theorem routeCompositionCertificate_final (carrier : Carrier Label Choice)
    (r₁ r₂ : List (RouteStep Label)) (c : Choice) :
    (routeCompositionCertificate carrier r₁ r₂ c).final =
      routeTarget carrier r₂ (routeTarget carrier r₁ c) :=
  rfl

theorem routeCompositionCertificate_append (carrier : Carrier Label Choice)
    (r₁ r₂ : List (RouteStep Label)) (c : Choice) :
    (routeCompositionCertificate carrier r₁ r₂ c).final =
      routeTarget carrier (r₁ ++ r₂) c :=
  (routeCompositionCertificate carrier r₁ r₂ c).append_eq

theorem routeCompositionCertificate_budget (carrier : Carrier Label Choice)
    (r₁ r₂ : List (RouteStep Label)) (c : Choice) :
    carrier.core.level (routeCompositionCertificate carrier r₁ r₂ c).final =
      carrier.core.level c + verticalBudget r₁ + verticalBudget r₂ :=
  (routeCompositionCertificate carrier r₁ r₂ c).budget_eq

theorem routeCompositionCertificate_profile (carrier : Carrier Label Choice)
    (r₁ r₂ : List (RouteStep Label)) (c : Choice) :
    carrier.profile.logVolume c ≤
      carrier.profile.logVolume
        (routeCompositionCertificate carrier r₁ r₂ c).final :=
  (routeCompositionCertificate carrier r₁ r₂ c).profile_bound

structure CanonicalRouteCertificate (carrier : Carrier Label Choice)
    (a b : Choice) (n : Nat)
    (hlevel : carrier.core.level a = carrier.core.level b) where
  route : List (RouteStep Label)
  route_eq : route = canonicalRoute carrier a b n
  horizontal_prefix : horizontalRoute carrier (carrier.connector a b)
  target : Choice
  target_eq : target = carrier.core.ind3 n b
  level_eq : carrier.core.level target = carrier.core.level b + n
  quotient_prefix : Core.generatedQuotientMap carrier.core a =
    Core.generatedQuotientMap carrier.core b
  profile_bound : carrier.profile.logVolume a ≤ carrier.profile.logVolume target
  image_upper : ∀ z, z ∈ carrier.profile.possibleImage a →
    ∃ w, w ∈ carrier.profile.possibleImage target ∧ z ≤ w

def canonicalRouteCertificate (carrier : Carrier Label Choice)
    (a b : Choice) (n : Nat)
    (hlevel : carrier.core.level a = carrier.core.level b) :
    CanonicalRouteCertificate carrier a b n hlevel where
  route := canonicalRoute carrier a b n
  route_eq := rfl
  horizontal_prefix := canonicalRoute_horizontal_prefix carrier a b n
  target := routeTarget carrier (canonicalRoute carrier a b n) a
  target_eq := canonicalRoute_target carrier a b n hlevel
  level_eq := canonicalRoute_level carrier a b n hlevel
  quotient_prefix := connector_quotient_eq carrier hlevel
  profile_bound := by
    exact routeTarget_profile_monotone carrier
      (canonicalRoute carrier a b n) a
  image_upper := routeTarget_image_upper carrier
      (canonicalRoute carrier a b n) a

theorem canonicalRouteCertificate_route (carrier : Carrier Label Choice)
    (a b : Choice) (n : Nat)
    (hlevel : carrier.core.level a = carrier.core.level b) :
    (canonicalRouteCertificate carrier a b n hlevel).route =
      canonicalRoute carrier a b n :=
  rfl

theorem canonicalRouteCertificate_target (carrier : Carrier Label Choice)
    (a b : Choice) (n : Nat)
    (hlevel : carrier.core.level a = carrier.core.level b) :
    (canonicalRouteCertificate carrier a b n hlevel).target =
      carrier.core.ind3 n b :=
  (canonicalRouteCertificate carrier a b n hlevel).target_eq

theorem canonicalRouteCertificate_level (carrier : Carrier Label Choice)
    (a b : Choice) (n : Nat)
    (hlevel : carrier.core.level a = carrier.core.level b) :
    carrier.core.level
        (canonicalRouteCertificate carrier a b n hlevel).target =
      carrier.core.level b + n :=
  (canonicalRouteCertificate carrier a b n hlevel).level_eq

theorem canonicalRouteCertificate_quotient (carrier : Carrier Label Choice)
    (a b : Choice) (n : Nat)
    (hlevel : carrier.core.level a = carrier.core.level b) :
    Core.generatedQuotientMap carrier.core a =
      Core.generatedQuotientMap carrier.core b :=
  (canonicalRouteCertificate carrier a b n hlevel).quotient_prefix

theorem canonicalRouteCertificate_profile (carrier : Carrier Label Choice)
    (a b : Choice) (n : Nat)
    (hlevel : carrier.core.level a = carrier.core.level b) :
    carrier.profile.logVolume a ≤
      carrier.profile.logVolume
        (canonicalRouteCertificate carrier a b n hlevel).target :=
  (canonicalRouteCertificate carrier a b n hlevel).profile_bound

theorem canonicalRouteCertificate_image (carrier : Carrier Label Choice)
    (a b : Choice) (n : Nat)
    (hlevel : carrier.core.level a = carrier.core.level b)
    (z : Real) (hz : z ∈ carrier.profile.possibleImage a) :
    ∃ w, w ∈ carrier.profile.possibleImage
      (canonicalRouteCertificate carrier a b n hlevel).target ∧ z ≤ w :=
  (canonicalRouteCertificate carrier a b n hlevel).image_upper z hz

structure RouteBudgetCertificate (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) where
  budget : Nat
  budget_eq : budget = verticalBudget route
  target_level : carrier.core.level (routeTarget carrier route c) =
    carrier.core.level c + budget
  nonnegative : 0 ≤ budget

def routeBudgetCertificate (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    RouteBudgetCertificate carrier route c where
  budget := verticalBudget route
  budget_eq := rfl
  target_level := routeTarget_level_eq_budget carrier route c
  nonnegative := Nat.zero_le _

theorem routeBudgetCertificate_budget (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    (routeBudgetCertificate carrier route c).budget = verticalBudget route :=
  rfl

theorem routeBudgetCertificate_level (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    carrier.core.level (routeTarget carrier route c) =
      carrier.core.level c + (routeBudgetCertificate carrier route c).budget :=
  (routeBudgetCertificate carrier route c).target_level

theorem routeBudgetCertificate_nonnegative (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    0 ≤ (routeBudgetCertificate carrier route c).budget :=
  (routeBudgetCertificate carrier route c).nonnegative

end ParametricRouteAlgebra

end

end LeanFormal.IUT
