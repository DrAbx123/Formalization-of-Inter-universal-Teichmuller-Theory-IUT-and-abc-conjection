import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteRouteNaturality
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u v

namespace ParametricTheorem311

open MultiradialKernel
open MultiradialKernel.Core

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-!
  A source carrier is the smallest parameterized object needed by the
  multiradial route calculation.  The connector is deliberately a field:
  constructing it from the actual Hodge-theater data is a separate obligation
  and is not hidden in this generic layer.
-/
structure Carrier (Label : Type u) (Choice : Type v) [AddGroup Label] where
  core : Core Label Choice
  profile : Profile core
  connector : Choice → Choice → List (RouteStep Label)
  connector_horizontal : ∀ a b, ∀ step ∈ connector a b, horizontal step
  connector_target_same_level : ∀ {a b},
    core.level a = core.level b →
      applyRoute core (connector a b) a = b
  ind3_level_eq : ∀ n c, core.level (core.ind3 n c) = core.level c + n

def verticalBudget : List (RouteStep Label) → Nat
  | [] => 0
  | .ind1 _ :: rest => verticalBudget rest
  | .ind2 _ :: rest => verticalBudget rest
  | .ind3 n :: rest => n + verticalBudget rest

omit [AddGroup Label] in
@[simp] theorem verticalBudget_nil :
    verticalBudget ([] : List (RouteStep Label)) = 0 :=
  rfl

omit [AddGroup Label] in
@[simp] theorem verticalBudget_ind1 (g : Label)
    (route : List (RouteStep Label)) :
    verticalBudget (.ind1 g :: route) = verticalBudget route :=
  rfl

omit [AddGroup Label] in
@[simp] theorem verticalBudget_ind2 (g : Label)
    (route : List (RouteStep Label)) :
    verticalBudget (.ind2 g :: route) = verticalBudget route :=
  rfl

omit [AddGroup Label] in
@[simp] theorem verticalBudget_ind3 (n : Nat)
    (route : List (RouteStep Label)) :
    verticalBudget (.ind3 n :: route) = n + verticalBudget route :=
  rfl

omit [AddGroup Label] in
theorem verticalBudget_append (r₁ r₂ : List (RouteStep Label)) :
    verticalBudget (r₁ ++ r₂) = verticalBudget r₁ + verticalBudget r₂ := by
  induction r₁ with
  | nil => simp
  | cons step rest ih =>
      cases step <;>
        simp [ih, Nat.add_comm, Nat.add_left_comm]

omit [AddGroup Label] in
theorem verticalBudget_nonnegative
    (route : List (RouteStep Label)) :
    0 ≤ verticalBudget route :=
  Nat.zero_le _

def routeTarget (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) : Choice :=
  applyRoute carrier.core route c

@[simp] theorem routeTarget_nil (carrier : Carrier Label Choice) (c : Choice) :
    routeTarget carrier [] c = c :=
  rfl

@[simp] theorem routeTarget_cons (carrier : Carrier Label Choice)
    (step : RouteStep Label) (route : List (RouteStep Label)) (c : Choice) :
    routeTarget carrier (step :: route) c =
      routeTarget carrier route (applyStep carrier.core step c) :=
  rfl

theorem routeTarget_append (carrier : Carrier Label Choice)
    (r₁ r₂ : List (RouteStep Label)) (c : Choice) :
    routeTarget carrier (r₁ ++ r₂) c =
      routeTarget carrier r₂ (routeTarget carrier r₁ c) :=
  applyRoute_append carrier.core r₁ r₂ c

def horizontalRoute (_carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) : Prop :=
  ∀ step ∈ route, horizontal step

theorem horizontalRoute_connector (carrier : Carrier Label Choice)
    (a b : Choice) :
    horizontalRoute carrier (carrier.connector a b) :=
  carrier.connector_horizontal a b

theorem routeTarget_level_eq_budget (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    carrier.core.level (routeTarget carrier route c) =
      carrier.core.level c + verticalBudget route := by
  induction route generalizing c with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | ind1 g =>
          rw [routeTarget_cons, applyStep_ind1, verticalBudget_ind1]
          have h := ih (carrier.core.ind1 g c)
          rw [h, carrier.core.ind1_level]
      | ind2 g =>
          rw [routeTarget_cons, applyStep_ind2, verticalBudget_ind2]
          have h := ih (carrier.core.ind2 g c)
          rw [h, carrier.core.ind2_level]
      | ind3 n =>
          rw [routeTarget_cons, applyStep_ind3, verticalBudget_ind3]
          have h := ih (carrier.core.ind3 n c)
          rw [h, carrier.ind3_level_eq]
          omega

theorem routeTarget_level_monotone (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    carrier.core.level c ≤ carrier.core.level (routeTarget carrier route c) := by
  rw [routeTarget_level_eq_budget]
  omega

theorem routeTarget_profile_monotone (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    carrier.profile.logVolume c ≤
      carrier.profile.logVolume (routeTarget carrier route c) :=
  logVolume_applyRoute_le carrier.core carrier.profile route c

theorem routeTarget_profile_horizontal (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice)
    (hroute : horizontalRoute carrier route) :
    carrier.profile.logVolume (routeTarget carrier route c) =
      carrier.profile.logVolume c :=
  logVolume_applyRoute_horizontal carrier.profile route hroute c

theorem routeTarget_image_upper (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) (z : Real)
    (hz : z ∈ carrier.profile.possibleImage c) :
    ∃ w, w ∈ carrier.profile.possibleImage
      (routeTarget carrier route c) ∧ z ≤ w :=
  possibleImage_applyRoute_ind3_upper carrier.profile route c z hz

theorem connector_target (carrier : Carrier Label Choice)
    {a b : Choice} (hlevel : carrier.core.level a = carrier.core.level b) :
    routeTarget carrier (carrier.connector a b) a = b :=
  carrier.connector_target_same_level hlevel

theorem horizontalRoute_budget_zero (carrier : Carrier Label Choice)
    (route : List (RouteStep Label))
    (hroute : horizontalRoute carrier route) :
    verticalBudget route = 0 := by
  induction route with
  | nil => rfl
  | cons step rest ih =>
      have hs := hroute step (by simp)
      have hr : horizontalRoute carrier rest := by
        intro s hs'
        exact hroute s (by simp [hs'])
      cases step with
      | ind1 g =>
          simp [verticalBudget_ind1, ih hr]
      | ind2 g =>
          simp [verticalBudget_ind2, ih hr]
      | ind3 n =>
          exact False.elim hs

def canonicalRoute (carrier : Carrier Label Choice)
    (a b : Choice) (n : Nat) : List (RouteStep Label) :=
  carrier.connector a b ++ [.ind3 n]

theorem canonicalRoute_budget (carrier : Carrier Label Choice)
    (a b : Choice) (n : Nat) :
    verticalBudget (canonicalRoute carrier a b n) = n := by
  rw [canonicalRoute, verticalBudget_append,
    horizontalRoute_budget_zero carrier (carrier.connector a b)
      (horizontalRoute_connector carrier a b)]
  simp

theorem canonicalRoute_horizontal_prefix (carrier : Carrier Label Choice)
    (a b : Choice) (_n : Nat) :
    horizontalRoute carrier (carrier.connector a b) :=
  horizontalRoute_connector carrier a b

theorem canonicalRoute_target (carrier : Carrier Label Choice)
    (a b : Choice) (n : Nat)
    (hlevel : carrier.core.level a = carrier.core.level b) :
    routeTarget carrier (canonicalRoute carrier a b n) a =
      carrier.core.ind3 n b := by
  unfold canonicalRoute routeTarget
  rw [applyRoute_append, carrier.connector_target_same_level hlevel]
  rfl

theorem canonicalRoute_level (carrier : Carrier Label Choice)
    (a b : Choice) (n : Nat)
    (hlevel : carrier.core.level a = carrier.core.level b) :
    carrier.core.level (routeTarget carrier
      (canonicalRoute carrier a b n) a) = carrier.core.level b + n := by
  rw [canonicalRoute_target carrier a b n hlevel, carrier.ind3_level_eq]

theorem canonicalRoute_profile (carrier : Carrier Label Choice)
    (a b : Choice) (n : Nat)
    (hlevel : carrier.core.level a = carrier.core.level b) :
    carrier.profile.logVolume (routeTarget carrier
      (canonicalRoute carrier a b n) a) ≥
      carrier.profile.logVolume b := by
  rw [canonicalRoute_target carrier a b n hlevel]
  exact (carrier.profile.ind3_upper n b)

theorem canonicalRoute_image_upper (carrier : Carrier Label Choice)
    (a b : Choice) (n : Nat)
    (hlevel : carrier.core.level a = carrier.core.level b)
    (z : Real) (hz : z ∈ carrier.profile.possibleImage a) :
    ∃ w, w ∈ carrier.profile.possibleImage
      (carrier.core.ind3 n b) ∧ z ≤ w := by
  rw [← canonicalRoute_target carrier a b n hlevel]
  exact routeTarget_image_upper carrier
    (canonicalRoute carrier a b n) a z hz

structure Ind1Certificate (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) where
  target : Choice
  target_eq : target = carrier.core.ind1 g c
  level_eq : carrier.core.level target = carrier.core.level c
  profile_eq : carrier.profile.logVolume target = carrier.profile.logVolume c
  image_eq : carrier.profile.possibleImage target =
    carrier.profile.possibleImage c

def ind1Certificate (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) : Ind1Certificate carrier g c where
  target := carrier.core.ind1 g c
  target_eq := rfl
  level_eq := carrier.core.ind1_level g c
  profile_eq := carrier.profile.ind1_invariant g c
  image_eq := carrier.profile.possibleImage_ind1 g c

theorem ind1Certificate_target (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    (ind1Certificate carrier g c).target = carrier.core.ind1 g c :=
  rfl

theorem ind1Certificate_level (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    carrier.core.level (ind1Certificate carrier g c).target =
      carrier.core.level c :=
  (ind1Certificate carrier g c).level_eq

theorem ind1Certificate_profile (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    carrier.profile.logVolume (ind1Certificate carrier g c).target =
      carrier.profile.logVolume c :=
  (ind1Certificate carrier g c).profile_eq

theorem ind1Certificate_image (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    carrier.profile.possibleImage (ind1Certificate carrier g c).target =
      carrier.profile.possibleImage c :=
  (ind1Certificate carrier g c).image_eq

structure Ind2Certificate (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) where
  target : Choice
  target_eq : target = carrier.core.ind2 g c
  level_eq : carrier.core.level target = carrier.core.level c
  profile_eq : carrier.profile.logVolume target = carrier.profile.logVolume c
  image_eq : carrier.profile.possibleImage target =
    carrier.profile.possibleImage c

def ind2Certificate (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) : Ind2Certificate carrier g c where
  target := carrier.core.ind2 g c
  target_eq := rfl
  level_eq := carrier.core.ind2_level g c
  profile_eq := carrier.profile.ind2_invariant g c
  image_eq := carrier.profile.possibleImage_ind2 g c

theorem ind2Certificate_target (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    (ind2Certificate carrier g c).target = carrier.core.ind2 g c :=
  rfl

theorem ind2Certificate_level (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    carrier.core.level (ind2Certificate carrier g c).target =
      carrier.core.level c :=
  (ind2Certificate carrier g c).level_eq

theorem ind2Certificate_profile (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    carrier.profile.logVolume (ind2Certificate carrier g c).target =
      carrier.profile.logVolume c :=
  (ind2Certificate carrier g c).profile_eq

theorem ind2Certificate_image (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    carrier.profile.possibleImage (ind2Certificate carrier g c).target =
      carrier.profile.possibleImage c :=
  (ind2Certificate carrier g c).image_eq

structure Ind3Certificate (carrier : Carrier Label Choice)
    (n : Nat) (c : Choice) where
  target : Choice
  target_eq : target = carrier.core.ind3 n c
  level_eq : carrier.core.level target = carrier.core.level c + n
  profile_le : carrier.profile.logVolume c ≤ carrier.profile.logVolume target
  image_upper : ∀ z, z ∈ carrier.profile.possibleImage c →
    ∃ w, w ∈ carrier.profile.possibleImage target ∧ z ≤ w

def ind3Certificate (carrier : Carrier Label Choice)
    (n : Nat) (c : Choice) : Ind3Certificate carrier n c where
  target := carrier.core.ind3 n c
  target_eq := rfl
  level_eq := carrier.ind3_level_eq n c
  profile_le := carrier.profile.ind3_upper n c
  image_upper := carrier.profile.possibleImage_ind3 n c

theorem ind3Certificate_target (carrier : Carrier Label Choice)
    (n : Nat) (c : Choice) :
    (ind3Certificate carrier n c).target = carrier.core.ind3 n c :=
  rfl

theorem ind3Certificate_level (carrier : Carrier Label Choice)
    (n : Nat) (c : Choice) :
    carrier.core.level (ind3Certificate carrier n c).target =
      carrier.core.level c + n :=
  (ind3Certificate carrier n c).level_eq

theorem ind3Certificate_profile (carrier : Carrier Label Choice)
    (n : Nat) (c : Choice) :
    carrier.profile.logVolume c ≤
      carrier.profile.logVolume (ind3Certificate carrier n c).target :=
  (ind3Certificate carrier n c).profile_le

theorem ind3Certificate_image (carrier : Carrier Label Choice)
    (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ carrier.profile.possibleImage c) :
    ∃ w, w ∈ carrier.profile.possibleImage
      (ind3Certificate carrier n c).target ∧ z ≤ w :=
  (ind3Certificate carrier n c).image_upper z hz

structure IndependenceBundle (carrier : Carrier Label Choice) where
  ind1 : ∀ g c, Ind1Certificate carrier g c
  ind2 : ∀ g c, Ind2Certificate carrier g c
  ind3 : ∀ n c, Ind3Certificate carrier n c
  ind1_ind2_commute : ∀ g h c,
    (ind1 g (carrier.core.ind2 h c)).target =
      (ind2 h (carrier.core.ind1 g c)).target
  ind1_ind3_commute : ∀ g n c,
    (ind1 g (carrier.core.ind3 n c)).target =
      (ind3 n (carrier.core.ind1 g c)).target
  ind2_ind3_commute : ∀ g n c,
    (ind2 g (carrier.core.ind3 n c)).target =
      (ind3 n (carrier.core.ind2 g c)).target

def independenceBundle (carrier : Carrier Label Choice) :
    IndependenceBundle carrier where
  ind1 := ind1Certificate carrier
  ind2 := ind2Certificate carrier
  ind3 := ind3Certificate carrier
  ind1_ind2_commute := by
    intro g h c
    change carrier.core.ind1 g (carrier.core.ind2 h c) =
      carrier.core.ind2 h (carrier.core.ind1 g c)
    exact carrier.core.ind1_ind2_commute g h c
  ind1_ind3_commute := by
    intro g n c
    change carrier.core.ind1 g (carrier.core.ind3 n c) =
      carrier.core.ind3 n (carrier.core.ind1 g c)
    exact carrier.core.ind1_ind3_commute g n c
  ind2_ind3_commute := by
    intro g n c
    change carrier.core.ind2 g (carrier.core.ind3 n c) =
      carrier.core.ind3 n (carrier.core.ind2 g c)
    exact carrier.core.ind2_ind3_commute g n c

theorem independenceBundle_ind1 (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    (independenceBundle carrier).ind1 g c = ind1Certificate carrier g c :=
  rfl

theorem independenceBundle_ind2 (carrier : Carrier Label Choice)
    (g : Label) (c : Choice) :
    (independenceBundle carrier).ind2 g c = ind2Certificate carrier g c :=
  rfl

theorem independenceBundle_ind3 (carrier : Carrier Label Choice)
    (n : Nat) (c : Choice) :
    (independenceBundle carrier).ind3 n c = ind3Certificate carrier n c :=
  rfl

structure AlgorithmInput (carrier : Carrier Label Choice) where
  source : Choice
  route : List (RouteStep Label)
  source_image_nonempty :
    (carrier.profile.possibleImage source).Nonempty

def AlgorithmInput.empty (carrier : Carrier Label Choice) :
    AlgorithmInput carrier where
  source := carrier.core.base
  route := []
  source_image_nonempty := carrier.profile.possibleImage_nonempty carrier.core.base

def algorithmTarget (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) : Choice :=
  routeTarget carrier input.route input.source

structure AlgorithmOutput (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) where
  target : Choice
  target_eq : target = algorithmTarget carrier input
  level_monotone : carrier.core.level input.source ≤ carrier.core.level target
  profile_monotone : carrier.profile.logVolume input.source ≤
    carrier.profile.logVolume target
  target_image_upper : ∀ z, z ∈ carrier.profile.possibleImage input.source →
    ∃ w, w ∈ carrier.profile.possibleImage target ∧ z ≤ w

def runAlgorithm (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) : AlgorithmOutput carrier input where
  target := algorithmTarget carrier input
  target_eq := rfl
  level_monotone := routeTarget_level_monotone carrier input.route input.source
  profile_monotone := routeTarget_profile_monotone carrier input.route input.source
  target_image_upper := routeTarget_image_upper carrier input.route input.source

theorem runAlgorithm_target (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) :
    (runAlgorithm carrier input).target = algorithmTarget carrier input :=
  rfl

theorem runAlgorithm_level (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) :
    carrier.core.level input.source ≤
      carrier.core.level (runAlgorithm carrier input).target :=
  (runAlgorithm carrier input).level_monotone

theorem runAlgorithm_profile (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) :
    carrier.profile.logVolume input.source ≤
      carrier.profile.logVolume (runAlgorithm carrier input).target :=
  (runAlgorithm carrier input).profile_monotone

theorem runAlgorithm_image (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) (z : Real)
    (hz : z ∈ carrier.profile.possibleImage input.source) :
    ∃ w, w ∈ carrier.profile.possibleImage
      (runAlgorithm carrier input).target ∧ z ≤ w :=
  (runAlgorithm carrier input).target_image_upper z hz

structure CanonicalInput (carrier : Carrier Label Choice) where
  left : Choice
  right : Choice
  lift : Nat
  same_level : carrier.core.level left = carrier.core.level right
  source_image_nonempty :
    (carrier.profile.possibleImage left).Nonempty

def canonicalInput (carrier : Carrier Label Choice)
    (left right : Choice) (lift : Nat)
    (hlevel : carrier.core.level left = carrier.core.level right) :
    CanonicalInput carrier where
  left := left
  right := right
  lift := lift
  same_level := hlevel
  source_image_nonempty := carrier.profile.possibleImage_nonempty left

def canonicalAlgorithmInput (carrier : Carrier Label Choice)
    (input : CanonicalInput carrier) : AlgorithmInput carrier where
  source := input.left
  route := canonicalRoute carrier input.left input.right input.lift
  source_image_nonempty := input.source_image_nonempty

theorem canonicalAlgorithmInput_route (carrier : Carrier Label Choice)
    (input : CanonicalInput carrier) :
    (canonicalAlgorithmInput carrier input).route =
      canonicalRoute carrier input.left input.right input.lift :=
  rfl

theorem canonicalAlgorithmInput_source (carrier : Carrier Label Choice)
    (input : CanonicalInput carrier) :
    (canonicalAlgorithmInput carrier input).source = input.left :=
  rfl

theorem canonicalAlgorithmOutput_target (carrier : Carrier Label Choice)
    (input : CanonicalInput carrier) :
    (runAlgorithm carrier (canonicalAlgorithmInput carrier input)).target =
      carrier.core.ind3 input.lift input.right := by
  rw [runAlgorithm_target, algorithmTarget,
    canonicalAlgorithmInput_route, canonicalAlgorithmInput_source]
  exact canonicalRoute_target carrier input.left input.right input.lift
    input.same_level

theorem canonicalAlgorithmOutput_level (carrier : Carrier Label Choice)
    (input : CanonicalInput carrier) :
    carrier.core.level
        (runAlgorithm carrier (canonicalAlgorithmInput carrier input)).target =
      carrier.core.level input.right + input.lift := by
  rw [canonicalAlgorithmOutput_target carrier input,
    carrier.ind3_level_eq]

theorem canonicalAlgorithmOutput_profile (carrier : Carrier Label Choice)
    (input : CanonicalInput carrier) :
    carrier.profile.logVolume input.left ≤
      carrier.profile.logVolume
        (runAlgorithm carrier (canonicalAlgorithmInput carrier input)).target := by
  exact (runAlgorithm carrier (canonicalAlgorithmInput carrier input)).profile_monotone

theorem canonicalAlgorithmOutput_image (carrier : Carrier Label Choice)
    (input : CanonicalInput carrier) (z : Real)
    (hz : z ∈ carrier.profile.possibleImage input.left) :
    ∃ w, w ∈ carrier.profile.possibleImage
      (runAlgorithm carrier (canonicalAlgorithmInput carrier input)).target ∧ z ≤ w := by
  exact (runAlgorithm carrier (canonicalAlgorithmInput carrier input)).target_image_upper z hz

structure Theorem311Interface (carrier : Carrier Label Choice) where
  input : AlgorithmInput carrier
  output : AlgorithmOutput carrier input
  output_is_run : output = runAlgorithm carrier input

def theorem311Interface (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) : Theorem311Interface carrier where
  input := input
  output := runAlgorithm carrier input
  output_is_run := rfl

theorem theorem311Interface_level (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) :
    carrier.core.level input.source ≤
      carrier.core.level (theorem311Interface carrier input).output.target := by
  exact (theorem311Interface carrier input).output.level_monotone

theorem theorem311Interface_profile (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) :
    carrier.profile.logVolume input.source ≤
      carrier.profile.logVolume (theorem311Interface carrier input).output.target := by
  exact (theorem311Interface carrier input).output.profile_monotone

theorem theorem311Interface_image (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) (z : Real)
    (hz : z ∈ carrier.profile.possibleImage input.source) :
    ∃ w, w ∈ carrier.profile.possibleImage
      (theorem311Interface carrier input).output.target ∧ z ≤ w := by
  exact (theorem311Interface carrier input).output.target_image_upper z hz

end ParametricTheorem311

end

end LeanFormal.IUT
