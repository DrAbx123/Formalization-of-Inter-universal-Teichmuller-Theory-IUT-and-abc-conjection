import LeanFormal.IUT.IUTIII.Theorem311.ParametricCarrier
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

namespace SourceFiniteParameterized

open ConcreteFiniteTheorem311
open MultiradialKernel
open ParametricTheorem311
open SourceFiniteMultiradial
open SourceFiniteRouteArithmetic
open SourceFiniteRouteNaturality

local instance primeFactForSourceFiniteParameterized (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) := l.factPrime

abbrev Label (l : PrimeGeFive) := ConcreteFiniteTheorem311.finiteLabel l
abbrev Choice (l : PrimeGeFive) := ConcreteFiniteTheorem311.ProcessionChoice l
abbrev Step (l : PrimeGeFive) := RouteStep (Label l)
abbrev Carrier (l : PrimeGeFive) :=
  ParametricTheorem311.Carrier (Label l) (Choice l)

def carrier (l : PrimeGeFive) : Carrier l where
  core := SourceFiniteMultiradial.core l
  profile := SourceFiniteMultiradial.profile l
  connector := sameLevelRoute
  connector_horizontal := by
    intro a b step hstep
    exact sameLevelRoute_horizontal a b step hstep
  connector_target_same_level := by
    intro a b hlevel
    exact sameLevelRoute_apply hlevel
  ind3_level_eq := by
    intro n c
    rfl

@[simp] theorem carrier_core (l : PrimeGeFive) :
    (carrier l).core = SourceFiniteMultiradial.core l :=
  rfl

@[simp] theorem carrier_profile (l : PrimeGeFive) :
    (carrier l).profile = SourceFiniteMultiradial.profile l :=
  rfl

@[simp] theorem carrier_connector (l : PrimeGeFive)
    (a b : Choice l) :
    (carrier l).connector a b = sameLevelRoute a b :=
  rfl

theorem carrier_connector_horizontal (l : PrimeGeFive)
    (a b : Choice l) :
    ParametricTheorem311.horizontalRoute (carrier l)
      ((carrier l).connector a b) :=
  ParametricTheorem311.horizontalRoute_connector (carrier l) a b

theorem carrier_connector_target (l : PrimeGeFive)
    {a b : Choice l}
    (hlevel : (carrier l).core.level a = (carrier l).core.level b) :
    ParametricTheorem311.routeTarget (carrier l)
        ((carrier l).connector a b) a = b :=
  ParametricTheorem311.connector_target (carrier l) hlevel

theorem carrier_ind3_level (l : PrimeGeFive)
    (n : Nat) (c : Choice l) :
    (carrier l).core.level ((carrier l).core.ind3 n c) =
      (carrier l).core.level c + n := by
  rfl

def finiteRouteTarget (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) : Choice l :=
  ParametricTheorem311.routeTarget (carrier l) route c

theorem finiteRouteTarget_eq_source (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    finiteRouteTarget l route c = target l route c :=
  rfl

theorem finiteRouteTarget_level_budget (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (carrier l).core.level (finiteRouteTarget l route c) =
      (carrier l).core.level c +
        ParametricTheorem311.verticalBudget route :=
  ParametricTheorem311.routeTarget_level_eq_budget (carrier l) route c

theorem finiteRouteTarget_profile_bound (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) :
    (carrier l).profile.logVolume c ≤
      (carrier l).profile.logVolume (finiteRouteTarget l route c) :=
  ParametricTheorem311.routeTarget_profile_monotone (carrier l) route c

theorem finiteRouteTarget_image_upper (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) (z : Real)
    (hz : z ∈ (carrier l).profile.possibleImage c) :
    ∃ w, w ∈ (carrier l).profile.possibleImage
      (finiteRouteTarget l route c) ∧ z ≤ w :=
  ParametricTheorem311.routeTarget_image_upper (carrier l) route c z hz

def finiteCanonicalRoute (l : PrimeGeFive)
    (a b : Choice l) (n : Nat) : List (Step l) :=
  ParametricTheorem311.canonicalRoute (carrier l) a b n

theorem finiteCanonicalRoute_eq_source (l : PrimeGeFive)
    (a b : Choice l) (n : Nat) :
    finiteCanonicalRoute l a b n = canonicalRoute a b n :=
  rfl

theorem finiteCanonicalRoute_budget (l : PrimeGeFive)
    (a b : Choice l) (n : Nat) :
    ParametricTheorem311.verticalBudget (finiteCanonicalRoute l a b n) = n :=
  ParametricTheorem311.canonicalRoute_budget (carrier l) a b n

theorem finiteCanonicalRoute_horizontal_prefix (l : PrimeGeFive)
    (a b : Choice l) (n : Nat) :
    ParametricTheorem311.horizontalRoute (carrier l)
      ((carrier l).connector a b) :=
  ParametricTheorem311.canonicalRoute_horizontal_prefix (carrier l) a b n

theorem finiteCanonicalRoute_target (l : PrimeGeFive)
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    finiteRouteTarget l (finiteCanonicalRoute l a b n) a =
      ProcessionChoice.ind3Lift n b := by
  rw [finiteCanonicalRoute_eq_source, finiteRouteTarget_eq_source]
  exact canonicalRoute_target a b n hlevel

theorem finiteCanonicalRoute_level (l : PrimeGeFive)
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    (finiteRouteTarget l (finiteCanonicalRoute l a b n) a).upperSemiLevel =
      b.upperSemiLevel + n := by
  rw [finiteCanonicalRoute_target l a b n hlevel]
  exact ProcessionChoice.ind3_upperSemiLevel n b

theorem finiteCanonicalRoute_profile (l : PrimeGeFive)
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    (carrier l).profile.logVolume
        (finiteRouteTarget l (finiteCanonicalRoute l a b n) a) ≥
      (carrier l).profile.logVolume b := by
  rw [finiteCanonicalRoute_target l a b n hlevel]
  exact (carrier l).profile.ind3_upper n b

theorem finiteCanonicalRoute_image (l : PrimeGeFive)
    (a b : Choice l) (n : Nat)
    (_hlevel : a.upperSemiLevel = b.upperSemiLevel)
    (z : Real) (hz : z ∈ (carrier l).profile.possibleImage a) :
    ∃ w, w ∈ (carrier l).profile.possibleImage
      (finiteRouteTarget l (finiteCanonicalRoute l a b n) a) ∧ z ≤ w := by
  exact finiteRouteTarget_image_upper l (finiteCanonicalRoute l a b n) a z hz

def finiteAlgorithmInput (l : PrimeGeFive)
    (source : Choice l) (route : List (Step l)) :
    ParametricTheorem311.AlgorithmInput (carrier l) where
  source := source
  route := route
  source_image_nonempty := (carrier l).profile.possibleImage_nonempty source

@[simp] theorem finiteAlgorithmInput_source (l : PrimeGeFive)
    (source : Choice l) (route : List (Step l)) :
    (finiteAlgorithmInput l source route).source = source :=
  rfl

@[simp] theorem finiteAlgorithmInput_route (l : PrimeGeFive)
    (source : Choice l) (route : List (Step l)) :
    (finiteAlgorithmInput l source route).route = route :=
  rfl

def finiteAlgorithmOutput (l : PrimeGeFive)
    (source : Choice l) (route : List (Step l)) :=
  ParametricTheorem311.runAlgorithm (carrier l)
    (finiteAlgorithmInput l source route)

theorem finiteAlgorithmOutput_target (l : PrimeGeFive)
    (source : Choice l) (route : List (Step l)) :
    (finiteAlgorithmOutput l source route).target =
      finiteRouteTarget l route source := by
  rfl

theorem finiteAlgorithmOutput_level (l : PrimeGeFive)
    (source : Choice l) (route : List (Step l)) :
    (carrier l).core.level source ≤
      (carrier l).core.level (finiteAlgorithmOutput l source route).target := by
  exact (finiteAlgorithmOutput l source route).level_monotone

theorem finiteAlgorithmOutput_profile (l : PrimeGeFive)
    (source : Choice l) (route : List (Step l)) :
    (carrier l).profile.logVolume source ≤
      (carrier l).profile.logVolume
        (finiteAlgorithmOutput l source route).target := by
  exact (finiteAlgorithmOutput l source route).profile_monotone

theorem finiteAlgorithmOutput_image (l : PrimeGeFive)
    (source : Choice l) (route : List (Step l)) (z : Real)
    (hz : z ∈ (carrier l).profile.possibleImage source) :
    ∃ w, w ∈ (carrier l).profile.possibleImage
      (finiteAlgorithmOutput l source route).target ∧ z ≤ w := by
  exact (finiteAlgorithmOutput l source route).target_image_upper z hz

def finiteCanonicalInput (l : PrimeGeFive)
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    ParametricTheorem311.CanonicalInput (carrier l) :=
  ParametricTheorem311.canonicalInput (carrier l) a b n hlevel

def finiteCanonicalAlgorithmInput (l : PrimeGeFive)
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    ParametricTheorem311.AlgorithmInput (carrier l) :=
  ParametricTheorem311.canonicalAlgorithmInput (carrier l)
    (finiteCanonicalInput l a b n hlevel)

def finiteCanonicalAlgorithmOutput (l : PrimeGeFive)
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :=
  ParametricTheorem311.runAlgorithm (carrier l)
    (finiteCanonicalAlgorithmInput l a b n hlevel)

theorem finiteCanonicalAlgorithmOutput_target (l : PrimeGeFive)
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    (finiteCanonicalAlgorithmOutput l a b n hlevel).target =
      ProcessionChoice.ind3Lift n b := by
  exact ParametricTheorem311.canonicalAlgorithmOutput_target (carrier l)
    (finiteCanonicalInput l a b n hlevel)

theorem finiteCanonicalAlgorithmOutput_level (l : PrimeGeFive)
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    (carrier l).core.level
        (finiteCanonicalAlgorithmOutput l a b n hlevel).target =
      (carrier l).core.level b + n := by
  exact ParametricTheorem311.canonicalAlgorithmOutput_level (carrier l)
    (finiteCanonicalInput l a b n hlevel)

theorem finiteCanonicalAlgorithmOutput_profile (l : PrimeGeFive)
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    (carrier l).profile.logVolume a ≤
      (carrier l).profile.logVolume
        (finiteCanonicalAlgorithmOutput l a b n hlevel).target := by
  exact ParametricTheorem311.canonicalAlgorithmOutput_profile (carrier l)
    (finiteCanonicalInput l a b n hlevel)

theorem finiteCanonicalAlgorithmOutput_image (l : PrimeGeFive)
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel)
    (z : Real) (hz : z ∈ (carrier l).profile.possibleImage a) :
    ∃ w, w ∈ (carrier l).profile.possibleImage
      (finiteCanonicalAlgorithmOutput l a b n hlevel).target ∧ z ≤ w := by
  exact ParametricTheorem311.canonicalAlgorithmOutput_image (carrier l)
    (finiteCanonicalInput l a b n hlevel) z hz

structure FiniteTheorem311Witness (l : PrimeGeFive) where
  source : Choice l
  route : List (Step l)
  source_nonempty :
    ((carrier l).profile.possibleImage source).Nonempty
  output : ParametricTheorem311.AlgorithmOutput (carrier l)
    (finiteAlgorithmInput l source route)

def finiteTheorem311Witness (l : PrimeGeFive)
    (source : Choice l) (route : List (Step l)) :
    FiniteTheorem311Witness l where
  source := source
  route := route
  source_nonempty := (carrier l).profile.possibleImage_nonempty source
  output := finiteAlgorithmOutput l source route

theorem finiteTheorem311Witness_target (l : PrimeGeFive)
    (source : Choice l) (route : List (Step l)) :
    (finiteTheorem311Witness l source route).output.target =
      finiteRouteTarget l route source :=
  finiteAlgorithmOutput_target l source route

theorem finiteTheorem311Witness_level (l : PrimeGeFive)
    (source : Choice l) (route : List (Step l)) :
    (carrier l).core.level source ≤
      (carrier l).core.level
        (finiteTheorem311Witness l source route).output.target :=
  finiteAlgorithmOutput_level l source route

theorem finiteTheorem311Witness_profile (l : PrimeGeFive)
    (source : Choice l) (route : List (Step l)) :
    (carrier l).profile.logVolume source ≤
      (carrier l).profile.logVolume
        (finiteTheorem311Witness l source route).output.target :=
  finiteAlgorithmOutput_profile l source route

theorem finiteTheorem311Witness_image (l : PrimeGeFive)
    (source : Choice l) (route : List (Step l)) (z : Real)
    (hz : z ∈ (carrier l).profile.possibleImage source) :
    ∃ w, w ∈ (carrier l).profile.possibleImage
      (finiteTheorem311Witness l source route).output.target ∧ z ≤ w := by
  exact finiteAlgorithmOutput_image l source route z hz

end SourceFiniteParameterized

end

end LeanFormal.IUT
