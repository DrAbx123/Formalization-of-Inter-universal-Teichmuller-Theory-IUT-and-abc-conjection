import LeanFormal.IUT.IUTIII.Theorem311.MultiradialOutputKernel
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic

namespace LeanFormal.IUT

universe u v

namespace MultiradialKernel

open Core

structure Profile {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : Core Label Choice) where
  logVolume : Choice → Real
  possibleImage : Choice → Set Real
  ind1_invariant : ∀ g c,
    logVolume (core.ind1 g c) = logVolume c
  ind2_invariant : ∀ g c,
    logVolume (core.ind2 g c) = logVolume c
  ind3_upper : ∀ n c,
    logVolume c ≤ logVolume (core.ind3 n c)
  possibleImage_nonempty : ∀ c, (possibleImage c).Nonempty
  possibleImage_ind1 : ∀ g c,
    possibleImage (core.ind1 g c) = possibleImage c
  possibleImage_ind2 : ∀ g c,
    possibleImage (core.ind2 g c) = possibleImage c
  possibleImage_ind3 : ∀ n c z, z ∈ possibleImage c →
    ∃ w, w ∈ possibleImage (core.ind3 n c) ∧ z ≤ w

namespace Profile

variable {Label : Type u} {Choice : Type v} [AddGroup Label]
  {core : Core Label Choice} (profile : Profile core)

theorem ind1_ind2_commute_log (g h : Label) (c : Choice) :
    profile.logVolume (core.ind1 g (core.ind2 h c)) =
      profile.logVolume (core.ind2 h (core.ind1 g c)) := by
  rw [profile.ind1_invariant, profile.ind2_invariant,
    profile.ind2_invariant, profile.ind1_invariant]

theorem ind1_ind3_commute_log (g : Label) (n : Nat) (c : Choice) :
    profile.logVolume (core.ind1 g (core.ind3 n c)) =
      profile.logVolume (core.ind3 n (core.ind1 g c)) := by
  rw [core.ind1_ind3_commute]

theorem ind2_ind3_commute_log (g : Label) (n : Nat) (c : Choice) :
    profile.logVolume (core.ind2 g (core.ind3 n c)) =
      profile.logVolume (core.ind3 n (core.ind2 g c)) := by
  rw [core.ind2_ind3_commute]

theorem logVolume_respects_ind1Step {a b : Choice}
    (h : Core.Ind1Step core a b) :
    profile.logVolume a = profile.logVolume b := by
  rcases h with ⟨g, rfl⟩
  exact (profile.ind1_invariant g a).symm

theorem logVolume_respects_ind2Step {a b : Choice}
    (h : Core.Ind2Step core a b) :
    profile.logVolume a = profile.logVolume b := by
  rcases h with ⟨g, rfl⟩
  exact (profile.ind2_invariant g a).symm

theorem logVolume_respects_generated
    {a b : Choice}
    (h : Core.GeneratedEqualityRelation core a b) :
    profile.logVolume a = profile.logVolume b := by
  induction h with
  | refl a => rfl
  | ind1 hstep => exact profile.logVolume_respects_ind1Step hstep
  | ind2 hstep => exact profile.logVolume_respects_ind2Step hstep
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem possibleImage_respects_generated
    {a b : Choice}
    (h : Core.GeneratedEqualityRelation core a b) :
    profile.possibleImage a = profile.possibleImage b := by
  induction h with
  | refl a => rfl
  | ind1 hstep =>
      rcases hstep with ⟨g, rfl⟩
      exact (profile.possibleImage_ind1 g _).symm
  | ind2 hstep =>
      rcases hstep with ⟨g, rfl⟩
      exact (profile.possibleImage_ind2 g _).symm
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

def quotientPossibleImage : Core.GeneratedQuotient core → Set Real :=
  fun q => Quotient.liftOn' q profile.possibleImage
    (fun a b h => by
      exact profile.possibleImage_respects_generated h)

theorem quotientPossibleImage_mk (c : Choice) :
    profile.quotientPossibleImage (Core.generatedQuotientMap core c) =
      profile.possibleImage c := by
  rfl

theorem quotientPossibleImage_nonempty
    (q : Core.GeneratedQuotient core) :
    (profile.quotientPossibleImage q).Nonempty := by
  refine Quotient.inductionOn q (fun c => ?_)
  change (profile.possibleImage c).Nonempty
  exact profile.possibleImage_nonempty c

theorem quotientPossibleImage_ind3_upper
    (c : Choice) (n : Nat) (z : Real)
    (hz : z ∈ profile.quotientPossibleImage
      (Core.generatedQuotientMap core c)) :
    ∃ w, w ∈ profile.quotientPossibleImage
      (Core.generatedQuotientMap core (core.ind3 n c)) ∧ z ≤ w := by
  rw [profile.quotientPossibleImage_mk] at hz ⊢
  exact profile.possibleImage_ind3 n c z hz

end Profile

variable {Label : Type u} {Choice : Type v} [AddGroup Label]
  {core : Core Label Choice}

inductive RouteStep (Label : Type u)
  | ind1 (g : Label)
  | ind2 (g : Label)
  | ind3 (n : Nat)
  deriving DecidableEq, Repr

def applyStep (core : Core Label Choice)
    (step : RouteStep Label) (c : Choice) : Choice :=
  match step with
  | .ind1 g => core.ind1 g c
  | .ind2 g => core.ind2 g c
  | .ind3 n => core.ind3 n c

def applyRoute (core : Core Label Choice)
    (route : List (RouteStep Label)) (c : Choice) : Choice :=
  match route with
  | [] => c
  | step :: rest => applyRoute core rest (applyStep core step c)

@[simp] theorem applyRoute_nil (core : Core Label Choice) (c : Choice) :
    applyRoute core [] c = c :=
  rfl

@[simp] theorem applyRoute_cons (core : Core Label Choice)
    (step : RouteStep Label) (rest : List (RouteStep Label)) (c : Choice) :
    applyRoute core (step :: rest) c =
      applyRoute core rest (applyStep core step c) :=
  rfl

theorem applyRoute_append (core : Core Label Choice)
    (r₁ r₂ : List (RouteStep Label)) (c : Choice) :
    applyRoute core (r₁ ++ r₂) c =
      applyRoute core r₂ (applyRoute core r₁ c) := by
  induction r₁ generalizing c with
  | nil => rfl
  | cons step rest ih =>
      change applyRoute core (rest ++ r₂) (applyStep core step c) =
        applyRoute core r₂ (applyRoute core rest (applyStep core step c))
      exact ih (applyStep core step c)

theorem applyRoute_one (core : Core Label Choice)
    (step : RouteStep Label) (c : Choice) :
    applyRoute core [step] c = applyStep core step c := by
  rfl

theorem applyStep_ind1 (core : Core Label Choice)
    (g : Label) (c : Choice) :
    applyStep core (.ind1 g) c = core.ind1 g c :=
  rfl

theorem applyStep_ind2 (core : Core Label Choice)
    (g : Label) (c : Choice) :
    applyStep core (.ind2 g) c = core.ind2 g c :=
  rfl

theorem applyStep_ind3 (core : Core Label Choice)
    (n : Nat) (c : Choice) :
    applyStep core (.ind3 n) c = core.ind3 n c :=
  rfl

theorem level_applyStep_ind1 (core : Core Label Choice)
    (g : Label) (c : Choice) :
    core.level (applyStep core (.ind1 g) c) = core.level c :=
  core.ind1_level g c

theorem level_applyStep_ind2 (core : Core Label Choice)
    (g : Label) (c : Choice) :
    core.level (applyStep core (.ind2 g) c) = core.level c :=
  core.ind2_level g c

theorem level_applyStep_ind3 (core : Core Label Choice)
    (n : Nat) (c : Choice) :
    core.level c ≤ core.level (applyStep core (.ind3 n) c) :=
  core.ind3_level n c

theorem level_applyRoute (core : Core Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    core.level c ≤ core.level (applyRoute core route c) := by
  induction route generalizing c with
  | nil => exact le_rfl
  | cons step rest ih =>
      cases step with
      | ind1 g =>
          rw [applyRoute_cons]
          exact (core.ind1_level g c).symm.le.trans (ih (core.ind1 g c))
      | ind2 g =>
          rw [applyRoute_cons]
          exact (core.ind2_level g c).symm.le.trans (ih (core.ind2 g c))
      | ind3 n =>
          rw [applyRoute_cons]
          exact (core.ind3_level n c).trans (ih (core.ind3 n c))

theorem logVolume_applyRoute_le (core : Core Label Choice)
    (profile : Profile core) (route : List (RouteStep Label)) (c : Choice) :
    profile.logVolume c ≤ profile.logVolume (applyRoute core route c) := by
  induction route generalizing c with
  | nil => exact le_rfl
  | cons step rest ih =>
      cases step with
      | ind1 g =>
          rw [applyRoute_cons]
          exact (profile.ind1_invariant g c).symm.le.trans
            (ih (core.ind1 g c))
      | ind2 g =>
          rw [applyRoute_cons]
          exact (profile.ind2_invariant g c).symm.le.trans
            (ih (core.ind2 g c))
      | ind3 n =>
          rw [applyRoute_cons]
          exact (profile.ind3_upper n c).trans (ih (core.ind3 n c))

def horizontal (step : RouteStep Label) : Prop :=
  match step with
  | .ind1 _ => True
  | .ind2 _ => True
  | .ind3 _ => False

omit [AddGroup Label] in
theorem horizontal_of_ind1 (g : Label) : horizontal (.ind1 g) :=
  trivial

omit [AddGroup Label] in
theorem horizontal_of_ind2 (g : Label) : horizontal (.ind2 g) :=
  trivial

theorem logVolume_applyStep_horizontal
    (profile : Profile core) {step : RouteStep Label}
    (hstep : horizontal step) (c : Choice) :
    profile.logVolume (applyStep core step c) = profile.logVolume c := by
  cases step with
  | ind1 g => exact profile.ind1_invariant g c
  | ind2 g => exact profile.ind2_invariant g c
  | ind3 n => exact False.elim (hstep)

theorem logVolume_applyRoute_horizontal
    (profile : Profile core) (route : List (RouteStep Label))
    (hroute : ∀ step ∈ route, horizontal step) (c : Choice) :
    profile.logVolume (applyRoute core route c) = profile.logVolume c := by
  induction route generalizing c with
  | nil => rfl
  | cons step rest ih =>
      have hs : horizontal step := hroute step (by simp)
      have hr : ∀ s ∈ rest, horizontal s := by
        intro s hs'
        exact hroute s (by simp [hs'])
      rw [applyRoute_cons, ih hr]
      exact logVolume_applyStep_horizontal profile hs c

theorem generated_of_horizontal_route
    (core : Core Label Choice) (route : List (RouteStep Label))
    (hroute : ∀ step ∈ route, horizontal step) (c : Choice) :
    Core.GeneratedEqualityRelation core c (applyRoute core route c) := by
  induction route generalizing c with
  | nil => exact Core.GeneratedEqualityRelation.refl c
  | cons step rest ih =>
      have hs : horizontal step := hroute step (by simp)
      have hr : ∀ s ∈ rest, horizontal s := by
        intro s hs'
        exact hroute s (by simp [hs'])
      have hstep : Core.GeneratedEqualityRelation core c
          (applyStep core step c) := by
        cases step with
        | ind1 g =>
            exact .ind1 ⟨g, rfl⟩
        | ind2 g =>
            exact .ind2 ⟨g, rfl⟩
        | ind3 n => exact False.elim hs
      exact .trans hstep (ih hr (applyStep core step c))

theorem possibleImage_applyRoute_horizontal
    (profile : Profile core) (route : List (RouteStep Label))
    (hroute : ∀ step ∈ route, horizontal step) (c : Choice) :
    profile.possibleImage (applyRoute core route c) =
      profile.possibleImage c := by
  exact (profile.possibleImage_respects_generated
    (generated_of_horizontal_route core route hroute c)).symm

theorem possibleImage_applyRoute_ind3_upper
    (profile : Profile core) (route : List (RouteStep Label))
    (c : Choice) (z : Real) (hz : z ∈ profile.possibleImage c) :
    ∃ w, w ∈ profile.possibleImage (applyRoute core route c) ∧ z ≤ w := by
  induction route generalizing c z with
  | nil => exact ⟨z, hz, le_rfl⟩
  | cons step rest ih =>
      cases step with
      | ind1 g =>
          rw [applyRoute_cons]
          have hz' : z ∈ profile.possibleImage (core.ind1 g c) := by
            rw [profile.possibleImage_ind1 g]
            exact hz
          obtain ⟨w, hw, hzw⟩ := ih (core.ind1 g c) z hz'
          exact ⟨w, hw, hzw⟩
      | ind2 g =>
          rw [applyRoute_cons]
          have hz' : z ∈ profile.possibleImage (core.ind2 g c) := by
            rw [profile.possibleImage_ind2 g]
            exact hz
          obtain ⟨w, hw, hzw⟩ := ih (core.ind2 g c) z hz'
          exact ⟨w, hw, hzw⟩
      | ind3 n =>
          rw [applyRoute_cons]
          obtain ⟨w₁, hw₁, hzw₁⟩ := profile.possibleImage_ind3 n c z hz
          obtain ⟨w₂, hw₂, hzw₂⟩ := ih (core.ind3 n c) w₁ hw₁
          exact ⟨w₂, hw₂, hzw₁.trans hzw₂⟩

structure Output {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : Core Label Choice) (profile : Profile core) where
  source : Choice
  route : List (RouteStep Label)
  source_image_nonempty : (profile.possibleImage source).Nonempty

namespace Output

variable {Label : Type u} {Choice : Type v} [AddGroup Label]
  {core : Core Label Choice} {profile : Profile core}
  (output : Output core profile)

def target : Choice := applyRoute core output.route output.source

theorem source_image_nonempty' :
    (profile.possibleImage output.source).Nonempty :=
  output.source_image_nonempty

theorem target_level_ge :
    core.level output.source ≤ core.level output.target := by
  exact level_applyRoute core output.route output.source

theorem source_logVolume_le_target :
    profile.logVolume output.source ≤ profile.logVolume output.target := by
  exact logVolume_applyRoute_le core profile output.route output.source

theorem horizontal_target_logVolume_eq
    (hroute : ∀ step ∈ output.route, horizontal step) :
    profile.logVolume output.target = profile.logVolume output.source := by
  exact logVolume_applyRoute_horizontal profile output.route hroute output.source

theorem horizontal_target_image_eq
    (hroute : ∀ step ∈ output.route, horizontal step) :
    profile.possibleImage output.target = profile.possibleImage output.source := by
  exact possibleImage_applyRoute_horizontal profile output.route hroute output.source

theorem target_image_upper
    (z : Real) (hz : z ∈ profile.possibleImage output.source) :
    ∃ w, w ∈ profile.possibleImage output.target ∧ z ≤ w := by
  exact possibleImage_applyRoute_ind3_upper profile output.route
    output.source z hz

end Output

end MultiradialKernel

end LeanFormal.IUT
