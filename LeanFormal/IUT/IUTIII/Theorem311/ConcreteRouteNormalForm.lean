import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteParameterized
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

namespace ConcreteRouteNormalForm

open ConcreteFiniteTheorem311
open SourceFiniteParameterized
open ParametricTheorem311
open MultiradialKernel
open MultiradialKernel.Core
open SourceFiniteMultiradial
open SourceFiniteRouteArithmetic

local instance primeFactForNormalForm (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) := l.factPrime

abbrev Label (l : PrimeGeFive) := ConcreteFiniteTheorem311.finiteLabel l
abbrev Choice (l : PrimeGeFive) := ConcreteFiniteTheorem311.ProcessionChoice l
abbrev Step (l : PrimeGeFive) := RouteStep (Label l)

def horizontalPart {l : PrimeGeFive} : List (Step l) → List (Step l)
  | [] => []
  | .ind1 g :: rest => .ind1 g :: horizontalPart rest
  | .ind2 g :: rest => .ind2 g :: horizontalPart rest
  | .ind3 _ :: rest => horizontalPart rest

def verticalPart {l : PrimeGeFive} : List (Step l) → List Nat
  | [] => []
  | .ind1 _ :: rest => verticalPart rest
  | .ind2 _ :: rest => verticalPart rest
  | .ind3 n :: rest => n :: verticalPart rest

theorem horizontalPart_nil {l : PrimeGeFive} :
    horizontalPart ([] : List (Step l)) = [] := rfl

theorem horizontalPart_ind1 {l : PrimeGeFive}
    (g : Label l) (route : List (Step l)) :
    horizontalPart (.ind1 g :: route) =
      .ind1 g :: horizontalPart route := rfl

theorem horizontalPart_ind2 {l : PrimeGeFive}
    (g : Label l) (route : List (Step l)) :
    horizontalPart (.ind2 g :: route) =
      .ind2 g :: horizontalPart route := rfl

theorem horizontalPart_ind3 {l : PrimeGeFive}
    (n : Nat) (route : List (Step l)) :
    horizontalPart (.ind3 n :: route) = horizontalPart route := rfl

theorem verticalPart_nil {l : PrimeGeFive} :
    verticalPart ([] : List (Step l)) = [] := rfl

theorem verticalPart_ind1 {l : PrimeGeFive}
    (g : Label l) (route : List (Step l)) :
    verticalPart (.ind1 g :: route) = verticalPart route := rfl

theorem verticalPart_ind2 {l : PrimeGeFive}
    (g : Label l) (route : List (Step l)) :
    verticalPart (.ind2 g :: route) = verticalPart route := rfl

theorem verticalPart_ind3 {l : PrimeGeFive}
    (n : Nat) (route : List (Step l)) :
    verticalPart (.ind3 n :: route) = n :: verticalPart route := rfl

theorem horizontalPart_append {l : PrimeGeFive}
    (r₁ r₂ : List (Step l)) :
    horizontalPart (r₁ ++ r₂) = horizontalPart r₁ ++ horizontalPart r₂ := by
  induction r₁ with
  | nil => rfl
  | cons step rest ih =>
      cases step <;> simp [horizontalPart, ih]

theorem verticalPart_append {l : PrimeGeFive}
    (r₁ r₂ : List (Step l)) :
    verticalPart (r₁ ++ r₂) = verticalPart r₁ ++ verticalPart r₂ := by
  induction r₁ with
  | nil => rfl
  | cons step rest ih =>
      cases step <;> simp [verticalPart, ih]

theorem horizontalPart_horizontal {l : PrimeGeFive}
    (route : List (Step l)) (step : Step l)
    (hstep : step ∈ horizontalPart route) :
    horizontal step := by
  induction route with
  | nil => simp [horizontalPart] at hstep
  | cons step' rest ih =>
      cases step' with
      | ind1 g =>
          simp only [horizontalPart, List.mem_cons] at hstep
          rcases hstep with rfl | hstep
          · exact horizontal_of_ind1 g
          · exact ih hstep
      | ind2 g =>
          simp only [horizontalPart, List.mem_cons] at hstep
          rcases hstep with rfl | hstep
          · exact horizontal_of_ind2 g
          · exact ih hstep
      | ind3 n =>
          simpa [horizontalPart] using ih hstep

theorem horizontalPart_isHorizontal {l : PrimeGeFive}
    (route : List (Step l)) :
    ∀ step ∈ horizontalPart route, horizontal step := by
  intro step hstep
  exact horizontalPart_horizontal route step hstep

theorem verticalPart_sum_eq_budget {l : PrimeGeFive}
    (route : List (Step l)) :
    (verticalPart route).sum = verticalBudget route := by
  induction route with
  | nil => rfl
  | cons step rest ih =>
      cases step <;> simp [verticalPart, verticalBudget, ih]

theorem verticalBudget_horizontalPart_zero {l : PrimeGeFive}
    (route : List (Step l)) :
    verticalBudget (horizontalPart route) = 0 := by
  induction route with
  | nil => rfl
  | cons step rest ih =>
      cases step <;> simp [horizontalPart, ih]

theorem applyRoute_horizontal_ind1 {l : PrimeGeFive}
    (route : List (Step l)) (g : Label l) (c : Choice l) :
    applyRoute (SourceFiniteMultiradial.core l) (horizontalPart route)
        (ProcessionChoice.ind1Act g c) =
      ProcessionChoice.ind1Act g
        (applyRoute (SourceFiniteMultiradial.core l)
          (horizontalPart route) c) := by
  induction route generalizing c with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | ind1 h =>
          simp only [horizontalPart, applyRoute, applyStep_ind1]
          rw [SourceFiniteMultiradial.core_ind1,
            SourceFiniteMultiradial.core_ind1]
          have hcomm : ProcessionChoice.ind1Act h
              (ProcessionChoice.ind1Act g c) =
              ProcessionChoice.ind1Act g
                (ProcessionChoice.ind1Act h c) := by
            simp [ProcessionChoice.ind1Act, add_left_comm]
          rw [hcomm]
          exact ih (ProcessionChoice.ind1Act h c)
      | ind2 h =>
          simp only [horizontalPart, applyRoute, applyStep_ind2]
          rw [SourceFiniteMultiradial.core_ind2,
            SourceFiniteMultiradial.core_ind2]
          rw [← ProcessionChoice.ind1_ind2_commute g h c]
          exact ih (ProcessionChoice.ind2Act h c)
      | ind3 n =>
          simpa [horizontalPart] using ih c

theorem applyRoute_horizontal_ind2 {l : PrimeGeFive}
    (route : List (Step l)) (g : Label l) (c : Choice l) :
    applyRoute (SourceFiniteMultiradial.core l) (horizontalPart route)
        (ProcessionChoice.ind2Act g c) =
      ProcessionChoice.ind2Act g
        (applyRoute (SourceFiniteMultiradial.core l)
          (horizontalPart route) c) := by
  induction route generalizing c with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | ind1 h =>
          simp only [horizontalPart, applyRoute, applyStep_ind1]
          rw [SourceFiniteMultiradial.core_ind1,
            SourceFiniteMultiradial.core_ind1]
          rw [ProcessionChoice.ind1_ind2_commute h g c]
          exact ih (ProcessionChoice.ind1Act h c)
      | ind2 h =>
          simp only [horizontalPart, applyRoute, applyStep_ind2]
          rw [SourceFiniteMultiradial.core_ind2,
            SourceFiniteMultiradial.core_ind2]
          have hcomm : ProcessionChoice.ind2Act h
              (ProcessionChoice.ind2Act g c) =
              ProcessionChoice.ind2Act g
                (ProcessionChoice.ind2Act h c) := by
            simp [ProcessionChoice.ind2Act, add_left_comm]
          rw [hcomm]
          exact ih (ProcessionChoice.ind2Act h c)
      | ind3 n =>
          simpa [horizontalPart] using ih c

theorem applyRoute_horizontal_ind3 {l : PrimeGeFive}
    (route : List (Step l)) (n : Nat) (c : Choice l) :
    applyRoute (SourceFiniteMultiradial.core l) (horizontalPart route)
        (ProcessionChoice.ind3Lift n c) =
      ProcessionChoice.ind3Lift n
        (applyRoute (SourceFiniteMultiradial.core l)
          (horizontalPart route) c) := by
  induction route generalizing c with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | ind1 g =>
          simp only [horizontalPart, applyRoute, applyStep_ind1]
          simp only [SourceFiniteMultiradial.core_ind1]
          rw [ProcessionChoice.ind1_ind3_commute g n c]
          exact ih (ProcessionChoice.ind1Act g c)
      | ind2 g =>
          simp only [horizontalPart, applyRoute, applyStep_ind2]
          simp only [SourceFiniteMultiradial.core_ind2]
          rw [ProcessionChoice.ind2_ind3_commute g n c]
          exact ih (ProcessionChoice.ind2Act g c)
      | ind3 k =>
          simpa [horizontalPart] using ih c

theorem applyRoute_normalize {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    applyRoute (SourceFiniteMultiradial.core l) route c =
      ProcessionChoice.ind3Lift (verticalBudget route)
        (applyRoute (SourceFiniteMultiradial.core l)
          (horizontalPart route) c) := by
  induction route generalizing c with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | ind1 g =>
          simp only [applyRoute, applyStep_ind1, horizontalPart, verticalBudget]
          rw [ih]
      | ind2 g =>
          simp only [applyRoute, applyStep_ind2, horizontalPart, verticalBudget]
          rw [ih]
      | ind3 n =>
          simp only [applyRoute, applyStep_ind3, horizontalPart, verticalBudget]
          rw [ih]
          simp only [SourceFiniteMultiradial.core_ind3]
          rw [applyRoute_horizontal_ind3]
          rw [← ProcessionChoice.ind3_add]

theorem normalized_target_eq {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    target l route c =
      ProcessionChoice.ind3Lift (verticalBudget route)
        (target l (horizontalPart route) c) := by
  exact applyRoute_normalize route c

def levelDrop {l : PrimeGeFive} (c : Choice l) (n : Nat) : Choice l :=
  { c with upperSemiLevel := c.upperSemiLevel - n }

@[simp] theorem levelDrop_processionLabel {l : PrimeGeFive}
    (c : Choice l) (n : Nat) :
    (levelDrop c n).processionLabel = c.processionLabel := rfl

@[simp] theorem levelDrop_tensorLabel {l : PrimeGeFive}
    (c : Choice l) (n : Nat) :
    (levelDrop c n).tensorLabel = c.tensorLabel := rfl

@[simp] theorem levelDrop_level {l : PrimeGeFive}
    (c : Choice l) (n : Nat) :
    (levelDrop c n).upperSemiLevel = c.upperSemiLevel - n := rfl

theorem levelDrop_add_lift {l : PrimeGeFive}
    (c : Choice l) (n : Nat) (h : n ≤ c.upperSemiLevel) :
    ProcessionChoice.ind3Lift n (levelDrop c n) = c := by
  cases c with
  | mk p t level =>
      simp [levelDrop, ProcessionChoice.ind3Lift, Nat.sub_add_cancel h]

theorem levelDrop_lift {l : PrimeGeFive}
    (c : Choice l) (n : Nat) :
    levelDrop (ProcessionChoice.ind3Lift n c) n = c := by
  cases c with
  | mk p t level =>
  simp [levelDrop, ProcessionChoice.ind3Lift]

theorem target_budget_le_level {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    verticalBudget route ≤ (target l route c).upperSemiLevel := by
  rw [normalized_target_eq]
  simp [ProcessionChoice.ind3_upperSemiLevel]

def horizontalTarget {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) : Choice l :=
  target l (horizontalPart route) c

theorem horizontalTarget_level {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (horizontalTarget route c).upperSemiLevel = c.upperSemiLevel := by
  exact routeTarget_level_eq_budget (carrier l) (horizontalPart route) c |>.trans
    (by simp [verticalBudget_horizontalPart_zero])

theorem normalized_target_horizontalProjection {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    levelDrop (target l route c) (verticalBudget route) =
      horizontalTarget route c := by
  rw [normalized_target_eq]
  exact levelDrop_lift (horizontalTarget route c) (verticalBudget route)

theorem normalized_target_level {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (target l route c).upperSemiLevel =
      c.upperSemiLevel + verticalBudget route := by
  exact routeTarget_level_eq_budget (carrier l) route c

theorem normalized_target_unique {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l)
    (b : Choice l)
    (h : target l route c =
      ProcessionChoice.ind3Lift (verticalBudget route) b) :
    b = horizontalTarget route c := by
  have hlevel : (target l route c).upperSemiLevel =
      b.upperSemiLevel + verticalBudget route := by
    rw [h, ProcessionChoice.ind3_upperSemiLevel]
  have hdrop := congrArg (fun x => levelDrop x (verticalBudget route)) h
  rw [normalized_target_horizontalProjection] at hdrop
  rw [levelDrop_lift] at hdrop
  exact hdrop.symm

def normalizedRoute {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) : List (Step l) :=
  sameLevelRoute c (horizontalTarget route c) ++
    [.ind3 (verticalBudget route)]

theorem normalizedRoute_horizontal_prefix {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    ∀ step ∈ sameLevelRoute c (horizontalTarget route c), horizontal step := by
  intro step hstep
  exact sameLevelRoute_horizontal c (horizontalTarget route c) step hstep

theorem normalizedRoute_budget {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    verticalBudget (normalizedRoute route c) = verticalBudget route := by
  simp [normalizedRoute, sameLevelRoute]

theorem normalizedRoute_target {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    target l (normalizedRoute route c) c = target l route c := by
  have hlevel : c.upperSemiLevel =
      (horizontalTarget route c).upperSemiLevel := by
    exact (horizontalTarget_level route c).symm
  unfold target
  rw [normalizedRoute, applyRoute_append,
    sameLevelRoute_apply hlevel]
  rw [applyRoute_one, applyStep_ind3]
  exact (normalized_target_eq route c).symm

theorem normalizedRoute_level {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (target l (normalizedRoute route c) c).upperSemiLevel =
      c.upperSemiLevel + verticalBudget route := by
  rw [normalizedRoute_target]
  exact normalized_target_level route c

theorem normalizedRoute_horizontal {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    horizontalRoute (carrier l) (sameLevelRoute c (horizontalTarget route c)) := by
  intro step hstep
  exact sameLevelRoute_horizontal c (horizontalTarget route c) step hstep

theorem normalizedRoute_profile {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (profile l).logVolume (target l route c) =
      (profile l).logVolume (target l (normalizedRoute route c) c) := by
  rw [normalizedRoute_target]

theorem normalizedRoute_image {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) (z : Real)
    (hz : z ∈ (profile l).possibleImage c) :
    ∃ w, w ∈ (profile l).possibleImage
      (target l (normalizedRoute route c) c) ∧ z ≤ w := by
  rw [normalizedRoute_target]
  exact possibleImage_applyRoute_ind3_upper (profile l) route c z hz

theorem normalizedRoute_isCanonical {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    normalizedRoute route c =
      SourceFiniteRouteNaturality.canonicalRoute c
        (horizontalTarget route c) (verticalBudget route) := rfl

theorem budget_recovered_from_target {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) (n : Nat)
    (h : target l route c = ProcessionChoice.ind3Lift n
      (horizontalTarget route c)) :
    n = verticalBudget route := by
  have hlev := congrArg (fun x => x.upperSemiLevel) h
  rw [ProcessionChoice.ind3_upperSemiLevel,
    normalized_target_level] at hlev
  rw [horizontalTarget_level route c] at hlev
  omega

theorem horizontalProjection_idempotent {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    levelDrop (horizontalTarget route c) 0 = horizontalTarget route c := by
  cases horizontalTarget route c with
  | mk p t level => simp [levelDrop]

theorem horizontalTarget_sameLevel {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (horizontalTarget route c).upperSemiLevel = c.upperSemiLevel :=
  horizontalTarget_level route c

theorem horizontalTarget_profile_eq_source {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (profile l).logVolume (horizontalTarget route c) =
      (profile l).logVolume c := by
  exact logVolume_applyRoute_horizontal (profile l)
    (horizontalPart route) (horizontalPart_isHorizontal route) c

theorem horizontalTarget_image_eq_source {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (profile l).possibleImage (horizontalTarget route c) =
      (profile l).possibleImage c := by
  exact possibleImage_applyRoute_horizontal (profile l)
    (horizontalPart route) (horizontalPart_isHorizontal route) c

structure NormalFormCertificate (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) where
  source : Choice l
  horizontal : Choice l
  budget : Nat
  route_normalized : List (Step l)
  source_eq : source = c
  horizontal_eq : horizontal = horizontalTarget route c
  budget_eq : budget = verticalBudget route
  horizontal_level : horizontal.upperSemiLevel = source.upperSemiLevel
  target_eq : target l route source =
    ProcessionChoice.ind3Lift budget horizontal
  route_eq : route_normalized =
    sameLevelRoute source horizontal ++ [.ind3 budget]

def normalFormCertificate {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    NormalFormCertificate l route c where
  source := c
  horizontal := horizontalTarget route c
  budget := verticalBudget route
  route_normalized := normalizedRoute route c
  source_eq := rfl
  horizontal_eq := rfl
  budget_eq := rfl
  horizontal_level := horizontalTarget_level route c
  target_eq := by
    exact normalized_target_eq route c
  route_eq := rfl

theorem normalFormCertificate_target {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    target l route c = ProcessionChoice.ind3Lift
      (verticalBudget route) (horizontalTarget route c) :=
  (normalFormCertificate route c).target_eq

theorem normalFormCertificate_horizontal_level {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (normalFormCertificate route c).horizontal.upperSemiLevel =
      (normalFormCertificate route c).source.upperSemiLevel :=
  (normalFormCertificate route c).horizontal_level

theorem normalFormCertificate_route {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (normalFormCertificate route c).route_normalized =
      sameLevelRoute c (horizontalTarget route c) ++
        [.ind3 (verticalBudget route)] :=
  (normalFormCertificate route c).route_eq

theorem normalFormCertificate_profile {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (profile l).logVolume (normalFormCertificate route c).horizontal =
      (profile l).logVolume c := by
  rw [(normalFormCertificate route c).horizontal_eq]
  exact horizontalTarget_profile_eq_source route c

theorem normalFormCertificate_image {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (profile l).possibleImage (normalFormCertificate route c).horizontal =
      (profile l).possibleImage c := by
  rw [(normalFormCertificate route c).horizontal_eq]
  exact horizontalTarget_image_eq_source route c

theorem normalFormCertificate_budget {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (normalFormCertificate route c).budget = verticalBudget route :=
  (normalFormCertificate route c).budget_eq

end ConcreteRouteNormalForm

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteRouteNormalForm : Obligation :=
  { id := "IUT-III.concrete-route-normal-form"
    source := "IUT III, Theorem 3.11, Ind1/Ind2/Ind3 route normalization"
    status := VerificationStatus.proved
    note :=
      "For the proved finite Q(i)-at-5 carrier, every mixed route is shown " ++
        "to equal its horizontal projection followed by one exact Ind3 lift. " ++
        "The horizontal projection has the source level and is uniquely recovered " ++
        "from the target and vertical budget. This is a real finite theorem, not " ++
        "an existence claim for arbitrary Hodge theaters."
    dependsOn :=
      [ "IUT-III.concrete-source-multiradial-kernel",
        "IUT-III.parametric-route-algebra" ] }

end LeanFormal.IUT.Audit
