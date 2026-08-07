import LeanFormal.IUT.IUTIII.Theorem311.ConcreteRouteNormalForm
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

namespace ConcreteRouteUniqueness

open ConcreteFiniteTheorem311
open ConcreteRouteNormalForm
open MultiradialKernel
open MultiradialKernel.Core
open SourceFiniteMultiradial
open SourceFiniteRouteArithmetic
open SourceFiniteRouteNaturality

local instance primeFactForUniqueness (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) := l.factPrime

abbrev Label (l : PrimeGeFive) := ConcreteFiniteTheorem311.finiteLabel l
abbrev Choice (l : PrimeGeFive) := ConcreteFiniteTheorem311.ProcessionChoice l
abbrev Step (l : PrimeGeFive) := RouteStep (Label l)

def SameNormalForm {l : PrimeGeFive}
    (r₁ r₂ : List (Step l)) (c : Choice l) : Prop :=
  horizontalTarget r₁ c = horizontalTarget r₂ c ∧
    ParametricTheorem311.verticalBudget r₁ =
      ParametricTheorem311.verticalBudget r₂

theorem sameNormalForm_refl {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    SameNormalForm route route c := by
  exact ⟨rfl, rfl⟩

theorem sameNormalForm_symm {l : PrimeGeFive}
    {r₁ r₂ : List (Step l)} {c : Choice l}
    (h : SameNormalForm r₁ r₂ c) :
    SameNormalForm r₂ r₁ c := by
  exact ⟨h.1.symm, h.2.symm⟩

theorem sameNormalForm_trans {l : PrimeGeFive}
    {r₁ r₂ r₃ : List (Step l)} {c : Choice l}
    (h₁₂ : SameNormalForm r₁ r₂ c)
    (h₂₃ : SameNormalForm r₂ r₃ c) :
    SameNormalForm r₁ r₃ c := by
  exact ⟨h₁₂.1.trans h₂₃.1, h₁₂.2.trans h₂₃.2⟩

theorem target_eq_of_sameNormalForm {l : PrimeGeFive}
    {r₁ r₂ : List (Step l)} {c : Choice l}
    (h : SameNormalForm r₁ r₂ c) :
    target l r₁ c = target l r₂ c := by
  calc
    target l r₁ c =
        ProcessionChoice.ind3Lift (ParametricTheorem311.verticalBudget r₁)
          (horizontalTarget r₁ c) := by
      simpa [horizontalTarget] using normalized_target_eq r₁ c
    _ = ProcessionChoice.ind3Lift (ParametricTheorem311.verticalBudget r₂)
          (horizontalTarget r₂ c) := by rw [h.1, h.2]
    _ = target l r₂ c := by
      simpa [horizontalTarget] using (normalized_target_eq r₂ c).symm

theorem profile_eq_of_sameNormalForm {l : PrimeGeFive}
    {r₁ r₂ : List (Step l)} {c : Choice l}
    (h : SameNormalForm r₁ r₂ c) :
    (profile l).logVolume (target l r₁ c) =
      (profile l).logVolume (target l r₂ c) := by
  exact congrArg (fun x => (profile l).logVolume x)
    (target_eq_of_sameNormalForm h)

theorem image_eq_of_sameNormalForm {l : PrimeGeFive}
    {r₁ r₂ : List (Step l)} {c : Choice l}
    (h : SameNormalForm r₁ r₂ c) :
    (profile l).possibleImage (target l r₁ c) =
      (profile l).possibleImage (target l r₂ c) := by
  exact congrArg (fun x => (profile l).possibleImage x)
    (target_eq_of_sameNormalForm h)

theorem packet_det_eq_of_sameNormalForm {l : PrimeGeFive}
    {r₁ r₂ : List (Step l)} {c : Choice l}
    (_h : SameNormalForm r₁ r₂ c) :
    packetDet (SourceFiniteRouteArithmetic.packet l r₁ c) =
      packetDet (SourceFiniteRouteArithmetic.packet l r₂ c) := by
  simp only [SourceFiniteRouteArithmetic.packet_det]

theorem packet_log_volume_eq_of_sameNormalForm {l : PrimeGeFive}
    {r₁ r₂ : List (Step l)} {c : Choice l}
    (_h : SameNormalForm r₁ r₂ c) :
    packetLogVolume (SourceFiniteRouteArithmetic.packet l r₁ c) =
      packetLogVolume (SourceFiniteRouteArithmetic.packet l r₂ c) := by
  simp only [SourceFiniteRouteArithmetic.packet_logVolume]

theorem sameNormalForm_of_target_eq {l : PrimeGeFive}
    {r₁ r₂ : List (Step l)} {c : Choice l}
    (hTarget : target l r₁ c = target l r₂ c) :
    SameNormalForm r₁ r₂ c := by
  have hlevel : ParametricTheorem311.verticalBudget r₁ =
      ParametricTheorem311.verticalBudget r₂ := by
    have h₁ := normalized_target_level r₁ c
    have h₂ := normalized_target_level r₂ c
    rw [hTarget] at h₁
    omega
  have hEq :
      ProcessionChoice.ind3Lift (ParametricTheorem311.verticalBudget r₁)
          (horizontalTarget r₁ c) =
        ProcessionChoice.ind3Lift (ParametricTheorem311.verticalBudget r₂)
          (horizontalTarget r₂ c) := by
    calc
      _ = target l r₁ c := by
        simpa [horizontalTarget] using (normalized_target_eq r₁ c).symm
      _ = target l r₂ c := hTarget
      _ = _ := by
        simpa [horizontalTarget] using normalized_target_eq r₂ c
  have hdrop := congrArg (fun x =>
    levelDrop x (ParametricTheorem311.verticalBudget r₁)) hEq
  have hdrop' : horizontalTarget r₁ c = horizontalTarget r₂ c := by
    simpa [hlevel, levelDrop_lift] using hdrop
  exact ⟨hdrop', hlevel⟩

theorem sameNormalForm_iff_target_eq {l : PrimeGeFive}
    {r₁ r₂ : List (Step l)} {c : Choice l} :
    SameNormalForm r₁ r₂ c ↔ target l r₁ c = target l r₂ c := by
  constructor
  · exact target_eq_of_sameNormalForm
  · exact sameNormalForm_of_target_eq

def normalFormClass {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    Choice l × Nat :=
    (horizontalTarget route c, ParametricTheorem311.verticalBudget route)

theorem normalFormClass_eq_iff {l : PrimeGeFive}
    {r₁ r₂ : List (Step l)} {c : Choice l} :
    normalFormClass r₁ c = normalFormClass r₂ c ↔
      target l r₁ c = target l r₂ c := by
  unfold normalFormClass
  constructor
  · intro h
    exact target_eq_of_sameNormalForm
      ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · intro h
    have hs := sameNormalForm_of_target_eq h
    exact Prod.ext hs.1 hs.2

theorem normalFormClass_target {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    target l route c =
      ProcessionChoice.ind3Lift (normalFormClass route c).2
        (normalFormClass route c).1 := by
  simpa [normalFormClass, horizontalTarget] using normalized_target_eq route c

theorem normalFormClass_level {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (normalFormClass route c).1.upperSemiLevel = c.upperSemiLevel := by
  exact horizontalTarget_level route c

theorem normalFormClass_budget {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (normalFormClass route c).2 = ParametricTheorem311.verticalBudget route := rfl

structure TargetNormalFormCertificate (l : PrimeGeFive)
    (route : List (Step l)) (c : Choice l) where
  normalForm : Choice l × Nat
  normalForm_eq : normalForm = normalFormClass route c
  source_level : normalForm.1.upperSemiLevel = c.upperSemiLevel
  target_eq : target l route c = ProcessionChoice.ind3Lift normalForm.2 normalForm.1
  normalForm_unique : ∀ b n,
    b.upperSemiLevel = c.upperSemiLevel →
    target l route c = ProcessionChoice.ind3Lift n b →
    b = normalForm.1 ∧ n = normalForm.2

def targetNormalFormCertificate {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    TargetNormalFormCertificate l route c where
  normalForm := normalFormClass route c
  normalForm_eq := rfl
  source_level := normalFormClass_level route c
  target_eq := normalFormClass_target route c
  normalForm_unique := by
    intro b n hlevel_b h
    have hnormEq :
        ProcessionChoice.ind3Lift (ParametricTheorem311.verticalBudget route)
            (horizontalTarget route c) =
          ProcessionChoice.ind3Lift n b := by
      calc
        _ = target l route c := by
          simpa [horizontalTarget] using (normalized_target_eq route c).symm
        _ = _ := h
    have hlevDrop := congrArg (fun x =>
      levelDrop x (ParametricTheorem311.verticalBudget route)) hnormEq
    have hn : n = ParametricTheorem311.verticalBudget route := by
      have hlev := congrArg (fun x => x.upperSemiLevel) h
      rw [ProcessionChoice.ind3_upperSemiLevel] at hlev
      have hnorm := normalized_target_level route c
      omega
    have hb := by
      simpa [hn, levelDrop_lift] using hlevDrop
    exact ⟨hb.symm, hn⟩

theorem targetNormalFormCertificate_class {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (targetNormalFormCertificate route c).normalForm = normalFormClass route c := rfl

theorem targetNormalFormCertificate_source_level {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (targetNormalFormCertificate route c).normalForm.1.upperSemiLevel =
      c.upperSemiLevel :=
  (targetNormalFormCertificate route c).source_level

theorem targetNormalFormCertificate_target {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    target l route c = ProcessionChoice.ind3Lift
      (targetNormalFormCertificate route c).normalForm.2
      (targetNormalFormCertificate route c).normalForm.1 :=
  (targetNormalFormCertificate route c).target_eq

theorem targetNormalFormCertificate_unique {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) (b : Choice l) (n : Nat)
    (hbase : b.upperSemiLevel = c.upperSemiLevel)
    (h : target l route c = ProcessionChoice.ind3Lift n b) :
    b = (targetNormalFormCertificate route c).normalForm.1 ∧
      n = (targetNormalFormCertificate route c).normalForm.2 :=
  (targetNormalFormCertificate route c).normalForm_unique b n hbase h

theorem targetNormalFormCertificate_profile {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (profile l).logVolume
        (targetNormalFormCertificate route c).normalForm.1 =
      (profile l).logVolume c := by
  rw [targetNormalFormCertificate_class]
  exact horizontalTarget_profile_eq_source route c

theorem targetNormalFormCertificate_image {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (profile l).possibleImage
        (targetNormalFormCertificate route c).normalForm.1 =
      (profile l).possibleImage c := by
  rw [targetNormalFormCertificate_class]
  exact horizontalTarget_image_eq_source route c

def routeEquivalence {l : PrimeGeFive} :
    List (Step l) → List (Step l) → Choice l → Prop :=
  fun r₁ r₂ c => target l r₁ c = target l r₂ c

theorem routeEquivalence_refl {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    routeEquivalence route route c := rfl

theorem routeEquivalence_symm {l : PrimeGeFive}
    {r₁ r₂ : List (Step l)} {c : Choice l}
    (h : routeEquivalence r₁ r₂ c) : routeEquivalence r₂ r₁ c := h.symm

theorem routeEquivalence_trans {l : PrimeGeFive}
    {r₁ r₂ r₃ : List (Step l)} {c : Choice l}
    (h₁₂ : routeEquivalence r₁ r₂ c)
    (h₂₃ : routeEquivalence r₂ r₃ c) : routeEquivalence r₁ r₃ c :=
  h₁₂.trans h₂₃

theorem routeEquivalence_iff_normalForm {l : PrimeGeFive}
    {r₁ r₂ : List (Step l)} {c : Choice l} :
    routeEquivalence r₁ r₂ c ↔
      normalFormClass r₁ c = normalFormClass r₂ c := by
  unfold routeEquivalence
  exact (normalFormClass_eq_iff).symm

end ConcreteRouteUniqueness

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteRouteUniqueness : Obligation :=
  { id := "IUT-III.concrete-route-uniqueness"
    source := "IUT III, Theorem 3.11, route quotient and normal form"
    status := VerificationStatus.proved
    note :=
      "The finite route quotient is identified exactly with the pair consisting " ++
        "of the horizontal target and the vertical budget. Target equality, " ++
        "profile/image invariance, and determinant invariance are proved from the " ++
        "concrete actions; no target value is postulated."
    dependsOn := [ "IUT-III.concrete-route-normal-form" ] }

end LeanFormal.IUT.Audit
