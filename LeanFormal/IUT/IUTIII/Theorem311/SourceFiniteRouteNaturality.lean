import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteRouteArithmetic
import Mathlib.Tactic

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

local instance primeFactForSourceRouteNaturality (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) := l.factPrime

namespace SourceFiniteRouteNaturality

open ConcreteFiniteTheorem311
open MultiradialKernel
open SourceFiniteMultiradial
open SourceFiniteRouteArithmetic

abbrev Label (l : PrimeGeFive) := ConcreteFiniteTheorem311.finiteLabel l
abbrev Choice (l : PrimeGeFive) := ConcreteFiniteTheorem311.ProcessionChoice l
abbrev Step (l : PrimeGeFive) := RouteStep (Label l)

def verticalBudget {l : PrimeGeFive} : List (Step l) → Nat
  | [] => 0
  | .ind1 _ :: rest => verticalBudget rest
  | .ind2 _ :: rest => verticalBudget rest
  | .ind3 n :: rest => n + verticalBudget rest

@[simp] theorem verticalBudget_nil {l : PrimeGeFive} :
    verticalBudget ([] : List (Step l)) = 0 :=
  rfl

@[simp] theorem verticalBudget_ind1 {l : PrimeGeFive}
    (g : Label l) (route : List (Step l)) :
    verticalBudget (.ind1 g :: route) = verticalBudget route :=
  rfl

@[simp] theorem verticalBudget_ind2 {l : PrimeGeFive}
    (g : Label l) (route : List (Step l)) :
    verticalBudget (.ind2 g :: route) = verticalBudget route :=
  rfl

@[simp] theorem verticalBudget_ind3 {l : PrimeGeFive}
    (n : Nat) (route : List (Step l)) :
    verticalBudget (.ind3 n :: route) = n + verticalBudget route :=
  rfl

theorem verticalBudget_append {l : PrimeGeFive}
    (r₁ r₂ : List (Step l)) :
    verticalBudget (r₁ ++ r₂) = verticalBudget r₁ + verticalBudget r₂ := by
  induction r₁ with
  | nil => simp
  | cons step rest ih =>
      cases step <;> simp [ih, Nat.add_left_comm,
        Nat.add_comm]

theorem verticalBudget_nonnegative {l : PrimeGeFive}
    (route : List (Step l)) : 0 ≤ verticalBudget route :=
  Nat.zero_le _

theorem target_level_eq_budget {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (target l route c).upperSemiLevel =
      c.upperSemiLevel + verticalBudget route := by
  induction route generalizing c with
  | nil => simp
  | cons step rest ih =>
      cases step with
      | ind1 g =>
          rw [target_cons, applyStep_ind1, core_ind1,
            verticalBudget_ind1]
          simpa [ProcessionChoice.ind1_upperSemiLevel] using
            ih (ProcessionChoice.ind1Act g c)
      | ind2 g =>
          rw [target_cons, applyStep_ind2, core_ind2,
            verticalBudget_ind2]
          simpa [ProcessionChoice.ind2_upperSemiLevel] using
            ih (ProcessionChoice.ind2Act g c)
      | ind3 n =>
          rw [target_cons, applyStep_ind3, core_ind3,
            verticalBudget_ind3]
          have h := ih (ProcessionChoice.ind3Lift n c)
          rw [h, ProcessionChoice.ind3_upperSemiLevel]
          omega

theorem target_level_eq_budget_core {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (SourceFiniteMultiradial.core l).level (target l route c) =
      (SourceFiniteMultiradial.core l).level c + verticalBudget route :=
  target_level_eq_budget route c

theorem profile_target_eq_budget {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (profile l).logVolume (target l route c) =
      (profile l).logVolume c + verticalBudget route := by
  rw [profile_logVolume_formula, profile_logVolume_formula,
    target_level_eq_budget]
  push_cast
  ring

theorem profile_target_eq_budget_source {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (profile l).logVolume (target l route c) =
      ConcreteFiniteTheorem311.thetaLogVolume l +
        (c.upperSemiLevel : Real) +
        (verticalBudget route : Real) := by
  rw [profile_logVolume_formula, target_level_eq_budget]
  push_cast
  ring

theorem profile_budget_gap {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    profilePacketGap l route c =
      (c.upperSemiLevel : Real) + (verticalBudget route : Real) := by
  rw [profilePacketGap_eq_level, target_level_eq_budget]
  push_cast
  ring

theorem profile_budget_zero_iff_same_level {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    verticalBudget route = 0 ↔
      (target l route c).upperSemiLevel = c.upperSemiLevel := by
  rw [target_level_eq_budget]
  constructor
  · intro h
    simp [h]
  · intro h
    omega

theorem target_level_horizontal_iff_budget_zero {l : PrimeGeFive}
    (route : List (Step l)) (c : Choice l) :
    (target l route c).upperSemiLevel = c.upperSemiLevel ↔
      verticalBudget route = 0 := by
  exact (profile_budget_zero_iff_same_level route c).symm

theorem target_append_budget {l : PrimeGeFive}
    (r₁ r₂ : List (Step l)) (c : Choice l) :
    (target l (r₁ ++ r₂) c).upperSemiLevel =
      c.upperSemiLevel + verticalBudget r₁ + verticalBudget r₂ := by
  rw [target_append, target_level_eq_budget, target_level_eq_budget]

theorem profile_append_budget {l : PrimeGeFive}
    (r₁ r₂ : List (Step l)) (c : Choice l) :
    (profile l).logVolume (target l (r₁ ++ r₂) c) =
      (profile l).logVolume c + verticalBudget r₁ + verticalBudget r₂ := by
  rw [profile_target_eq_budget, verticalBudget_append, Nat.cast_add]
  ring

theorem packet_append_det_eq {l : PrimeGeFive}
    (r₁ r₂ : List (Step l)) (c : Choice l) :
    packetDet (packet l (r₁ ++ r₂) c) =
      packetDet (packet l r₁ c) := by
  rw [packet_det, packet_det]

theorem packet_append_logVolume_eq {l : PrimeGeFive}
    (r₁ r₂ : List (Step l)) (c : Choice l) :
    packetLogVolume (packet l (r₁ ++ r₂) c) =
      packetLogVolume (packet l r₁ c) := by
  rw [packet_logVolume, packet_logVolume]

def canonicalRoute {l : PrimeGeFive}
    (a b : Choice l) (n : Nat) : List (Step l) :=
  sameLevelRoute a b ++ [.ind3 n]

theorem canonicalRoute_budget {l : PrimeGeFive}
    (a b : Choice l) (n : Nat) :
    verticalBudget (canonicalRoute a b n) = n := by
    simp [canonicalRoute, sameLevelRoute]

theorem canonicalRoute_horizontal_prefix {l : PrimeGeFive}
    (a b : Choice l) (_n : Nat) :
    horizontalRoute l (sameLevelRoute a b) := by
  intro step hstep
  exact sameLevelRoute_horizontal a b step hstep

theorem canonicalRoute_target {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    target l (canonicalRoute a b n) a =
      ProcessionChoice.ind3Lift n b := by
  unfold canonicalRoute target
  rw [applyRoute_append,
    sameLevelRoute_apply (a := a) (b := b) hlevel]
  rfl

theorem canonicalRoute_level {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    (target l (canonicalRoute a b n) a).upperSemiLevel = b.upperSemiLevel + n := by
  rw [canonicalRoute_target a b n hlevel,
    ProcessionChoice.ind3_upperSemiLevel]

theorem canonicalRoute_profile {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    (profile l).logVolume (target l (canonicalRoute a b n) a) =
      (profile l).logVolume b + n := by
  rw [canonicalRoute_target a b n hlevel, profile_logVolume_formula,
    profile_logVolume_formula, ProcessionChoice.ind3_upperSemiLevel]
  push_cast
  ring

theorem canonicalRoute_packet {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (_hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    packetLogVolume (packet l (canonicalRoute a b n) a) =
      ConcreteFiniteTheorem311.thetaLogVolume l :=
  packet_logVolume l (canonicalRoute a b n) a

theorem canonicalRoute_quotient_eq {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    Core.generatedQuotientMap (SourceFiniteMultiradial.core l)
        (target l (canonicalRoute a b n) a) =
      Core.generatedQuotientMap (SourceFiniteMultiradial.core l)
        (ProcessionChoice.ind3Lift n b) := by
  rw [canonicalRoute_target a b n hlevel]

theorem canonicalRoute_gap {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    profilePacketGap l (canonicalRoute a b n) a =
      (b.upperSemiLevel : Real) + n := by
  rw [profile_budget_gap, canonicalRoute_budget, hlevel]

structure CanonicalRouteCertificate {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) where
  target : Choice l
  target_eq : target = ProcessionChoice.ind3Lift n b
  quotient_target :
    Core.generatedQuotientMap (SourceFiniteMultiradial.core l) target =
      Core.generatedQuotientMap (SourceFiniteMultiradial.core l)
        (ProcessionChoice.ind3Lift n b)
  level_eq : target.upperSemiLevel = b.upperSemiLevel + n
  profile_eq :
    (profile l).logVolume target = (profile l).logVolume b + n
  packet_log_eq :
    packetLogVolume (packet l (canonicalRoute a b n) a) =
      ConcreteFiniteTheorem311.thetaLogVolume l

def canonicalRouteCertificate {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    CanonicalRouteCertificate a b n hlevel where
  target := target l (canonicalRoute a b n) a
  target_eq := canonicalRoute_target a b n hlevel
  quotient_target := canonicalRoute_quotient_eq a b n hlevel
  level_eq := canonicalRoute_level a b n hlevel
  profile_eq := canonicalRoute_profile a b n hlevel
  packet_log_eq := canonicalRoute_packet a b n hlevel

theorem canonicalCertificate_target {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    (canonicalRouteCertificate a b n hlevel).target =
      ProcessionChoice.ind3Lift n b :=
  canonicalRoute_target a b n hlevel

theorem canonicalCertificate_level {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    (canonicalRouteCertificate a b n hlevel).target.upperSemiLevel =
      b.upperSemiLevel + n :=
  canonicalRoute_level a b n hlevel

theorem canonicalCertificate_profile {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    (profile l).logVolume (canonicalRouteCertificate a b n hlevel).target =
      (profile l).logVolume b + n :=
  canonicalRoute_profile a b n hlevel

theorem canonicalCertificate_packet {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (_hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    packetLogVolume (packet l (canonicalRoute a b n) a) =
      ConcreteFiniteTheorem311.thetaLogVolume l :=
  packet_logVolume l (canonicalRoute a b n) a

theorem canonicalCertificate_q_image_upper {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel)
    (z : Real) (hz : z ∈ (profile l).possibleImage a) :
    ∃ w, w ∈ (profile l).possibleImage
      (canonicalRouteCertificate a b n hlevel).target ∧ z ≤ w := by
  rw [canonicalCertificate_target a b n hlevel]
  have htarget :
      applyRoute (SourceFiniteMultiradial.core l)
          (canonicalRoute a b n) a = ProcessionChoice.ind3Lift n b := by
    exact canonicalRoute_target a b n hlevel
  have hupper := possibleImage_applyRoute_ind3_upper (profile l)
    (canonicalRoute a b n) a z hz
  rw [htarget] at hupper
  exact hupper

theorem canonicalCertificate_determinant_positive {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (_hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    0 < packetDet (packet l (canonicalRoute a b n) a) :=
  packet_det_positive l (canonicalRoute a b n) a

theorem canonicalCertificate_determinant_log {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (_hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    Real.log (packetDet (packet l (canonicalRoute a b n) a)) =
      ConcreteFiniteTheorem311.thetaLogVolume l :=
  packet_log_det_eq_theta l (canonicalRoute a b n) a

theorem canonicalCertificate_rescale {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (_hlevel : a.upperSemiLevel = b.upperSemiLevel)
    (scale : Real) (hscale : 0 < scale) :
    packetLogVolume (rescaledPacket l (canonicalRoute a b n) a scale hscale) =
      (Fintype.card (SignedLabel l.value) : Real) * Real.log scale +
        ConcreteFiniteTheorem311.thetaLogVolume l :=
  rescaledPacket_logVolume l (canonicalRoute a b n) a scale hscale

theorem canonicalCertificate_tensor {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (_hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    packetLogVolume (SourceFiniteRouteArithmetic.tensorPacket l
      (canonicalRoute a b n) a) =
      (2 * (Fintype.card (SignedLabel l.value) : Real)) *
        ConcreteFiniteTheorem311.thetaLogVolume l :=
  tensorPacket_logVolume l (canonicalRoute a b n) a

theorem canonicalCertificate_horizontal_prefix_profile {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (_hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    (profile l).logVolume (target l (sameLevelRoute a b) a) =
      (profile l).logVolume a := by
  exact profile_target_horizontal l (sameLevelRoute a b) a
    (canonicalRoute_horizontal_prefix a b n)

theorem canonicalCertificate_source_level {l : PrimeGeFive}
    (a b : Choice l) (n : Nat)
    (hlevel : a.upperSemiLevel = b.upperSemiLevel) :
    (target l (canonicalRoute a b n) a).upperSemiLevel =
      b.upperSemiLevel + n :=
  canonicalRoute_level a b n hlevel

end SourceFiniteRouteNaturality

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteSourceRouteNaturality : Obligation :=
  { id := "IUT-III.concrete-source-route-naturality"
    source := "IUT III, Theorem 3.11 procession and Ind3 route composition"
    status := VerificationStatus.interface
    note :=
      "The explicit finite carrier has an exact vertical-budget theorem. A " ++
        "canonical horizontal-plus-vertical route connects any same-level pair " ++
        "to its Ind3 lift and preserves the determinant/log-volume certificate. " ++
        "The arbitrary source procession and its realization remain pending."
    dependsOn :=
      [ "IUT-III.concrete-source-route-arithmetic",
        "IUT-III.concrete-source-multiradial-kernel" ] }

end LeanFormal.IUT.Audit
