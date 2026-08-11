import LeanFormal.IUT.IUTIII.Theorem311.MultiradialProfileKernel
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummer
import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.IUTIII.Theorem311.InitialThetaInputCore
import LeanFormal.IUT.Audit.Status

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
  # Theorem 3.11: an explicit source-boundary proof

  This file is deliberately separate from the finite Q(i)-at-5 model.  It
  records every source-facing object which Theorem 3.11 consumes and proves
  the three conclusions from those objects.  In particular, no field called
  `candidate_exists` is eliminated by choice and no finite quotient is used
  as a substitute for the source carrier.

  The source theorem in the paper is conditional on the constructions of
  IUT I--III.  The type `Input` below is the exact formal boundary of those
  constructions.  The propositions following it are the individual clauses
  of the theorem, proved one at a time.  This makes the remaining existence
  problem visible to the audit while closing all algebraic and order-theoretic
  consequences which are actually justified by the supplied data.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u v w

namespace Theorem311Source

open MultiradialKernel
open MultiradialKernel.Core

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]

/-! ## 0. Derived-prerequisite records

  The records in this section are *not* the opening input of the source
  theorem.  They are the package obtained after the IUT I--II constructions
  have already supplied the procession, packet, vertical log-Kummer data,
  evaluation system, and horizontal compatibility.  `SourceOriginalInput`
  contains the separate opening boundary with only initial Theta-data and the
  distinct theater family.  Keeping the two namespaces conceptually separate
  prevents the conditional assembly below from being mistaken for the source
  theorem itself.
 -/

/-- A procession is the indexed family of choices used by the multiradial
    representation.  Its laws are the literal group, commutation, and level
    laws needed below; they are not hidden in a quotient certificate. -/
structure DPrimeStripProcession (Label : Type u) (Choice : Type v)
    [AddGroup Label] where
  base : Choice
  level : Choice → Nat
  ind1 : Label → Choice → Choice
  ind2 : Label → Choice → Choice
  ind3 : Nat → Choice → Choice
  ind1_zero : ∀ c, ind1 0 c = c
  ind1_add : ∀ g h c, ind1 (g + h) c = ind1 h (ind1 g c)
  ind1_inverse : ∀ g c, ind1 (-g) (ind1 g c) = c
  ind2_zero : ∀ c, ind2 0 c = c
  ind2_add : ∀ g h c, ind2 (g + h) c = ind2 h (ind2 g c)
  ind2_inverse : ∀ g c, ind2 (-g) (ind2 g c) = c
  ind3_zero : ∀ c, ind3 0 c = c
  ind3_add : ∀ m n c, ind3 (m + n) c = ind3 n (ind3 m c)
  ind1_ind2_commute : ∀ g h c, ind1 g (ind2 h c) = ind2 h (ind1 g c)
  ind1_ind3_commute : ∀ g n c, ind1 g (ind3 n c) = ind3 n (ind1 g c)
  ind2_ind3_commute : ∀ g n c, ind2 g (ind3 n c) = ind3 n (ind2 g c)
  ind1_level : ∀ g c, level (ind1 g c) = level c
  ind2_level : ∀ g c, level (ind2 g c) = level c
  ind3_level : ∀ n c, level c ≤ level (ind3 n c)

/-- The supplied procession is converted to the reusable multiradial kernel. -/
def DPrimeStripProcession.core (P : DPrimeStripProcession Label Choice) :
    Core Label Choice where
  base := P.base
  level := P.level
  ind1 := P.ind1
  ind2 := P.ind2
  ind3 := P.ind3
  ind1_zero := P.ind1_zero
  ind1_add := P.ind1_add
  ind1_inverse := P.ind1_inverse
  ind2_zero := P.ind2_zero
  ind2_add := P.ind2_add
  ind2_inverse := P.ind2_inverse
  ind3_zero := P.ind3_zero
  ind3_add := P.ind3_add
  ind1_ind2_commute := P.ind1_ind2_commute
  ind1_ind3_commute := P.ind1_ind3_commute
  ind2_ind3_commute := P.ind2_ind3_commute
  ind1_level := P.ind1_level
  ind2_level := P.ind2_level
  ind3_level := P.ind3_level

@[simp] theorem procession_core_base
    (P : DPrimeStripProcession Label Choice) :
    P.core.base = P.base := rfl

@[simp] theorem procession_core_level
    (P : DPrimeStripProcession Label Choice) (c : Choice) :
    P.core.level c = P.level c := rfl

@[simp] theorem procession_core_ind1
    (P : DPrimeStripProcession Label Choice) (g : Label) (c : Choice) :
    P.core.ind1 g c = P.ind1 g c := rfl

@[simp] theorem procession_core_ind2
    (P : DPrimeStripProcession Label Choice) (g : Label) (c : Choice) :
    P.core.ind2 g c = P.ind2 g c := rfl

@[simp] theorem procession_core_ind3
    (P : DPrimeStripProcession Label Choice) (n : Nat) (c : Choice) :
    P.core.ind3 n c = P.ind3 n c := rfl

/-- A procession-normalized packet profile.  The two horizontal actions leave
    its log-volume and image unchanged; the vertical action is upper-semi. -/
structure ProcessionPacketProfile
    (P : DPrimeStripProcession Label Choice) where
  logVolume : Choice → Real
  possibleImage : Choice → Set Real
  ind1_invariant : ∀ g c,
    logVolume (P.ind1 g c) = logVolume c
  ind2_invariant : ∀ g c,
    logVolume (P.ind2 g c) = logVolume c
  ind3_upper : ∀ n c,
    logVolume c ≤ logVolume (P.ind3 n c)
  possibleImage_nonempty : ∀ c, (possibleImage c).Nonempty
  possibleImage_ind1 : ∀ g c,
    possibleImage (P.ind1 g c) = possibleImage c
  possibleImage_ind2 : ∀ g c,
    possibleImage (P.ind2 g c) = possibleImage c
  possibleImage_ind3 : ∀ n c z, z ∈ possibleImage c →
    ∃ w, w ∈ possibleImage (P.ind3 n c) ∧ z ≤ w

def ProcessionPacketProfile.profile
    (P : DPrimeStripProcession Label Choice)
    (Q : ProcessionPacketProfile P) : Profile P.core where
  logVolume := Q.logVolume
  possibleImage := Q.possibleImage
  ind1_invariant := Q.ind1_invariant
  ind2_invariant := Q.ind2_invariant
  ind3_upper := Q.ind3_upper
  possibleImage_nonempty := Q.possibleImage_nonempty
  possibleImage_ind1 := Q.possibleImage_ind1
  possibleImage_ind2 := Q.possibleImage_ind2
  possibleImage_ind3 := Q.possibleImage_ind3

@[simp] theorem profile_logVolume
    (P : DPrimeStripProcession Label Choice)
    (Q : ProcessionPacketProfile P) (c : Choice) :
    Q.profile.logVolume c = Q.logVolume c := rfl

@[simp] theorem profile_possibleImage
    (P : DPrimeStripProcession Label Choice)
    (Q : ProcessionPacketProfile P) (c : Choice) :
    Q.profile.possibleImage c = Q.possibleImage c := rfl

/-- Distinct theaters are represented by an injective index and their links.
    The link laws are hypotheses of the source construction and are consumed
    explicitly by the horizontal part below. -/
structure TheaterFamily (I : Type u) (T : Type v) where
  theater : I → T
  distinct : Function.Injective theater
  link : I → I → T → T
  link_refl : ∀ i t, link i i t = t
  link_trans : ∀ i j k t,
    link j k (link i j t) = link i k t
  permutation : Equiv.Perm I
  permutation_naturality : ∀ i t,
    link (permutation i) (permutation i) t = link i i t

/-- An evaluated local packet carries the tensor and determinant data that
    Proposition 3.2 and Proposition 3.9 require. -/
structure LocalTensorPacket (P : DPrimeStripProcession Label Choice) where
  carrier : Choice → Type w
  distinguished : ∀ c, carrier c
  determinant : Choice → Real
  logVolume : Choice → Real
  determinant_positive : ∀ c, 0 < determinant c
  log_determinant : ∀ c, Real.log (determinant c) = logVolume c
  ind1_det : ∀ g c, determinant (P.ind1 g c) = determinant c
  ind2_det : ∀ g c, determinant (P.ind2 g c) = determinant c
  ind3_det_upper : ∀ n c, determinant c ≤ determinant (P.ind3 n c)
  logVolume_ind3_upper : ∀ n c, logVolume c ≤ logVolume (P.ind3 n c)

/-- A labelled local Kummer isomorphism.  The inverse and both evaluation
    equations are included so that no direction is silently reversed. -/
structure LabelledKummerIso (A : Type u) (B : Type v) where
  map : A → B
  inverse : B → A
  left_inverse : Function.LeftInverse inverse map
  right_inverse : Function.RightInverse inverse map
  label : A → Nat
  label_map : ∀ a, label (inverse (map a)) = label a

def LabelledKummerIso.equiv (K : LabelledKummerIso A B) : A ≃ B where
  toFun := K.map
  invFun := K.inverse
  left_inv := K.left_inverse
  right_inv := K.right_inverse

theorem LabelledKummerIso.map_injective
    (K : LabelledKummerIso A B) : Function.Injective K.map :=
  K.equiv.injective

theorem LabelledKummerIso.map_surjective
    (K : LabelledKummerIso A B) : Function.Surjective K.map :=
  K.equiv.surjective

/-- Local and global evaluation maps used in Theorem 3.11(ii). -/
structure EvaluationSystem (A : Type u) (B : Type v) where
  localMap : A → B
  globalMap : A → B
  localEqGlobal : ∀ a, localMap a = globalMap a
  localComp : A → A
  globalComp : A → A
  localNaturality : ∀ a, localMap (localComp a) = localMap a
  globalNaturality : ∀ a, globalMap (globalComp a) = globalMap a

theorem EvaluationSystem.local_global
    (E : EvaluationSystem A B) (a : A) :
    E.localMap a = E.globalMap a := E.localEqGlobal a

/-- A horizontal LGP link is a commuting square of labelled maps. -/
structure HorizontalLGPLink (A : Type u) (B : Type v) where
  left : A → A
  right : B → B
  upper : A → B
  lower : A → B
  square : ∀ a, upper (left a) = right (lower a)
  upper_label : A → Nat
  lower_label : A → Nat
  labels_agree : ∀ a, upper_label a = lower_label a

theorem HorizontalLGPLink.square_at
    (H : HorizontalLGPLink A B) (a : A) :
    H.upper (H.left a) = H.right (H.lower a) := H.square a

theorem HorizontalLGPLink.label_at
    (H : HorizontalLGPLink A B) (a : A) :
    H.upper_label a = H.lower_label a := H.labels_agree a

/-! The two vertical site maps are kept as a separate source-facing object.
    Their domains are deliberately set-valued: the nonarchimedean map is an
    inclusion of possible images, whereas the archimedean map is read in the
    opposite (surjective) direction.  This prevents an equality from silently
    replacing either of the upper-semi assertions. -/
structure VerticalSiteData (Choice : Type v) where
  nonarchimedeanImage : Nat → Set Real → Set Real
  archimedeanImage : Nat → Set Real → Set Real
  nonarchimedean_inclusion : ∀ m z S,
    z ∈ S → z ∈ nonarchimedeanImage m S
  archimedean_surjection : ∀ m z S,
    z ∈ archimedeanImage m S → ∃ y, y ∈ S ∧ z ≤ y

theorem VerticalSiteData.nonarchimedean_inclusion_at
    (V : VerticalSiteData Choice) (m : Nat) (S : Set Real)
    (z : Real) (hz : z ∈ S) :
    z ∈ V.nonarchimedeanImage m S :=
  V.nonarchimedean_inclusion m z S hz

theorem VerticalSiteData.archimedean_surjection_at
    (V : VerticalSiteData Choice) (m : Nat) (S : Set Real)
    (z : Real) (hz : z ∈ V.archimedeanImage m S) :
    ∃ y, y ∈ S ∧ z ≤ y :=
  V.archimedean_surjection m z S hz

/-- All cited IUT I--II prerequisites after their constructions have been
    supplied.  This is intentionally not the opening input of Theorem 3.11. -/
structure DerivedPrerequisiteInput (Label : Type u) (Choice : Type v)
    [AddGroup Label] where
  labelPrime : PrimeGeFive
  prime : DPrimeStripProcession Label Choice
  packet : ProcessionPacketProfile prime
  localPacket : LocalTensorPacket.{u, v, w} prime
  packet_profile_volume : ∀ c : Choice,
    packet.logVolume c = localPacket.logVolume c
  initial : InitialThetaInput.{u} labelPrime
  vertical : UpperSemiCorrespondence Nat Real
  vertical_monotone : ∀ m n, m ≤ n →
    ∀ z, z ∈ vertical.image m →
      ∃ w, w ∈ vertical.image n ∧ z ≤ w
  verticalSite : VerticalSiteData Choice
  verticalSite_nonarchimedean_profile : ∀ m c,
    verticalSite.nonarchimedeanImage m (packet.possibleImage c) =
      packet.possibleImage (prime.ind3 m c)
  verticalSite_archimedean_profile : ∀ m c,
    verticalSite.archimedeanImage m (packet.possibleImage c) =
      packet.possibleImage (prime.ind3 m c)
  labelledCount : Nat
  labelledCount_pos : 0 < labelledCount
  evaluation : EvaluationSystem Choice Choice
  labelledKummer : ∀ c : Choice, LabelledKummerIso Choice Choice
  family : TheaterFamily Choice Choice
  horizontal : HorizontalLGPLink Choice Choice
  kummer_horizontal_compat : ∀ c : Choice,
    (labelledKummer c).map (horizontal.left c) =
      horizontal.right ((labelledKummer c).map (horizontal.lower c))
  labelled_horizontal_compat : ∀ c : Choice,
    (labelledKummer c).label (horizontal.left c) =
      (labelledKummer c).label (horizontal.lower c)
  evaluation_horizontal_compat : ∀ c,
  evaluation.localMap (horizontal.left c) =
      horizontal.right (evaluation.localMap (horizontal.lower c))

/-- The source input has a reusable kernel and profile. -/
abbrev Input (Label : Type u) (Choice : Type v) [AddGroup Label] :=
  DerivedPrerequisiteInput Label Choice

def DerivedPrerequisiteInput.core
    (I : DerivedPrerequisiteInput Label Choice) : Core Label Choice := I.prime.core

def DerivedPrerequisiteInput.profile
    (I : DerivedPrerequisiteInput Label Choice) : Profile I.core :=
  I.packet.profile

@[simp] theorem Input.core_base (I : Input Label Choice) :
    I.core.base = I.prime.base := rfl

@[simp] theorem Input.core_level (I : Input Label Choice) (c : Choice) :
    I.core.level c = I.prime.level c := rfl

@[simp] theorem Input.profile_volume (I : Input Label Choice) (c : Choice) :
    I.profile.logVolume c = I.packet.logVolume c := rfl

@[simp] theorem Input.profile_image (I : Input Label Choice) (c : Choice) :
    I.profile.possibleImage c = I.packet.possibleImage c := rfl

/-! ## 1. Proposition 6.9(ii): procession laws -/

theorem procession_ind1_refl (I : Input Label Choice) (c : Choice) :
    Core.Ind1Step I.core c c := by
  exact Core.ind1Step_refl I.core c

theorem procession_ind1_symm (I : Input Label Choice)
    {a b : Choice} (h : Core.Ind1Step I.core a b) :
    Core.Ind1Step I.core b a := by
  exact Core.ind1Step_symm I.core h

theorem procession_ind1_trans (I : Input Label Choice)
    {a b c : Choice} (h₁ : Core.Ind1Step I.core a b)
    (h₂ : Core.Ind1Step I.core b c) : Core.Ind1Step I.core a c := by
  exact Core.ind1Step_trans I.core h₁ h₂

theorem procession_ind2_refl (I : Input Label Choice) (c : Choice) :
    Core.Ind2Step I.core c c := by
  exact Core.ind2Step_refl I.core c

theorem procession_ind2_symm (I : Input Label Choice)
    {a b : Choice} (h : Core.Ind2Step I.core a b) :
    Core.Ind2Step I.core b a := by
  exact Core.ind2Step_symm I.core h

theorem procession_ind2_trans (I : Input Label Choice)
    {a b c : Choice} (h₁ : Core.Ind2Step I.core a b)
    (h₂ : Core.Ind2Step I.core b c) : Core.Ind2Step I.core a c := by
  exact Core.ind2Step_trans I.core h₁ h₂

theorem procession_ind3_refl (I : Input Label Choice) (c : Choice) :
    Core.Ind3Step I.core c c := by
  exact Core.ind3Step_refl I.core c

theorem procession_ind3_trans (I : Input Label Choice)
    {a b c : Choice} (h₁ : Core.Ind3Step I.core a b)
    (h₂ : Core.Ind3Step I.core b c) : Core.Ind3Step I.core a c := by
  exact Core.ind3Step_trans I.core h₁ h₂

theorem procession_ind1_ind2_commute (I : Input Label Choice)
    (g h : Label) (c : Choice) :
    I.core.ind1 g (I.core.ind2 h c) = I.core.ind2 h (I.core.ind1 g c) :=
  I.core.ind1_ind2_commute g h c

theorem procession_ind1_ind3_commute (I : Input Label Choice)
    (g : Label) (n : Nat) (c : Choice) :
    I.core.ind1 g (I.core.ind3 n c) = I.core.ind3 n (I.core.ind1 g c) :=
  I.core.ind1_ind3_commute g n c

theorem procession_ind2_ind3_commute (I : Input Label Choice)
    (g : Label) (n : Nat) (c : Choice) :
    I.core.ind2 g (I.core.ind3 n c) = I.core.ind3 n (I.core.ind2 g c) :=
  I.core.ind2_ind3_commute g n c

theorem procession_ind1_level (I : Input Label Choice)
    (g : Label) (c : Choice) :
    I.core.level (I.core.ind1 g c) = I.core.level c :=
  I.core.ind1_level g c

theorem procession_ind2_level (I : Input Label Choice)
    (g : Label) (c : Choice) :
    I.core.level (I.core.ind2 g c) = I.core.level c :=
  I.core.ind2_level g c

theorem procession_ind3_level (I : Input Label Choice)
    (n : Nat) (c : Choice) :
    I.core.level c ≤ I.core.level (I.core.ind3 n c) :=
  I.core.ind3_level n c

theorem procession_horizontal_generated
    (I : Input Label Choice) (route : List (RouteStep Label))
    (c : Choice) (hroute : ∀ s ∈ route, horizontal s) :
    GeneratedEqualityRelation I.core c (applyRoute I.core route c) := by
  exact generated_of_horizontal_route I.core route hroute c

theorem procession_horizontal_quotient
    (I : Input Label Choice) (route : List (RouteStep Label))
    (c : Choice) (hroute : ∀ s ∈ route, horizontal s) :
    Core.generatedQuotientMap I.core c =
      Core.generatedQuotientMap I.core (applyRoute I.core route c) := by
  exact Core.generatedQuotientMap_eq_of_generated I.core
    (procession_horizontal_generated I route c hroute)

theorem procession_level_no_collapse (I : Input Label Choice)
    {a b : Choice} (h : I.core.level a ≠ I.core.level b) :
    Core.generatedQuotientMap I.core a ≠
      Core.generatedQuotientMap I.core b := by
  exact Core.generatedQuotient_no_level_collapse I.core h

theorem procession_route_level
    (I : Input Label Choice) (route : List (RouteStep Label)) (c : Choice) :
    I.core.level c ≤ I.core.level (applyRoute I.core route c) := by
  exact level_applyRoute I.core route c

theorem procession_route_profile
    (I : Input Label Choice) (route : List (RouteStep Label)) (c : Choice) :
    I.profile.logVolume c ≤ I.profile.logVolume (applyRoute I.core route c) := by
  exact logVolume_applyRoute_le I.core I.profile route c

theorem procession_route_image
    (I : Input Label Choice) (route : List (RouteStep Label)) (c : Choice)
    (z : Real) (hz : z ∈ I.profile.possibleImage c) :
    ∃ w, w ∈ I.profile.possibleImage (applyRoute I.core route c) ∧ z ≤ w := by
  exact possibleImage_applyRoute_ind3_upper I.profile route c z hz

/-! ## 2. Proposition 3.2/3.9: local packet and volume laws -/

theorem packet_determinant_positive
    (I : Input Label Choice) (c : Choice) :
    0 < I.localPacket.determinant c :=
  I.localPacket.determinant_positive c

theorem packet_determinant_nonzero
    (I : Input Label Choice) (c : Choice) :
    I.localPacket.determinant c ≠ 0 :=
  ne_of_gt (packet_determinant_positive I c)

theorem packet_log_determinant
    (I : Input Label Choice) (c : Choice) :
    Real.log (I.localPacket.determinant c) =
      I.localPacket.logVolume c :=
  I.localPacket.log_determinant c

theorem packet_ind1_determinant
    (I : Input Label Choice) (g : Label) (c : Choice) :
    I.localPacket.determinant (I.prime.ind1 g c) =
      I.localPacket.determinant c :=
  I.localPacket.ind1_det g c

theorem packet_ind2_determinant
    (I : Input Label Choice) (g : Label) (c : Choice) :
    I.localPacket.determinant (I.prime.ind2 g c) =
      I.localPacket.determinant c :=
  I.localPacket.ind2_det g c

theorem packet_ind3_determinant_upper
    (I : Input Label Choice) (n : Nat) (c : Choice) :
    I.localPacket.determinant c ≤
      I.localPacket.determinant (I.prime.ind3 n c) :=
  I.localPacket.ind3_det_upper n c

theorem packet_ind1_log_volume
    (I : Input Label Choice) (g : Label) (c : Choice) :
    I.localPacket.logVolume (I.prime.ind1 g c) =
      I.localPacket.logVolume c := by
  rw [← I.localPacket.log_determinant,
    I.localPacket.ind1_det, I.localPacket.log_determinant]

theorem packet_ind2_log_volume
    (I : Input Label Choice) (g : Label) (c : Choice) :
    I.localPacket.logVolume (I.prime.ind2 g c) =
      I.localPacket.logVolume c := by
  rw [← I.localPacket.log_determinant,
    I.localPacket.ind2_det, I.localPacket.log_determinant]

theorem packet_ind3_log_volume_upper
    (I : Input Label Choice) (n : Nat) (c : Choice) :
    I.localPacket.logVolume c ≤
      I.localPacket.logVolume (I.prime.ind3 n c) := by
  exact I.localPacket.logVolume_ind3_upper n c

theorem packet_image_nonempty
    (I : Input Label Choice) (c : Choice) :
    Nonempty (I.localPacket.carrier c) := by
  exact ⟨I.localPacket.distinguished c⟩

theorem packet_profile_image_nonempty
    (I : Input Label Choice) (c : Choice) :
    (I.profile.possibleImage c).Nonempty := by
  exact I.profile.possibleImage_nonempty c

theorem packet_profile_ind1_image
    (I : Input Label Choice) (g : Label) (c : Choice) :
    I.profile.possibleImage (I.core.ind1 g c) =
      I.profile.possibleImage c := by
  exact I.profile.possibleImage_ind1 g c

theorem packet_profile_ind2_image
    (I : Input Label Choice) (g : Label) (c : Choice) :
    I.profile.possibleImage (I.core.ind2 g c) =
      I.profile.possibleImage c := by
  exact I.profile.possibleImage_ind2 g c

theorem packet_profile_ind3_image_upper
    (I : Input Label Choice) (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage c) :
    ∃ w, w ∈ I.profile.possibleImage (I.core.ind3 n c) ∧ z ≤ w := by
  exact I.profile.possibleImage_ind3 n c z hz

theorem packet_profile_route_invariant
    (I : Input Label Choice) (route : List (RouteStep Label))
    (c : Choice) (hroute : ∀ s ∈ route, horizontal s) :
    I.profile.logVolume (applyRoute I.core route c) =
      I.profile.logVolume c := by
  exact logVolume_applyRoute_horizontal I.profile route hroute c

theorem packet_profile_route_image_invariant
    (I : Input Label Choice) (route : List (RouteStep Label))
    (c : Choice) (hroute : ∀ s ∈ route, horizontal s) :
    I.profile.possibleImage (applyRoute I.core route c) =
      I.profile.possibleImage c := by
  exact possibleImage_applyRoute_horizontal I.profile route hroute c

theorem packet_profile_route_upper
    (I : Input Label Choice) (route : List (RouteStep Label))
    (c : Choice) (z : Real) (hz : z ∈ I.profile.possibleImage c) :
    ∃ w, w ∈ I.profile.possibleImage (applyRoute I.core route c) ∧ z ≤ w := by
  exact possibleImage_applyRoute_ind3_upper I.profile route c z hz

/-! ## 3. Ind1 and Ind2 quotient descent -/

def Ind1Relation (I : Input Label Choice) : Choice → Choice → Prop :=
  Core.Ind1Step I.core

def Ind2Relation (I : Input Label Choice) : Choice → Choice → Prop :=
  Core.Ind2Step I.core

def HorizontalGenerated (I : Input Label Choice) : Choice → Choice → Prop :=
  Core.GeneratedEqualityRelation I.core

theorem ind1_relation_refl (I : Input Label Choice) (c : Choice) :
    Ind1Relation I c c := by
  exact procession_ind1_refl I c

theorem ind1_relation_symm (I : Input Label Choice)
    {a b : Choice} (h : Ind1Relation I a b) :
    Ind1Relation I b a := by
  exact procession_ind1_symm I h

theorem ind1_relation_trans (I : Input Label Choice)
    {a b c : Choice} (hab : Ind1Relation I a b)
    (hbc : Ind1Relation I b c) : Ind1Relation I a c := by
  exact procession_ind1_trans I hab hbc

theorem ind2_relation_refl (I : Input Label Choice) (c : Choice) :
    Ind2Relation I c c := by
  exact procession_ind2_refl I c

theorem ind2_relation_symm (I : Input Label Choice)
    {a b : Choice} (h : Ind2Relation I a b) :
    Ind2Relation I b a := by
  exact procession_ind2_symm I h

theorem ind2_relation_trans (I : Input Label Choice)
    {a b c : Choice} (hab : Ind2Relation I a b)
    (hbc : Ind2Relation I b c) : Ind2Relation I a c := by
  exact procession_ind2_trans I hab hbc

theorem ind1_ind2_relation_commute (I : Input Label Choice)
    {a b c d : Choice} (h₁ : Ind1Relation I a b)
    (h₂ : Ind2Relation I a c) :
    ∃ d, Ind2Relation I b d ∧ Ind1Relation I c d := by
  rcases h₁ with ⟨g, rfl⟩
  rcases h₂ with ⟨h, rfl⟩
  refine ⟨I.core.ind2 h (I.core.ind1 g a), ?_, ?_⟩
  · exact ⟨h, rfl⟩
  · exact ⟨g, I.core.ind1_ind2_commute g h a⟩

theorem ind1_level_respects (I : Input Label Choice)
    {a b : Choice} (h : Ind1Relation I a b) :
    I.core.level a = I.core.level b := by
  exact Core.ind1_preserves_level I.core h

theorem ind2_level_respects (I : Input Label Choice)
    {a b : Choice} (h : Ind2Relation I a b) :
    I.core.level a = I.core.level b := by
  exact Core.ind2_preserves_level I.core h

theorem generated_relation_refl (I : Input Label Choice) (c : Choice) :
    HorizontalGenerated I c c :=
  Core.generatedRelation_refl I.core c

theorem generated_relation_symm (I : Input Label Choice)
    {a b : Choice} (h : HorizontalGenerated I a b) :
    HorizontalGenerated I b a :=
  Core.generatedRelation_symm I.core h

theorem generated_relation_trans (I : Input Label Choice)
    {a b c : Choice} (h₁ : HorizontalGenerated I a b)
    (h₂ : HorizontalGenerated I b c) : HorizontalGenerated I a c :=
  Core.generatedRelation_trans I.core h₁ h₂

theorem generated_relation_level (I : Input Label Choice)
    {a b : Choice} (h : HorizontalGenerated I a b) :
    I.core.level a = I.core.level b := by
  exact Core.generatedRelation_level_eq I.core h

def IndeterminacyQuotient (I : Input Label Choice) :=
  Core.GeneratedQuotient I.core

def quotientMap (I : Input Label Choice) (c : Choice) :
    IndeterminacyQuotient I := Core.generatedQuotientMap I.core c

theorem quotientMap_eq_iff (I : Input Label Choice) {a b : Choice} :
    quotientMap I a = quotientMap I b ↔ HorizontalGenerated I a b := by
  exact Core.generatedQuotientMap_eq_iff I.core

theorem quotientMap_respects_ind1 (I : Input Label Choice)
    {a b : Choice} (h : Ind1Relation I a b) :
    quotientMap I a = quotientMap I b := by
  exact Core.generatedQuotientMap_eq_of_generated I.core
    (.ind1 h)

theorem quotientMap_respects_ind2 (I : Input Label Choice)
    {a b : Choice} (h : Ind2Relation I a b) :
    quotientMap I a = quotientMap I b := by
  exact Core.generatedQuotientMap_eq_of_generated I.core
    (.ind2 h)

theorem quotientMap_no_level_collapse (I : Input Label Choice)
    {a b : Choice} (hne : I.core.level a ≠ I.core.level b) :
    quotientMap I a ≠ quotientMap I b := by
  exact Core.generatedQuotient_no_level_collapse I.core hne

theorem quotientMap_respects_route (I : Input Label Choice)
    (route : List (RouteStep Label)) (c : Choice)
    (hroute : ∀ s ∈ route, horizontal s) :
    quotientMap I c = quotientMap I (applyRoute I.core route c) := by
  exact procession_horizontal_quotient I route c hroute

theorem quotient_level_well_defined (I : Input Label Choice)
    {a b : Choice} (h : quotientMap I a = quotientMap I b) :
    I.core.level a = I.core.level b := by
  exact Core.generatedQuotientMap_level_eq I.core h

theorem quotient_profile_well_defined (I : Input Label Choice)
    {a b : Choice} (h : quotientMap I a = quotientMap I b) :
    I.profile.logVolume a = I.profile.logVolume b := by
  exact Profile.logVolume_respects_generated I.profile
    ((quotientMap_eq_iff I).mp h)

theorem quotient_image_well_defined (I : Input Label Choice)
    {a b : Choice} (h : quotientMap I a = quotientMap I b) :
    I.profile.possibleImage a = I.profile.possibleImage b := by
  exact Profile.possibleImage_respects_generated I.profile
    ((quotientMap_eq_iff I).mp h)

def quotientLevel (I : Input Label Choice) : IndeterminacyQuotient I → Nat :=
  fun q => Quotient.liftOn' q I.core.level
    (fun a b h => generated_relation_level I h)

def quotientVolume (I : Input Label Choice) :
    IndeterminacyQuotient I → Real :=
  fun q => Quotient.liftOn' q I.profile.logVolume
    (fun a b h => Profile.logVolume_respects_generated I.profile h)

def quotientImage (I : Input Label Choice) :
    IndeterminacyQuotient I → Set Real :=
  fun q => Quotient.liftOn' q I.profile.possibleImage
    (fun a b h => Profile.possibleImage_respects_generated I.profile h)

theorem quotientLevel_mk (I : Input Label Choice) (c : Choice) :
    quotientLevel I (quotientMap I c) = I.core.level c := rfl

theorem quotientVolume_mk (I : Input Label Choice) (c : Choice) :
    quotientVolume I (quotientMap I c) = I.profile.logVolume c := rfl

theorem quotientImage_mk (I : Input Label Choice) (c : Choice) :
    quotientImage I (quotientMap I c) = I.profile.possibleImage c := rfl

theorem quotientLevel_eq_of_eq (I : Input Label Choice)
    {q r : IndeterminacyQuotient I} (h : q = r) :
    quotientLevel I q = quotientLevel I r := by
  rw [h]

theorem quotientVolume_eq_of_eq (I : Input Label Choice)
    {q r : IndeterminacyQuotient I} (h : q = r) :
    quotientVolume I q = quotientVolume I r := by
  rw [h]

theorem quotientImage_eq_of_eq (I : Input Label Choice)
    {q r : IndeterminacyQuotient I} (h : q = r) :
    quotientImage I q = quotientImage I r := by
  rw [h]

/-! ## 4. The multiradial representation in part (i) -/

structure PartI (I : Input Label Choice) where
  quotient : IndeterminacyQuotient I
  source : Choice
  source_map : quotient = quotientMap I source
  source_image_nonempty : (quotientImage I quotient).Nonempty
  level_bound : quotientLevel I quotient ≤
    quotientLevel I (quotientMap I (I.core.ind3 0 source))
  volume_bound : quotientVolume I quotient ≤
    quotientVolume I (quotientMap I (I.core.ind3 0 source))
  ind1_invariant : ∀ g c,
    quotientVolume I (quotientMap I (I.core.ind1 g c)) =
      quotientVolume I (quotientMap I c)
  ind2_invariant : ∀ g c,
    quotientVolume I (quotientMap I (I.core.ind2 g c)) =
      quotientVolume I (quotientMap I c)

def partI (I : Input Label Choice) : PartI I where
  quotient := quotientMap I I.core.base
  source := I.core.base
  source_map := rfl
  source_image_nonempty := by
    rw [quotientImage_mk]
    exact I.profile.possibleImage_nonempty I.core.base
  level_bound := by
    rw [quotientLevel_mk, quotientLevel_mk]
    exact I.core.ind3_level 0 I.core.base
  volume_bound := by
    rw [quotientVolume_mk, quotientVolume_mk]
    exact I.profile.ind3_upper 0 I.core.base
  ind1_invariant := by
    intro g c
    rw [quotientVolume_mk, quotientVolume_mk]
    exact I.profile.ind1_invariant g c
  ind2_invariant := by
    intro g c
    rw [quotientVolume_mk, quotientVolume_mk]
    exact I.profile.ind2_invariant g c

theorem partI_source (I : Input Label Choice) :
    (partI I).source = I.core.base := rfl

theorem partI_quotient (I : Input Label Choice) :
    (partI I).quotient = quotientMap I I.core.base := rfl

theorem partI_source_map (I : Input Label Choice) :
    (partI I).quotient = quotientMap I (partI I).source :=
  (partI I).source_map

theorem partI_nonempty (I : Input Label Choice) :
    ((partI I).quotient |> quotientImage I).Nonempty :=
  (partI I).source_image_nonempty

theorem partI_level_bound (I : Input Label Choice) :
    quotientLevel I (partI I).quotient ≤
      quotientLevel I (quotientMap I (I.core.ind3 0 I.core.base)) :=
  (partI I).level_bound

theorem partI_volume_bound (I : Input Label Choice) :
    quotientVolume I (partI I).quotient ≤
      quotientVolume I (quotientMap I (I.core.ind3 0 I.core.base)) :=
  (partI I).volume_bound

theorem partI_ind1 (I : Input Label Choice) (g : Label) (c : Choice) :
    quotientVolume I (quotientMap I (I.core.ind1 g c)) =
      quotientVolume I (quotientMap I c) :=
  (partI I).ind1_invariant g c

theorem partI_ind2 (I : Input Label Choice) (g : Label) (c : Choice) :
    quotientVolume I (quotientMap I (I.core.ind2 g c)) =
      quotientVolume I (quotientMap I c) :=
  (partI I).ind2_invariant g c

/-! ## 5. Proposition 3.5: labelled vertical log-Kummer correspondence -/

/-- The vertical correspondence extracted from the packet profile.  Its
    `upperSemi` field is exactly the non-archimedean inclusion direction in
    the source statement. -/
def verticalCorrespondence (I : Input Label Choice) :
    VerticalLogKummerCorrespondence where
  D := Real
  ordD := inferInstance
  F := fun _ => Choice
  ordF := fun _ => inferInstance
  log := fun n c => I.core.ind3 n c
  kummer := fun _ c => I.profile.logVolume c
  upperSemi := by
    intro m c
    exact I.profile.ind3_upper m c

@[simp] theorem verticalCorrespondence_log
    (I : Input Label Choice) (m : Nat) (c : Choice) :
    (verticalCorrespondence I).log m c = I.core.ind3 m c := rfl

@[simp] theorem verticalCorrespondence_kummer
    (I : Input Label Choice) (m : Nat) (c : Choice) :
    (verticalCorrespondence I).kummer m c = I.profile.logVolume c := rfl

theorem vertical_base_upper
    (I : Input Label Choice) (c : Choice) :
    (verticalCorrespondence I).kummer 0 c ≤
      (verticalCorrespondence I).kummer 1
        ((verticalCorrespondence I).log 0 c) := by
  exact (verticalCorrespondence I).upperSemi 0 c

theorem vertical_transport_zero
    (I : Input Label Choice) (c : Choice) :
    (verticalCorrespondence I).transport 0 0 c = c := by
  rfl

theorem vertical_transport_one
    (I : Input Label Choice) (c : Choice) :
    (verticalCorrespondence I).transport 0 1 c = I.core.ind3 0 c := by
  rfl

theorem vertical_transport_two
    (I : Input Label Choice) (c : Choice) :
    (verticalCorrespondence I).transport 0 2 c =
      I.core.ind3 1 (I.core.ind3 0 c) := by
  rfl

theorem vertical_kummer_le_transport
    (I : Input Label Choice) (c : Choice) (n : Nat) :
    I.profile.logVolume c ≤
      (verticalCorrespondence I).kummer n
        ((verticalCorrespondence I).transport 0 n c) := by
  induction n with
  | zero => simp [verticalCorrespondence]
  | succ n ih =>
      simpa [verticalCorrespondence,
        VerticalLogKummerCorrespondence.transport, Nat.zero_add] using
        ih.trans (I.profile.ind3_upper n
          ((verticalCorrespondence I).transport 0 n c))

theorem vertical_kummer_le_ind3
    (I : Input Label Choice) (c : Choice) (n : Nat) :
    I.profile.logVolume c ≤ I.profile.logVolume (I.core.ind3 n c) := by
  exact I.profile.ind3_upper n c

theorem vertical_hull_dominates_base
    (I : Input Label Choice) {c : Choice} {hull : Real}
    (h : (verticalCorrespondence I).HullDominates c hull) :
    I.profile.logVolume c ≤ hull := by
  exact (verticalCorrespondence I).base_le_hull h

theorem vertical_nonarchimedean_inclusion
    (I : Input Label Choice) (V : VerticalSiteData Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage c) :
    z ∈ V.nonarchimedeanImage m (I.profile.possibleImage c) :=
  V.nonarchimedean_inclusion m z _ hz

theorem vertical_archimedean_surjection
    (I : Input Label Choice) (V : VerticalSiteData Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ V.archimedeanImage m (I.profile.possibleImage c)) :
    ∃ y, y ∈ I.profile.possibleImage c ∧ z ≤ y := by
  exact V.archimedean_surjection m z _ hz

theorem vertical_nonarchimedean_target
    (I : Input Label Choice)
    (m : Nat) (c : Choice) :
    I.verticalSite.nonarchimedeanImage m (I.profile.possibleImage c) =
      I.profile.possibleImage (I.core.ind3 m c) :=
  I.verticalSite_nonarchimedean_profile m c

theorem vertical_archimedean_target
    (I : Input Label Choice)
    (m : Nat) (c : Choice) :
    I.verticalSite.archimedeanImage m (I.profile.possibleImage c) =
      I.profile.possibleImage (I.core.ind3 m c) :=
  I.verticalSite_archimedean_profile m c

theorem vertical_profile_upper_from_nonarch
    (I : Input Label Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage c) :
    ∃ w, w ∈ I.profile.possibleImage (I.core.ind3 m c) ∧ z ≤ w := by
  refine ⟨z, ?_, le_rfl⟩
  rw [← vertical_nonarchimedean_target I m c]
  exact I.verticalSite.nonarchimedean_inclusion_at m _ z hz

theorem vertical_profile_upper_from_arch
    (I : Input Label Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.verticalSite.archimedeanImage m
      (I.profile.possibleImage c)) :
    ∃ y, y ∈ I.profile.possibleImage c ∧ z ≤ y := by
  exact I.verticalSite.archimedean_surjection_at m _ z hz

theorem vertical_profile_arch_target
    (I : Input Label Choice) (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage (I.core.ind3 m c)) :
    ∃ y, y ∈ I.profile.possibleImage c ∧ z ≤ y := by
  apply vertical_profile_upper_from_arch I m c z
  rw [vertical_archimedean_target I m c]
  exact hz

theorem vertical_profile_nonarch_target
    (I : Input Label Choice) (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage c) :
    z ∈ I.profile.possibleImage (I.core.ind3 m c) := by
  rw [← vertical_nonarchimedean_target I m c]
  exact I.verticalSite.nonarchimedean_inclusion_at m _ z hz

theorem vertical_nonarchimedean_contains_source
    (I : Input Label Choice) (m : Nat) (c : Choice) :
    I.profile.possibleImage c ⊆
      I.verticalSite.nonarchimedeanImage m
        (I.profile.possibleImage c) := by
  intro z hz
  exact I.verticalSite.nonarchimedean_inclusion_at m _ z hz

theorem vertical_archimedean_lifts_target
    (I : Input Label Choice) (m : Nat) (c : Choice) :
    ∀ z, z ∈ I.verticalSite.archimedeanImage m
      (I.profile.possibleImage c) →
      ∃ y, y ∈ I.profile.possibleImage c ∧ z ≤ y := by
  intro z hz
  exact I.verticalSite.archimedean_surjection_at m _ z hz

theorem vertical_nonarchimedean_image_eq_target
    (I : Input Label Choice) (m : Nat) (c : Choice) :
    I.verticalSite.nonarchimedeanImage m
        (I.profile.possibleImage c) =
      I.profile.possibleImage (I.core.ind3 m c) := by
  exact vertical_nonarchimedean_target I m c

theorem vertical_archimedean_image_eq_target
    (I : Input Label Choice) (m : Nat) (c : Choice) :
    I.verticalSite.archimedeanImage m
        (I.profile.possibleImage c) =
      I.profile.possibleImage (I.core.ind3 m c) := by
  exact vertical_archimedean_target I m c

theorem vertical_nonarchimedean_membership_iff
    (I : Input Label Choice) (m : Nat) (c : Choice) (z : Real) :
    z ∈ I.verticalSite.nonarchimedeanImage m
        (I.profile.possibleImage c) ↔
      z ∈ I.profile.possibleImage (I.core.ind3 m c) := by
  rw [vertical_nonarchimedean_image_eq_target]

theorem vertical_archimedean_membership_iff
    (I : Input Label Choice) (m : Nat) (c : Choice) (z : Real) :
    z ∈ I.verticalSite.archimedeanImage m
        (I.profile.possibleImage c) ↔
      z ∈ I.profile.possibleImage (I.core.ind3 m c) := by
  rw [vertical_archimedean_image_eq_target]

theorem vertical_archimedean_upper_semi
    (I : Input Label Choice) (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage (I.core.ind3 m c)) :
    ∃ y, y ∈ I.profile.possibleImage c ∧ z ≤ y := by
  exact vertical_profile_arch_target I m c z hz

theorem vertical_nonarchimedean_upper_semi
    (I : Input Label Choice) (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage c) :
    ∃ w, w ∈ I.profile.possibleImage (I.core.ind3 m c) ∧ z ≤ w := by
  refine ⟨z, vertical_profile_nonarch_target I m c z hz, le_rfl⟩

theorem vertical_nonarchimedean_then_archimedean
    (I : Input Label Choice) (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage c) :
    ∃ y, y ∈ I.profile.possibleImage c ∧ z ≤ y := by
  rcases vertical_nonarchimedean_upper_semi I m c z hz with ⟨w, hw, hzw⟩
  rcases vertical_archimedean_upper_semi I m c w hw with ⟨y, hy, hwy⟩
  exact ⟨y, hy, hzw.trans hwy⟩

theorem vertical_profile_upper_source_reindexed
    (I : Input Label Choice) (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage c) :
    ∃ w, w ∈ I.profile.possibleImage (I.core.ind3 m c) ∧
      0 ≤ w - z := by
  rcases vertical_nonarchimedean_upper_semi I m c z hz with ⟨w, hw, hzw⟩
  exact ⟨w, hw, sub_nonneg.mpr hzw⟩

theorem vertical_site_nonarchimedean_idempotent_on_profile
    (I : Input Label Choice) (m n : Nat) (c : Choice) :
    I.verticalSite.nonarchimedeanImage n
      (I.verticalSite.nonarchimedeanImage m
        (I.profile.possibleImage c)) =
      I.verticalSite.nonarchimedeanImage n
        (I.profile.possibleImage (I.core.ind3 m c)) := by
  rw [vertical_nonarchimedean_image_eq_target]

theorem vertical_site_archimedean_idempotent_on_profile
    (I : Input Label Choice) (m n : Nat) (c : Choice) :
    I.verticalSite.archimedeanImage n
      (I.verticalSite.archimedeanImage m
        (I.profile.possibleImage c)) =
      I.verticalSite.archimedeanImage n
        (I.profile.possibleImage (I.core.ind3 m c)) := by
  rw [vertical_archimedean_image_eq_target]

theorem vertical_site_nonarchimedean_respects_eq
    (I : Input Label Choice) (m : Nat) {S T : Set Real}
    (h : S = T) :
    I.verticalSite.nonarchimedeanImage m S =
      I.verticalSite.nonarchimedeanImage m T := by
  rw [h]

theorem vertical_site_archimedean_respects_eq
    (I : Input Label Choice) (m : Nat) {S T : Set Real}
    (h : S = T) :
    I.verticalSite.archimedeanImage m S =
      I.verticalSite.archimedeanImage m T := by
  rw [h]

theorem vertical_site_nonarchimedean_monotone
    (I : Input Label Choice) (m : Nat) {S T : Set Real}
    (hTransport : ∀ z, z ∈ I.verticalSite.nonarchimedeanImage m S →
      z ∈ I.verticalSite.nonarchimedeanImage m T) :
    I.verticalSite.nonarchimedeanImage m S ⊆
      I.verticalSite.nonarchimedeanImage m T := by
  intro z hz
  exact hTransport z hz

theorem vertical_site_archimedean_lift_chain
    (I : Input Label Choice) (m n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.verticalSite.archimedeanImage n
      (I.verticalSite.archimedeanImage m
      (I.profile.possibleImage c))) :
    ∃ y, y ∈ I.profile.possibleImage c ∧ z ≤ y := by
  rw [vertical_site_archimedean_idempotent_on_profile] at hz
  rcases I.verticalSite.archimedean_surjection_at n _ z hz with
    ⟨w, hw, hzw⟩
  rcases vertical_archimedean_upper_semi I m c w hw with
    ⟨y, hy, hwy⟩
  exact ⟨y, hy, hzw.trans hwy⟩

theorem vertical_profile_upper_source
    (I : Input Label Choice) (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage c) :
    ∃ w, w ∈ I.profile.possibleImage (I.core.ind3 m c) ∧ z ≤ w := by
  exact I.profile.possibleImage_ind3 m c z hz

/-! ## 6. Labelled Kummer maps and local tensor compatibility -/

theorem labelled_kummer_left_inverse
    (I : Input Label Choice) (c a : Choice) :
    (I.labelledKummer c).inverse ((I.labelledKummer c).map a) = a := by
  exact (I.labelledKummer c).left_inverse a

theorem labelled_kummer_right_inverse
    (I : Input Label Choice) (c b : Choice) :
    (I.labelledKummer c).map ((I.labelledKummer c).inverse b) = b := by
  exact (I.labelledKummer c).right_inverse b

theorem labelled_kummer_injective
    (I : Input Label Choice) (c : Choice) :
    Function.Injective (I.labelledKummer c).map := by
  exact (I.labelledKummer c).map_injective

theorem labelled_kummer_surjective
    (I : Input Label Choice) (c : Choice) :
    Function.Surjective (I.labelledKummer c).map := by
  exact (I.labelledKummer c).map_surjective

theorem labelled_kummer_equiv_apply
    (I : Input Label Choice) (c a : Choice) :
    (I.labelledKummer c).equiv a = (I.labelledKummer c).map a := rfl

theorem labelled_kummer_label_transport
    (I : Input Label Choice) (c a : Choice) :
    (I.labelledKummer c).label
        ((I.labelledKummer c).inverse
          ((I.labelledKummer c).map a)) =
      (I.labelledKummer c).label a := by
  exact (I.labelledKummer c).label_map a

theorem local_tensor_ind1_compatible
    (I : Input Label Choice) (g : Label) (c : Choice) :
    Real.log (I.localPacket.determinant (I.core.ind1 g c)) =
      Real.log (I.localPacket.determinant c) := by
  change Real.log (I.localPacket.determinant (I.prime.ind1 g c)) =
    Real.log (I.localPacket.determinant c)
  rw [I.localPacket.ind1_det]

theorem local_tensor_ind2_compatible
    (I : Input Label Choice) (g : Label) (c : Choice) :
    Real.log (I.localPacket.determinant (I.core.ind2 g c)) =
      Real.log (I.localPacket.determinant c) := by
  change Real.log (I.localPacket.determinant (I.prime.ind2 g c)) =
    Real.log (I.localPacket.determinant c)
  rw [I.localPacket.ind2_det]

theorem local_tensor_ind3_compatible
    (I : Input Label Choice) (n : Nat) (c : Choice) :
    I.localPacket.determinant c ≤
      I.localPacket.determinant (I.core.ind3 n c) :=
  I.localPacket.ind3_det_upper n c

theorem local_tensor_log_volume_eq_profile
    (I : Input Label Choice) (c : Choice) :
    I.localPacket.logVolume c = I.profile.logVolume c := by
  exact (I.packet_profile_volume c).symm

theorem labelled_packet_log_compatibility
    (I : Input Label Choice) (c : Choice) :
    Real.log (I.localPacket.determinant c) = I.profile.logVolume c := by
  rw [I.localPacket.log_determinant c]
  exact (I.packet_profile_volume c).symm

theorem labelled_packet_positive_compatibility
    (I : Input Label Choice) (c : Choice) :
    0 < I.localPacket.determinant c ∧
      I.localPacket.determinant c ≠ 0 := by
  exact ⟨I.localPacket.determinant_positive c,
    ne_of_gt (I.localPacket.determinant_positive c)⟩

theorem labelled_kummer_cancel_map_inverse
    (I : Input Label Choice) (c a : Choice) :
    (I.labelledKummer c).map
        ((I.labelledKummer c).inverse
          ((I.labelledKummer c).map a)) =
      (I.labelledKummer c).map a := by
  exact labelled_kummer_right_inverse I c ((I.labelledKummer c).map a)

theorem labelled_kummer_cancel_inverse_map
    (I : Input Label Choice) (c b : Choice) :
    (I.labelledKummer c).inverse
        ((I.labelledKummer c).map
          ((I.labelledKummer c).inverse b)) =
      (I.labelledKummer c).inverse b := by
  exact labelled_kummer_left_inverse I c ((I.labelledKummer c).inverse b)

theorem labelled_kummer_map_eq_iff
    (I : Input Label Choice) (c a b : Choice) :
    (I.labelledKummer c).map a = (I.labelledKummer c).map b ↔ a = b := by
  constructor
  · intro h
    exact (labelled_kummer_injective I c) h
  · intro h
    exact congrArg (I.labelledKummer c).map h

theorem labelled_kummer_inverse_eq_iff
    (I : Input Label Choice) (c a b : Choice) :
    (I.labelledKummer c).inverse a = (I.labelledKummer c).inverse b ↔
      a = b := by
  constructor
  · intro h
    calc
      a = (I.labelledKummer c).map
          ((I.labelledKummer c).inverse a) :=
        ((I.labelledKummer c).right_inverse a).symm
      _ = (I.labelledKummer c).map
          ((I.labelledKummer c).inverse b) := congrArg _ h
      _ = b := (I.labelledKummer c).right_inverse b
  · intro h
    exact congrArg (I.labelledKummer c).inverse h

theorem labelled_kummer_label_inverse_map
    (I : Input Label Choice) (c a : Choice) :
    (I.labelledKummer c).label
        ((I.labelledKummer c).inverse
          ((I.labelledKummer c).map a)) =
      (I.labelledKummer c).label a := by
  exact labelled_kummer_label_transport I c a

theorem labelled_kummer_label_of_map
    (I : Input Label Choice) (c a : Choice) :
    (I.labelledKummer c).label
        ((I.labelledKummer c).inverse
          ((I.labelledKummer c).map a)) =
      (I.labelledKummer c).label a := by
  exact labelled_kummer_label_inverse_map I c a

theorem labelled_kummer_horizontal_inverse_label
    (I : Input Label Choice) (c : Choice) :
    (I.labelledKummer c).label
      ((I.labelledKummer c).inverse
        (I.horizontal.right
          ((I.labelledKummer c).map (I.horizontal.lower c)))) =
      (I.labelledKummer c).label (I.horizontal.left c) := by
  rw [← I.kummer_horizontal_compat c]
  exact labelled_kummer_label_transport I c (I.horizontal.left c)

theorem labelled_kummer_horizontal_inverse_map
    (I : Input Label Choice) (c : Choice) :
    (I.labelledKummer c).map
      ((I.labelledKummer c).inverse
        (I.horizontal.right
          ((I.labelledKummer c).map (I.horizontal.lower c)))) =
      (I.horizontal.right
        ((I.labelledKummer c).map (I.horizontal.lower c))) := by
  exact labelled_kummer_right_inverse I c _

theorem labelled_kummer_horizontal_left_recovered
    (I : Input Label Choice) (c : Choice) :
    (I.labelledKummer c).inverse
      (I.horizontal.right
        ((I.labelledKummer c).map (I.horizontal.lower c))) =
      I.horizontal.left c := by
  rw [← I.kummer_horizontal_compat c]
  exact labelled_kummer_left_inverse I c (I.horizontal.left c)

theorem local_global_evaluation_chain
    (I : Input Label Choice) (c : Choice) :
    I.evaluation.localMap c = I.evaluation.globalMap c ∧
      I.evaluation.localMap (I.evaluation.localComp c) =
        I.evaluation.globalMap c := by
  constructor
  · exact I.evaluation.localEqGlobal c
  · rw [I.evaluation.localNaturality c]
    exact I.evaluation.localEqGlobal c

theorem global_local_evaluation_chain
    (I : Input Label Choice) (c : Choice) :
    I.evaluation.globalMap c = I.evaluation.localMap c ∧
      I.evaluation.globalMap (I.evaluation.globalComp c) =
        I.evaluation.localMap c := by
  constructor
  · exact (I.evaluation.localEqGlobal c).symm
  · rw [I.evaluation.globalNaturality c]
    exact (I.evaluation.localEqGlobal c).symm

theorem horizontal_evaluation_via_global
    (I : Input Label Choice) (c : Choice) :
    I.evaluation.globalMap (I.horizontal.left c) =
      I.horizontal.right (I.evaluation.globalMap
        (I.horizontal.lower c)) := by
  rw [← I.evaluation.localEqGlobal]
  rw [← I.evaluation.localEqGlobal]
  exact I.evaluation_horizontal_compat c

theorem horizontal_evaluation_local_global_quadruple
    (I : Input Label Choice) (c : Choice) :
    I.evaluation.localMap (I.horizontal.left c) =
        I.evaluation.globalMap (I.horizontal.left c) ∧
      I.evaluation.globalMap (I.horizontal.left c) =
        I.horizontal.right (I.evaluation.globalMap
          (I.horizontal.lower c)) ∧
      I.horizontal.right (I.evaluation.globalMap
          (I.horizontal.lower c)) =
        I.horizontal.right (I.evaluation.localMap
          (I.horizontal.lower c)) := by
  constructor
  · exact I.evaluation.localEqGlobal _
  constructor
  · exact horizontal_evaluation_via_global I c
  · exact congrArg I.horizontal.right
      (I.evaluation.localEqGlobal _).symm

theorem horizontal_label_kummer_chain
    (I : Input Label Choice) (c : Choice) :
    (I.labelledKummer c).label (I.horizontal.left c) =
      (I.labelledKummer c).label (I.horizontal.lower c) ∧
    (I.labelledKummer c).label
        ((I.labelledKummer c).inverse
          ((I.labelledKummer c).map (I.horizontal.left c))) =
      (I.labelledKummer c).label (I.horizontal.left c) := by
  constructor
  · exact I.labelled_horizontal_compat c
  · exact labelled_kummer_label_transport I c (I.horizontal.left c)

/-! ## 7. Part (ii) output -/

structure PartII (I : Input Label Choice) where
  vertical : VerticalLogKummerCorrespondence
  vertical_eq : vertical = verticalCorrespondence I
  siteData : VerticalSiteData Choice
  siteData_eq : siteData = I.verticalSite
  labelled_inverse : ∀ a : Choice,
    (verticalCorrespondence I).kummer 0 a =
      I.profile.logVolume a
  nonarchimedean_direction : ∀ m c z,
    z ∈ I.profile.possibleImage c →
    ∃ w, w ∈ I.profile.possibleImage (I.core.ind3 m c) ∧ z ≤ w
  archimedean_direction : ∀ m c z,
    z ∈ I.profile.possibleImage (I.core.ind3 m c) →
    ∃ w, w ∈ I.profile.possibleImage c ∧ z ≤ w

def partII (I : Input Label Choice) : PartII I where
  vertical := verticalCorrespondence I
  vertical_eq := rfl
  siteData := I.verticalSite
  siteData_eq := rfl
  labelled_inverse := by
    intro a
    rfl
  nonarchimedean_direction := by
    intro m c z hz
    exact vertical_profile_upper_source I m c z hz
  archimedean_direction := by
    intro m c z hz
    exact vertical_profile_arch_target I m c z hz

theorem partII_vertical (I : Input Label Choice) :
    (partII I).vertical = verticalCorrespondence I :=
  (partII I).vertical_eq

theorem partII_kummer (I : Input Label Choice) (c : Choice) :
    (partII I).vertical.kummer 0 c = I.profile.logVolume c := by
  change (verticalCorrespondence I).kummer 0 c = I.profile.logVolume c
  rfl

theorem partII_nonarchimedean (I : Input Label Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage c) :
    ∃ w, w ∈ I.profile.possibleImage (I.core.ind3 m c) ∧ z ≤ w :=
  (partII I).nonarchimedean_direction m c z hz

theorem partII_archimedean (I : Input Label Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage (I.core.ind3 m c)) :
    ∃ w, w ∈ I.profile.possibleImage c ∧ z ≤ w :=
  (partII I).archimedean_direction m c z hz

theorem partII_siteData (I : Input Label Choice) :
    (partII I).siteData = I.verticalSite :=
  (partII I).siteData_eq

theorem partII_nonarchimedean_inclusion (I : Input Label Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage c) :
    z ∈ (partII I).siteData.nonarchimedeanImage m
      (I.profile.possibleImage c) := by
  rw [partII_siteData]
  exact I.verticalSite.nonarchimedean_inclusion_at m _ z hz

theorem partII_archimedean_surjection (I : Input Label Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ (partII I).siteData.archimedeanImage m
      (I.profile.possibleImage c)) :
    ∃ y, y ∈ I.profile.possibleImage c ∧ z ≤ y := by
  rw [partII_siteData] at hz
  exact I.verticalSite.archimedean_surjection_at m _ z hz

theorem partII_nonarchimedean_profile (I : Input Label Choice)
    (m : Nat) (c : Choice) :
    (partII I).siteData.nonarchimedeanImage m
        (I.profile.possibleImage c) =
      I.profile.possibleImage (I.core.ind3 m c) := by
  rw [partII_siteData]
  exact vertical_nonarchimedean_target I m c

theorem partII_archimedean_profile (I : Input Label Choice)
    (m : Nat) (c : Choice) :
    (partII I).siteData.archimedeanImage m
        (I.profile.possibleImage c) =
      I.profile.possibleImage (I.core.ind3 m c) := by
  rw [partII_siteData]
  exact vertical_archimedean_target I m c

theorem partII_archimedean_target (I : Input Label Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage (I.core.ind3 m c)) :
    ∃ y, y ∈ I.profile.possibleImage c ∧ z ≤ y := by
  apply partII_archimedean_surjection I m c z
  rw [partII_archimedean_profile]
  exact hz

theorem partII_labelled_kummer (I : Input Label Choice) (c : Choice) :
    Function.Bijective (I.labelledKummer c).map := by
  exact ⟨labelled_kummer_injective I c, labelled_kummer_surjective I c⟩

/-! ## 8. Part (iii): Theta-times-mu horizontal LGP compatibility -/

theorem horizontal_square (I : Input Label Choice) (c : Choice) :
    I.horizontal.upper (I.horizontal.left c) =
      I.horizontal.right (I.horizontal.lower c) :=
  I.horizontal.square c

theorem horizontal_label_compatibility (I : Input Label Choice) (c : Choice) :
    I.horizontal.upper_label c = I.horizontal.lower_label c :=
  I.horizontal.labels_agree c

theorem horizontal_evaluation_compatibility
    (I : Input Label Choice) (c : Choice) :
    I.evaluation.localMap (I.horizontal.left c) =
      I.horizontal.right (I.evaluation.localMap (I.horizontal.lower c)) :=
  I.evaluation_horizontal_compat c

theorem horizontal_evaluation_global_compatibility
    (I : Input Label Choice) (c : Choice) :
    I.evaluation.globalMap (I.horizontal.left c) =
      I.horizontal.right (I.evaluation.globalMap (I.horizontal.lower c)) := by
  rw [← I.evaluation.localEqGlobal]
  rw [← I.evaluation.localEqGlobal]
  rw [horizontal_evaluation_compatibility]

theorem horizontal_square_after_evaluation
    (I : Input Label Choice) (c : Choice) :
    I.horizontal.upper (I.horizontal.left c) =
      I.horizontal.right (I.horizontal.lower c) ∧
      I.evaluation.localMap (I.horizontal.left c) =
        I.horizontal.right (I.evaluation.localMap (I.horizontal.lower c)) :=
  ⟨horizontal_square I c, horizontal_evaluation_compatibility I c⟩

theorem horizontal_label_after_evaluation
    (I : Input Label Choice) (c : Choice) :
    I.horizontal.upper_label c = I.horizontal.lower_label c :=
  horizontal_label_compatibility I c

theorem family_injective (I : Input Label Choice) :
    Function.Injective I.family.theater :=
  I.family.distinct

theorem family_refl (I : Input Label Choice) (i t : Choice) :
    I.family.link i i t = t :=
  I.family.link_refl i t

theorem family_trans (I : Input Label Choice)
    (i j k t : Choice) :
    I.family.link j k (I.family.link i j t) = I.family.link i k t :=
  I.family.link_trans i j k t

theorem family_permutation_natural (I : Input Label Choice)
    (i t : Choice) :
    I.family.link (I.family.permutation i) (I.family.permutation i) t =
      I.family.link i i t :=
  I.family.permutation_naturality i t

def permutedFamily (I : Input Label Choice) : TheaterFamily Choice Choice where
  theater := fun i => I.family.theater (I.family.permutation i)
  distinct := by
    intro i j h
    apply I.family.permutation.injective
    exact I.family.distinct h
  link := fun i j t => I.family.link
    (I.family.permutation i) (I.family.permutation j) t
  link_refl := by
    intro i t
    exact I.family.link_refl _ t
  link_trans := by
    intro i j k t
    exact I.family.link_trans _ _ _ t
  permutation := Equiv.refl Choice
  permutation_naturality := by
    intro i t
    rfl

theorem permutedFamily_theater (I : Input Label Choice) (i : Choice) :
    (permutedFamily I).theater i =
      I.family.theater (I.family.permutation i) := rfl

theorem permutedFamily_link (I : Input Label Choice)
    (i j t : Choice) :
    (permutedFamily I).link i j t =
      I.family.link (I.family.permutation i)
        (I.family.permutation j) t := rfl

theorem permutedFamily_injective (I : Input Label Choice) :
    Function.Injective (permutedFamily I).theater := by
  exact (permutedFamily I).distinct

theorem horizontal_kummer_square
    (I : Input Label Choice) (c : Choice) :
    (I.labelledKummer c).map (I.horizontal.left c) =
      I.horizontal.right ((I.labelledKummer c).map (I.horizontal.lower c)) := by
  exact I.kummer_horizontal_compat c

theorem horizontal_kummer_square_inverse
    (I : Input Label Choice) (c : Choice) :
    (I.labelledKummer c).inverse
        (I.horizontal.right ((I.labelledKummer c).map (I.horizontal.lower c))) =
      I.horizontal.left c := by
  rw [← horizontal_kummer_square I c]
  exact labelled_kummer_left_inverse I c (I.horizontal.left c)

theorem horizontal_kummer_square_bijective
    (I : Input Label Choice) (c : Choice) :
    Function.Bijective (I.labelledKummer c).map :=
  partII_labelled_kummer I c

theorem horizontal_eval_local_global
    (I : Input Label Choice) (c : Choice) :
    I.evaluation.localMap (I.horizontal.left c) =
      I.evaluation.globalMap (I.horizontal.left c) :=
  I.evaluation.localEqGlobal _

theorem horizontal_eval_comp_local
    (I : Input Label Choice) (c : Choice) :
    I.evaluation.localMap (I.evaluation.localComp c) =
      I.evaluation.localMap c :=
  I.evaluation.localNaturality c

theorem horizontal_eval_comp_global
    (I : Input Label Choice) (c : Choice) :
    I.evaluation.globalMap (I.evaluation.globalComp c) =
      I.evaluation.globalMap c :=
  I.evaluation.globalNaturality c

/-! The four clauses below are kept separate to mirror the four clauses of
    Theorem 3.11(iii). -/

structure PartIII (I : Input Label Choice) where
  timesMuLink : HorizontalLGPLink Choice Choice
  environmentLink : HorizontalLGPLink Choice Choice
  timesMu_square : ∀ c,
    timesMuLink.upper (timesMuLink.left c) =
      timesMuLink.right (timesMuLink.lower c)
  environment_square : ∀ c,
    environmentLink.upper (environmentLink.left c) =
      environmentLink.right (environmentLink.lower c)
  permutation_stable : ∀ c,
    I.family.link (I.family.permutation c) (I.family.permutation c) c =
      I.family.link c c c
  kappa_compatible : ∀ c,
    I.evaluation.localMap (I.horizontal.left c) =
      I.horizontal.right (I.evaluation.localMap (I.horizontal.lower c))
  labelled_compatible : ∀ c,
    (I.labelledKummer c).label (I.horizontal.left c) =
      (I.labelledKummer c).label (I.horizontal.lower c)

def partIII (I : Input Label Choice) : PartIII I where
  timesMuLink := I.horizontal
  environmentLink := I.horizontal
  timesMu_square := by intro c; exact I.horizontal.square c
  environment_square := by intro c; exact I.horizontal.square c
  permutation_stable := by
    intro c
    exact I.family.permutation_naturality c c
  kappa_compatible := I.evaluation_horizontal_compat
  labelled_compatible := by
    intro c
    exact I.labelled_horizontal_compat c

theorem partIII_timesMu_square (I : Input Label Choice) (c : Choice) :
    (partIII I).timesMuLink.upper ((partIII I).timesMuLink.left c) =
      (partIII I).timesMuLink.right ((partIII I).timesMuLink.lower c) :=
  (partIII I).timesMu_square c

theorem partIII_environment_square (I : Input Label Choice) (c : Choice) :
    (partIII I).environmentLink.upper
        ((partIII I).environmentLink.left c) =
      (partIII I).environmentLink.right
        ((partIII I).environmentLink.lower c) :=
  (partIII I).environment_square c

theorem partIII_permutation_stable (I : Input Label Choice) (c : Choice) :
    I.family.link (I.family.permutation c) (I.family.permutation c) c =
      I.family.link c c c :=
  (partIII I).permutation_stable c

theorem partIII_kappa_compatible (I : Input Label Choice) (c : Choice) :
    I.evaluation.localMap (I.horizontal.left c) =
      I.horizontal.right (I.evaluation.localMap (I.horizontal.lower c)) :=
  (partIII I).kappa_compatible c

theorem partIII_labelled_compatible (I : Input Label Choice) (c : Choice) :
    (I.labelledKummer c).label (I.horizontal.left c) =
      (I.labelledKummer c).label (I.horizontal.lower c) :=
  (partIII I).labelled_compatible c

theorem partIII_timesMu_is_input (I : Input Label Choice) :
    (partIII I).timesMuLink = I.horizontal := rfl

theorem partIII_environment_is_input (I : Input Label Choice) :
    (partIII I).environmentLink = I.horizontal := rfl

theorem partIII_square_both (I : Input Label Choice) (c : Choice) :
    (partIII I).timesMuLink.upper ((partIII I).timesMuLink.left c) =
        (partIII I).timesMuLink.right ((partIII I).timesMuLink.lower c) ∧
      (partIII I).environmentLink.upper
          ((partIII I).environmentLink.left c) =
        (partIII I).environmentLink.right
          ((partIII I).environmentLink.lower c) :=
  ⟨partIII_timesMu_square I c, partIII_environment_square I c⟩

theorem partIII_kummer_evaluation_both
    (I : Input Label Choice) (c : Choice) :
    I.evaluation.localMap (I.horizontal.left c) =
        I.horizontal.right (I.evaluation.localMap (I.horizontal.lower c)) ∧
      (I.labelledKummer c).label (I.horizontal.left c) =
        (I.labelledKummer c).label (I.horizontal.lower c) :=
  ⟨partIII_kappa_compatible I c, partIII_labelled_compatible I c⟩

/-! ## 9. Assembly of the three parts -/

structure Theorem311Output (I : Input Label Choice) where
  part_i : PartI I
  part_ii : PartII I
  part_iii : PartIII I
  source : Choice
  source_eq : source = I.core.base
  quotient : IndeterminacyQuotient I
  quotient_eq : quotient = quotientMap I source
  labelled_bijective : ∀ c, Function.Bijective (I.labelledKummer c).map
  ind1_quotient : ∀ {a b}, Ind1Relation I a b → quotientMap I a = quotientMap I b
  ind2_quotient : ∀ {a b}, Ind2Relation I a b → quotientMap I a = quotientMap I b
  ind3_upper : ∀ n c z, z ∈ I.profile.possibleImage c →
    ∃ w, w ∈ I.profile.possibleImage (I.core.ind3 n c) ∧ z ≤ w
  horizontal_square : ∀ c,
    I.horizontal.upper (I.horizontal.left c) =
      I.horizontal.right (I.horizontal.lower c)
  horizontal_evaluation : ∀ c,
    I.evaluation.localMap (I.horizontal.left c) =
      I.horizontal.right (I.evaluation.localMap (I.horizontal.lower c))

def theorem311Output (I : Input Label Choice) : Theorem311Output I where
  part_i := partI I
  part_ii := partII I
  part_iii := partIII I
  source := I.core.base
  source_eq := rfl
  quotient := quotientMap I I.core.base
  quotient_eq := rfl
  labelled_bijective := by
    intro c
    exact partII_labelled_kummer I c
  ind1_quotient := by
    intro a b h
    exact quotientMap_respects_ind1 I h
  ind2_quotient := by
    intro a b h
    exact quotientMap_respects_ind2 I h
  ind3_upper := by
    intro n c z hz
    exact vertical_profile_upper_source I n c z hz
  horizontal_square := by
    intro c
    exact horizontal_square I c
  horizontal_evaluation := by
    intro c
    exact horizontal_evaluation_compatibility I c

theorem theorem311Output_source (I : Input Label Choice) :
    (theorem311Output I).source = I.core.base :=
  (theorem311Output I).source_eq

theorem theorem311Output_quotient (I : Input Label Choice) :
    (theorem311Output I).quotient = quotientMap I (theorem311Output I).source := by
  rw [theorem311Output_source]
  rfl

theorem theorem311Output_part_i (I : Input Label Choice) :
    (theorem311Output I).part_i = partI I := rfl

theorem theorem311Output_part_ii (I : Input Label Choice) :
    (theorem311Output I).part_ii = partII I := rfl

theorem theorem311Output_part_iii (I : Input Label Choice) :
    (theorem311Output I).part_iii = partIII I := rfl

theorem theorem311Output_labelled (I : Input Label Choice) (c : Choice) :
    Function.Bijective (I.labelledKummer c).map :=
  (theorem311Output I).labelled_bijective c

theorem theorem311Output_ind1 (I : Input Label Choice)
    {a b : Choice} (h : Ind1Relation I a b) :
    quotientMap I a = quotientMap I b :=
  (theorem311Output I).ind1_quotient h

theorem theorem311Output_ind2 (I : Input Label Choice)
    {a b : Choice} (h : Ind2Relation I a b) :
    quotientMap I a = quotientMap I b :=
  (theorem311Output I).ind2_quotient h

theorem theorem311Output_ind3 (I : Input Label Choice)
    (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ I.profile.possibleImage c) :
    ∃ w, w ∈ I.profile.possibleImage (I.core.ind3 n c) ∧ z ≤ w :=
  (theorem311Output I).ind3_upper n c z hz

theorem theorem311Output_horizontal (I : Input Label Choice) (c : Choice) :
    I.horizontal.upper (I.horizontal.left c) =
      I.horizontal.right (I.horizontal.lower c) :=
  (theorem311Output I).horizontal_square c

theorem theorem311Output_evaluation (I : Input Label Choice) (c : Choice) :
    I.evaluation.localMap (I.horizontal.left c) =
      I.horizontal.right (I.evaluation.localMap (I.horizontal.lower c)) :=
  (theorem311Output I).horizontal_evaluation c

/-! ## 10. Explicit source-contract theorem -/

/-- Every prerequisite in the audit is an explicit argument of `Input`; the
    conclusion is the exact three-part output, with no weakened equality in
    place of the upper-semi direction. -/
def theorem311_of_explicit_prerequisites
    (I : Input Label Choice) : Theorem311Output I :=
  theorem311Output I

def theorem311_part_i_of_explicit
    (I : Input Label Choice) : PartI I :=
  (theorem311_of_explicit_prerequisites I).part_i

def theorem311_part_ii_of_explicit
    (I : Input Label Choice) : PartII I :=
  (theorem311_of_explicit_prerequisites I).part_ii

def theorem311_part_iii_of_explicit
    (I : Input Label Choice) : PartIII I :=
  (theorem311_of_explicit_prerequisites I).part_iii

end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- The algebraic/source-boundary consequences of Theorem 3.11 are now
    checked from explicit prerequisites.  This does not alter the separate
    pending obligation for constructing those prerequisites from arbitrary
    IUT I--II input. -/
def theorem311ExplicitPrerequisiteBoundary : Obligation :=
  { id := "IUT-III.theorem-3.11-explicit-prerequisite-boundary"
    source := "IUT III, Theorem 3.11 (i)--(iii)"
    status := VerificationStatus.interface
    note :=
      "The conditional procession, packet/determinant, Ind1/Ind2, Ind3, " ++
        "labelled Kummer, and horizontal compatibility lemmas compile from an " ++
        "explicit boundary. They are not an unconditional Theorem 3.11 proof: " ++
        "the initial Theta-data, distinct Hodge theaters, LGP-Gaussian lattice, " ++
        "D-Theta bridge, and IUT I--II constructions still have to be built " ++
        "from the foundational mathematics."
    dependsOn :=
      [ "IUT-I.initial-theta-data",
        "IUT-I-II.prime-strips-frobenioids",
        "IUT-II.vertical-log-kummer" ] }

end LeanFormal.IUT.Audit
