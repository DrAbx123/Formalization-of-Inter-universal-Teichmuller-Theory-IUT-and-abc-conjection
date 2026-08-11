import LeanFormal.IUT.IUTIII.Theorem311.SourceDependencyChain
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.UpperSemi
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummer
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # Source-facing K1/K2 assembly

  This module separates the two IUT-II gates which are read by Theorem 3.11
  from the preceding H1/H2 source projection.  K1 consumes an actual source
  vertical realization and exposes its carrier, maps, and the two upper-semi
  directions with their original quantifiers.  K2 consumes K1 together with
  the supplied local/global Frobenioid and MOD/mod data and exposes the degree,
  realification, comparison, and upper-semi transports.

  Neither record has an inhabitant manufactured from `OriginalInput`.  The
  canonical K1 projection is available once a `SourceTheorem311Realization`
  has supplied `SourceVerticalRealization`; K2 remains an explicit boundary
  because the paper's local/global Frobenioid and MOD/mod constructions are
  not consequences of H1/H2 alone.

  Source references:

  * IUT II, Definition 4.9 and Corollaries 4.10--4.11;
  * IUT III, Proposition 3.5 and Theorem 3.11(ii);
  * IUT III, Propositions 3.7 and 3.10.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u v w ux uy

namespace Theorem311Source

open SourceHodgeTheaterBridge
open SourceDependencyChain

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## K1: vertical log-Kummer boundary -/

/-!
  `K1VerticalBoundary` has exactly the source-facing vertical fields.  The
  `toSource` map is deliberately field-by-field: it does not choose a new
  carrier or replace either inclusion/surjection by an equality.
-/
structure K1VerticalBoundary
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization P) where
  vertical : UpperSemiCorrespondence Nat Real
  vertical_monotone : ∀ m n, m ≤ n →
    ∀ z, z ∈ vertical.image m →
      ∃ w, w ∈ vertical.image n ∧ z ≤ w
  nonarchimedeanImage : Nat → Set Real → Set Real
  archimedeanImage : Nat → Set Real → Set Real
  nonarchimedean_inclusion : ∀ (m : Nat) (z : Real) (S : Set Real),
    z ∈ S → z ∈ nonarchimedeanImage m S
  archimedean_surjection : ∀ (m : Nat) (z : Real) (S : Set Real),
    z ∈ archimedeanImage m S → ∃ y, y ∈ S ∧ z ≤ y
  nonarchimedean_profile : ∀ (m : Nat) (c : Choice),
    nonarchimedeanImage m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c)
  archimedean_profile : ∀ (m : Nat) (c : Choice),
    archimedeanImage m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c)
  labelledKummer : ∀ c : Choice, LabelledKummerIso Choice Choice
  labelled_label : ∀ (c a : Choice),
    (labelledKummer c).label
        ((labelledKummer c).inverse ((labelledKummer c).map a)) =
      (labelledKummer c).label a

namespace K1VerticalBoundary

variable {P : SourceLGPProcession l Label Choice}
variable {Q : SourcePacketRealization P}
variable (K : K1VerticalBoundary P Q)
include K

def toSource : SourceVerticalRealization P Q where
  vertical := K.vertical
  vertical_monotone := K.vertical_monotone
  nonarchimedeanImage := K.nonarchimedeanImage
  archimedeanImage := K.archimedeanImage
  nonarchimedean_inclusion := K.nonarchimedean_inclusion
  archimedean_surjection := K.archimedean_surjection
  nonarchimedean_profile := K.nonarchimedean_profile
  archimedean_profile := K.archimedean_profile
  kummer := K.labelledKummer
  kummer_label := K.labelled_label

@[simp] theorem toSource_vertical : K.toSource.vertical = K.vertical := rfl

@[simp] theorem toSource_nonarchimedeanImage (m : Nat) (S : Set Real) :
    K.toSource.nonarchimedeanImage m S = K.nonarchimedeanImage m S := rfl

@[simp] theorem toSource_archimedeanImage (m : Nat) (S : Set Real) :
    K.toSource.archimedeanImage m S = K.archimedeanImage m S := rfl

@[simp] theorem toSource_kummer (c : Choice) :
    K.toSource.kummer c = K.labelledKummer c := rfl

def correspondence : VerticalLogKummerCorrespondence :=
  K.toSource.correspondence

@[simp] theorem correspondence_log (m : Nat) (c : Choice) :
    K.correspondence.log m c = P.ind3 m c := rfl

@[simp] theorem correspondence_kummer (m : Nat) (c : Choice) :
    K.correspondence.kummer m c = Q.logVolume c := rfl

theorem correspondence_upper (m : Nat) (c : Choice) :
    K.correspondence.kummer m c ≤
      K.correspondence.kummer (m + 1) (K.correspondence.log m c) := by
  exact K.correspondence.upperSemi m c

theorem transport_zero (c : Choice) :
    K.correspondence.transport 0 0 c = c := rfl

theorem transport_one (c : Choice) :
    K.correspondence.transport 0 1 c = P.ind3 0 c := rfl

theorem transport_two (c : Choice) :
    K.correspondence.transport 0 2 c = P.ind3 1 (P.ind3 0 c) := rfl

theorem kummer_le_transport (c : Choice) (n : Nat) :
    Q.logVolume c ≤ K.correspondence.kummer n
      (K.correspondence.transport 0 n c) := by
  exact K.correspondence.kummer_le_transport 0 c n

theorem kummer_le_ind3 (c : Choice) (n : Nat) :
    Q.logVolume c ≤ Q.logVolume (P.ind3 n c) :=
  Q.ind3_volume n c

theorem hull_base_le {c : Choice} {hull : Real}
    (h : K.correspondence.HullDominates c hull) :
    Q.logVolume c ≤ hull := by
  exact K.correspondence.base_le_hull h

theorem nonarchimedean_inclusion_at (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    z ∈ K.nonarchimedeanImage m (Q.possibleImage c) :=
  K.nonarchimedean_inclusion m z _ hz

theorem archimedean_surjection_at (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ K.archimedeanImage m (Q.possibleImage c)) :
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y :=
  K.archimedean_surjection m z _ hz

theorem nonarchimedean_profile_at (m : Nat) (c : Choice) :
    K.nonarchimedeanImage m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c) :=
  K.nonarchimedean_profile m c

theorem archimedean_profile_at (m : Nat) (c : Choice) :
    K.archimedeanImage m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c) :=
  K.archimedean_profile m c

theorem nonarchimedean_target_mem (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    z ∈ Q.possibleImage (P.ind3 m c) := by
  rw [← K.nonarchimedean_profile_at m c]
  exact K.nonarchimedean_inclusion_at m c z hz

theorem nonarchimedean_upper (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    ∃ y, y ∈ Q.possibleImage (P.ind3 m c) ∧ z ≤ y := by
  exact ⟨z, K.nonarchimedean_target_mem m c z hz, le_rfl⟩

theorem archimedean_target_lift (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage (P.ind3 m c)) :
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y := by
  apply K.archimedean_surjection_at m c z
  rw [K.archimedean_profile_at m c]
  exact hz

theorem nonarchimedean_subset (m : Nat) (c : Choice) :
    Q.possibleImage c ⊆ K.nonarchimedeanImage m (Q.possibleImage c) := by
  intro z hz
  exact K.nonarchimedean_inclusion_at m c z hz

theorem archimedean_target_dominates (m : Nat) (c : Choice) :
    ∀ z, z ∈ K.archimedeanImage m (Q.possibleImage c) →
      ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y := by
  intro z hz
  exact K.archimedean_surjection_at m c z hz

theorem vertical_image_nonempty (m : Nat) (c : Choice) :
    (Q.possibleImage (P.ind3 m c)).Nonempty := by
  rw [← K.nonarchimedean_profile_at m c]
  exact Set.Nonempty.mono (K.nonarchimedean_subset m c)
    (Q.possibleImage_nonempty c)

theorem vertical_monotone_at (m n : Nat) (h : m ≤ n)
    (z : Real) (hz : z ∈ K.vertical.image m) :
    ∃ w, w ∈ K.vertical.image n ∧ z ≤ w :=
  K.vertical_monotone m n h z hz

theorem labelled_left (c a : Choice) :
    (K.labelledKummer c).inverse ((K.labelledKummer c).map a) = a :=
  (K.labelledKummer c).left_inverse a

theorem labelled_right (c b : Choice) :
    (K.labelledKummer c).map ((K.labelledKummer c).inverse b) = b :=
  (K.labelledKummer c).right_inverse b

theorem labelled_injective (c : Choice) :
    Function.Injective (K.labelledKummer c).map := by
  intro a b h
  calc
    a = (K.labelledKummer c).inverse ((K.labelledKummer c).map a) :=
      (K.labelled_left c a).symm
    _ = (K.labelledKummer c).inverse ((K.labelledKummer c).map b) :=
      congrArg (K.labelledKummer c).inverse h
    _ = b := K.labelled_left c b

theorem labelled_surjective (c : Choice) :
    Function.Surjective (K.labelledKummer c).map := by
  intro b
  exact ⟨(K.labelledKummer c).inverse b, K.labelled_right c b⟩

theorem labelled_bijective (c : Choice) :
    Function.Bijective (K.labelledKummer c).map :=
  ⟨K.labelled_injective c, K.labelled_surjective c⟩

theorem labelled_map_eq_iff (c a b : Choice) :
    (K.labelledKummer c).map a = (K.labelledKummer c).map b ↔ a = b := by
  constructor
  · intro h
    exact K.labelled_injective c h
  · intro h
    exact congrArg (K.labelledKummer c).map h

theorem labelled_inverse_eq_iff (c a b : Choice) :
    (K.labelledKummer c).inverse a = (K.labelledKummer c).inverse b ↔
      a = b := by
  constructor
  · intro h
    calc
      a = (K.labelledKummer c).map ((K.labelledKummer c).inverse a) :=
        (K.labelled_right c a).symm
      _ = (K.labelledKummer c).map ((K.labelledKummer c).inverse b) :=
        congrArg (K.labelledKummer c).map h
      _ = b := K.labelled_right c b
  · intro h
    exact congrArg (K.labelledKummer c).inverse h

theorem labelled_label_transport (c a : Choice) :
    (K.labelledKummer c).label
        ((K.labelledKummer c).inverse ((K.labelledKummer c).map a)) =
      (K.labelledKummer c).label a :=
  K.labelled_label c a

theorem nonarchimedean_then_archimedean (m : Nat) (c : Choice)
    (z : Real) (hz : z ∈ Q.possibleImage c) :
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y := by
  rcases K.nonarchimedean_upper m c z hz with ⟨w, hw, hzw⟩
  rcases K.archimedean_target_lift m c w hw with ⟨y, hy, hwy⟩
  exact ⟨y, hy, hzw.trans hwy⟩

end K1VerticalBoundary

/-! The canonical K1 projection from a supplied source realization. -/

def k1OfRealization
    (R : SourceTheorem311Realization l Label Choice) :
    K1VerticalBoundary R.procession R.packet where
  vertical := R.vertical.vertical
  vertical_monotone := R.vertical.vertical_monotone
  nonarchimedeanImage := R.vertical.nonarchimedeanImage
  archimedeanImage := R.vertical.archimedeanImage
  nonarchimedean_inclusion := R.vertical.nonarchimedean_inclusion
  archimedean_surjection := R.vertical.archimedean_surjection
  nonarchimedean_profile := R.vertical.nonarchimedean_profile
  archimedean_profile := R.vertical.archimedean_profile
  labelledKummer := R.vertical.kummer
  labelled_label := R.vertical.kummer_label

@[simp] theorem k1OfRealization_vertical
    (R : SourceTheorem311Realization l Label Choice) :
    (k1OfRealization R).vertical = R.vertical.vertical := rfl

@[simp] theorem k1OfRealization_nonarchimedeanImage
    (R : SourceTheorem311Realization l Label Choice) (m : Nat) (S : Set Real) :
    (k1OfRealization R).nonarchimedeanImage m S =
      R.vertical.nonarchimedeanImage m S := rfl

@[simp] theorem k1OfRealization_archimedeanImage
    (R : SourceTheorem311Realization l Label Choice) (m : Nat) (S : Set Real) :
    (k1OfRealization R).archimedeanImage m S =
      R.vertical.archimedeanImage m S := rfl

@[simp] theorem k1OfRealization_labelledKummer
    (R : SourceTheorem311Realization l Label Choice) (c : Choice) :
    (k1OfRealization R).labelledKummer c = R.vertical.kummer c := rfl

theorem k1OfRealization_toSource
    (R : SourceTheorem311Realization l Label Choice) :
    (k1OfRealization R).toSource = R.vertical := by
  rfl

theorem k1_realization_nonarchimedean
    (R : SourceTheorem311Realization l Label Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage c) :
    ∃ y, y ∈ R.packet.possibleImage (R.procession.ind3 m c) ∧ z ≤ y := by
  exact (k1OfRealization R).nonarchimedean_upper m c z hz

theorem k1_realization_archimedean
    (R : SourceTheorem311Realization l Label Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage (R.procession.ind3 m c)) :
    ∃ y, y ∈ R.packet.possibleImage c ∧ z ≤ y := by
  exact (k1OfRealization R).archimedean_target_lift m c z hz

theorem k1_realization_labelled_bijective
    (R : SourceTheorem311Realization l Label Choice) (c : Choice) :
    Function.Bijective (R.vertical.kummer c).map := by
  simpa using (k1OfRealization R).labelled_bijective c

theorem k1_realization_upper_chain
    (R : SourceTheorem311Realization l Label Choice)
    (m n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage c) :
    ∃ y, y ∈ R.packet.possibleImage
      (R.procession.ind3 n (R.procession.ind3 m c)) ∧ z ≤ y := by
  rcases (k1OfRealization R).nonarchimedean_upper m c z hz with
    ⟨w, hw, hzw⟩
  rcases (k1OfRealization R).nonarchimedean_upper n
      (R.procession.ind3 m c) w hw with ⟨y, hy, hwy⟩
  exact ⟨y, hy, hzw.trans hwy⟩

/-! ## K2: Frobenioid, MOD/mod, and comparison boundary -/

/-!
  K2 deliberately keeps local and global Frobenioid carriers separate.  The
  fields `modMap` and `MODMap` are the two source directions; only the degree,
  realification, and transport equations explicitly supplied by the source
  boundary are used.  No inverse law is inferred from their names.
-/
structure K2FrobenioidBoundary
    (R : SourceTheorem311Realization l Label Choice)
    (K : K1VerticalBoundary R.procession R.packet)
    (X : Type ux) (Y : Type uy)
    [CommMonoid X] [CommMonoid Y] where
  localFrobenioid : SourceProposition37Frobenioid X
  globalFrobenioid : SourceProposition37Frobenioid Y
  modMap : X → Y
  MODMap : Y → X
  mod_degree : ∀ x,
    globalFrobenioid.degree (modMap x) = localFrobenioid.degree x
  MOD_degree : ∀ y,
    localFrobenioid.degree (MODMap y) = globalFrobenioid.degree y
  mod_realification : ∀ x,
    globalFrobenioid.realification (modMap x) =
      localFrobenioid.realification x
  MOD_realification : ∀ y,
    localFrobenioid.realification (MODMap y) =
      globalFrobenioid.realification y
  mod_transport : ∀ x,
    modMap (localFrobenioid.transport x) =
      globalFrobenioid.transport (modMap x)
  MOD_transport : ∀ y,
    MODMap (globalFrobenioid.transport y) =
      localFrobenioid.transport (MODMap y)
  comparison : SourceProposition310Comparison Choice Choice
  comparison_local : comparison.localMap =
    R.evaluation.evaluation.localMap
  comparison_global : comparison.globalMap =
    R.evaluation.evaluation.globalMap
  comparison_lower : comparison.lower =
    R.evaluation.evaluation.localComp
  comparison_upper : comparison.upper =
    R.evaluation.evaluation.globalComp
  upperSemi : UpperSemiCorrespondence Nat Real
  upperSemi_eq_k1 : upperSemi = K.vertical

namespace K2FrobenioidBoundary

variable {R : SourceTheorem311Realization l Label Choice}
variable {K : K1VerticalBoundary R.procession R.packet}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable (B : K2FrobenioidBoundary R K X Y)
include B

theorem mod_degree_at (x : X) :
    B.globalFrobenioid.degree (B.modMap x) =
      B.localFrobenioid.degree x :=
  B.mod_degree x

theorem MOD_degree_at (y : Y) :
    B.localFrobenioid.degree (B.MODMap y) =
      B.globalFrobenioid.degree y :=
  B.MOD_degree y

theorem mod_realification_at (x : X) :
    B.globalFrobenioid.realification (B.modMap x) =
      B.localFrobenioid.realification x :=
  B.mod_realification x

theorem MOD_realification_at (y : Y) :
    B.localFrobenioid.realification (B.MODMap y) =
      B.globalFrobenioid.realification y :=
  B.MOD_realification y

theorem mod_degree_real (x : X) :
    (B.globalFrobenioid.degree (B.modMap x) : Real) =
      (B.localFrobenioid.degree x : Real) := by
  rw [B.mod_degree x]

theorem MOD_degree_real (y : Y) :
    (B.localFrobenioid.degree (B.MODMap y) : Real) =
      (B.globalFrobenioid.degree y : Real) := by
  rw [B.MOD_degree y]

theorem mod_realification_degree (x : X) :
    (B.globalFrobenioid.degree (B.modMap x) : Real) =
      B.localFrobenioid.realification x := by
  calc
    (B.globalFrobenioid.degree (B.modMap x) : Real) =
        B.globalFrobenioid.realification (B.modMap x) :=
      B.globalFrobenioid.degree_realification _
    _ = B.localFrobenioid.realification x := B.mod_realification x

theorem MOD_realification_degree (y : Y) :
    (B.localFrobenioid.degree (B.MODMap y) : Real) =
      B.globalFrobenioid.realification y := by
  calc
    (B.localFrobenioid.degree (B.MODMap y) : Real) =
        B.localFrobenioid.realification (B.MODMap y) :=
      B.localFrobenioid.degree_realification _
    _ = B.globalFrobenioid.realification y := B.MOD_realification y

theorem mod_transport_at (x : X) :
    B.modMap (B.localFrobenioid.transport x) =
      B.globalFrobenioid.transport (B.modMap x) :=
  B.mod_transport x

theorem MOD_transport_at (y : Y) :
    B.MODMap (B.globalFrobenioid.transport y) =
      B.localFrobenioid.transport (B.MODMap y) :=
  B.MOD_transport y

theorem local_degree_mul (x₁ x₂ : X) :
    B.localFrobenioid.degree (x₁ * x₂) =
      B.localFrobenioid.degree x₁ * B.localFrobenioid.degree x₂ :=
  B.localFrobenioid.degree_mul x₁ x₂

theorem global_degree_mul (y₁ y₂ : Y) :
    B.globalFrobenioid.degree (y₁ * y₂) =
      B.globalFrobenioid.degree y₁ * B.globalFrobenioid.degree y₂ :=
  B.globalFrobenioid.degree_mul y₁ y₂

theorem local_realification_mul (x₁ x₂ : X) :
    B.localFrobenioid.realification (x₁ * x₂) =
      B.localFrobenioid.realification x₁ +
        B.localFrobenioid.realification x₂ :=
  B.localFrobenioid.realification_mul_at x₁ x₂

theorem global_realification_mul (y₁ y₂ : Y) :
    B.globalFrobenioid.realification (y₁ * y₂) =
      B.globalFrobenioid.realification y₁ +
        B.globalFrobenioid.realification y₂ :=
  B.globalFrobenioid.realification_mul_at y₁ y₂

theorem local_transport_degree (x : X) :
    B.localFrobenioid.degree (B.localFrobenioid.transport x) =
      B.localFrobenioid.degree x :=
  B.localFrobenioid.transport_degree_at x

theorem global_transport_degree (y : Y) :
    B.globalFrobenioid.degree (B.globalFrobenioid.transport y) =
      B.globalFrobenioid.degree y :=
  B.globalFrobenioid.transport_degree_at y

theorem local_transport_realification (x : X) :
    B.localFrobenioid.realification
        (B.localFrobenioid.transport x) =
      B.localFrobenioid.realification x := by
  exact (B.localFrobenioid.degree_realification _).symm.trans
    (B.localFrobenioid.realification_transport x)

theorem global_transport_realification (y : Y) :
    B.globalFrobenioid.realification
        (B.globalFrobenioid.transport y) =
      B.globalFrobenioid.realification y := by
  exact (B.globalFrobenioid.degree_realification _).symm.trans
    (B.globalFrobenioid.realification_transport y)

theorem comparison_local_at (c : Choice) :
    B.comparison.localMap c = R.evaluation.evaluation.localMap c := by
  exact congrFun B.comparison_local c

theorem comparison_global_at (c : Choice) :
    B.comparison.globalMap c = R.evaluation.evaluation.globalMap c := by
  exact congrFun B.comparison_global c

theorem comparison_lower_at (c : Choice) :
    B.comparison.lower c = R.evaluation.evaluation.localComp c := by
  exact congrFun B.comparison_lower c

theorem comparison_upper_at (c : Choice) :
    B.comparison.upper c = R.evaluation.evaluation.globalComp c := by
  exact congrFun B.comparison_upper c

theorem comparison_square (c : Choice) :
    B.comparison.localMap c =
      B.comparison.upper (B.comparison.localMap (B.comparison.lower c)) :=
  B.comparison.square_at c

theorem comparison_local_global (c : Choice) :
    B.comparison.localMap c = B.comparison.globalMap c :=
  B.comparison.local_eq_global c

theorem comparison_labelled_bijective :
    Function.Bijective B.comparison.labelledMap :=
  B.comparison.labelled_bijective

theorem comparison_labelled_left (c : Choice) :
    B.comparison.labelledInverse (B.comparison.labelledMap c) = c :=
  B.comparison.labelled_left c

theorem comparison_labelled_right (c : Choice) :
    B.comparison.labelledMap (B.comparison.labelledInverse c) = c :=
  B.comparison.labelled_right c

theorem upperSemi_recovered : B.upperSemi = K.vertical :=
  B.upperSemi_eq_k1

theorem upperSemi_upper (m : Nat) (z : Real)
    (hz : z ∈ B.upperSemi.image m) :
    ∃ w, w ∈ B.upperSemi.image (m + 1) ∧ z ≤ w := by
  rw [B.upperSemi_eq_k1] at hz ⊢
  exact K.vertical_monotone m (m + 1) (Nat.le_succ m) z hz

theorem upperSemi_upper_chain (m n : Nat) (z : Real)
    (hz : z ∈ B.upperSemi.image m) (h : m ≤ n) :
    ∃ w, w ∈ B.upperSemi.image n ∧ z ≤ w := by
  rw [B.upperSemi_eq_k1] at hz ⊢
  exact K.vertical_monotone m n h z hz

theorem k1_nonarchimedean_upper (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage c) :
    ∃ w, w ∈ R.packet.possibleImage (R.procession.ind3 m c) ∧ z ≤ w := by
  exact K.nonarchimedean_upper m c z hz

theorem k1_archimedean_upper (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage (R.procession.ind3 m c)) :
    ∃ w, w ∈ R.packet.possibleImage c ∧ z ≤ w := by
  exact K.archimedean_target_lift m c z hz

end K2FrobenioidBoundary

/-! A small constructor keeps the source input dependencies visible. -/

def k2FromFields
    (R : SourceTheorem311Realization l Label Choice)
    (K : K1VerticalBoundary R.procession R.packet)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (localFrobenioid : SourceProposition37Frobenioid X)
    (globalFrobenioid : SourceProposition37Frobenioid Y)
    (modMap : X → Y) (MODMap : Y → X)
    (mod_degree : ∀ x, globalFrobenioid.degree (modMap x) =
      localFrobenioid.degree x)
    (MOD_degree : ∀ y, localFrobenioid.degree (MODMap y) =
      globalFrobenioid.degree y)
    (mod_realification : ∀ x,
      globalFrobenioid.realification (modMap x) =
        localFrobenioid.realification x)
    (MOD_realification : ∀ y,
      localFrobenioid.realification (MODMap y) =
        globalFrobenioid.realification y)
    (mod_transport : ∀ x,
      modMap (localFrobenioid.transport x) =
        globalFrobenioid.transport (modMap x))
    (MOD_transport : ∀ y,
      MODMap (globalFrobenioid.transport y) =
        localFrobenioid.transport (MODMap y))
    (comparison : SourceProposition310Comparison Choice Choice)
    (comparison_local : comparison.localMap =
      R.evaluation.evaluation.localMap)
    (comparison_global : comparison.globalMap =
      R.evaluation.evaluation.globalMap)
    (comparison_lower : comparison.lower =
      R.evaluation.evaluation.localComp)
    (comparison_upper : comparison.upper =
      R.evaluation.evaluation.globalComp)
    (upperSemi : UpperSemiCorrespondence Nat Real)
    (upperSemi_eq_k1 : upperSemi = K.vertical) :
    K2FrobenioidBoundary R K X Y where
  localFrobenioid := localFrobenioid
  globalFrobenioid := globalFrobenioid
  modMap := modMap
  MODMap := MODMap
  mod_degree := mod_degree
  MOD_degree := MOD_degree
  mod_realification := mod_realification
  MOD_realification := MOD_realification
  mod_transport := mod_transport
  MOD_transport := MOD_transport
  comparison := comparison
  comparison_local := comparison_local
  comparison_global := comparison_global
  comparison_lower := comparison_lower
  comparison_upper := comparison_upper
  upperSemi := upperSemi
  upperSemi_eq_k1 := upperSemi_eq_k1

theorem k2FromFields_local
    (R : SourceTheorem311Realization l Label Choice)
    (K : K1VerticalBoundary R.procession R.packet)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (localFrobenioid : SourceProposition37Frobenioid X)
    (globalFrobenioid : SourceProposition37Frobenioid Y)
    (modMap : X → Y) (MODMap : Y → X)
    (mod_degree : ∀ x, globalFrobenioid.degree (modMap x) =
      localFrobenioid.degree x)
    (MOD_degree : ∀ y, localFrobenioid.degree (MODMap y) =
      globalFrobenioid.degree y)
    (mod_realification : ∀ x, globalFrobenioid.realification (modMap x) =
      localFrobenioid.realification x)
    (MOD_realification : ∀ y, localFrobenioid.realification (MODMap y) =
      globalFrobenioid.realification y)
    (mod_transport : ∀ x, modMap (localFrobenioid.transport x) =
      globalFrobenioid.transport (modMap x))
    (MOD_transport : ∀ y, MODMap (globalFrobenioid.transport y) =
      localFrobenioid.transport (MODMap y))
    (comparison : SourceProposition310Comparison Choice Choice)
    (comparison_local : comparison.localMap = R.evaluation.evaluation.localMap)
    (comparison_global : comparison.globalMap = R.evaluation.evaluation.globalMap)
    (comparison_lower : comparison.lower = R.evaluation.evaluation.localComp)
    (comparison_upper : comparison.upper = R.evaluation.evaluation.globalComp)
    (upperSemi : UpperSemiCorrespondence Nat Real)
    (upperSemi_eq_k1 : upperSemi = K.vertical) :
    (k2FromFields R K localFrobenioid globalFrobenioid modMap MODMap
      mod_degree MOD_degree mod_realification MOD_realification mod_transport
      MOD_transport comparison comparison_local comparison_global comparison_lower
      comparison_upper upperSemi upperSemi_eq_k1).localFrobenioid =
      localFrobenioid := rfl

/-! Completed source-gate markers.  `True` is only a machine-readable marker;
    the records above remain conditional on their explicit source fields. -/

theorem k1_boundary_status : True := by trivial

theorem k2_boundary_status : True := by trivial

end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def theorem311K1VerticalBoundary : Obligation :=
  { id := "IUT-III.K1.vertical-log-kummer-boundary"
    source := "IUT II, Definition 4.9; IUT III, Proposition 3.5 and Theorem 3.11(ii)"
    status := VerificationStatus.interface
    note :=
      "K1 exposes the real vertical carrier, labelled Kummer maps, " ++
        "nonarchimedean inclusion, archimedean target-to-source lift, and " ++
        "upper-semi transport from an explicit SourceVerticalRealization. " ++
        "The actual local/global log-shell and Frobenioid construction is " ++
        "still an explicit source obligation."
    dependsOn := [ "IUT-II.vertical-log-kummer",
      "IUT-III.source-procession-boundary" ] }

def theorem311K2FrobenioidBoundary : Obligation :=
  { id := "IUT-III.K2.frobenioid-mod-realification-boundary"
    source := "IUT II, Definition 4.9; IUT III, Propositions 3.7, 3.10"
    status := VerificationStatus.interface
    note :=
      "K2 keeps local/global Frobenioids, MOD/mod maps, degree and " ++
        "realification transport, comparison squares, and the upper-semi " ++
        "direction as explicit fields. No inverse law or source existence is " ++
        "inferred from the names of MOD/mod."
    dependsOn := [ "IUT-III.K1.vertical-log-kummer-boundary",
      "IUT-III.source-theorem311-dependency-chain" ] }

end LeanFormal.IUT.Audit
