import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2Construction
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # The completion-to-K1/K2 dependency ledger

  `SourceTheorem311Completion` is the first package which has already
  supplied the IUT I--II prerequisites needed by the realization lift.  The
  opening `OriginalInput` is deliberately not used here: this file records
  the later arrow after the source constructions have been supplied.  The
  purpose is to make the arrow itself explicit and reusable, rather than
  letting a later theorem rely on a convenient coercion or on a theorem name.

  The four levels recorded here are:

  * the completed source package and its lifted realization;
  * the K1 vertical boundary obtained from that realization;
  * the K2 Frobenioid/comparison boundary supplied over that K1 boundary; and
  * the recovery equations consumed by the theorem-facing assembly.

  No field in this file manufactures a source completion.  In particular,
  the `SourceTheorem311Completion` argument remains an explicit premise and
  the K2 Frobenioid boundary remains an explicit premise.  The statements
  below only prove consequences of those premises, with the source
  directions and upper-semi quantifiers unchanged.

  Source references: IUT III Theorem 3.11 and Propositions 3.5, 3.7, 3.10.
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

/-! The completion boundary is local to this ledger.  It is intentionally a
    record of already supplied source fields, not a constructor from
    `InitialThetaArithmeticData`. -/

structure SourceTheorem311Completion
    (l : PrimeGeFive) (Label : Type u) (Choice : Type v)
  [AddGroup Label] [Preorder Choice] where
  source : SourceDefinition31Data.{u} l
  input : Input.{u, v, w} Label Choice
  realization : SourceTheorem311Realization.{u, v, w} l Label Choice
  procession : SourceLGPProcession.{u, v} l Label Choice
  packet : SourcePacketRealization.{u, v, w} realization.procession
  vertical : SourceVerticalRealization.{u, v, w}
    realization.procession realization.packet
  evaluation : SourceEvaluationBridge.{u, v, w}
    realization.procession realization.packet realization.vertical
  labelPrime_alignment : input.labelPrime = l
  initial_alignment : HEq input.initial source.toInitialThetaInput
  realization_procession : realization.procession = procession
  realization_packet : realization.packet = packet
  realization_vertical : realization.vertical = vertical
  realization_evaluation : realization.evaluation = evaluation
  qParameter : Choice → Real
  q_nonzero : ∀ c, qParameter c ≠ 0
  q_contracting : ∀ c, ‖qParameter c‖ < 1
  q_naturality : ∀ c d, qParameter c = qParameter d
  scale : Choice → SignedLabel l.value → Real
  scale_naturality : ∀ c d x, scale c x = scale d x
  realization_labelledCount : realization.labelledCount = input.labelledCount
  realization_labelledCount_pos : 0 < realization.labelledCount
  realization_procession_base : realization.procession.base = input.prime.base
  realization_procession_level : ∀ c,
    realization.procession.level c = input.prime.level c
  realization_procession_ind1 : ∀ g c,
    realization.procession.ind1 g c = input.prime.ind1 g c
  realization_procession_ind2 : ∀ g c,
    realization.procession.ind2 g c = input.prime.ind2 g c
  realization_procession_ind3 : ∀ n c,
    realization.procession.ind3 n c = input.prime.ind3 n c
  realization_packet_volume : ∀ c,
    realization.packet.logVolume c = input.packet.logVolume c
  realization_packet_determinant : ∀ c,
    realization.packet.determinant c = input.localPacket.determinant c
  realization_packet_image : ∀ c,
    realization.packet.possibleImage c = input.packet.possibleImage c
  realization_vertical_image : ∀ m S,
    realization.vertical.nonarchimedeanImage m S =
      input.verticalSite.nonarchimedeanImage m S
  realization_archimedean_image : ∀ m S,
    realization.vertical.archimedeanImage m S =
      input.verticalSite.archimedeanImage m S
  realization_family : realization.genericFamily = input.family
  realization_source_definition31 :
    realization.procession.hodge.source = source
  input_initial : HEq realization.input.initial input.initial
  source_selected_nonempty : Nonempty source.selectedPlaces
  source_bad_finite : Fintype source.badPlaces
  source_bad_finite_nonempty : Nonempty (Fintype source.badPlaces)
  source_stable_reduction : ∀ b : source.badPlaces,
    source.reduction.stableReduction b
  source_multiplicative_reduction : ∀ b : source.badPlaces,
    source.reduction.multiplicativeReduction b
  source_split_multiplicative_reduction : ∀ b : source.badPlaces,
    source.reduction.splitMultiplicativeReduction b
  source_q_nonzero : ∀ b : source.badPlaces,
    source.reduction.qParameter b ≠ 0
  source_q_contracting : ∀ b : source.badPlaces,
    ‖source.reduction.qParameter b‖ < 1
  source_torsion_image_contains_SL2 : source.torsion.imageContainsSL2
  source_torsion_six_independent : source.torsion.sixTorsionIndependent
  source_torsion_l_compatible : source.torsion.lTorsionCompatible
  source_cover_surjective :
    Function.Surjective source.orbicurve.coverToPunctured
  source_exact_injective :
    Function.Injective source.orbicurve.exactSequence.injection
  source_exact_surjective :
    Function.Surjective source.orbicurve.exactSequence.projection
  source_sections_bijective :
    Function.Bijective source.sections.sectionMap
  source_cusp_positive : 0 < source.cusp.epsilon
  source_cusp_nonzero : source.cusp.epsilon ≠ 0
  source_reduction_compatibility : source.arithmetic_reduction_compatibility
  source_torsion_compatibility : source.arithmetic_torsion_compatibility
  source_orbicurve_compatibility : source.arithmetic_orbicurve_compatibility
  source_section_compatibility : source.arithmetic_section_compatibility
  source_cusp_compatibility : source.arithmetic_cusp_compatibility

namespace SourceTheorem311Completion

variable {C : SourceTheorem311Completion l Label Choice}
include C

theorem q_norm_positive (c : Choice) :
    0 < ‖C.qParameter c‖ := by
  exact norm_pos_iff.mpr (C.q_nonzero c)

theorem q_norm_interval (c : Choice) :
    ‖C.qParameter c‖ ∈ Set.Ioo (0 : Real) 1 :=
  ⟨C.q_norm_positive c, C.q_contracting c⟩

theorem q_norm_le_one (c : Choice) : ‖C.qParameter c‖ ≤ 1 :=
  le_of_lt (C.q_contracting c)

theorem q_power_nonzero (c : Choice) (n : Nat) :
    C.qParameter c ^ n ≠ 0 :=
  pow_ne_zero n (C.q_nonzero c)

theorem q_power_norm_nonnegative (c : Choice) (n : Nat) :
    0 ≤ ‖C.qParameter c‖ ^ n := by
  positivity

theorem q_square_contracting (c : Choice) :
    ‖C.qParameter c‖ ^ 2 < 1 := by
  exact pow_lt_one₀ (norm_nonneg _) (C.q_contracting c) (by norm_num)

theorem q_cube_contracting (c : Choice) :
    ‖C.qParameter c‖ ^ 3 < 1 := by
  exact pow_lt_one₀ (norm_nonneg _) (C.q_contracting c) (by norm_num)

theorem q_naturality_trans (c d e : Choice) :
    C.qParameter c = C.qParameter e :=
  (C.q_naturality c d).trans (C.q_naturality d e)

theorem q_naturality_refl (c : Choice) :
    C.qParameter c = C.qParameter c := rfl

theorem scale_naturality_trans (c d e : Choice)
    (x : SignedLabel l.value) :
    C.scale c x = C.scale e x :=
  (C.scale_naturality c d x).trans (C.scale_naturality d e x)

theorem scale_naturality_refl (c : Choice) (x : SignedLabel l.value) :
    C.scale c x = C.scale c x := rfl

end SourceTheorem311Completion

/-! ## 1. The typed completion-to-K1/K2 arrow -/

structure SourceCompletionK1K2Wiring
    (C : SourceTheorem311Completion.{u, v, w} l Label Choice)
    (X : Type ux) (Y : Type uy)
    [CommMonoid X] [CommMonoid Y] where
  k1 : K1VerticalBoundary C.realization.procession C.realization.packet
  k1_eq : k1 = k1OfRealization C.realization
  k2 : K2FrobenioidBoundary C.realization k1 X Y

namespace SourceCompletionK1K2Wiring

variable {C : SourceTheorem311Completion.{u, v, w} l Label Choice}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable (W : SourceCompletionK1K2Wiring C X Y)
include W

def completion (W : SourceCompletionK1K2Wiring C X Y) :
    SourceTheorem311Completion.{u, v, w} l Label Choice := C

@[simp] theorem completion_eq : W.completion = C := rfl

def realization (W : SourceCompletionK1K2Wiring C X Y) :
    SourceTheorem311Realization.{u, v, w} l Label Choice :=
  C.realization

@[simp] theorem realization_eq : W.realization = C.realization := rfl

def canonical
    (C : SourceTheorem311Completion.{u, v, w} l Label Choice)
    (B : K2FrobenioidBoundary C.realization
      (k1OfRealization C.realization) X Y) :
    SourceCompletionK1K2Wiring C X Y where
  k1 := k1OfRealization C.realization
  k1_eq := rfl
  k2 := B

theorem canonical_realization
    (C : SourceTheorem311Completion.{u, v, w} l Label Choice)
    (B : K2FrobenioidBoundary C.realization
      (k1OfRealization C.realization) X Y) :
    (canonical C B).realization = C.realization := rfl

theorem canonical_k1
    (C : SourceTheorem311Completion.{u, v, w} l Label Choice)
    (B : K2FrobenioidBoundary C.realization
      (k1OfRealization C.realization) X Y) :
    (canonical C B).k1 = k1OfRealization C.realization := rfl

theorem canonical_k2
    (C : SourceTheorem311Completion.{u, v, w} l Label Choice)
    (B : K2FrobenioidBoundary C.realization
      (k1OfRealization C.realization) X Y) :
    (canonical C B).k2 = B := rfl

theorem realization_recovered :
    W.realization = W.completion.realization :=
  by
    calc
      W.realization = C.realization := W.realization_eq
      _ = W.completion.realization := by rw [W.completion_eq]

theorem k1_recovered :
    W.k1 = k1OfRealization W.realization :=
  W.k1_eq

theorem realization_procession_recovered :
    W.realization.procession = W.completion.realization.procession := by
  cases W.completion_eq
  rfl

theorem realization_packet_recovered :
    W.realization.packet = W.completion.realization.packet := by
  cases W.completion_eq
  rfl

theorem realization_vertical_recovered :
    W.realization.vertical = W.completion.realization.vertical := by
  cases W.completion_eq
  rfl

theorem realization_evaluation_recovered :
    W.realization.evaluation = W.completion.realization.evaluation := by
  cases W.completion_eq
  rfl

theorem k1_procession_recovered :
    W.k1.toSource = W.realization.vertical := by
  rw [W.k1_eq]
  rfl

theorem k1_packet_recovered :
    W.k1.toSource = W.realization.vertical :=
  W.k1_procession_recovered

theorem k2_upperSemi_recovered :
    W.k2.upperSemi = W.k1.vertical :=
  W.k2.upperSemi_eq_k1

theorem k2_upperSemi_realization :
    W.k2.upperSemi = W.realization.vertical.vertical := by
  calc
    W.k2.upperSemi = W.k1.vertical := W.k2_upperSemi_recovered
    _ = W.realization.vertical.vertical := by
      rw [W.k1_eq]
      rfl

theorem completion_to_realization_to_k1_to_k2 :
    W.realization = W.completion.realization ∧
      W.k1 = k1OfRealization W.realization ∧
      W.k2.upperSemi = W.realization.vertical.vertical :=
  ⟨W.realization_recovered, W.k1_recovered, W.k2_upperSemi_realization⟩

end SourceCompletionK1K2Wiring

/-! ## 7. K2 comparison and upper-semi projections -/

namespace SourceCompletionK1K2Wiring

variable {C : SourceTheorem311Completion.{u, v, w} l Label Choice}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable (W : SourceCompletionK1K2Wiring C X Y)
include W

theorem k2_comparison_local (c : Choice) :
    W.k2.comparison.localMap c =
      W.realization.evaluation.evaluation.localMap c := by
  exact W.k2.comparison_local_at c

theorem k2_comparison_global (c : Choice) :
    W.k2.comparison.globalMap c =
      W.realization.evaluation.evaluation.globalMap c := by
  exact W.k2.comparison_global_at c

theorem k2_comparison_lower (c : Choice) :
    W.k2.comparison.lower c =
      W.realization.evaluation.evaluation.localComp c := by
  exact W.k2.comparison_lower_at c

theorem k2_comparison_upper (c : Choice) :
    W.k2.comparison.upper c =
      W.realization.evaluation.evaluation.globalComp c := by
  exact W.k2.comparison_upper_at c

theorem k2_comparison_square (c : Choice) :
    W.k2.comparison.localMap c =
      W.k2.comparison.upper
        (W.k2.comparison.localMap (W.k2.comparison.lower c)) :=
  W.k2.comparison_square c

theorem k2_comparison_local_global (c : Choice) :
    W.k2.comparison.localMap c = W.k2.comparison.globalMap c :=
  W.k2.comparison_local_global c

theorem k2_comparison_labelled_bijective :
    Function.Bijective W.k2.comparison.labelledMap :=
  W.k2.comparison_labelled_bijective

theorem k2_comparison_labelled_left (c : Choice) :
    W.k2.comparison.labelledInverse
        (W.k2.comparison.labelledMap c) = c :=
  W.k2.comparison_labelled_left c

theorem k2_comparison_labelled_right (c : Choice) :
    W.k2.comparison.labelledMap
        (W.k2.comparison.labelledInverse c) = c :=
  W.k2.comparison_labelled_right c

theorem k2_comparison_labelled_injective :
    Function.Injective W.k2.comparison.labelledMap := by
  exact W.k2.comparison_labelled_bijective.injective

theorem k2_comparison_labelled_surjective :
    Function.Surjective W.k2.comparison.labelledMap := by
  exact W.k2.comparison_labelled_bijective.surjective

theorem k2_upperSemi (m : Nat) (z : Real)
    (hz : z ∈ W.k2.upperSemi.image m) :
    ∃ w, w ∈ W.k2.upperSemi.image (m + 1) ∧ z ≤ w := by
  exact W.k2.upperSemi_upper m z hz

theorem k2_upperSemi_chain (m n : Nat) (z : Real)
    (hz : z ∈ W.k2.upperSemi.image m) (h : m ≤ n) :
    ∃ w, w ∈ W.k2.upperSemi.image n ∧ z ≤ w := by
  exact W.k2.upperSemi_upper_chain m n z hz h

theorem k2_upperSemi_boundary_recovered :
    W.k2.upperSemi = W.k1.vertical :=
  W.k2.upperSemi_recovered

theorem k2_upperSemi_realization_vertical :
    W.k2.upperSemi = W.realization.vertical.vertical := by
  exact W.k2_upperSemi_realization

theorem k2_k1_nonarchimedean_upper (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ W.realization.packet.possibleImage c) :
    ∃ w, w ∈ W.realization.packet.possibleImage
      (W.realization.procession.ind3 m c) ∧ z ≤ w := by
  exact W.k2.k1_nonarchimedean_upper m c z hz

theorem k2_k1_archimedean_upper (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ W.realization.packet.possibleImage
      (W.realization.procession.ind3 m c)) :
    ∃ w, w ∈ W.realization.packet.possibleImage c ∧ z ≤ w := by
  exact W.k2.k1_archimedean_upper m c z hz

theorem k2_nonarchimedean_then_archimedean (m : Nat) (c : Choice)
    (z : Real) (hz : z ∈ W.realization.packet.possibleImage c) :
    ∃ y, y ∈ W.realization.packet.possibleImage c ∧ z ≤ y := by
  rcases W.k2_k1_nonarchimedean_upper m c z hz with ⟨w, hw, hzw⟩
  rcases W.k2_k1_archimedean_upper m c w hw with ⟨y, hy, hwy⟩
  exact ⟨y, hy, hzw.trans hwy⟩

theorem k2_upperSemi_image_rewrite (m : Nat) (S : Set Real) :
    W.k2.upperSemi.image m =
      W.k1.vertical.image m := by
  rw [W.k2.upperSemi_recovered]

theorem k2_upperSemi_image_realization (m : Nat) (S : Set Real) :
    W.k2.upperSemi.image m =
      W.realization.vertical.vertical.image m := by
  rw [W.k2_upperSemi_realization_vertical]

theorem k2_upperSemi_chain_from_realization (m n : Nat) (z : Real)
    (hz : z ∈ W.realization.vertical.vertical.image m) (h : m ≤ n) :
    ∃ w, w ∈ W.realization.vertical.vertical.image n ∧ z ≤ w := by
  rw [← W.k2_upperSemi_realization_vertical] at hz ⊢
  exact W.k2.upperSemi_upper_chain m n z hz h

theorem k2_mod_transport_degree (x : X) :
    W.k2.globalFrobenioid.degree
        (W.k2.modMap (W.k2.localFrobenioid.transport x)) =
      W.k2.localFrobenioid.degree x := by
  rw [W.k2.mod_transport_at, W.k2.global_transport_degree,
    W.k2.mod_degree_at]

theorem k2_MOD_transport_degree (y : Y) :
    W.k2.localFrobenioid.degree
        (W.k2.MODMap (W.k2.globalFrobenioid.transport y)) =
      W.k2.globalFrobenioid.degree y := by
  rw [W.k2.MOD_transport_at, W.k2.local_transport_degree,
    W.k2.MOD_degree_at]

theorem k2_mod_transport_realification (x : X) :
    W.k2.globalFrobenioid.realification
        (W.k2.modMap (W.k2.localFrobenioid.transport x)) =
      W.k2.localFrobenioid.realification x := by
  rw [W.k2.mod_transport_at, W.k2.global_transport_realification,
    W.k2.mod_realification_at]

theorem k2_MOD_transport_realification (y : Y) :
    W.k2.localFrobenioid.realification
        (W.k2.MODMap (W.k2.globalFrobenioid.transport y)) =
      W.k2.globalFrobenioid.realification y := by
  rw [W.k2.MOD_transport_at, W.k2.local_transport_realification,
    W.k2.MOD_realification_at]

theorem k2_mod_degree_round_trip (x : X) :
    W.k2.localFrobenioid.degree
        (W.k2.MODMap (W.k2.modMap x)) =
      W.k2.localFrobenioid.degree x := by
  exact (W.k2.MOD_degree_at (W.k2.modMap x)).trans
    (W.k2.mod_degree_at x)

theorem k2_global_degree_round_trip (y : Y) :
    W.k2.globalFrobenioid.degree
        (W.k2.modMap (W.k2.MODMap y)) =
      W.k2.globalFrobenioid.degree y := by
  exact (W.k2.mod_degree_at (W.k2.MODMap y)).trans
    (W.k2.MOD_degree_at y)

theorem k2_mod_realification_round_trip (x : X) :
    W.k2.localFrobenioid.realification
        (W.k2.MODMap (W.k2.modMap x)) =
      W.k2.localFrobenioid.realification x := by
  calc
    W.k2.localFrobenioid.realification
        (W.k2.MODMap (W.k2.modMap x)) =
        W.k2.globalFrobenioid.realification (W.k2.modMap x) :=
      W.k2.MOD_realification_at (W.k2.modMap x)
    _ = W.k2.localFrobenioid.realification x := W.k2.mod_realification_at x

theorem k2_global_realification_round_trip (y : Y) :
    W.k2.globalFrobenioid.realification
        (W.k2.modMap (W.k2.MODMap y)) =
      W.k2.globalFrobenioid.realification y := by
  calc
    W.k2.globalFrobenioid.realification
        (W.k2.modMap (W.k2.MODMap y)) =
        W.k2.localFrobenioid.realification (W.k2.MODMap y) :=
      W.k2.mod_realification_at (W.k2.MODMap y)
    _ = W.k2.globalFrobenioid.realification y := W.k2.MOD_realification_at y

theorem k2_mod_degree_pow (x : X) (n : Nat) :
    W.k2.globalFrobenioid.degree
        (W.k2.modMap (x ^ n)) =
      (W.k2.localFrobenioid.degree x) ^ n := by
  calc
    W.k2.globalFrobenioid.degree (W.k2.modMap (x ^ n)) =
        W.k2.localFrobenioid.degree (x ^ n) := W.k2.mod_degree_at (x ^ n)
    _ = (W.k2.localFrobenioid.degree x) ^ n :=
      W.k2.localFrobenioid.degree_pow x n

theorem k2_MOD_degree_pow (y : Y) (n : Nat) :
    W.k2.localFrobenioid.degree
        (W.k2.MODMap (y ^ n)) =
      (W.k2.globalFrobenioid.degree y) ^ n := by
  calc
    W.k2.localFrobenioid.degree (W.k2.MODMap (y ^ n)) =
        W.k2.globalFrobenioid.degree (y ^ n) := W.k2.MOD_degree_at (y ^ n)
    _ = (W.k2.globalFrobenioid.degree y) ^ n :=
      W.k2.globalFrobenioid.degree_pow y n

theorem k2_mod_realification_pow (x : X) (n : Nat) :
    W.k2.globalFrobenioid.realification
        (W.k2.modMap (x ^ n)) =
      n * W.k2.localFrobenioid.realification x := by
  calc
    W.k2.globalFrobenioid.realification (W.k2.modMap (x ^ n)) =
        W.k2.localFrobenioid.realification (x ^ n) :=
      W.k2.mod_realification_at (x ^ n)
    _ = n * W.k2.localFrobenioid.realification x :=
      W.k2.localFrobenioid.realification_pow x n

theorem k2_MOD_realification_pow (y : Y) (n : Nat) :
    W.k2.localFrobenioid.realification
        (W.k2.MODMap (y ^ n)) =
      n * W.k2.globalFrobenioid.realification y := by
  calc
    W.k2.localFrobenioid.realification (W.k2.MODMap (y ^ n)) =
        W.k2.globalFrobenioid.realification (y ^ n) :=
      W.k2.MOD_realification_at (y ^ n)
    _ = n * W.k2.globalFrobenioid.realification y :=
      W.k2.globalFrobenioid.realification_pow y n

end SourceCompletionK1K2Wiring

/-! ## 5. K1 projections and direction-preserving transport -/

namespace SourceCompletionK1K2Wiring

variable {C : SourceTheorem311Completion.{u, v, w} l Label Choice}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable (W : SourceCompletionK1K2Wiring C X Y)
include W

theorem k1_toSource_vertical :
    W.k1.toSource.vertical = W.k1.vertical := rfl

theorem k1_toSource_nonarchimedeanImage (m : Nat) (S : Set Real) :
    W.k1.toSource.nonarchimedeanImage m S =
      W.k1.nonarchimedeanImage m S := rfl

theorem k1_toSource_archimedeanImage (m : Nat) (S : Set Real) :
    W.k1.toSource.archimedeanImage m S =
      W.k1.archimedeanImage m S := rfl

theorem k1_toSource_kummer (c : Choice) :
    W.k1.toSource.kummer c = W.k1.labelledKummer c := rfl

theorem k1_correspondence_log (m : Nat) (c : Choice) :
    W.k1.correspondence.log m c =
      W.realization.procession.ind3 m c := by
  exact W.k1.correspondence_log m c

theorem k1_correspondence_kummer (m : Nat) (c : Choice) :
    W.k1.correspondence.kummer m c =
      W.realization.packet.logVolume c := by
  exact W.k1.correspondence_kummer m c

theorem k1_correspondence_upper (m : Nat) (c : Choice) :
    W.realization.packet.logVolume c ≤
      W.realization.packet.logVolume
        (W.realization.procession.ind3 m c) := by
  exact W.k1.correspondence_upper m c

theorem k1_transport_zero (c : Choice) :
    W.k1.correspondence.transport 0 0 c = c := by
  exact W.k1.transport_zero c

theorem k1_transport_one (c : Choice) :
    W.k1.correspondence.transport 0 1 c =
      W.realization.procession.ind3 0 c := by
  exact W.k1.transport_one c

theorem k1_transport_two (c : Choice) :
    W.k1.correspondence.transport 0 2 c =
      W.realization.procession.ind3 1
        (W.realization.procession.ind3 0 c) := by
  exact W.k1.transport_two c

theorem k1_kummer_le_transport (c : Choice) (n : Nat) :
    W.k1.correspondence.kummer n c ≤
      W.k1.correspondence.kummer n
        (W.k1.correspondence.transport 0 n c) := by
  exact W.k1.kummer_le_transport c n

theorem k1_kummer_le_ind3 (c : Choice) (n : Nat) :
    W.realization.packet.logVolume c ≤
      W.realization.packet.logVolume
        (W.realization.procession.ind3 n c) := by
  exact W.k1.kummer_le_ind3 c n

theorem k1_nonarchimedean_inclusion (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ W.realization.packet.possibleImage c) :
    z ∈ W.k1.nonarchimedeanImage m
      (W.realization.packet.possibleImage c) := by
  exact W.k1.nonarchimedean_inclusion_at m c z hz

theorem k1_archimedean_surjection (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ W.k1.archimedeanImage m
      (W.realization.packet.possibleImage c)) :
    ∃ y, y ∈ W.realization.packet.possibleImage c ∧ z ≤ y := by
  exact W.k1.archimedean_surjection_at m c z hz

theorem k1_nonarchimedean_profile (m : Nat) (c : Choice) :
    W.k1.nonarchimedeanImage m
        (W.realization.packet.possibleImage c) =
      W.realization.packet.possibleImage
        (W.realization.procession.ind3 m c) := by
  exact W.k1.nonarchimedean_profile_at m c

theorem k1_archimedean_profile (m : Nat) (c : Choice) :
    W.k1.archimedeanImage m
        (W.realization.packet.possibleImage c) =
      W.realization.packet.possibleImage
        (W.realization.procession.ind3 m c) := by
  exact W.k1.archimedean_profile_at m c

theorem k1_nonarchimedean_target_mem (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ W.realization.packet.possibleImage c) :
    z ∈ W.realization.packet.possibleImage
      (W.realization.procession.ind3 m c) := by
  exact W.k1.nonarchimedean_target_mem m c z hz

theorem k1_nonarchimedean_upper (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ W.realization.packet.possibleImage c) :
    ∃ y, y ∈ W.realization.packet.possibleImage
      (W.realization.procession.ind3 m c) ∧ z ≤ y := by
  exact W.k1.nonarchimedean_upper m c z hz

theorem k1_archimedean_target_lift (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ W.realization.packet.possibleImage
      (W.realization.procession.ind3 m c)) :
    ∃ y, y ∈ W.realization.packet.possibleImage c ∧ z ≤ y := by
  exact W.k1.archimedean_target_lift m c z hz

theorem k1_nonarchimedean_subset (m : Nat) (c : Choice) :
    W.realization.packet.possibleImage c ⊆
      W.k1.nonarchimedeanImage m
        (W.realization.packet.possibleImage c) := by
  intro z hz
  exact W.k1.nonarchimedean_inclusion_at m c z hz

theorem k1_archimedean_target_dominates (m : Nat) (c : Choice) :
    ∀ z ∈ W.k1.archimedeanImage m
      (W.realization.packet.possibleImage c),
      ∃ y, y ∈ W.realization.packet.possibleImage c ∧ z ≤ y := by
  intro z hz
  exact W.k1.archimedean_surjection_at m c z hz

theorem k1_vertical_image_nonempty (m : Nat) (c : Choice) :
    (W.realization.packet.possibleImage
      (W.realization.procession.ind3 m c)).Nonempty := by
  exact W.k1.vertical_image_nonempty m c

theorem k1_vertical_monotone (m n : Nat) (h : m ≤ n)
    (z : Real) (hz : z ∈ W.k1.vertical.image m) :
    ∃ w, w ∈ W.k1.vertical.image n ∧ z ≤ w := by
  exact W.k1.vertical_monotone_at m n h z hz

theorem k1_labelled_left (c a : Choice) :
    (W.k1.labelledKummer c).inverse
        ((W.k1.labelledKummer c).map a) = a :=
  W.k1.labelled_left c a

theorem k1_labelled_right (c b : Choice) :
    (W.k1.labelledKummer c).map
        ((W.k1.labelledKummer c).inverse b) = b :=
  W.k1.labelled_right c b

theorem k1_labelled_injective (c : Choice) :
    Function.Injective (W.k1.labelledKummer c).map :=
  W.k1.labelled_injective c

theorem k1_labelled_surjective (c : Choice) :
    Function.Surjective (W.k1.labelledKummer c).map :=
  W.k1.labelled_surjective c

theorem k1_labelled_bijective (c : Choice) :
    Function.Bijective (W.k1.labelledKummer c).map :=
  W.k1.labelled_bijective c

theorem k1_labelled_map_eq_iff (c a b : Choice) :
    (W.k1.labelledKummer c).map a =
        (W.k1.labelledKummer c).map b ↔ a = b := by
  exact W.k1.labelled_map_eq_iff c a b

theorem k1_labelled_inverse_eq_iff (c a b : Choice) :
    (W.k1.labelledKummer c).inverse a =
        (W.k1.labelledKummer c).inverse b ↔ a = b := by
  exact W.k1.labelled_inverse_eq_iff c a b

theorem k1_labelled_label_transport (c a : Choice) :
    (W.k1.labelledKummer c).label
        ((W.k1.labelledKummer c).inverse
          ((W.k1.labelledKummer c).map a)) =
      (W.k1.labelledKummer c).label a :=
  W.k1.labelled_label_transport c a

theorem k1_nonarchimedean_then_archimedean (m : Nat) (c : Choice)
    (z : Real) (hz : z ∈ W.realization.packet.possibleImage c) :
    ∃ y, y ∈ W.realization.packet.possibleImage c ∧ z ≤ y := by
  exact W.k1.nonarchimedean_then_archimedean m c z hz

theorem k1_realization_projection :
    W.k1 = k1OfRealization W.realization := W.k1_eq

theorem k1_realization_vertical :
    W.k1.vertical = W.realization.vertical.vertical := by
  rw [W.k1_eq]
  rfl

theorem k1_realization_nonarchimedeanImage (m : Nat) (S : Set Real) :
    W.k1.nonarchimedeanImage m S =
      W.realization.vertical.nonarchimedeanImage m S := by
  rw [W.k1_eq]
  rfl

theorem k1_realization_archimedeanImage (m : Nat) (S : Set Real) :
    W.k1.archimedeanImage m S =
      W.realization.vertical.archimedeanImage m S := by
  rw [W.k1_eq]
  rfl

theorem k1_realization_labelledKummer (c : Choice) :
    W.k1.labelledKummer c = W.realization.vertical.kummer c := by
  rw [W.k1_eq]
  rfl

theorem k1_realization_upper_chain (m n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ W.realization.packet.possibleImage c) :
    ∃ y, y ∈ W.realization.packet.possibleImage
      (W.realization.procession.ind3 n
        (W.realization.procession.ind3 m c)) ∧ z ≤ y := by
  exact Theorem311Source.k1_realization_upper_chain
    (R := W.realization) m n c z hz

theorem k1_realization_upper_chain_three (m n p : Nat) (c : Choice)
    (z : Real) (hz : z ∈ W.realization.packet.possibleImage c) :
    ∃ y, y ∈ W.realization.packet.possibleImage
      (W.realization.procession.ind3 p
        (W.realization.procession.ind3 n
          (W.realization.procession.ind3 m c))) ∧ z ≤ y := by
  rcases W.k1_realization_upper_chain m n c z hz with ⟨y, hy, hzy⟩
  rcases W.k1_nonarchimedean_upper p
      (W.realization.procession.ind3 n
        (W.realization.procession.ind3 m c)) y hy with ⟨z', hz', hyz'⟩
  exact ⟨z', hz', hzy.trans hyz'⟩

theorem k1_realization_profile_both (m : Nat) (c : Choice) :
    W.k1.nonarchimedeanImage m
        (W.realization.packet.possibleImage c) =
      W.realization.packet.possibleImage
        (W.realization.procession.ind3 m c) ∧
    W.k1.archimedeanImage m
        (W.realization.packet.possibleImage c) =
      W.realization.packet.possibleImage
        (W.realization.procession.ind3 m c) :=
  ⟨W.k1_nonarchimedean_profile m c, W.k1_archimedean_profile m c⟩

theorem k1_realization_directions (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ W.realization.packet.possibleImage c) :
    z ∈ W.k1.nonarchimedeanImage m
      (W.realization.packet.possibleImage c) ∧
      ∃ y, y ∈ W.realization.packet.possibleImage
        (W.realization.procession.ind3 m c) ∧ z ≤ y := by
  exact ⟨W.k1_nonarchimedean_inclusion m c z hz,
    W.k1_nonarchimedean_upper m c z hz⟩

end SourceCompletionK1K2Wiring

/-! ## 6. K2 degree, realification, and transport projections -/

namespace SourceCompletionK1K2Wiring

variable {C : SourceTheorem311Completion.{u, v, w} l Label Choice}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable (W : SourceCompletionK1K2Wiring C X Y)
include W

theorem k2_mod_degree (x : X) :
    W.k2.globalFrobenioid.degree (W.k2.modMap x) =
      W.k2.localFrobenioid.degree x :=
  W.k2.mod_degree_at x

theorem k2_MOD_degree (y : Y) :
    W.k2.localFrobenioid.degree (W.k2.MODMap y) =
      W.k2.globalFrobenioid.degree y :=
  W.k2.MOD_degree_at y

theorem k2_mod_realification (x : X) :
    W.k2.globalFrobenioid.realification (W.k2.modMap x) =
      W.k2.localFrobenioid.realification x :=
  W.k2.mod_realification_at x

theorem k2_MOD_realification (y : Y) :
    W.k2.localFrobenioid.realification (W.k2.MODMap y) =
      W.k2.globalFrobenioid.realification y :=
  W.k2.MOD_realification_at y

theorem k2_mod_degree_real (x : X) :
    (W.k2.globalFrobenioid.degree (W.k2.modMap x) : Real) =
      (W.k2.localFrobenioid.degree x : Real) :=
  W.k2.mod_degree_real x

theorem k2_MOD_degree_real (y : Y) :
    (W.k2.localFrobenioid.degree (W.k2.MODMap y) : Real) =
      (W.k2.globalFrobenioid.degree y : Real) :=
  W.k2.MOD_degree_real y

theorem k2_mod_realification_degree (x : X) :
    (W.k2.globalFrobenioid.degree (W.k2.modMap x) : Real) =
      W.k2.localFrobenioid.realification x :=
  W.k2.mod_realification_degree x

theorem k2_MOD_realification_degree (y : Y) :
    (W.k2.localFrobenioid.degree (W.k2.MODMap y) : Real) =
      W.k2.globalFrobenioid.realification y :=
  W.k2.MOD_realification_degree y

theorem k2_mod_transport (x : X) :
    W.k2.modMap (W.k2.localFrobenioid.transport x) =
      W.k2.globalFrobenioid.transport (W.k2.modMap x) :=
  W.k2.mod_transport_at x

theorem k2_MOD_transport (y : Y) :
    W.k2.MODMap (W.k2.globalFrobenioid.transport y) =
      W.k2.localFrobenioid.transport (W.k2.MODMap y) :=
  W.k2.MOD_transport_at y

theorem k2_local_degree_mul (x₁ x₂ : X) :
    W.k2.localFrobenioid.degree (x₁ * x₂) =
      W.k2.localFrobenioid.degree x₁ *
        W.k2.localFrobenioid.degree x₂ :=
  W.k2.local_degree_mul x₁ x₂

theorem k2_global_degree_mul (y₁ y₂ : Y) :
    W.k2.globalFrobenioid.degree (y₁ * y₂) =
      W.k2.globalFrobenioid.degree y₁ *
        W.k2.globalFrobenioid.degree y₂ :=
  W.k2.global_degree_mul y₁ y₂

theorem k2_local_realification_mul (x₁ x₂ : X) :
    W.k2.localFrobenioid.realification (x₁ * x₂) =
      W.k2.localFrobenioid.realification x₁ +
        W.k2.localFrobenioid.realification x₂ :=
  W.k2.local_realification_mul x₁ x₂

theorem k2_global_realification_mul (y₁ y₂ : Y) :
    W.k2.globalFrobenioid.realification (y₁ * y₂) =
      W.k2.globalFrobenioid.realification y₁ +
        W.k2.globalFrobenioid.realification y₂ :=
  W.k2.global_realification_mul y₁ y₂

theorem k2_local_transport_degree (x : X) :
    W.k2.localFrobenioid.degree
        (W.k2.localFrobenioid.transport x) =
      W.k2.localFrobenioid.degree x :=
  W.k2.local_transport_degree x

theorem k2_global_transport_degree (y : Y) :
    W.k2.globalFrobenioid.degree
        (W.k2.globalFrobenioid.transport y) =
      W.k2.globalFrobenioid.degree y :=
  W.k2.global_transport_degree y

theorem k2_local_transport_realification (x : X) :
    W.k2.localFrobenioid.realification
        (W.k2.localFrobenioid.transport x) =
      W.k2.localFrobenioid.realification x :=
  W.k2.local_transport_realification x

theorem k2_global_transport_realification (y : Y) :
    W.k2.globalFrobenioid.realification
        (W.k2.globalFrobenioid.transport y) =
      W.k2.globalFrobenioid.realification y :=
  W.k2.global_transport_realification y

theorem k2_local_degree_pow (x : X) (n : Nat) :
    W.k2.localFrobenioid.degree (x ^ n) =
      (W.k2.localFrobenioid.degree x) ^ n :=
  W.k2.localFrobenioid.degree_pow x n

theorem k2_global_degree_pow (y : Y) (n : Nat) :
    W.k2.globalFrobenioid.degree (y ^ n) =
      (W.k2.globalFrobenioid.degree y) ^ n :=
  W.k2.globalFrobenioid.degree_pow y n

theorem k2_local_realification_pow (x : X) (n : Nat) :
    W.k2.localFrobenioid.realification (x ^ n) =
      n * W.k2.localFrobenioid.realification x :=
  W.k2.localFrobenioid.realification_pow x n

theorem k2_global_realification_pow (y : Y) (n : Nat) :
    W.k2.globalFrobenioid.realification (y ^ n) =
      n * W.k2.globalFrobenioid.realification y :=
  W.k2.globalFrobenioid.realification_pow y n

theorem k2_local_degree_one :
    W.k2.localFrobenioid.degree 1 = 1 :=
  W.k2.localFrobenioid.degree_one

theorem k2_global_degree_one :
    W.k2.globalFrobenioid.degree 1 = 1 :=
  W.k2.globalFrobenioid.degree_one

theorem k2_local_realification_one :
    W.k2.localFrobenioid.realification 1 = 0 :=
  W.k2.localFrobenioid.realification_one

theorem k2_global_realification_one :
    W.k2.globalFrobenioid.realification 1 = 0 :=
  W.k2.globalFrobenioid.realification_one

theorem k2_local_transport_twice_degree (x : X) :
    W.k2.localFrobenioid.degree
        (W.k2.localFrobenioid.transport
          (W.k2.localFrobenioid.transport x)) =
      W.k2.localFrobenioid.degree x := by
  exact W.k2.localFrobenioid.transport_twice_degree x

theorem k2_global_transport_twice_degree (y : Y) :
    W.k2.globalFrobenioid.degree
        (W.k2.globalFrobenioid.transport
          (W.k2.globalFrobenioid.transport y)) =
      W.k2.globalFrobenioid.degree y := by
  exact W.k2.globalFrobenioid.transport_twice_degree y

theorem k2_local_transport_pow_degree (x : X) (n : Nat) :
    W.k2.localFrobenioid.degree
        ((W.k2.localFrobenioid.transport x) ^ n) =
      (W.k2.localFrobenioid.degree x) ^ n := by
  exact W.k2.localFrobenioid.transport_pow_degree x n

theorem k2_global_transport_pow_degree (y : Y) (n : Nat) :
    W.k2.globalFrobenioid.degree
        ((W.k2.globalFrobenioid.transport y) ^ n) =
      (W.k2.globalFrobenioid.degree y) ^ n := by
  exact W.k2.globalFrobenioid.transport_pow_degree y n

theorem k2_local_transport_pow_realification (x : X) (n : Nat) :
    W.k2.localFrobenioid.realification
        ((W.k2.localFrobenioid.transport x) ^ n) =
      n * W.k2.localFrobenioid.realification x := by
  exact W.k2.localFrobenioid.realification_transport_pow x n

theorem k2_global_transport_pow_realification (y : Y) (n : Nat) :
    W.k2.globalFrobenioid.realification
        ((W.k2.globalFrobenioid.transport y) ^ n) =
      n * W.k2.globalFrobenioid.realification y := by
  exact W.k2.globalFrobenioid.realification_transport_pow y n

theorem k2_mod_degree_realification (x : X) :
    (W.k2.globalFrobenioid.degree (W.k2.modMap x) : Real) =
      W.k2.localFrobenioid.realification x :=
  W.k2.mod_realification_degree x

theorem k2_MOD_degree_realification (y : Y) :
    (W.k2.localFrobenioid.degree (W.k2.MODMap y) : Real) =
      W.k2.globalFrobenioid.realification y :=
  W.k2.MOD_realification_degree y

end SourceCompletionK1K2Wiring

/-! ## 2. A machine-readable arrow ledger -/

structure SourceCompletionK1K2ArrowLedger
    {C : SourceTheorem311Completion.{u, v, w} l Label Choice}
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (W : SourceCompletionK1K2Wiring.{u, v, w, ux, uy} C X Y) where
  completion_realization :
    W.realization = W.completion.realization
  realization_k1 :
    W.k1 = k1OfRealization W.realization
  k1_k2_upperSemi :
    W.k2.upperSemi = W.k1.vertical
  k2_realization_upperSemi :
    W.k2.upperSemi = W.realization.vertical.vertical
  source_recovery :
    W.realization.procession.hodge.source = W.completion.source
  input_initial_recovery :
    HEq W.realization.input.initial W.completion.input.initial

namespace SourceCompletionK1K2ArrowLedger

variable {C : SourceTheorem311Completion.{u, v, w} l Label Choice}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable {W : SourceCompletionK1K2Wiring.{u, v, w, ux, uy} C X Y}

theorem assemble (W : SourceCompletionK1K2Wiring C X Y) :
    SourceCompletionK1K2ArrowLedger W where
  completion_realization := W.realization_recovered
  realization_k1 := W.k1_eq
  k1_k2_upperSemi := W.k2.upperSemi_eq_k1
  k2_realization_upperSemi := by
    calc
      W.k2.upperSemi = W.k1.vertical := W.k2.upperSemi_eq_k1
      _ = W.realization.vertical.vertical := by
        rw [W.k1_eq]
        rfl
  source_recovery := by
    cases W.completion_eq
    exact W.completion.realization_source_definition31
  input_initial_recovery := by
    cases W.completion_eq
    exact W.completion.input_initial

theorem canonical
    (C : SourceTheorem311Completion.{u, v, w} l Label Choice)
    (B : K2FrobenioidBoundary C.realization
      (k1OfRealization C.realization) X Y) :
    SourceCompletionK1K2ArrowLedger (SourceCompletionK1K2Wiring.canonical C B) :=
  assemble (SourceCompletionK1K2Wiring.canonical C B)

theorem completion_realization_eq (L : SourceCompletionK1K2ArrowLedger W) :
    W.realization = W.completion.realization :=
  L.completion_realization

theorem realization_k1_eq (L : SourceCompletionK1K2ArrowLedger W) :
    W.k1 = k1OfRealization W.realization :=
  L.realization_k1

theorem k1_k2_upperSemi_eq (L : SourceCompletionK1K2ArrowLedger W) :
    W.k2.upperSemi = W.k1.vertical :=
  L.k1_k2_upperSemi

theorem k2_realization_upperSemi_eq (L : SourceCompletionK1K2ArrowLedger W) :
    W.k2.upperSemi = W.realization.vertical.vertical :=
  L.k2_realization_upperSemi

theorem source_recovery_eq (L : SourceCompletionK1K2ArrowLedger W) :
    W.realization.procession.hodge.source = W.completion.source :=
  L.source_recovery

theorem input_initial_recovery_heq (L : SourceCompletionK1K2ArrowLedger W) :
    HEq W.realization.input.initial W.completion.input.initial :=
  L.input_initial_recovery

theorem closed (L : SourceCompletionK1K2ArrowLedger W) :
    W.realization = W.completion.realization ∧
      W.k1 = k1OfRealization W.realization ∧
      W.k2.upperSemi = W.realization.vertical.vertical :=
  ⟨L.completion_realization, L.realization_k1,
    L.k2_realization_upperSemi⟩

end SourceCompletionK1K2ArrowLedger

/-! ## 3. Completion-level source projections -/

namespace SourceCompletionK1K2Wiring

variable {C : SourceTheorem311Completion.{u, v, w} l Label Choice}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable (W : SourceCompletionK1K2Wiring C X Y)
include W

theorem source_eq :
    W.realization.procession.hodge.source = W.completion.source := by
  cases W.completion_eq
  exact W.completion.realization_source_definition31

theorem source_initial_alignment :
    HEq W.completion.input.initial W.completion.source.toInitialThetaInput :=
  W.completion.initial_alignment

theorem source_initial_alignment_symm :
    HEq W.completion.source.toInitialThetaInput W.completion.input.initial :=
  W.completion.initial_alignment.symm

theorem labelPrime_eq : W.completion.input.labelPrime = l :=
  W.completion.labelPrime_alignment

theorem q_nonzero (c : Choice) : W.completion.qParameter c ≠ 0 :=
  W.completion.q_nonzero c

theorem q_contracting (c : Choice) :
    ‖W.completion.qParameter c‖ < 1 :=
  W.completion.q_contracting c

theorem q_natural (c d : Choice) :
    W.completion.qParameter c = W.completion.qParameter d :=
  W.completion.q_naturality c d

theorem q_norm_positive (c : Choice) :
    0 < ‖W.completion.qParameter c‖ :=
  W.completion.q_norm_positive c

theorem q_norm_interval (c : Choice) :
    ‖W.completion.qParameter c‖ ∈ Set.Ioo (0 : Real) 1 :=
  W.completion.q_norm_interval c

theorem q_norm_le_one (c : Choice) :
    ‖W.completion.qParameter c‖ ≤ 1 :=
  W.completion.q_norm_le_one c

theorem q_power_nonzero (c : Choice) (n : Nat) :
    W.completion.qParameter c ^ n ≠ 0 :=
  W.completion.q_power_nonzero c n

theorem q_power_norm_nonnegative (c : Choice) (n : Nat) :
    0 ≤ ‖W.completion.qParameter c‖ ^ n :=
  W.completion.q_power_norm_nonnegative c n

theorem q_square_contracting (c : Choice) :
    ‖W.completion.qParameter c‖ ^ 2 < 1 :=
  W.completion.q_square_contracting c

theorem q_cube_contracting (c : Choice) :
    ‖W.completion.qParameter c‖ ^ 3 < 1 :=
  W.completion.q_cube_contracting c

theorem q_natural_trans (c d e : Choice) :
    W.completion.qParameter c = W.completion.qParameter e :=
  W.completion.q_naturality_trans c d e

theorem q_natural_refl (c : Choice) :
    W.completion.qParameter c = W.completion.qParameter c :=
  W.completion.q_naturality_refl c

theorem scale_natural (c d : Choice) (x : SignedLabel l.value) :
    W.completion.scale c x = W.completion.scale d x :=
  W.completion.scale_naturality c d x

theorem scale_natural_trans (c d e : Choice) (x : SignedLabel l.value) :
    W.completion.scale c x = W.completion.scale e x :=
  W.completion.scale_naturality_trans c d e x

theorem scale_natural_refl (c : Choice) (x : SignedLabel l.value) :
    W.completion.scale c x = W.completion.scale c x :=
  W.completion.scale_naturality_refl c x

theorem source_selected_nonempty :
    Nonempty W.completion.source.selectedPlaces :=
  W.completion.source_selected_nonempty

@[reducible] noncomputable def source_bad_finite :
    Fintype W.completion.source.badPlaces :=
  W.completion.source_bad_finite

theorem source_bad_finite_nonempty :
    Nonempty (Fintype W.completion.source.badPlaces) :=
  W.completion.source_bad_finite_nonempty

theorem source_stable_reduction (b : W.completion.source.badPlaces) :
    W.completion.source.reduction.stableReduction b :=
  W.completion.source_stable_reduction b

theorem source_multiplicative_reduction (b : W.completion.source.badPlaces) :
    W.completion.source.reduction.multiplicativeReduction b :=
  W.completion.source_multiplicative_reduction b

theorem source_split_multiplicative_reduction (b : W.completion.source.badPlaces) :
    W.completion.source.reduction.splitMultiplicativeReduction b :=
  W.completion.source_split_multiplicative_reduction b

theorem source_q_nonzero (b : W.completion.source.badPlaces) :
    W.completion.source.reduction.qParameter b ≠ 0 :=
  W.completion.source_q_nonzero b

theorem source_q_contracting (b : W.completion.source.badPlaces) :
    ‖W.completion.source.reduction.qParameter b‖ < 1 :=
  W.completion.source_q_contracting b

theorem source_torsion_image_contains_SL2 :
    W.completion.source.torsion.imageContainsSL2 :=
  W.completion.source_torsion_image_contains_SL2

theorem source_torsion_six_independent :
    W.completion.source.torsion.sixTorsionIndependent :=
  W.completion.source_torsion_six_independent

theorem source_torsion_l_compatible :
    W.completion.source.torsion.lTorsionCompatible :=
  W.completion.source_torsion_l_compatible

theorem source_cover_surjective :
    Function.Surjective W.completion.source.orbicurve.coverToPunctured :=
  W.completion.source_cover_surjective

theorem source_exact_injective :
    Function.Injective W.completion.source.orbicurve.exactSequence.injection :=
  W.completion.source_exact_injective

theorem source_exact_surjective :
    Function.Surjective W.completion.source.orbicurve.exactSequence.projection :=
  W.completion.source_exact_surjective

theorem source_sections_bijective :
    Function.Bijective W.completion.source.sections.sectionMap :=
  W.completion.source_sections_bijective

theorem source_cusp_positive : 0 < W.completion.source.cusp.epsilon :=
  W.completion.source_cusp_positive

theorem source_cusp_nonzero : W.completion.source.cusp.epsilon ≠ 0 :=
  W.completion.source_cusp_nonzero

theorem source_reduction_compatibility :
    W.completion.source.arithmetic_reduction_compatibility :=
  W.completion.source_reduction_compatibility

theorem source_torsion_compatibility :
    W.completion.source.arithmetic_torsion_compatibility :=
  W.completion.source_torsion_compatibility

theorem source_orbicurve_compatibility :
    W.completion.source.arithmetic_orbicurve_compatibility :=
  W.completion.source_orbicurve_compatibility

theorem source_section_compatibility :
    W.completion.source.arithmetic_section_compatibility :=
  W.completion.source_section_compatibility

theorem source_cusp_compatibility :
    W.completion.source.arithmetic_cusp_compatibility :=
  W.completion.source_cusp_compatibility

theorem source_arithmetic_bundle :
    W.completion.source.arithmetic_reduction_compatibility ∧
      W.completion.source.arithmetic_torsion_compatibility ∧
      W.completion.source.arithmetic_orbicurve_compatibility ∧
      W.completion.source.arithmetic_section_compatibility ∧
      W.completion.source.arithmetic_cusp_compatibility := by
  exact ⟨W.source_reduction_compatibility,
    W.source_torsion_compatibility,
    W.source_orbicurve_compatibility,
    W.source_section_compatibility,
    W.source_cusp_compatibility⟩

theorem source_clause_bundle :
    W.completion.source.torsion.imageContainsSL2 ∧
      W.completion.source.torsion.sixTorsionIndependent ∧
      W.completion.source.torsion.lTorsionCompatible ∧
      W.completion.source.cusp.epsilon ≠ 0 := by
  exact ⟨W.source_torsion_image_contains_SL2,
    W.source_torsion_six_independent,
    W.source_torsion_l_compatible,
    W.source_cusp_nonzero⟩

end SourceCompletionK1K2Wiring

/-! ## 4. Realization-level projections -/

namespace SourceCompletionK1K2Wiring

variable {C : SourceTheorem311Completion.{u, v, w} l Label Choice}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable (W : SourceCompletionK1K2Wiring C X Y)
include W

theorem realization_procession :
    W.realization.procession = W.completion.procession := by
  cases W.completion_eq
  exact W.completion.realization_procession

theorem realization_packet :
    W.realization.packet = W.completion.packet := by
  cases W.completion_eq
  exact W.completion.realization_packet

theorem realization_vertical :
    W.realization.vertical = W.completion.vertical := by
  cases W.completion_eq
  exact W.completion.realization_vertical

theorem realization_evaluation :
    W.realization.evaluation = W.completion.evaluation := by
  cases W.completion_eq
  exact W.completion.realization_evaluation

theorem realization_generic_family :
    W.realization.genericFamily = W.completion.input.family := by
  cases W.completion_eq
  exact W.completion.realization_family

theorem realization_labelled_count :
    W.realization.labelledCount = W.completion.input.labelledCount := by
  cases W.completion_eq
  exact W.completion.realization_labelledCount

theorem realization_labelled_count_positive :
    0 < W.realization.labelledCount := by
  cases W.completion_eq
  exact W.completion.realization_labelledCount_pos

theorem procession_base :
    W.realization.procession.base = W.completion.input.prime.base := by
  cases W.completion_eq
  exact W.completion.realization_procession_base

theorem procession_level (c : Choice) :
    W.realization.procession.level c = W.completion.input.prime.level c := by
  cases W.completion_eq
  exact W.completion.realization_procession_level c

theorem procession_ind1 (g : Label) (c : Choice) :
    W.realization.procession.ind1 g c = W.completion.input.prime.ind1 g c := by
  cases W.completion_eq
  exact W.completion.realization_procession_ind1 g c

theorem procession_ind2 (g : Label) (c : Choice) :
    W.realization.procession.ind2 g c = W.completion.input.prime.ind2 g c := by
  cases W.completion_eq
  exact W.completion.realization_procession_ind2 g c

theorem procession_ind3 (n : Nat) (c : Choice) :
    W.realization.procession.ind3 n c = W.completion.input.prime.ind3 n c := by
  cases W.completion_eq
  exact W.completion.realization_procession_ind3 n c

theorem packet_volume (c : Choice) :
    W.realization.packet.logVolume c = W.completion.input.packet.logVolume c := by
  cases W.completion_eq
  exact W.completion.realization_packet_volume c

theorem packet_determinant (c : Choice) :
    W.realization.packet.determinant c =
      W.completion.input.localPacket.determinant c := by
  cases W.completion_eq
  exact W.completion.realization_packet_determinant c

theorem packet_image (c : Choice) :
    W.realization.packet.possibleImage c =
      W.completion.input.packet.possibleImage c := by
  cases W.completion_eq
  exact W.completion.realization_packet_image c

theorem packet_volume_determinant (c : Choice) :
    Real.log (W.realization.packet.determinant c) =
      W.realization.packet.logVolume c := by
  exact W.realization.packet.log_determinant c

theorem packet_determinant_positive (c : Choice) :
    0 < W.realization.packet.determinant c :=
  W.realization.packet.determinant_positive c

theorem packet_determinant_nonzero (c : Choice) :
    W.realization.packet.determinant c ≠ 0 :=
  ne_of_gt (W.packet_determinant_positive c)

theorem packet_ind1_volume (g : Label) (c : Choice) :
    W.realization.packet.logVolume (W.realization.procession.ind1 g c) =
      W.realization.packet.logVolume c :=
  W.realization.packet.ind1_volume g c

theorem packet_ind2_volume (g : Label) (c : Choice) :
    W.realization.packet.logVolume (W.realization.procession.ind2 g c) =
      W.realization.packet.logVolume c :=
  W.realization.packet.ind2_volume g c

theorem packet_ind3_volume (n : Nat) (c : Choice) :
    W.realization.packet.logVolume c ≤
      W.realization.packet.logVolume (W.realization.procession.ind3 n c) :=
  W.realization.packet.ind3_volume n c

theorem packet_ind1_image (g : Label) (c : Choice) :
    W.realization.packet.possibleImage
        (W.realization.procession.ind1 g c) =
      W.realization.packet.possibleImage c :=
  W.realization.packet.image_ind1 g c

theorem packet_ind2_image (g : Label) (c : Choice) :
    W.realization.packet.possibleImage
        (W.realization.procession.ind2 g c) =
      W.realization.packet.possibleImage c :=
  W.realization.packet.image_ind2 g c

theorem packet_ind3_image (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ W.realization.packet.possibleImage c) :
    ∃ y, y ∈ W.realization.packet.possibleImage
      (W.realization.procession.ind3 n c) ∧ z ≤ y :=
  W.realization.packet.image_ind3 n c z hz

theorem vertical_nonarchimedean_image (m : Nat) (S : Set Real) :
    W.realization.vertical.nonarchimedeanImage m S =
      W.completion.input.verticalSite.nonarchimedeanImage m S := by
  cases W.completion_eq
  exact W.completion.realization_vertical_image m S

theorem vertical_archimedean_image (m : Nat) (S : Set Real) :
    W.realization.vertical.archimedeanImage m S =
      W.completion.input.verticalSite.archimedeanImage m S := by
  cases W.completion_eq
  exact W.completion.realization_archimedean_image m S

theorem vertical_nonarchimedean_inclusion (m : Nat) (z : Real)
    (S : Set Real) (hz : z ∈ S) :
    z ∈ W.realization.vertical.nonarchimedeanImage m S :=
  W.realization.vertical.nonarchimedean_inclusion m z S hz

theorem vertical_archimedean_surjection (m : Nat) (z : Real)
    (S : Set Real)
    (hz : z ∈ W.realization.vertical.archimedeanImage m S) :
    ∃ y, y ∈ S ∧ z ≤ y :=
  W.realization.vertical.archimedean_surjection m z S hz

theorem vertical_nonarchimedean_profile (m : Nat) (c : Choice) :
    W.realization.vertical.nonarchimedeanImage m
        (W.realization.packet.possibleImage c) =
      W.realization.packet.possibleImage
        (W.realization.procession.ind3 m c) :=
  W.realization.vertical.nonarchimedean_profile m c

theorem vertical_archimedean_profile (m : Nat) (c : Choice) :
    W.realization.vertical.archimedeanImage m
        (W.realization.packet.possibleImage c) =
      W.realization.packet.possibleImage
        (W.realization.procession.ind3 m c) :=
  W.realization.vertical.archimedean_profile m c

theorem vertical_monotone (m n : Nat) (h : m ≤ n) (z : Real)
    (hz : z ∈ W.realization.vertical.vertical.image m) :
    ∃ w, w ∈ W.realization.vertical.vertical.image n ∧ z ≤ w :=
  W.realization.vertical.vertical_monotone m n h z hz

theorem vertical_nonarchimedean_upper (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ W.realization.packet.possibleImage c) :
    ∃ w, w ∈ W.realization.packet.possibleImage
      (W.realization.procession.ind3 m c) ∧ z ≤ w := by
  exact W.realization.vertical.nonarch_upper m c z hz

theorem vertical_archimedean_target_lift (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ W.realization.packet.possibleImage
      (W.realization.procession.ind3 m c)) :
    ∃ w, w ∈ W.realization.packet.possibleImage c ∧ z ≤ w := by
  exact W.realization.vertical.arch_target_lift m c z hz

theorem vertical_kummer_bijective (c : Choice) :
    Function.Bijective (W.realization.vertical.kummer c).map :=
  W.realization.vertical.kummer_bijective c

theorem vertical_kummer_left (c a : Choice) :
    (W.realization.vertical.kummer c).inverse
        ((W.realization.vertical.kummer c).map a) = a :=
  W.realization.vertical.kummer_left_inverse c a

theorem vertical_kummer_right (c b : Choice) :
    (W.realization.vertical.kummer c).map
        ((W.realization.vertical.kummer c).inverse b) = b :=
  W.realization.vertical.kummer_right_inverse c b

theorem vertical_kummer_label (c a : Choice) :
    (W.realization.vertical.kummer c).label
        ((W.realization.vertical.kummer c).inverse
          ((W.realization.vertical.kummer c).map a)) =
      (W.realization.vertical.kummer c).label a :=
  W.realization.vertical.kummer_label_at c a

theorem evaluation_local_global (c : Choice) :
    W.realization.evaluation.evaluation.localMap c =
      W.realization.evaluation.evaluation.globalMap c :=
  W.realization.evaluation.local_global c

theorem evaluation_local_natural (c : Choice) :
    W.realization.evaluation.evaluation.localMap
        (W.realization.evaluation.evaluation.localComp c) =
      W.realization.evaluation.evaluation.localMap c :=
  W.realization.evaluation.local_comp c

theorem evaluation_global_natural (c : Choice) :
    W.realization.evaluation.evaluation.globalMap
        (W.realization.evaluation.evaluation.globalComp c) =
      W.realization.evaluation.evaluation.globalMap c :=
  W.realization.evaluation.global_comp c

theorem evaluation_horizontal_square (c : Choice) :
    W.realization.evaluation.horizontal.upper
        (W.realization.evaluation.horizontal.left c) =
      W.realization.evaluation.horizontal.right
        (W.realization.evaluation.horizontal.lower c) :=
  W.realization.evaluation.horizontal_square c

theorem evaluation_horizontal_kummer (c : Choice) :
    (W.realization.vertical.kummer c).map
        (W.realization.evaluation.horizontal.left c) =
      W.realization.evaluation.horizontal.right
        ((W.realization.vertical.kummer c).map
          (W.realization.evaluation.horizontal.lower c)) :=
  W.realization.evaluation.horizontal_kummer c

theorem evaluation_horizontal_label (c : Choice) :
    (W.realization.vertical.kummer c).label
        (W.realization.evaluation.horizontal.left c) =
      (W.realization.vertical.kummer c).label
        (W.realization.evaluation.horizontal.lower c) :=
  W.realization.evaluation.horizontal_label c

theorem evaluation_horizontal_evaluation (c : Choice) :
    W.realization.evaluation.evaluation.localMap
        (W.realization.evaluation.horizontal.left c) =
      W.realization.evaluation.horizontal.right
        (W.realization.evaluation.evaluation.localMap
          (W.realization.evaluation.horizontal.lower c)) :=
  W.realization.evaluation.horizontal_evaluation c

theorem generic_family_injective :
    Function.Injective W.realization.genericFamily.theater :=
  W.realization.genericFamily.distinct

theorem generic_family_link_refl (i t : Choice) :
    W.realization.genericFamily.link i i t = t :=
  W.realization.genericFamily.link_refl i t

theorem generic_family_link_trans (i j k t : Choice) :
    W.realization.genericFamily.link j k
        (W.realization.genericFamily.link i j t) =
      W.realization.genericFamily.link i k t :=
  W.realization.genericFamily.link_trans i j k t

theorem generic_family_permutation_natural (i t : Choice) :
    W.realization.genericFamily.link
        (W.realization.genericFamily.permutation i)
        (W.realization.genericFamily.permutation i) t =
      W.realization.genericFamily.link i i t :=
  W.realization.genericFamily.permutation_naturality i t

end SourceCompletionK1K2Wiring

end Theorem311Source

end

end LeanFormal.IUT
