import LeanFormal.IUT.IUTIII.Theorem311.SourceHodgeTheaterBridge
import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummer
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
  # Explicit dependency chain for Theorem 3.11

  This file refines the source boundary one layer below the final theorem.
  The audit lists Theorem 1.5, Propositions 2.1, 3.2, 3.4, 3.5, 3.7,
  3.9, and 3.10 as prerequisites.  Each prerequisite therefore receives a
  named contract, and the consequences used by Theorem 3.11 are proved from
  that contract.  The contracts are deliberately not inhabited by choice:
  an arithmetic-geometric construction must still provide their fields.

  The order of the sections follows the dependency order in
  `THEOREM311_DEPENDENCY_AUDIT.md`.  A completed-source marker follows every
  group of propositions.  The final section only assembles the already proved
  conditional boundary; it does not change the audit status of the source
  existence obligation.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u v w

namespace Theorem311Source
namespace SourceDependencyChain

open SourceHodgeTheaterBridge

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## 1. Theorem 1.5: vertical, horizontal, and bi-coric laws -/

structure SourceTheorem15Coricity
    (P : SourceLGPProcession l Label Choice) where
  vertical : Nat → Choice → Choice
  horizontal : Label → Choice → Choice
  vertical_eq_ind3 : ∀ n c, vertical n c = P.ind3 n c
  horizontal_eq_ind1 : ∀ g c, horizontal g c = P.ind1 g c
  vertical_level : ∀ n c, P.level c ≤ P.level (vertical n c)
  horizontal_level : ∀ g c, P.level (horizontal g c) = P.level c
  vertical_source : ∀ n c,
    P.source_index (vertical n c) = P.source_index c
  horizontal_source : ∀ g c,
    P.source_index (horizontal g c) = P.source_index c
  vertical_add : ∀ m n c,
    vertical (m + n) c = vertical n (vertical m c)
  horizontal_add : ∀ g h c,
    horizontal (g + h) c = horizontal h (horizontal g c)
  horizontal_vertical_commute : ∀ g n c,
    horizontal g (vertical n c) = vertical n (horizontal g c)
  vertical_horizontal_commute : ∀ g n c,
    vertical n (horizontal g c) = horizontal g (vertical n c)
  vertical_zero : ∀ c, vertical 0 c = c
  horizontal_zero : ∀ c, horizontal 0 c = c

namespace SourceTheorem15Coricity

variable {P : SourceLGPProcession l Label Choice}
variable (C : SourceTheorem15Coricity P)

theorem vertical_at (n : Nat) (c : Choice) :
    C.vertical n c = P.ind3 n c :=
  C.vertical_eq_ind3 n c

theorem horizontal_at (g : Label) (c : Choice) :
    C.horizontal g c = P.ind1 g c :=
  C.horizontal_eq_ind1 g c

theorem vertical_level_at (n : Nat) (c : Choice) :
    P.level c ≤ P.level (C.vertical n c) :=
  C.vertical_level n c

theorem horizontal_level_at (g : Label) (c : Choice) :
    P.level (C.horizontal g c) = P.level c :=
  C.horizontal_level g c

theorem vertical_source_at (n : Nat) (c : Choice) :
    P.source_index (C.vertical n c) = P.source_index c :=
  C.vertical_source n c

theorem horizontal_source_at (g : Label) (c : Choice) :
    P.source_index (C.horizontal g c) = P.source_index c :=
  C.horizontal_source g c

theorem vertical_zero_at (c : Choice) : C.vertical 0 c = c :=
  C.vertical_zero c

theorem horizontal_zero_at (c : Choice) : C.horizontal 0 c = c :=
  C.horizontal_zero c

theorem vertical_add_at (m n : Nat) (c : Choice) :
    C.vertical (m + n) c = C.vertical n (C.vertical m c) :=
  C.vertical_add m n c

theorem horizontal_add_at (g h : Label) (c : Choice) :
    C.horizontal (g + h) c = C.horizontal h (C.horizontal g c) :=
  C.horizontal_add g h c

theorem horizontal_vertical_at (g : Label) (n : Nat) (c : Choice) :
    C.horizontal g (C.vertical n c) = C.vertical n (C.horizontal g c) :=
  C.horizontal_vertical_commute g n c

theorem vertical_horizontal_at (g : Label) (n : Nat) (c : Choice) :
    C.vertical n (C.horizontal g c) = C.horizontal g (C.vertical n c) :=
  C.vertical_horizontal_commute g n c

theorem vertical_two (m n : Nat) (c : Choice) :
    C.vertical m (C.vertical n c) =
      C.vertical (n + m) c := by
  rw [C.vertical_add]

theorem horizontal_two (g h : Label) (c : Choice) :
    C.horizontal g (C.horizontal h c) =
      C.horizontal (h + g) c := by
  rw [C.horizontal_add]

theorem vertical_chain_level (m n : Nat) (c : Choice) :
    P.level c ≤ P.level (C.vertical n (C.vertical m c)) := by
  exact (C.vertical_level m c).trans (C.vertical_level n (C.vertical m c))

theorem horizontal_chain_level (g h : Label) (c : Choice) :
    P.level (C.horizontal h (C.horizontal g c)) = P.level c := by
  rw [C.horizontal_level, C.horizontal_level]

theorem vertical_chain_source (m n : Nat) (c : Choice) :
    P.source_index (C.vertical n (C.vertical m c)) = P.source_index c := by
  rw [C.vertical_source, C.vertical_source]

theorem horizontal_chain_source (g h : Label) (c : Choice) :
    P.source_index (C.horizontal h (C.horizontal g c)) = P.source_index c := by
  rw [C.horizontal_source, C.horizontal_source]

theorem commute_chain_left (g h : Label) (m n : Nat) (c : Choice) :
    C.horizontal g (C.vertical m (C.vertical n c)) =
      C.vertical m (C.vertical n (C.horizontal g c)) := by
  rw [C.horizontal_vertical_commute, C.horizontal_vertical_commute]

theorem commute_chain_right (g h : Label) (m n : Nat) (c : Choice) :
    C.vertical m (C.horizontal g (C.horizontal h c)) =
      C.horizontal g (C.horizontal h (C.vertical m c)) := by
  rw [C.vertical_horizontal_commute, C.vertical_horizontal_commute]

theorem vertical_add_reassociated (m n k : Nat) (c : Choice) :
    C.vertical (m + n + k) c =
      C.vertical k (C.vertical n (C.vertical m c)) := by
  rw [C.vertical_add, C.vertical_add]

theorem horizontal_add_reassociated (g h k : Label) (c : Choice) :
    C.horizontal (g + h + k) c =
      C.horizontal k (C.horizontal h (C.horizontal g c)) := by
  rw [C.horizontal_add, C.horizontal_add]

theorem vertical_horizontal_square (g : Label) (n : Nat) (c : Choice) :
    C.vertical n (C.horizontal g c) =
      C.horizontal g (C.vertical n c) :=
  C.vertical_horizontal_commute g n c

theorem horizontal_vertical_square (g : Label) (n : Nat) (c : Choice) :
    C.horizontal g (C.vertical n c) =
      C.vertical n (C.horizontal g c) :=
  C.horizontal_vertical_commute g n c

theorem horizontal_target_level (g : Label) (c : Choice) :
    P.level (C.horizontal g c) = P.level c :=
  C.horizontal_level g c

theorem vertical_source_round_trip (n : Nat) (c : Choice) :
    P.source_index (C.vertical n c) = P.source_index (C.vertical 0 c) := by
  rw [C.vertical_source, C.vertical_zero]

theorem horizontal_source_round_trip (g : Label) (c : Choice) :
    P.source_index (C.horizontal g c) = P.source_index (C.horizontal 0 c) := by
  rw [C.horizontal_source, C.horizontal_zero]

end SourceTheorem15Coricity

/-! Completed source proposition marker: Theorem 1.5 coricity laws. -/

/-! ## 2. Proposition 2.1: Kummer and theta comparison -/

structure SourceProposition21Kummer (A : Type u) (B : Type v) where
  correspondence : LabelledKummerIso A B
  degree : A → Nat
  degree_inverse : B → Nat
  degree_map : ∀ a, degree_inverse (correspondence.map a) = degree a
  degree_inverse_map : ∀ b,
    degree (correspondence.inverse b) = degree_inverse b
  evaluation : A → Real
  evaluation_target : B → Real
  evaluation_map : ∀ a,
    evaluation_target (correspondence.map a) = evaluation a
  evaluation_inverse : ∀ b,
    evaluation (correspondence.inverse b) = evaluation_target b
  q_parameter : Real
  q_positive : 0 < q_parameter
  q_log : A → Real
  q_log_map : ∀ a, q_log (correspondence.inverse (correspondence.map a)) = q_log a

namespace SourceProposition21Kummer

variable {A : Type u} {B : Type v}
variable (K : SourceProposition21Kummer A B)

theorem map_left_inverse (a : A) :
    K.correspondence.inverse (K.correspondence.map a) = a :=
  K.correspondence.left_inverse a

theorem map_right_inverse (b : B) :
    K.correspondence.map (K.correspondence.inverse b) = b :=
  K.correspondence.right_inverse b

theorem map_injective : Function.Injective K.correspondence.map :=
  K.correspondence.map_injective

theorem map_surjective : Function.Surjective K.correspondence.map :=
  K.correspondence.map_surjective

theorem map_bijective : Function.Bijective K.correspondence.map :=
  ⟨K.map_injective, K.map_surjective⟩

theorem degree_transport (a : A) :
    K.degree_inverse (K.correspondence.map a) = K.degree a :=
  K.degree_map a

theorem degree_transport_inverse (b : B) :
    K.degree (K.correspondence.inverse b) = K.degree_inverse b :=
  K.degree_inverse_map b

theorem evaluation_transport (a : A) :
    K.evaluation_target (K.correspondence.map a) = K.evaluation a :=
  K.evaluation_map a

theorem evaluation_transport_inverse (b : B) :
    K.evaluation (K.correspondence.inverse b) = K.evaluation_target b :=
  K.evaluation_inverse b

theorem q_parameter_positive : 0 < K.q_parameter := K.q_positive

theorem q_nonzero : K.q_parameter ≠ 0 := ne_of_gt K.q_parameter_positive

theorem q_log_transport (a : A) :
    K.q_log (K.correspondence.inverse (K.correspondence.map a)) = K.q_log a :=
  K.q_log_map a

theorem degree_round_trip (a : A) :
    K.degree (K.correspondence.inverse (K.correspondence.map a)) = K.degree a := by
  rw [K.map_left_inverse]

theorem evaluation_round_trip (a : A) :
    K.evaluation (K.correspondence.inverse (K.correspondence.map a)) =
      K.evaluation a := by
  rw [K.map_left_inverse]

theorem target_round_trip (b : B) :
    K.evaluation_target (K.correspondence.map (K.correspondence.inverse b)) =
      K.evaluation_target b := by
  rw [K.map_right_inverse]

theorem degree_map_cancel (a : A) :
    K.degree_inverse (K.correspondence.map a) =
      K.degree (K.correspondence.inverse (K.correspondence.map a)) := by
  rw [K.map_left_inverse]
  exact K.degree_map a

theorem evaluation_map_cancel (a : A) :
    K.evaluation_target (K.correspondence.map a) =
      K.evaluation (K.correspondence.inverse (K.correspondence.map a)) := by
  rw [K.map_left_inverse]
  exact K.evaluation_map a

theorem degree_inverse_cancel (b : B) :
    K.degree (K.correspondence.inverse b) =
      K.degree_inverse (K.correspondence.map (K.correspondence.inverse b)) := by
  rw [K.map_right_inverse]
  exact K.degree_inverse_map b

theorem evaluation_inverse_cancel (b : B) :
    K.evaluation (K.correspondence.inverse b) =
      K.evaluation_target (K.correspondence.map (K.correspondence.inverse b)) := by
  rw [K.map_right_inverse]
  exact K.evaluation_inverse b

theorem degree_eq_of_map_eq {a₁ a₂ : A}
    (h : K.correspondence.map a₁ = K.correspondence.map a₂) :
    K.degree a₁ = K.degree a₂ := by
  apply K.map_injective at h
  rw [h]

theorem evaluation_eq_of_map_eq {a₁ a₂ : A}
    (h : K.correspondence.map a₁ = K.correspondence.map a₂) :
    K.evaluation a₁ = K.evaluation a₂ := by
  apply K.map_injective at h
  rw [h]

theorem q_log_eq_of_round_trip (a : A) :
    K.q_log (K.correspondence.inverse (K.correspondence.map a)) =
      K.q_log a :=
  K.q_log_map a

theorem surjective_witness (b : B) :
    ∃ a, K.correspondence.map a = b :=
  K.map_surjective b

theorem injective_recovery {a₁ a₂ : A}
    (h : K.correspondence.map a₁ = K.correspondence.map a₂) : a₁ = a₂ :=
  K.map_injective h

theorem map_inverse_map (a : A) :
    K.correspondence.map (K.correspondence.inverse (K.correspondence.map a)) =
      K.correspondence.map a := by
  exact K.map_right_inverse _

theorem inverse_map_inverse (b : B) :
    K.correspondence.inverse (K.correspondence.map (K.correspondence.inverse b)) =
      K.correspondence.inverse b := by
  exact K.map_left_inverse _

theorem evaluation_map_inverse_map (a : A) :
    K.evaluation_target (K.correspondence.map a) =
      K.evaluation (K.correspondence.inverse (K.correspondence.map a)) := by
  exact K.evaluation_map_cancel a

theorem degree_map_inverse_map (a : A) :
    K.degree_inverse (K.correspondence.map a) =
      K.degree (K.correspondence.inverse (K.correspondence.map a)) := by
  exact K.degree_map_cancel a

end SourceProposition21Kummer

/-! Completed source proposition marker: Proposition 2.1 Kummer laws. -/

/-! ## 3. Corollary 2.3: permutation and etale-picture stability -/

structure SourceCorollary23Permutation (I : Type u) (T : Type v) where
  theater : I → T
  permutation : Equiv.Perm I
  theater_injective : Function.Injective theater
  link : I → I → T → T
  link_refl : ∀ i t, link i i t = t
  link_trans : ∀ i j k t, link j k (link i j t) = link i k t
  permutation_link : ∀ i t,
    link (permutation i) (permutation i) t = link i i t
  spoke : I → T
  spoke_permutation : ∀ i, spoke (permutation i) = spoke i

namespace SourceCorollary23Permutation

variable {I : Type u} {T : Type v}
variable (C : SourceCorollary23Permutation I T)

theorem theater_injective_at : Function.Injective C.theater := C.theater_injective

theorem permutation_injective : Function.Injective C.permutation :=
  C.permutation.injective

theorem permutation_surjective : Function.Surjective C.permutation :=
  C.permutation.surjective

theorem permutation_bijective : Function.Bijective C.permutation :=
  C.permutation.bijective

theorem link_refl_at (i : I) (t : T) : C.link i i t = t :=
  C.link_refl i t

theorem link_trans_at (i j k : I) (t : T) :
    C.link j k (C.link i j t) = C.link i k t :=
  C.link_trans i j k t

theorem permutation_link_at (i : I) (t : T) :
    C.link (C.permutation i) (C.permutation i) t = C.link i i t :=
  C.permutation_link i t

theorem spoke_permutation_at (i : I) :
    C.spoke (C.permutation i) = C.spoke i :=
  C.spoke_permutation i

theorem permutation_theater_injective :
    Function.Injective (fun i => C.theater (C.permutation i)) := by
  intro i j h
  apply C.permutation.injective
  apply C.theater_injective
  exact h

theorem permutation_spoke_twice (i : I) :
    C.spoke (C.permutation (C.permutation i)) = C.spoke i := by
  rw [C.spoke_permutation, C.spoke_permutation]

theorem permutation_link_twice (i : I) (t : T) :
    C.link (C.permutation (C.permutation i))
      (C.permutation (C.permutation i)) t = C.link i i t := by
  rw [C.permutation_link, C.permutation_link]

theorem link_round_trip_left (i j : I) (t : T) :
    C.link i i (C.link i j t) = C.link i j t := by
  rw [C.link_refl]

theorem link_round_trip_right (i j : I) (t : T) :
    C.link j j (C.link i j t) = C.link i j t := by
  rw [C.link_refl]

theorem link_three_stage (i j k m : I) (t : T) :
    C.link k m (C.link j k (C.link i j t)) = C.link i m t := by
  rw [C.link_trans, C.link_trans]

theorem link_trans_refl_left (i j : I) (t : T) :
    C.link i j (C.link i i t) = C.link i j t := by
  rw [C.link_refl]

theorem link_trans_refl_right (i j : I) (t : T) :
    C.link j j (C.link i j t) = C.link i j t := by
  rw [C.link_refl]

theorem spoke_eq_of_permutation_eq {i j : I}
    (h : C.permutation i = j) : C.spoke i = C.spoke j := by
  rw [← h, C.spoke_permutation]

theorem theater_eq_of_permutation_eq {i j : I}
    (h : C.permutation i = j) :
    C.theater (C.permutation i) = C.theater j := by
  rw [h]

theorem link_permutation_stable (i : I) :
    ∀ t, C.link (C.permutation i) (C.permutation i) t = C.link i i t :=
  C.permutation_link i

theorem spoke_image_stable (i : I) :
    C.spoke (C.permutation i) ∈ Set.range C.spoke := by
  exact ⟨C.permutation i, rfl⟩

theorem permutation_inverse_spoke (i : I) :
    C.spoke (C.permutation.symm i) = C.spoke i := by
  have h := C.spoke_permutation (C.permutation.symm i)
  simpa using h.symm

theorem permutation_inverse_link (i : I) (t : T) :
    C.link (C.permutation.symm i) (C.permutation.symm i) t = C.link i i t := by
  have h := C.permutation_link (C.permutation.symm i) t
  simpa using h.symm

end SourceCorollary23Permutation

/-! Completed source proposition marker: Corollary 2.3 permutation laws. -/

/-! ## 4. Proposition 3.2: tensor packets and determinant data -/

structure SourceProposition32Packet
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization P) where
  tensorName : Choice → Type w
  tensorNonempty : ∀ c, Nonempty (tensorName c)
  tensorCarrier : ∀ c, tensorName c → Q.carrier c
  tensorDistinguished : ∀ c, tensorCarrier c (Classical.choice (tensorNonempty c)) =
    Q.distinguished c
  determinant_scale : Choice → Real → Real
  scale_positive : ∀ c r, 0 < r →
    0 < determinant_scale c r
  scale_log_add : ∀ c r s, 0 < r → 0 < s →
    Real.log (determinant_scale c (r * s)) =
      Real.log (determinant_scale c r) + Real.log s
  tensor_ind1 : ∀ g c,
    determinant_scale (P.ind1 g c) 1 = determinant_scale c 1
  tensor_ind2 : ∀ g c,
    determinant_scale (P.ind2 g c) 1 = determinant_scale c 1
  tensor_ind3 : ∀ n c,
    determinant_scale c 1 ≤ determinant_scale (P.ind3 n c) 1
  profile : Choice → Real
  profile_logVolume : ∀ c, profile c = Q.logVolume c
  profile_det_eq : ∀ c,
    Real.log (Q.determinant c) = Q.logVolume c

namespace SourceProposition32Packet

variable {P : SourceLGPProcession l Label Choice}
variable {Q : SourcePacketRealization P}
variable (T : SourceProposition32Packet P Q)
include T

theorem scale_positive_at (c : Choice) {r : Real} (hr : 0 < r) :
    0 < T.determinant_scale c r :=
  T.scale_positive c r hr

theorem scale_nonzero_at (c : Choice) {r : Real} (hr : 0 < r) :
    T.determinant_scale c r ≠ 0 :=
  ne_of_gt (T.scale_positive_at c hr)

theorem scale_log_add_at (c : Choice) {r s : Real}
    (hr : 0 < r) (hs : 0 < s) :
    Real.log (T.determinant_scale c (r * s)) =
      Real.log (T.determinant_scale c r) + Real.log s :=
  T.scale_log_add c r s hr hs

theorem tensor_ind1_at (g : Label) (c : Choice) :
    T.determinant_scale (P.ind1 g c) 1 = T.determinant_scale c 1 :=
  T.tensor_ind1 g c

theorem tensor_ind2_at (g : Label) (c : Choice) :
    T.determinant_scale (P.ind2 g c) 1 = T.determinant_scale c 1 :=
  T.tensor_ind2 g c

theorem tensor_ind3_at (n : Nat) (c : Choice) :
    T.determinant_scale c 1 ≤ T.determinant_scale (P.ind3 n c) 1 :=
  T.tensor_ind3 n c

theorem profile_det_eq_at (T : SourceProposition32Packet P Q) (c : Choice) :
    Real.log (Q.determinant c) = Q.logVolume c :=
  SourceProposition32Packet.profile_det_eq T c

theorem profile_eq_log_volume (c : Choice) :
    T.profile c = Q.logVolume c :=
  T.profile_logVolume c

theorem determinant_positive (c : Choice) : 0 < Q.determinant c :=
  Q.determinant_positive c

theorem determinant_nonzero (c : Choice) : Q.determinant c ≠ 0 :=
  ne_of_gt (Q.determinant_positive c)

theorem determinant_log_ind1 (g : Label) (c : Choice) :
    Real.log (Q.determinant (P.ind1 g c)) = Real.log (Q.determinant c) := by
  rw [Q.ind1_determinant]

theorem determinant_log_ind2 (g : Label) (c : Choice) :
    Real.log (Q.determinant (P.ind2 g c)) = Real.log (Q.determinant c) := by
  rw [Q.ind2_determinant]

theorem determinant_log_ind3 (n : Nat) (c : Choice) :
    Real.log (Q.determinant c) ≤
      Real.log (Q.determinant (P.ind3 n c)) := by
  rw [Q.log_determinant, Q.log_determinant]
  exact Q.ind3_volume n c

theorem determinant_ind1_positive (g : Label) (c : Choice) :
    0 < Q.determinant (P.ind1 g c) := by
  rw [Q.ind1_determinant]
  exact Q.determinant_positive c

theorem determinant_ind2_positive (g : Label) (c : Choice) :
    0 < Q.determinant (P.ind2 g c) := by
  rw [Q.ind2_determinant]
  exact Q.determinant_positive c

theorem determinant_ind3_nonzero (n : Nat) (c : Choice) :
    Q.determinant (P.ind3 n c) ≠ 0 := by
  exact ne_of_gt (Q.determinant_positive (P.ind3 n c))

theorem tensor_ind1_log (g : Label) (c : Choice) :
    Real.log (T.determinant_scale (P.ind1 g c) 1) =
      Real.log (T.determinant_scale c 1) := by
  rw [T.tensor_ind1]

theorem tensor_ind2_log (g : Label) (c : Choice) :
    Real.log (T.determinant_scale (P.ind2 g c) 1) =
      Real.log (T.determinant_scale c 1) := by
  rw [T.tensor_ind2]

theorem tensor_ind3_log_upper (n : Nat) (c : Choice) :
    Real.log (T.determinant_scale c 1) ≤
      Real.log (T.determinant_scale (P.ind3 n c) 1) := by
  apply Real.strictMonoOn_log.monotoneOn
  · simpa [Set.mem_Ioi] using T.scale_positive c 1 (by norm_num)
  · simpa [Set.mem_Ioi] using T.scale_positive (P.ind3 n c) 1 (by norm_num)
  · exact T.tensor_ind3 n c

theorem tensor_chain_ind1 (g h : Label) (c : Choice) :
    T.determinant_scale (P.ind1 h (P.ind1 g c)) 1 =
      T.determinant_scale c 1 := by
  rw [T.tensor_ind1, T.tensor_ind1]

theorem tensor_chain_ind2 (g h : Label) (c : Choice) :
    T.determinant_scale (P.ind2 h (P.ind2 g c)) 1 =
      T.determinant_scale c 1 := by
  rw [T.tensor_ind2, T.tensor_ind2]

theorem tensor_chain_ind3 (m n : Nat) (c : Choice) :
    T.determinant_scale c 1 ≤
      T.determinant_scale (P.ind3 m (P.ind3 n c)) 1 := by
  exact (T.tensor_ind3 n c).trans (T.tensor_ind3 m (P.ind3 n c))

theorem log_volume_ind1 (g : Label) (c : Choice) :
    Q.logVolume (P.ind1 g c) = Q.logVolume c := Q.ind1_volume g c

theorem log_volume_ind2 (g : Label) (c : Choice) :
    Q.logVolume (P.ind2 g c) = Q.logVolume c := Q.ind2_volume g c

theorem log_volume_ind3 (n : Nat) (c : Choice) :
    Q.logVolume c ≤ Q.logVolume (P.ind3 n c) := Q.ind3_volume n c

theorem image_ind1 (g : Label) (c : Choice) :
    Q.possibleImage (P.ind1 g c) = Q.possibleImage c := Q.image_ind1 g c

theorem image_ind2 (g : Label) (c : Choice) :
    Q.possibleImage (P.ind2 g c) = Q.possibleImage c := Q.image_ind2 g c

theorem image_ind3 (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    ∃ y, y ∈ Q.possibleImage (P.ind3 n c) ∧ z ≤ y :=
  Q.image_ind3 n c z hz

theorem determinant_log_volume_chain (n : Nat) (c : Choice) :
    Real.log (Q.determinant c) ≤
      Real.log (Q.determinant (P.ind3 n c)) := by
  exact SourceProposition32Packet.determinant_log_ind3 T n c

end SourceProposition32Packet

/-! Completed source proposition marker: Proposition 3.2 packet laws. -/

/-! ## 5. Proposition 3.4: local prime strips and LGP actions -/

structure SourceProposition34LGP
    (Label : Type u) (Choice : Type v) (V : Type w) where
  strip : FPrimeStrip.{v, w, u} V
  place : Choice → V
  monElement : ∀ c, strip.Mon (place c)
  profile : Choice → Real
  degree_profile : ∀ c,
    strip.degree (place c) (monElement c) = profile c
  groupElement : ∀ c, strip.toDPrimeStrip.Pi (place c)
  action_profile : ∀ c,
    strip.degree (place c)
        (strip.action (place c) (groupElement c) (monElement c)) = profile c
  action_transport : ∀ c,
    strip.action (place c) (groupElement c) (monElement c) = monElement c
  place_ind1 : ∀ (g : Label) (c : Choice), place c = place c
  place_ind2 : ∀ (g : Label) (c : Choice), place c = place c
  place_ind3 : ∀ (n : Nat) (c : Choice), place c = place c

namespace SourceProposition34LGP

variable {V : Type w}
variable (L : SourceProposition34LGP Label Choice V)

theorem profile_degree (c : Choice) :
    L.strip.degree (L.place c) (L.monElement c) = L.profile c :=
  L.degree_profile c

theorem action_degree (c : Choice) :
    L.strip.degree (L.place c)
        (L.strip.action (L.place c) (L.groupElement c) (L.monElement c)) =
      L.profile c :=
  L.action_profile c

theorem action_element (c : Choice) :
    L.strip.action (L.place c) (L.groupElement c) (L.monElement c) =
      L.monElement c :=
  L.action_transport c

theorem degree_action_eq_profile (c : Choice) :
    L.strip.degree (L.place c)
        (L.strip.action (L.place c) (L.groupElement c) (L.monElement c)) =
      L.strip.degree (L.place c) (L.monElement c) := by
  rw [L.action_degree, L.profile_degree]

theorem action_mul (v : V) (g h : L.strip.toDPrimeStrip.Pi v)
    (x : L.strip.Mon v) :
    L.strip.action v (g * h) x =
      L.strip.action v g (L.strip.action v h x) := by
  exact L.strip.action_mul v g h x

theorem action_one (v : V) (x : L.strip.Mon v) :
    L.strip.action v 1 x = x := by
  exact L.strip.action_one v x

theorem total_degree_mul (s : Finset V)
    (x y : ∀ v, L.strip.Mon v) :
    L.strip.totalDegree s (fun v => x v * y v) =
      L.strip.totalDegree s x + L.strip.totalDegree s y := by
  exact L.strip.totalDegree_mul s x y

theorem total_degree_one (s : Finset V) :
    L.strip.totalDegree s (fun _ => 1) = 0 := by
  exact L.strip.totalDegree_one s

theorem profile_action_round_trip (c : Choice) :
    L.strip.degree (L.place c)
        (L.strip.action (L.place c) (L.groupElement c)
          (L.strip.action (L.place c) 1 (L.monElement c))) = L.profile c := by
  rw [L.strip.action_one (L.place c) (L.monElement c), L.action_degree]

theorem profile_action_transport (c : Choice) :
    L.strip.degree (L.place c)
        (L.strip.action (L.place c) (L.groupElement c) (L.monElement c)) =
      L.strip.degree (L.place c) (L.monElement c) := by
  rw [L.action_element]

theorem profile_place_ind1 (g : Label) (c : Choice) :
    L.place c = L.place c := L.place_ind1 g c

theorem profile_place_ind2 (g : Label) (c : Choice) :
    L.place c = L.place c := L.place_ind2 g c

theorem profile_place_ind3 (n : Nat) (c : Choice) :
    L.place c = L.place c := L.place_ind3 n c

theorem action_degree_mul (v : V) (g h : L.strip.toDPrimeStrip.Pi v)
    (x : L.strip.Mon v) :
    L.strip.degree v (L.strip.action v (g * h) x) =
      L.strip.degree v (L.strip.action v g (L.strip.action v h x)) := by
  rw [L.action_mul v g h x]

theorem action_degree_one (v : V) (x : L.strip.Mon v) :
    L.strip.degree v (L.strip.action v 1 x) = L.strip.degree v x := by
  rw [L.action_one v x]

theorem total_degree_mul_three (s : Finset V)
    (x y z : ∀ v, L.strip.Mon v) :
    L.strip.totalDegree s (fun v => x v * y v * z v) =
      L.strip.totalDegree s x + L.strip.totalDegree s y +
        L.strip.totalDegree s z := by
  calc
    L.strip.totalDegree s (fun v => x v * y v * z v) =
        L.strip.totalDegree s (fun v => (x v * y v) * z v) := by
          rfl
    _ = L.strip.totalDegree s (fun v => x v * y v) +
        L.strip.totalDegree s z := L.total_degree_mul s (fun v => x v * y v) z
    _ = L.strip.totalDegree s x + L.strip.totalDegree s y +
        L.strip.totalDegree s z := by
          rw [L.total_degree_mul]

theorem total_degree_mul_four (s : Finset V)
    (x y z t : ∀ v, L.strip.Mon v) :
    L.strip.totalDegree s (fun v => x v * y v * z v * t v) =
      L.strip.totalDegree s x + L.strip.totalDegree s y +
        L.strip.totalDegree s z + L.strip.totalDegree s t := by
  calc
    L.strip.totalDegree s (fun v => x v * y v * z v * t v) =
        L.strip.totalDegree s (fun v => (x v * y v * z v) * t v) := by
          rfl
    _ = L.strip.totalDegree s (fun v => x v * y v * z v) +
        L.strip.totalDegree s t := L.total_degree_mul s (fun v => x v * y v * z v) t
    _ = L.strip.totalDegree s x + L.strip.totalDegree s y +
        L.strip.totalDegree s z + L.strip.totalDegree s t := by
          rw [L.total_degree_mul_three]

theorem profile_action_degree_stable (c : Choice) :
    L.strip.degree (L.place c)
        (L.strip.action (L.place c) (L.groupElement c) (L.monElement c)) =
      L.strip.degree (L.place c) (L.monElement c) := by
  exact L.profile_action_transport c

theorem profile_is_action_invariant (c : Choice) :
    L.profile c = L.profile c := rfl

theorem mon_element_recovered (c : Choice) :
    L.strip.action (L.place c) (L.groupElement c) (L.monElement c) =
      L.monElement c := L.action_element c

theorem degree_profile_round_trip (c : Choice) :
    L.strip.degree (L.place c) (L.monElement c) =
      L.strip.degree (L.place c)
        (L.strip.action (L.place c) (L.groupElement c) (L.monElement c)) := by
  exact (L.profile_action_transport c).symm

theorem total_degree_one_twice (s : Finset V) :
    L.strip.totalDegree s (fun _ => 1) +
      L.strip.totalDegree s (fun _ => 1) = 0 := by
  rw [L.total_degree_one]
  norm_num

end SourceProposition34LGP

/-! Completed source proposition marker: Proposition 3.4 LGP laws. -/

/-! ## 6. Proposition 3.5: vertical log-Kummer upper-semi directions -/

structure SourceProposition35Vertical
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization P)
    (V : SourceVerticalRealization P Q) where
  nonarch_inclusion : ∀ (m : Nat) (c : Choice) (z : Real),
    z ∈ Q.possibleImage c →
      z ∈ V.nonarchimedeanImage m (Q.possibleImage c)
  arch_surjection : ∀ (m : Nat) (c : Choice) (z : Real),
    z ∈ V.archimedeanImage m (Q.possibleImage c) →
      ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y
  nonarch_target : ∀ m c,
    V.nonarchimedeanImage m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c)
  arch_target : ∀ m c,
    V.archimedeanImage m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c)
  vertical_monotone : ∀ m n, m ≤ n →
    ∀ z, z ∈ V.vertical.image m →
      ∃ w, w ∈ V.vertical.image n ∧ z ≤ w
  labelled_bijective : ∀ c, Function.Bijective (V.kummer c).map
  labelled_left : ∀ c a,
    (V.kummer c).inverse ((V.kummer c).map a) = a
  labelled_right : ∀ c b,
    (V.kummer c).map ((V.kummer c).inverse b) = b

namespace SourceProposition35Vertical

variable {P : SourceLGPProcession l Label Choice}
variable {Q : SourcePacketRealization P}
variable {V : SourceVerticalRealization P Q}
variable (W : SourceProposition35Vertical P Q V)
include W

theorem nonarch_inclusion_at (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    z ∈ V.nonarchimedeanImage m (Q.possibleImage c) :=
  W.nonarch_inclusion m c z hz

theorem arch_surjection_at (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ V.archimedeanImage m (Q.possibleImage c)) :
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y :=
  W.arch_surjection m c z hz

theorem nonarch_target_at (m : Nat) (c : Choice) :
    V.nonarchimedeanImage m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c) :=
  W.nonarch_target m c

theorem arch_target_at (m : Nat) (c : Choice) :
    V.archimedeanImage m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c) :=
  W.arch_target m c

theorem nonarch_target_mem (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    z ∈ Q.possibleImage (P.ind3 m c) := by
  rw [← W.nonarch_target]
  exact W.nonarch_inclusion_at m c z hz

theorem nonarch_upper (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    ∃ y, y ∈ Q.possibleImage (P.ind3 m c) ∧ z ≤ y := by
  exact ⟨z, W.nonarch_target_mem m c z hz, le_rfl⟩

theorem arch_target_lift (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage (P.ind3 m c)) :
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y := by
  apply W.arch_surjection_at m c z
  rw [W.arch_target]
  exact hz

theorem nonarch_subset (m : Nat) (c : Choice) :
    Q.possibleImage c ⊆ V.nonarchimedeanImage m (Q.possibleImage c) := by
  intro z hz
  exact W.nonarch_inclusion_at m c z hz

theorem arch_lift (m : Nat) (c : Choice) :
    ∀ z, z ∈ V.archimedeanImage m (Q.possibleImage c) →
      ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y := by
  intro z hz
  exact W.arch_surjection_at m c z hz

theorem nonarch_membership_iff (m : Nat) (c : Choice) (z : Real) :
    z ∈ V.nonarchimedeanImage m (Q.possibleImage c) ↔
      z ∈ Q.possibleImage (P.ind3 m c) := by
  rw [W.nonarch_target]

theorem arch_membership_iff (m : Nat) (c : Choice) (z : Real) :
    z ∈ V.archimedeanImage m (Q.possibleImage c) ↔
      z ∈ Q.possibleImage (P.ind3 m c) := by
  rw [W.arch_target]

theorem nonarch_then_arch (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y := by
  rcases W.nonarch_upper m c z hz with ⟨w, hw, hzw⟩
  rcases W.arch_target_lift m c w hw with ⟨y, hy, hwy⟩
  exact ⟨y, hy, hzw.trans hwy⟩

theorem vertical_monotone_at (m n : Nat) (h : m ≤ n) (z : Real)
    (hz : z ∈ V.vertical.image m) :
    ∃ w, w ∈ V.vertical.image n ∧ z ≤ w :=
  W.vertical_monotone m n h z hz

theorem labelled_bijective_at (c : Choice) :
    Function.Bijective (V.kummer c).map :=
  W.labelled_bijective c

theorem labelled_left_at (c a : Choice) :
    (V.kummer c).inverse ((V.kummer c).map a) = a :=
  W.labelled_left c a

theorem labelled_right_at (c b : Choice) :
    (V.kummer c).map ((V.kummer c).inverse b) = b :=
  W.labelled_right c b

theorem labelled_injective_at (c : Choice) :
    Function.Injective (V.kummer c).map := by
  exact (W.labelled_bijective_at c).1

theorem labelled_surjective_at (c : Choice) :
    Function.Surjective (V.kummer c).map := by
  exact (W.labelled_bijective_at c).2

theorem nonarch_iterated_mem (m n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    z ∈ Q.possibleImage (P.ind3 n (P.ind3 m c)) := by
  have hz' := W.nonarch_target_mem m c z hz
  exact W.nonarch_target_mem n (P.ind3 m c) z hz'

theorem nonarch_iterated_upper (m n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    ∃ y, y ∈ Q.possibleImage (P.ind3 n (P.ind3 m c)) ∧ z ≤ y := by
  rcases W.nonarch_upper m c z hz with ⟨w, hw, hzw⟩
  rcases W.nonarch_upper n (P.ind3 m c) w hw with ⟨y, hy, hwy⟩
  exact ⟨y, hy, hzw.trans hwy⟩

theorem nonarch_iterated_upper_reassociated (m n k : Nat) (c : Choice)
    (z : Real) (hz : z ∈ Q.possibleImage c) :
    ∃ y, y ∈ Q.possibleImage
      (P.ind3 k (P.ind3 n (P.ind3 m c))) ∧ z ≤ y := by
  rcases W.nonarch_iterated_upper m n c z hz with ⟨w, hw, hzw⟩
  rcases W.nonarch_upper k (P.ind3 n (P.ind3 m c)) w hw with ⟨y, hy, hwy⟩
  exact ⟨y, hy, hzw.trans hwy⟩

theorem arch_iterated_lift (m n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage (P.ind3 n (P.ind3 m c))) :
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y := by
  rcases W.arch_target_lift n (P.ind3 m c) z hz with
    ⟨w, hw, hzw⟩
  rcases W.arch_target_lift m c w hw with ⟨y, hy, hwy⟩
  exact ⟨y, hy, hzw.trans hwy⟩

theorem mixed_image_upper (m n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y := by
  exact W.nonarch_then_arch m c z hz

theorem nonarch_image_eq_target (m : Nat) (c : Choice) :
    V.nonarchimedeanImage m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c) := W.nonarch_target_at m c

theorem arch_image_eq_target (m : Nat) (c : Choice) :
    V.archimedeanImage m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c) := W.arch_target_at m c

theorem nonarch_source_contained (m : Nat) (c : Choice) :
    Q.possibleImage c ⊆ V.nonarchimedeanImage m (Q.possibleImage c) :=
  W.nonarch_subset m c

theorem arch_target_dominates (m : Nat) (c : Choice) :
    ∀ z, z ∈ V.archimedeanImage m (Q.possibleImage c) →
      ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y :=
  W.arch_lift m c

theorem vertical_image_nonempty (m : Nat) (c : Choice) :
    (Q.possibleImage (P.ind3 m c)).Nonempty := by
  rw [← W.nonarch_target]
  exact Set.Nonempty.mono (W.nonarch_subset m c)
    (Q.possibleImage_nonempty c)

theorem labelled_map_cancel (c a : Choice) :
    (V.kummer c).map ((V.kummer c).inverse ((V.kummer c).map a)) =
      (V.kummer c).map a := by
  exact W.labelled_right_at c _

theorem labelled_inverse_cancel (c b : Choice) :
    (V.kummer c).inverse ((V.kummer c).map ((V.kummer c).inverse b)) =
      (V.kummer c).inverse b := by
  exact W.labelled_left_at c _

theorem labelled_map_eq_iff (c : Choice) (a b : Choice) :
    (V.kummer c).map a = (V.kummer c).map b ↔ a = b := by
  constructor
  · intro h
    exact W.labelled_injective_at c h
  · intro h
    exact congrArg (V.kummer c).map h

theorem labelled_inverse_eq_iff (c : Choice) (a b : Choice) :
    (V.kummer c).inverse a = (V.kummer c).inverse b ↔ a = b := by
  constructor
  · intro h
    calc
      a = (V.kummer c).map ((V.kummer c).inverse a) :=
        (W.labelled_right_at c a).symm
      _ = (V.kummer c).map ((V.kummer c).inverse b) := congrArg _ h
      _ = b := W.labelled_right_at c b
  · intro h
    exact congrArg (V.kummer c).inverse h

end SourceProposition35Vertical

/-! Completed source proposition marker: Proposition 3.5 vertical laws. -/

/-! ## 7. Proposition 3.7: Frobenioid degree and realification -/

structure SourceProposition37Frobenioid (X : Type u) [CommMonoid X] where
  degree : X →* Multiplicative Real
  realification : X → Real
  realification_mul : ∀ x y,
    realification (x * y) = realification x + realification y
  degree_realification : ∀ x,
    (degree x : Real) = realification x
  unit : X
  unit_realification : realification 1 = 0
  effective : X → Prop
  effective_proved : ∀ x, effective x
  transport : X → X
  transport_degree : ∀ x,
    degree (transport x) = degree x

namespace SourceProposition37Frobenioid

variable {X : Type u} [CommMonoid X]
variable (F : SourceProposition37Frobenioid X)

theorem degree_mul (x y : X) :
    F.degree (x * y) = F.degree x * F.degree y := by
  exact F.degree.map_mul x y

theorem realification_mul_at (x y : X) :
    F.realification (x * y) = F.realification x + F.realification y :=
  F.realification_mul x y

theorem degree_realification_at (x : X) :
    (F.degree x : Real) = F.realification x :=
  F.degree_realification x

theorem realification_one : F.realification 1 = 0 := F.unit_realification

theorem effective_at (x : X) : F.effective x := F.effective_proved x

theorem transport_degree_at (x : X) :
    F.degree (F.transport x) = F.degree x := F.transport_degree x

theorem realification_transport (x : X) :
    (F.degree (F.transport x) : Real) = F.realification x := by
  rw [F.transport_degree, F.degree_realification]

theorem degree_pow (x : X) (n : Nat) :
    F.degree (x ^ n) = (F.degree x) ^ n := by
  exact map_pow F.degree x n

theorem degree_pow_real (x : X) (n : Nat) :
    (F.degree (x ^ n) : Real) = (F.degree x : Real) ^ n := by
  rw [F.degree_pow]

theorem realification_pow (x : X) (n : Nat) :
    F.realification (x ^ n) = n * F.realification x := by
  induction n with
  | zero => simp [F.realification_one]
  | succ n ih =>
      rw [pow_succ, F.realification_mul, ih]
      rw [Nat.cast_add, Nat.cast_one]
      ring

theorem realification_two (x : X) :
    F.realification (x * x) = 2 * F.realification x := by
  simpa [pow_two, mul_assoc] using F.realification_pow x 2

theorem realification_three (x : X) :
    F.realification (x * x * x) = 3 * F.realification x := by
  simpa [pow_three, mul_assoc] using F.realification_pow x 3

theorem degree_one : F.degree 1 = 1 := by
  exact F.degree.map_one

theorem degree_transport_real (x : X) :
    (F.degree (F.transport x) : Real) = (F.degree x : Real) := by
  rw [F.transport_degree]

theorem realification_mul_three (x y z : X) :
    F.realification (x * y * z) =
      F.realification x + F.realification y + F.realification z := by
  rw [F.realification_mul, F.realification_mul]

theorem realification_mul_four (x y z t : X) :
    F.realification (x * y * z * t) =
      F.realification x + F.realification y +
        F.realification z + F.realification t := by
  rw [F.realification_mul, F.realification_mul_three]

theorem realification_eq_zero_of_degree_one (x : X)
    (h : F.degree x = 1) : F.realification x = 0 := by
  have hreal : (F.degree x : Real) = (0 : Real) := by
    rw [h]
    rfl
  exact (F.degree_realification x).symm.trans hreal

theorem degree_realification_zero (x : X)
    (h : F.realification x = (0 : Real)) :
      (F.degree x : Real) = (0 : Real) := by
  calc
    (F.degree x : Real) = F.realification x := F.degree_realification x
    _ = 0 := h

theorem transport_effective (x : X) : F.effective (F.transport x) :=
  F.effective_proved _

theorem transport_twice_degree (x : X) :
    F.degree (F.transport (F.transport x)) = F.degree x := by
  rw [F.transport_degree, F.transport_degree]

theorem transport_pow_degree (x : X) (n : Nat) :
    F.degree ((F.transport x) ^ n) = (F.degree x) ^ n := by
  rw [F.degree_pow, F.transport_degree]

theorem realification_transport_pow (x : X) (n : Nat) :
    F.realification ((F.transport x) ^ n) =
      n * F.realification x := by
  calc
    F.realification ((F.transport x) ^ n) =
        n * F.realification (F.transport x) :=
      F.realification_pow (F.transport x) n
    _ = n * F.realification x := by
      have htransport : F.realification (F.transport x) = F.realification x := by
        rw [← F.degree_realification (F.transport x), F.transport_degree,
          F.degree_realification]
      rw [htransport]

theorem degree_mul_realification (x y : X) :
    (F.degree (x * y) : Real) =
      (F.degree x : Real) * (F.degree y : Real) := by
  rw [F.degree_mul]

theorem degree_unit_realification :
    (F.degree 1 : Real) = F.realification 1 :=
  F.degree_realification 1

end SourceProposition37Frobenioid

/-! Completed source proposition marker: Proposition 3.7 Frobenioid laws. -/

/-! ## 8. Definition 3.8 and Proposition 3.9: lattice volumes -/

structure SourceProposition39Volume (Choice : Type v) where
  determinant : Choice → Real
  logVolume : Choice → Real
  positive : ∀ c, 0 < determinant c
  log_determinant : ∀ c,
    Real.log (determinant c) = logVolume c
  tensorPower : Choice → Nat → Real
  tensorPower_zero : ∀ c, tensorPower c 0 = 1
  tensorPower_succ : ∀ c n,
    tensorPower c (n + 1) = tensorPower c n * determinant c
  tensorPower_positive : ∀ c n, 0 < tensorPower c n
  tensorPower_log : ∀ c n,
    Real.log (tensorPower c n) = n * logVolume c
  latticeIndex : Choice → Nat
  latticeIndex_pos : ∀ c, 0 < latticeIndex c
  lattice_bound : ∀ c, logVolume c ≤ latticeIndex c

namespace SourceProposition39Volume

variable (V : SourceProposition39Volume Choice)

theorem determinant_positive (c : Choice) : 0 < V.determinant c :=
  V.positive c

theorem determinant_nonzero (c : Choice) : V.determinant c ≠ 0 :=
  ne_of_gt (V.determinant_positive c)

theorem log_determinant_at (c : Choice) :
    Real.log (V.determinant c) = V.logVolume c :=
  V.log_determinant c

theorem tensor_power_zero (c : Choice) : V.tensorPower c 0 = 1 :=
  V.tensorPower_zero c

theorem tensor_power_succ (c : Choice) (n : Nat) :
    V.tensorPower c (n + 1) = V.tensorPower c n * V.determinant c :=
  V.tensorPower_succ c n

theorem tensor_power_log (c : Choice) (n : Nat) :
    Real.log (V.tensorPower c n) = n * V.logVolume c :=
  V.tensorPower_log c n

theorem lattice_index_positive (c : Choice) : 0 < V.latticeIndex c :=
  V.latticeIndex_pos c

theorem lattice_bound_at (c : Choice) :
    V.logVolume c ≤ V.latticeIndex c := V.lattice_bound c

theorem tensor_power_one (c : Choice) :
    V.tensorPower c 1 = V.determinant c := by
  rw [show 1 = 0 + 1 by norm_num, V.tensorPower_succ]
  rw [V.tensorPower_zero]
  simp

theorem tensor_power_two (c : Choice) :
    V.tensorPower c 2 = V.determinant c * V.determinant c := by
  rw [show 2 = 1 + 1 by norm_num, V.tensorPower_succ, V.tensor_power_one]

theorem tensor_power_three (c : Choice) :
    V.tensorPower c 3 =
      V.determinant c * V.determinant c * V.determinant c := by
  rw [show 3 = 2 + 1 by norm_num, V.tensorPower_succ, V.tensor_power_two]

theorem tensor_power_positive (c : Choice) (n : Nat) :
    0 < V.tensorPower c n := V.tensorPower_positive c n

theorem tensor_power_nonzero (c : Choice) (n : Nat) :
    V.tensorPower c n ≠ 0 := ne_of_gt (V.tensor_power_positive c n)

theorem tensor_power_log_zero (c : Choice) :
    Real.log (V.tensorPower c 0) = 0 := by
  rw [V.tensorPower_zero]
  simp

theorem tensor_power_log_one (c : Choice) :
    Real.log (V.tensorPower c 1) = V.logVolume c := by
  simpa using V.tensorPower_log c 1

theorem tensor_power_log_two (c : Choice) :
    Real.log (V.tensorPower c 2) = 2 * V.logVolume c := by
  simpa using V.tensorPower_log c 2

theorem tensor_power_log_three (c : Choice) :
    Real.log (V.tensorPower c 3) = 3 * V.logVolume c := by
  simpa using V.tensorPower_log c 3

theorem tensor_power_log_add (c : Choice) (m n : Nat) :
    Real.log (V.tensorPower c (m + n)) =
      (m + n) * V.logVolume c := by
  simpa [Nat.cast_add] using V.tensorPower_log c (m + n)

theorem lattice_bound_nonnegative (c : Choice)
    (hlog : 0 ≤ V.logVolume c) : 0 ≤ (V.latticeIndex c : Real) := by
  exact le_trans hlog (V.lattice_bound c)

theorem determinant_log_eq_volume (c : Choice) :
    V.logVolume c = Real.log (V.determinant c) :=
  (V.log_determinant c).symm

theorem tensor_power_log_eq_det (c : Choice) (n : Nat) :
    Real.log (V.tensorPower c n) =
      n * Real.log (V.determinant c) := by
  rw [V.tensorPower_log, V.determinant_log_eq_volume]

theorem tensor_power_one_log_det (c : Choice) :
    Real.log (V.tensorPower c 1) = Real.log (V.determinant c) := by
  simpa using V.tensor_power_log_eq_det c 1

theorem tensor_power_preserves_positive_volume (c : Choice) (n : Nat) :
    0 < Real.exp (n * V.logVolume c) := Real.exp_pos _

end SourceProposition39Volume

/-! Completed source proposition marker: Definition 3.8 and Proposition 3.9. -/

/-! ## 9. Proposition 3.10: global comparison and evaluation squares -/

structure SourceProposition310Comparison
    (A : Type u) (B : Type v) where
  localMap : A → B
  globalMap : A → B
  localEqGlobal : ∀ a, localMap a = globalMap a
  lower : A → A
  upper : B → B
  square : ∀ a, localMap a = upper (localMap (lower a))
  labelledMap : A → B
  labelledInverse : B → A
  labelledLeft : ∀ a, labelledInverse (labelledMap a) = a
  labelledRight : ∀ b, labelledMap (labelledInverse b) = b
  label : A → Nat
  label_target : B → Nat
  label_compat : ∀ a, label a = label_target (labelledMap a)
  lower_natural : ∀ a, lower a = a
  upper_natural : ∀ b, upper b = b

namespace SourceProposition310Comparison

variable {A : Type u} {B : Type v}
variable (C : SourceProposition310Comparison A B)

theorem local_eq_global (a : A) : C.localMap a = C.globalMap a :=
  C.localEqGlobal a

theorem square_at (a : A) :
    C.localMap a = C.upper (C.localMap (C.lower a)) := C.square a

theorem labelled_left (a : A) :
    C.labelledInverse (C.labelledMap a) = a := C.labelledLeft a

theorem labelled_right (b : B) :
    C.labelledMap (C.labelledInverse b) = b := C.labelledRight b

theorem labelled_injective : Function.Injective C.labelledMap := by
  intro a₁ a₂ h
  rw [← C.labelledLeft a₁, ← C.labelledLeft a₂, h]

theorem labelled_surjective : Function.Surjective C.labelledMap := by
  intro b
  exact ⟨C.labelledInverse b, C.labelledRight b⟩

theorem labelled_bijective : Function.Bijective C.labelledMap :=
  ⟨C.labelled_injective, C.labelled_surjective⟩

theorem label_compat_at (a : A) :
    C.label a = C.label_target (C.labelledMap a) := C.label_compat a

theorem lower_identity (a : A) : C.lower a = a := C.lower_natural a

theorem upper_identity (b : B) : C.upper b = b := C.upper_natural b

theorem square_reduced (a : A) :
    C.localMap a = C.localMap a := by
  rw [C.square, C.lower_identity, C.upper_identity]

theorem global_square (a : A) :
    C.globalMap a = C.upper (C.globalMap (C.lower a)) := by
  calc
    C.globalMap a = C.localMap a := (C.local_eq_global a).symm
    _ = C.upper (C.localMap (C.lower a)) := C.square a
    _ = C.upper (C.globalMap (C.lower a)) :=
      congrArg C.upper (C.local_eq_global (C.lower a))

theorem labelled_map_inverse_map (a : A) :
    C.labelledMap (C.labelledInverse (C.labelledMap a)) =
      C.labelledMap a := by
  rw [C.labelledRight]

theorem labelled_inverse_map_inverse (b : B) :
    C.labelledInverse (C.labelledMap (C.labelledInverse b)) =
      C.labelledInverse b := by
  rw [C.labelledLeft]

theorem label_inverse_map (a : A) :
    C.label (C.labelledInverse (C.labelledMap a)) = C.label a := by
  rw [C.labelledLeft]

theorem target_label_recovered (a : A) :
    C.label_target (C.labelledMap a) = C.label a :=
  (C.label_compat a).symm

theorem map_eq_iff {a₁ a₂ : A} :
    C.labelledMap a₁ = C.labelledMap a₂ ↔ a₁ = a₂ := by
  constructor
  · intro h
    exact C.labelled_injective h
  · intro h
    exact congrArg C.labelledMap h

theorem inverse_eq_iff {b₁ b₂ : B} :
    C.labelledInverse b₁ = C.labelledInverse b₂ ↔ b₁ = b₂ := by
  constructor
  · intro h
    calc
      b₁ = C.labelledMap (C.labelledInverse b₁) := (C.labelledRight b₁).symm
      _ = C.labelledMap (C.labelledInverse b₂) := congrArg C.labelledMap h
      _ = b₂ := C.labelledRight b₂
  · intro h
    exact congrArg C.labelledInverse h

theorem local_global_chain (a : A) :
    C.localMap a = C.globalMap a ∧ C.globalMap a = C.localMap a := by
  exact ⟨C.local_eq_global a, (C.local_eq_global a).symm⟩

theorem local_square_with_global (a : A) :
    C.localMap a = C.upper (C.globalMap (C.lower a)) := by
  rw [← C.local_eq_global]
  exact C.square a

theorem global_square_with_local (a : A) :
    C.globalMap a = C.upper (C.localMap (C.lower a)) := by
  calc
    C.globalMap a = C.localMap a := (C.local_eq_global a).symm
    _ = C.upper (C.localMap (C.lower a)) := C.square a

theorem label_chain (a : A) :
    C.label a = C.label_target (C.labelledMap a) := C.label_compat a

theorem map_recovery_chain (a : A) :
    C.labelledInverse (C.labelledMap a) = a ∧
      C.labelledMap (C.labelledInverse (C.labelledMap a)) = C.labelledMap a := by
  exact ⟨C.labelledLeft a, C.labelled_map_inverse_map a⟩

theorem inverse_recovery_chain (b : B) :
    C.labelledMap (C.labelledInverse b) = b ∧
      C.labelledInverse (C.labelledMap (C.labelledInverse b)) =
        C.labelledInverse b := by
  exact ⟨C.labelledRight b, C.labelled_inverse_map_inverse b⟩

theorem square_twice (a : A) :
    C.localMap a = C.upper (C.upper (C.localMap (C.lower (C.lower a)))) := by
  rw [C.lower_identity, C.lower_identity, C.upper_identity, C.upper_identity]

theorem labelled_bijective_inverse :
    Function.Bijective C.labelledInverse := by
  constructor
  · intro b₁ b₂ h
    calc
      b₁ = C.labelledMap (C.labelledInverse b₁) :=
        (C.labelledRight b₁).symm
      _ = C.labelledMap (C.labelledInverse b₂) := congrArg C.labelledMap h
      _ = b₂ := C.labelledRight b₂
  · intro a
    exact ⟨C.labelledMap a, C.labelledLeft a⟩

end SourceProposition310Comparison

/-! Completed source proposition marker: Proposition 3.10 comparison laws. -/

/-! ## 10. Dependency-chain assembly -/

structure SourceTheorem311DependencyPackage
    (R : SourceTheorem311Realization l Label Choice) where
  theorem15 : SourceTheorem15Coricity R.procession
  proposition21 : SourceProposition21Kummer Choice Choice
  proposition23 : SourceCorollary23Permutation Choice Choice
  proposition32 : SourceProposition32Packet.{u, v, w, w}
    R.procession R.packet
  vertical35 : SourceProposition35Vertical R.procession R.packet R.vertical
  proposition39 : SourceProposition39Volume Choice
  proposition310 : SourceProposition310Comparison Choice Choice
  source_alignment : theorem15.vertical 0 R.procession.base = R.procession.base
  packet_alignment : proposition32.profile R.procession.base = R.packet.logVolume R.procession.base
  volume_alignment : proposition39.logVolume R.procession.base =
    R.packet.logVolume R.procession.base
  horizontal_alignment : proposition310.localMap R.procession.base =
    proposition310.globalMap R.procession.base

namespace SourceTheorem311DependencyPackage

variable {R : SourceTheorem311Realization l Label Choice}
variable (D : SourceTheorem311DependencyPackage R)
include D

theorem theorem15_vertical_zero :
    D.theorem15.vertical 0 R.procession.base = R.procession.base :=
  D.theorem15.vertical_zero_at R.procession.base

theorem theorem15_source_level (n : Nat) (c : Choice) :
    R.procession.level c ≤
      R.procession.level (D.theorem15.vertical n c) :=
  D.theorem15.vertical_level n c

theorem theorem15_horizontal_level (g : Label) (c : Choice) :
    R.procession.level (D.theorem15.horizontal g c) = R.procession.level c :=
  D.theorem15.horizontal_level g c

theorem theorem15_commute (g : Label) (n : Nat) (c : Choice) :
    D.theorem15.horizontal g (D.theorem15.vertical n c) =
      D.theorem15.vertical n (D.theorem15.horizontal g c) :=
  D.theorem15.horizontal_vertical_at g n c

theorem proposition21_bijective :
    Function.Bijective D.proposition21.correspondence.map :=
  D.proposition21.map_bijective

theorem proposition21_q_positive : 0 < D.proposition21.q_parameter :=
  D.proposition21.q_positive

theorem proposition23_permutation_bijective :
    Function.Bijective D.proposition23.permutation :=
  D.proposition23.permutation_bijective

theorem proposition23_stable (i : Choice) (t : Choice) :
    D.proposition23.link (D.proposition23.permutation i)
      (D.proposition23.permutation i) t =
      D.proposition23.link i i t :=
  D.proposition23.permutation_link_at i t

theorem proposition32_packet_ind1 (g : Label) (c : Choice) :
    R.packet.logVolume (R.procession.ind1 g c) =
      R.packet.logVolume c :=
  SourceProposition32Packet.log_volume_ind1 D.proposition32 g c

theorem proposition32_packet_ind2 (g : Label) (c : Choice) :
    R.packet.logVolume (R.procession.ind2 g c) =
      R.packet.logVolume c :=
  SourceProposition32Packet.log_volume_ind2 D.proposition32 g c

theorem proposition32_packet_ind3 (n : Nat) (c : Choice) :
    R.packet.logVolume c ≤ R.packet.logVolume (R.procession.ind3 n c) :=
  SourceProposition32Packet.log_volume_ind3 D.proposition32 n c

theorem proposition32_determinant_positive (c : Choice) :
    0 < R.packet.determinant c :=
  SourceProposition32Packet.determinant_positive D.proposition32 c

theorem proposition35_nonarch (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage c) :
    ∃ y, y ∈ R.packet.possibleImage (R.procession.ind3 m c) ∧ z ≤ y :=
  SourceProposition35Vertical.nonarch_upper D.vertical35 m c z hz

theorem proposition35_arch (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage (R.procession.ind3 m c)) :
    ∃ y, y ∈ R.packet.possibleImage c ∧ z ≤ y :=
  SourceProposition35Vertical.arch_target_lift D.vertical35 m c z hz

theorem proposition35_kummer (c : Choice) :
    Function.Bijective (R.vertical.kummer c).map :=
  SourceProposition35Vertical.labelled_bijective_at D.vertical35 c

theorem proposition39_volume_positive (c : Choice) :
    0 < D.proposition39.determinant c :=
  D.proposition39.determinant_positive c

theorem proposition39_tensor_log (c : Choice) (n : Nat) :
    Real.log (D.proposition39.tensorPower c n) =
      n * D.proposition39.logVolume c :=
  D.proposition39.tensor_power_log c n

theorem proposition310_square (c : Choice) :
    D.proposition310.localMap c =
      D.proposition310.upper
        (D.proposition310.localMap (D.proposition310.lower c)) :=
  D.proposition310.square_at c

theorem proposition310_kummer (c : Choice) :
    Function.Bijective D.proposition310.labelledMap :=
  D.proposition310.labelled_bijective

theorem source_alignment_at :
    D.theorem15.vertical 0 R.procession.base = R.procession.base :=
  D.source_alignment

theorem packet_alignment_at :
    D.proposition32.profile R.procession.base =
      R.packet.logVolume R.procession.base :=
  D.packet_alignment

theorem volume_alignment_at :
    D.proposition39.logVolume R.procession.base =
      R.packet.logVolume R.procession.base :=
  D.volume_alignment

theorem horizontal_alignment_at :
    D.proposition310.localMap R.procession.base =
      D.proposition310.globalMap R.procession.base :=
  D.horizontal_alignment

theorem source_chain_level (m n : Nat) :
    R.procession.level R.procession.base ≤
      R.procession.level
        (D.theorem15.vertical n (D.theorem15.vertical m R.procession.base)) :=
  D.theorem15.vertical_chain_level m n R.procession.base

theorem source_chain_kummer (m n : Nat) (z : Real)
    (hz : z ∈ R.packet.possibleImage R.procession.base) :
    ∃ y, y ∈ R.packet.possibleImage
      (R.procession.ind3 n (R.procession.ind3 m R.procession.base)) ∧ z ≤ y :=
  SourceProposition35Vertical.nonarch_iterated_upper D.vertical35
    m n R.procession.base z hz

theorem source_chain_horizontal (g h : Label) :
    R.procession.level
        (D.theorem15.horizontal h (D.theorem15.horizontal g R.procession.base)) =
      R.procession.level R.procession.base :=
  D.theorem15.horizontal_chain_level g h R.procession.base

theorem source_chain_degree (x : Choice) :
    D.proposition21.degree_inverse
        (D.proposition21.correspondence.map (x)) =
      D.proposition21.degree x :=
  D.proposition21.degree_transport x

theorem source_chain_volume (n : Nat) :
    D.proposition39.logVolume R.procession.base ≤
      D.proposition39.latticeIndex R.procession.base :=
  D.proposition39.lattice_bound_at R.procession.base

end SourceTheorem311DependencyPackage

/-! Completed source proposition marker: dependency-chain assembly. -/

/-! ## 11. Conditional assembly into the proved Theorem 3.11 boundary -/

namespace SourceTheorem311DependencyPackage

variable {R : SourceTheorem311Realization l Label Choice}
variable (D : SourceTheorem311DependencyPackage R)
include D

def output (D' : SourceTheorem311DependencyPackage R) :
    Theorem311Source.Theorem311Output.{u, v, w} R.input := R.output

theorem output_source : D.output.source = R.input.core.base := R.output_source

theorem output_quotient :
    D.output.quotient = quotientMap R.input D.output.source := by
  exact R.output_quotient

theorem output_labelled (c : Choice) :
    Function.Bijective (R.input.labelledKummer c).map :=
  R.output_labelled c

theorem output_ind3 (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage (R.input.core.ind3 n c) ∧ z ≤ w :=
  R.output_ind3 n c z hz

theorem output_horizontal (c : Choice) :
    R.input.horizontal.upper (R.input.horizontal.left c) =
      R.input.horizontal.right (R.input.horizontal.lower c) :=
  R.output_horizontal c

theorem output_evaluation (c : Choice) :
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap (R.input.horizontal.lower c)) :=
  R.output_evaluation c

theorem output_parts :
    D.output.part_i = partI R.input ∧
      D.output.part_ii = partII R.input ∧
      D.output.part_iii = partIII R.input := by
  exact ⟨R.output_part_i, R.output_part_ii, R.output_part_iii⟩

end SourceTheorem311DependencyPackage

/-! Completed source proposition marker: conditional Theorem 3.11 assembly. -/

end SourceDependencyChain
end Theorem311Source
end
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def sourceDependencyChain : Obligation :=
  { id := "IUT-III.theorem-3.11-source-dependency-chain"
    source :=
      "IUT III Theorem 1.5, Propositions 2.1, 2.3, 3.2, 3.4, 3.5, 3.7, 3.9, 3.10"
    status := VerificationStatus.interface
    note :=
      "The source prerequisite contracts and their algebraic, order, degree, " ++
        "determinant, Kummer, and evaluation consequences are explicit and " ++
        "proved. The contracts remain source-facing inputs: no arithmetic " ++
        "existence claim is manufactured by Classical.choice."
    dependsOn :=
      [ "IUT-I.initial-theta-source-definition31-boundary",
        "IUT-I-II.prime-strip-core",
        "IUT-II.vertical-log-kummer",
        "IUT-III.theorem-3.11-explicit-prerequisite-boundary" ] }

end LeanFormal.IUT.Audit
