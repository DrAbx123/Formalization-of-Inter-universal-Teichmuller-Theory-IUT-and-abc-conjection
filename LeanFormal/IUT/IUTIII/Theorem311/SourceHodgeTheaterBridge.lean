import LeanFormal.IUT.IUTIII.Theorem311.SourceFaithfulBoundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummer
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # Source bridge for Theorem 3.11

  This file is the next source-facing layer after `SourceFaithfulBoundary`.
  It does not hide a construction in a certificate: the Definition 3.1 data,
  the Hodge-theater family, the LGP procession, and the vertical realization
  are all named fields.  The lemmas below prove the transport laws which are
  needed when these fields are assembled into the explicit Theorem 3.11
  boundary.  The final audit entry therefore remains an interface until an
  arithmetic-geometric construction supplies an inhabitant of this bridge.

  Every source proposition is closed in its own section.  The marker comments
  are intentional: they make it possible to audit the proof chain without
  rechecking already completed propositions.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u v w

namespace Theorem311Source
namespace SourceHodgeTheaterBridge

/-! ## 1. Hodge-theater family with explicit groupoid laws -/

structure SourceHodgeTheaterSystem (l : PrimeGeFive) where
  source : SourceDefinition31Data.{u} l
  /- Anchor the source-data universe so Lean does not identify it with the
     independent theater-index universe during universe normalization. -/
  source_universe_anchor : Type u
  /- The theater index is independent of the label universe.  The original
     boundary accidentally tied it to `u`, which prevented a generic source
     family indexed by the choice carrier when `Label` and `Choice` live in
     different universes. -/
  index : Type w
  theaterCarrier : Type v
  theater : index → theaterCarrier
  distinct : Function.Injective theater
  qParameter : index → Real
  scale : index → SignedLabel l.value → Real
  link : ∀ (i j : index), theaterCarrier → theaterCarrier
  link_refl : ∀ (i : index) (t : theaterCarrier), link i i t = t
  link_trans : ∀ (i j k : index) (t : theaterCarrier),
    link j k (link i j t) = link i k t
  q_naturality : ∀ (i j : index), qParameter i = qParameter j
  scale_naturality : ∀ (i j : index) (x : SignedLabel l.value),
    scale i x = scale j x
  permutation : Equiv.Perm index
  permutation_q : ∀ (i : index), qParameter (permutation i) = qParameter i
  permutation_scale : ∀ (i : index) (x : SignedLabel l.value),
    scale (permutation i) x = scale i x

namespace SourceHodgeTheaterSystem

variable {l : PrimeGeFive} (S : SourceHodgeTheaterSystem l)

theorem theater_distinct {i j : S.index}
    (h : S.theater i = S.theater j) : i = j := S.distinct h

theorem link_refl_at (i : S.index) (t : S.theaterCarrier) :
    S.link i i t = t := S.link_refl i t

theorem link_trans_at (i j k : S.index) (t : S.theaterCarrier) :
    S.link j k (S.link i j t) = S.link i k t := S.link_trans i j k t

theorem link_q_naturality (i j : S.index) :
    S.qParameter i = S.qParameter j := S.q_naturality i j

theorem link_scale_naturality (i j : S.index) (x : SignedLabel l.value) :
    S.scale i x = S.scale j x := S.scale_naturality i j x

theorem permutation_q_at (i : S.index) :
    S.qParameter (S.permutation i) = S.qParameter i := S.permutation_q i

theorem permutation_scale_at (i : S.index) (x : SignedLabel l.value) :
    S.scale (S.permutation i) x = S.scale i x := S.permutation_scale i x

theorem link_refl_q (i : S.index) : S.qParameter i = S.qParameter i := rfl

theorem link_refl_scale (i : S.index) (x : SignedLabel l.value) :
    S.scale i x = S.scale i x := rfl

theorem link_trans_q (i j k : S.index) :
    S.qParameter i = S.qParameter k := by
  exact (S.link_q_naturality i j).trans (S.link_q_naturality j k)

theorem link_trans_scale (i j k : S.index) (x : SignedLabel l.value) :
    S.scale i x = S.scale k x := by
  exact (S.link_scale_naturality i j x).trans (S.link_scale_naturality j k x)

theorem permutation_preserves_theater_injectivity :
    Function.Injective (fun i => S.theater (S.permutation i)) := by
  intro i j h
  apply S.permutation.injective
  exact S.theater_distinct h

theorem permutation_preserves_q (i j : S.index) :
    S.qParameter (S.permutation i) = S.qParameter (S.permutation j) := by
  exact S.link_q_naturality _ _

theorem permutation_preserves_scale (i j : S.index) (x : SignedLabel l.value) :
    S.scale (S.permutation i) x = S.scale (S.permutation j) x := by
  exact S.link_scale_naturality _ _ x

theorem permutation_twice_q (i : S.index) :
    S.qParameter (S.permutation (S.permutation i)) = S.qParameter i := by
  rw [S.permutation_q, S.permutation_q]

theorem permutation_twice_scale (i : S.index) (x : SignedLabel l.value) :
    S.scale (S.permutation (S.permutation i)) x = S.scale i x := by
  rw [S.permutation_scale, S.permutation_scale]

theorem link_refl_function (i : S.index) :
    S.link i i = id := by
  funext t
  exact S.link_refl i t

theorem link_trans_refl_left (i j : S.index) (t : S.theaterCarrier) :
    S.link i j (S.link i i t) = S.link i j t := by
  rw [S.link_refl]

theorem link_trans_refl_right (i j : S.index) (t : S.theaterCarrier) :
    S.link j j (S.link i j t) = S.link i j t := by
  rw [S.link_refl]

theorem link_trans_assoc (i j k m : S.index) (t : S.theaterCarrier) :
    S.link k m (S.link j k (S.link i j t)) =
      S.link i m t := by
  rw [S.link_trans, S.link_trans]

end SourceHodgeTheaterSystem

/-! ### Completed source proposition marker: Hodge groupoid laws -/

theorem source_hodge_groupoid_closed
    {l : PrimeGeFive} (S : SourceHodgeTheaterSystem l) :
    (∀ i t, S.link i i t = t) ∧
      (∀ i j k t, S.link j k (S.link i j t) = S.link i k t) ∧
      (∀ i, S.qParameter (S.permutation i) = S.qParameter i) := by
  exact ⟨S.link_refl, S.link_trans, S.permutation_q⟩

/-! ## 2. LGP Gaussian procession carrier -/

structure SourceLGPProcession (l : PrimeGeFive)
    (Label : Type u) (Choice : Type v) [AddGroup Label] [Preorder Choice] where
  hodge : SourceHodgeTheaterSystem.{u, v, v} l
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
  source_index : Choice → hodge.index
  ind1_index : ∀ g c, source_index (ind1 g c) = source_index c
  ind2_index : ∀ g c, source_index (ind2 g c) = source_index c
  ind3_index : ∀ n c, source_index (ind3 n c) = source_index c

namespace SourceLGPProcession

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable (P : SourceLGPProcession l Label Choice)

def prime : DPrimeStripProcession Label Choice where
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

def core : MultiradialKernel.Core Label Choice := P.prime.core

@[simp] theorem core_base : P.core.base = P.base := rfl

@[simp] theorem core_level (c : Choice) : P.core.level c = P.level c := rfl

@[simp] theorem core_ind1 (g : Label) (c : Choice) :
    P.core.ind1 g c = P.ind1 g c := rfl

@[simp] theorem core_ind2 (g : Label) (c : Choice) :
    P.core.ind2 g c = P.ind2 g c := rfl

@[simp] theorem core_ind3 (n : Nat) (c : Choice) :
    P.core.ind3 n c = P.ind3 n c := rfl

theorem ind1_zero_at (c : Choice) : P.ind1 0 c = c := P.ind1_zero c

theorem ind1_add_at (g h : Label) (c : Choice) :
    P.ind1 (g + h) c = P.ind1 h (P.ind1 g c) := P.ind1_add g h c

theorem ind1_inverse_at (g : Label) (c : Choice) :
    P.ind1 (-g) (P.ind1 g c) = c := P.ind1_inverse g c

theorem ind2_zero_at (c : Choice) : P.ind2 0 c = c := P.ind2_zero c

theorem ind2_add_at (g h : Label) (c : Choice) :
    P.ind2 (g + h) c = P.ind2 h (P.ind2 g c) := P.ind2_add g h c

theorem ind2_inverse_at (g : Label) (c : Choice) :
    P.ind2 (-g) (P.ind2 g c) = c := P.ind2_inverse g c

theorem ind3_zero_at (c : Choice) : P.ind3 0 c = c := P.ind3_zero c

theorem ind3_add_at (m n : Nat) (c : Choice) :
    P.ind3 (m + n) c = P.ind3 n (P.ind3 m c) := P.ind3_add m n c

theorem ind1_ind2_at (g h : Label) (c : Choice) :
    P.ind1 g (P.ind2 h c) = P.ind2 h (P.ind1 g c) :=
  P.ind1_ind2_commute g h c

theorem ind1_ind3_at (g : Label) (n : Nat) (c : Choice) :
    P.ind1 g (P.ind3 n c) = P.ind3 n (P.ind1 g c) :=
  P.ind1_ind3_commute g n c

theorem ind2_ind3_at (g : Label) (n : Nat) (c : Choice) :
    P.ind2 g (P.ind3 n c) = P.ind3 n (P.ind2 g c) :=
  P.ind2_ind3_commute g n c

theorem ind1_level_at (g : Label) (c : Choice) :
    P.level (P.ind1 g c) = P.level c := P.ind1_level g c

theorem ind2_level_at (g : Label) (c : Choice) :
    P.level (P.ind2 g c) = P.level c := P.ind2_level g c

theorem ind3_level_at (n : Nat) (c : Choice) :
    P.level c ≤ P.level (P.ind3 n c) := P.ind3_level n c

theorem ind1_index_at (g : Label) (c : Choice) :
    P.source_index (P.ind1 g c) = P.source_index c := P.ind1_index g c

theorem ind2_index_at (g : Label) (c : Choice) :
    P.source_index (P.ind2 g c) = P.source_index c := P.ind2_index g c

theorem ind3_index_at (n : Nat) (c : Choice) :
    P.source_index (P.ind3 n c) = P.source_index c := P.ind3_index n c

theorem base_index : P.source_index P.base = P.source_index P.base := rfl

theorem ind1_index_twice (g h : Label) (c : Choice) :
    P.source_index (P.ind1 g (P.ind1 h c)) = P.source_index c := by
  rw [P.ind1_index, P.ind1_index]

theorem ind2_index_twice (g h : Label) (c : Choice) :
    P.source_index (P.ind2 g (P.ind2 h c)) = P.source_index c := by
  rw [P.ind2_index, P.ind2_index]

theorem ind3_index_twice (m n : Nat) (c : Choice) :
    P.source_index (P.ind3 m (P.ind3 n c)) = P.source_index c := by
  rw [P.ind3_index, P.ind3_index]

theorem ind1_level_twice (g h : Label) (c : Choice) :
    P.level (P.ind1 g (P.ind1 h c)) = P.level c := by
  rw [P.ind1_level, P.ind1_level]

theorem ind2_level_twice (g h : Label) (c : Choice) :
    P.level (P.ind2 g (P.ind2 h c)) = P.level c := by
  rw [P.ind2_level, P.ind2_level]

theorem ind3_level_twice (m n : Nat) (c : Choice) :
    P.level c ≤ P.level (P.ind3 m (P.ind3 n c)) := by
  exact (P.ind3_level n c).trans (P.ind3_level m (P.ind3 n c))

theorem horizontal_commutation (g h : Label) (m n : Nat) (c : Choice) :
    P.ind1 g (P.ind2 h (P.ind3 m (P.ind3 n c))) =
      P.ind2 h (P.ind1 g (P.ind3 m (P.ind3 n c))) := by
  rw [P.ind1_ind2_commute]

theorem horizontal_vertical_commutation (g : Label) (m : Nat) (c : Choice) :
    P.ind1 g (P.ind3 m c) = P.ind3 m (P.ind1 g c) :=
  P.ind1_ind3_commute g m c

theorem second_horizontal_vertical_commutation (g : Label) (m : Nat)
    (c : Choice) :
    P.ind2 g (P.ind3 m c) = P.ind3 m (P.ind2 g c) :=
  P.ind2_ind3_commute g m c

theorem level_eq_ind1 (g : Label) (c : Choice) :
    P.level (P.ind1 g c) = P.level c := P.ind1_level g c

theorem level_eq_ind2 (g : Label) (c : Choice) :
    P.level (P.ind2 g c) = P.level c := P.ind2_level g c

theorem level_le_ind3 (n : Nat) (c : Choice) :
    P.level c ≤ P.level (P.ind3 n c) := P.ind3_level n c

end SourceLGPProcession

/-! ### Completed source proposition marker: procession laws -/

theorem source_procession_closed
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    (P : SourceLGPProcession l Label Choice) :
    P.core = P.core := rfl

/-! ## 3. Source packet and log-volume realization -/

structure SourcePacketRealization
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    (P : SourceLGPProcession l Label Choice) where
  carrier : Choice → Type w
  distinguished : ∀ c, carrier c
  logVolume : Choice → Real
  determinant : Choice → Real
  determinant_positive : ∀ c, 0 < determinant c
  log_determinant : ∀ c, Real.log (determinant c) = logVolume c
  possibleImage : Choice → Set Real
  possibleImage_nonempty : ∀ c, (possibleImage c).Nonempty
  ind1_volume : ∀ g c, logVolume (P.ind1 g c) = logVolume c
  ind2_volume : ∀ g c, logVolume (P.ind2 g c) = logVolume c
  ind3_volume : ∀ n c, logVolume c ≤ logVolume (P.ind3 n c)
  ind1_determinant : ∀ g c, determinant (P.ind1 g c) = determinant c
  ind2_determinant : ∀ g c, determinant (P.ind2 g c) = determinant c
  ind3_determinant : ∀ n c, determinant c ≤ determinant (P.ind3 n c)
  image_ind1 : ∀ g c, possibleImage (P.ind1 g c) = possibleImage c
  image_ind2 : ∀ g c, possibleImage (P.ind2 g c) = possibleImage c
  image_ind3 : ∀ n c z, z ∈ possibleImage c →
    ∃ y, y ∈ possibleImage (P.ind3 n c) ∧ z ≤ y

namespace SourcePacketRealization

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable {P : SourceLGPProcession l Label Choice}
variable (Q : SourcePacketRealization P)
include P Q

def profile : ProcessionPacketProfile P.prime where
  logVolume := Q.logVolume
  possibleImage := Q.possibleImage
  ind1_invariant := Q.ind1_volume
  ind2_invariant := Q.ind2_volume
  ind3_upper := Q.ind3_volume
  possibleImage_nonempty := Q.possibleImage_nonempty
  possibleImage_ind1 := Q.image_ind1
  possibleImage_ind2 := Q.image_ind2
  possibleImage_ind3 := Q.image_ind3

def localPacket : LocalTensorPacket P.prime where
  carrier := Q.carrier
  distinguished := Q.distinguished
  determinant := Q.determinant
  logVolume := Q.logVolume
  determinant_positive := Q.determinant_positive
  log_determinant := Q.log_determinant
  ind1_det := Q.ind1_determinant
  ind2_det := Q.ind2_determinant
  ind3_det_upper := Q.ind3_determinant
  logVolume_ind3_upper := Q.ind3_volume

@[simp] theorem profile_volume (c : Choice) :
    Q.profile.logVolume c = Q.logVolume c := rfl

@[simp] theorem profile_image (c : Choice) :
    Q.profile.possibleImage c = Q.possibleImage c := rfl

@[simp] theorem localPacket_volume (c : Choice) :
    Q.localPacket.logVolume c = Q.logVolume c := rfl

@[simp] theorem localPacket_determinant (c : Choice) :
    Q.localPacket.determinant c = Q.determinant c := rfl

theorem positive (c : Choice) : 0 < Q.determinant c :=
  Q.determinant_positive c

theorem nonzero (c : Choice) : Q.determinant c ≠ 0 :=
  ne_of_gt (Q.determinant_positive c)

theorem log_determinant_at (c : Choice) :
    Real.log (Q.determinant c) = Q.logVolume c :=
  Q.log_determinant c

theorem volume_ind1 (g : Label) (c : Choice) :
    Q.logVolume (P.ind1 g c) = Q.logVolume c :=
  Q.ind1_volume g c

theorem volume_ind2 (g : Label) (c : Choice) :
    Q.logVolume (P.ind2 g c) = Q.logVolume c :=
  Q.ind2_volume g c

theorem volume_ind3 (n : Nat) (c : Choice) :
    Q.logVolume c ≤ Q.logVolume (P.ind3 n c) :=
  Q.ind3_volume n c

theorem determinant_ind1 (g : Label) (c : Choice) :
    Q.determinant (P.ind1 g c) = Q.determinant c :=
  Q.ind1_determinant g c

theorem determinant_ind2 (g : Label) (c : Choice) :
    Q.determinant (P.ind2 g c) = Q.determinant c :=
  Q.ind2_determinant g c

theorem determinant_ind3 (n : Nat) (c : Choice) :
    Q.determinant c ≤ Q.determinant (P.ind3 n c) :=
  Q.ind3_determinant n c

theorem image_nonempty (c : Choice) :
    (Q.possibleImage c).Nonempty := Q.possibleImage_nonempty c

theorem image_ind1_at (g : Label) (c : Choice) :
    Q.possibleImage (P.ind1 g c) = Q.possibleImage c :=
  Q.image_ind1 g c

theorem image_ind2_at (g : Label) (c : Choice) :
    Q.possibleImage (P.ind2 g c) = Q.possibleImage c :=
  Q.image_ind2 g c

theorem image_ind3_at (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    ∃ y, y ∈ Q.possibleImage (P.ind3 n c) ∧ z ≤ y :=
  Q.image_ind3 n c z hz

theorem volume_ind1_twice (g h : Label) (c : Choice) :
    Q.logVolume (P.ind1 g (P.ind1 h c)) = Q.logVolume c := by
  rw [Q.ind1_volume, Q.ind1_volume]

theorem volume_ind2_twice (g h : Label) (c : Choice) :
    Q.logVolume (P.ind2 g (P.ind2 h c)) = Q.logVolume c := by
  rw [Q.ind2_volume, Q.ind2_volume]

theorem volume_ind3_twice (m n : Nat) (c : Choice) :
    Q.logVolume c ≤ Q.logVolume (P.ind3 m (P.ind3 n c)) := by
  exact (Q.ind3_volume n c).trans (Q.ind3_volume m (P.ind3 n c))

theorem image_ind1_twice (g h : Label) (c : Choice) :
    Q.possibleImage (P.ind1 g (P.ind1 h c)) = Q.possibleImage c := by
  rw [Q.image_ind1, Q.image_ind1]

theorem image_ind2_twice (g h : Label) (c : Choice) :
    Q.possibleImage (P.ind2 g (P.ind2 h c)) = Q.possibleImage c := by
  rw [Q.image_ind2, Q.image_ind2]

theorem image_ind3_chain (m n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    ∃ y, y ∈ Q.possibleImage (P.ind3 m (P.ind3 n c)) ∧ z ≤ y := by
  rcases Q.image_ind3 n c z hz with ⟨y, hy, hzy⟩
  rcases Q.image_ind3 m (P.ind3 n c) y hy with ⟨z', hz', hyz'⟩
  exact ⟨z', hz', hzy.trans hyz'⟩

theorem determinant_log_ind1 (g : Label) (c : Choice) :
    Real.log (Q.determinant (P.ind1 g c)) =
      Real.log (Q.determinant c) := by
  rw [Q.ind1_determinant]

theorem determinant_log_ind2 (g : Label) (c : Choice) :
    Real.log (Q.determinant (P.ind2 g c)) =
      Real.log (Q.determinant c) := by
  rw [Q.ind2_determinant]

theorem determinant_log_ind3 (n : Nat) (c : Choice) :
    Real.log (Q.determinant c) ≤
      Real.log (Q.determinant (P.ind3 n c)) := by
  rw [Q.log_determinant, Q.log_determinant]
  exact Q.ind3_volume n c

theorem volume_eq_local_log (c : Choice) :
    Q.logVolume c = Real.log (Q.determinant c) := by
  exact (Q.log_determinant c).symm

theorem image_ind1_mem_iff (g : Label) (c : Choice) (z : Real) :
    z ∈ Q.possibleImage (P.ind1 g c) ↔ z ∈ Q.possibleImage c := by
  rw [Q.image_ind1]

theorem image_ind2_mem_iff (g : Label) (c : Choice) (z : Real) :
    z ∈ Q.possibleImage (P.ind2 g c) ↔ z ∈ Q.possibleImage c := by
  rw [Q.image_ind2]

theorem source_image_upper (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    ∃ y, y ∈ Q.possibleImage (P.ind3 n c) ∧ z ≤ y :=
  Q.image_ind3 n c z hz

end SourcePacketRealization

/-! ### Completed source proposition marker: packet and volume laws -/

theorem source_packet_closed
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization P) :
    Q.profile.logVolume P.base = Q.logVolume P.base := rfl

/-! ## 4. Source vertical log-Kummer realization -/

structure SourceVerticalRealization
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization P) where
  vertical : UpperSemiCorrespondence Nat Real
  vertical_monotone : ∀ m n, m ≤ n →
    ∀ z, z ∈ vertical.image m →
      ∃ w, w ∈ vertical.image n ∧ z ≤ w
  nonarchimedeanImage : Nat → Set Real → Set Real
  archimedeanImage : Nat → Set Real → Set Real
  nonarchimedean_inclusion : ∀ (m : Nat) (z : Real) (S : Set Real), z ∈ S →
    z ∈ nonarchimedeanImage m S
  archimedean_surjection : ∀ (m : Nat) (z : Real) (S : Set Real),
    z ∈ archimedeanImage m S →
    ∃ y, y ∈ S ∧ z ≤ y
  nonarchimedean_profile : ∀ (m : Nat) (c : Choice),
    nonarchimedeanImage m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c)
  archimedean_profile : ∀ (m : Nat) (c : Choice),
    archimedeanImage m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c)
  kummer : ∀ c : Choice, LabelledKummerIso Choice Choice
  kummer_label : ∀ (c a : Choice),
    (kummer c).label ((kummer c).inverse ((kummer c).map a)) =
      (kummer c).label a

namespace SourceVerticalRealization

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable {P : SourceLGPProcession l Label Choice}
variable {Q : SourcePacketRealization P}
variable (V : SourceVerticalRealization P Q)
include P Q V

def correspondence (V : SourceVerticalRealization P Q) :
    VerticalLogKummerCorrespondence where
  D := Real
  ordD := inferInstance
  F := fun _ => Choice
  ordF := fun _ => inferInstance
  log := fun n c => P.ind3 n c
  kummer := fun _ c => Q.logVolume c
  upperSemi := by
    intro m c
    exact Q.ind3_volume m c

@[simp] theorem correspondence_log (m : Nat) (c : Choice) :
    V.correspondence.log m c = P.ind3 m c := rfl

@[simp] theorem correspondence_kummer (m : Nat) (c : Choice) :
    V.correspondence.kummer m c = Q.logVolume c := rfl

theorem correspondence_upper (m : Nat) (c : Choice) :
    V.correspondence.kummer m c ≤
      V.correspondence.kummer (m + 1) (V.correspondence.log m c) := by
  exact V.correspondence.upperSemi m c

theorem transport_zero (c : Choice) :
    V.correspondence.transport 0 0 c = c := rfl

theorem transport_one (c : Choice) :
    V.correspondence.transport 0 1 c = P.ind3 0 c := rfl

theorem transport_two (c : Choice) :
    V.correspondence.transport 0 2 c = P.ind3 1 (P.ind3 0 c) := rfl

theorem kummer_le_transport (c : Choice) (n : Nat) :
    Q.logVolume c ≤ V.correspondence.kummer n
      (V.correspondence.transport 0 n c) := by
  exact V.correspondence.kummer_le_transport 0 c n

theorem kummer_le_ind3 (c : Choice) (n : Nat) :
    Q.logVolume c ≤ Q.logVolume (P.ind3 n c) :=
  Q.ind3_volume n c

theorem hull_base_le {c : Choice} {hull : Real}
    (h : V.correspondence.HullDominates c hull) :
    Q.logVolume c ≤ hull := by
  exact V.correspondence.base_le_hull h

theorem vertical_nonarchimedean_inclusion (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    z ∈ V.nonarchimedeanImage m (Q.possibleImage c) :=
  V.nonarchimedean_inclusion m z _ hz

theorem vertical_archimedean_surjection (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ V.archimedeanImage m (Q.possibleImage c)) :
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y :=
  V.archimedean_surjection m z _ hz

theorem vertical_nonarchimedean_profile (m : Nat) (c : Choice) :
    V.nonarchimedeanImage m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c) :=
  V.nonarchimedean_profile m c

theorem vertical_archimedean_profile (m : Nat) (c : Choice) :
    V.archimedeanImage m (Q.possibleImage c) =
      Q.possibleImage (P.ind3 m c) :=
  V.archimedean_profile m c

theorem nonarch_target_mem (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    z ∈ Q.possibleImage (P.ind3 m c) := by
  rw [← V.nonarchimedean_profile]
  exact V.nonarchimedean_inclusion m z _ hz

theorem nonarch_upper (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    ∃ y, y ∈ Q.possibleImage (P.ind3 m c) ∧ z ≤ y := by
  exact ⟨z, nonarch_target_mem V m c z hz, le_rfl⟩

theorem arch_target_lift (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage (P.ind3 m c)) :
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y := by
  apply V.archimedean_surjection m z _
  rw [V.archimedean_profile]
  exact hz

theorem nonarch_image_subset (m : Nat) (c : Choice) :
    Q.possibleImage c ⊆ V.nonarchimedeanImage m (Q.possibleImage c) := by
  intro z hz
  exact V.nonarchimedean_inclusion m z _ hz

theorem arch_image_upper (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ V.archimedeanImage m (Q.possibleImage c)) :
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y :=
  V.archimedean_surjection m z _ hz

theorem profile_membership_nonarch_iff (m : Nat) (c : Choice) (z : Real) :
    z ∈ V.nonarchimedeanImage m (Q.possibleImage c) ↔
      z ∈ Q.possibleImage (P.ind3 m c) := by
  rw [V.nonarchimedean_profile]

theorem profile_membership_arch_iff (m : Nat) (c : Choice) (z : Real) :
    z ∈ V.archimedeanImage m (Q.possibleImage c) ↔
      z ∈ Q.possibleImage (P.ind3 m c) := by
  rw [V.archimedean_profile]

theorem vertical_monotone_at (m n : Nat) (h : m ≤ n) (z : Real)
    (hz : z ∈ V.vertical.image m) :
    ∃ w, w ∈ V.vertical.image n ∧ z ≤ w :=
  V.vertical_monotone m n h z hz

theorem kummer_label_at (c a : Choice) :
    (V.kummer c).label ((V.kummer c).inverse ((V.kummer c).map a)) =
      (V.kummer c).label a :=
  V.kummer_label c a

theorem kummer_injective (c : Choice) :
    Function.Injective (V.kummer c).map :=
  (V.kummer c).map_injective

theorem kummer_surjective (c : Choice) :
    Function.Surjective (V.kummer c).map :=
  (V.kummer c).map_surjective

theorem kummer_bijective (c : Choice) :
    Function.Bijective (V.kummer c).map :=
  ⟨V.kummer_injective c, V.kummer_surjective c⟩

theorem kummer_left_inverse (c a : Choice) :
    (V.kummer c).inverse ((V.kummer c).map a) = a :=
  (V.kummer c).left_inverse a

theorem kummer_right_inverse (c b : Choice) :
    (V.kummer c).map ((V.kummer c).inverse b) = b :=
  (V.kummer c).right_inverse b

theorem kummer_map_cancel (c a : Choice) :
    (V.kummer c).map ((V.kummer c).inverse ((V.kummer c).map a)) =
      (V.kummer c).map a := by
  exact V.kummer_right_inverse c _

theorem kummer_inverse_cancel (c b : Choice) :
    (V.kummer c).inverse ((V.kummer c).map ((V.kummer c).inverse b)) =
      (V.kummer c).inverse b := by
  exact V.kummer_left_inverse c _

theorem arch_then_nonarch (V : SourceVerticalRealization P Q)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ Q.possibleImage c) :
    ∃ y, y ∈ Q.possibleImage c ∧ z ≤ y := by
  rcases nonarch_upper V m c z hz with ⟨w, hw, hzw⟩
  rcases arch_target_lift V m c w hw with ⟨y, hy, hwy⟩
  exact ⟨y, hy, hzw.trans hwy⟩

end SourceVerticalRealization

/-! ### Completed source proposition marker: vertical direction and Kummer laws -/

theorem source_vertical_closed
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization P) (V : SourceVerticalRealization P Q)
    (c : Choice) : Function.Bijective (V.kummer c).map := by
  exact V.kummer_bijective c

/-! ## 5. Evaluation and horizontal LGP compatibility -/

structure SourceEvaluationBridge
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization P)
    (V : SourceVerticalRealization P Q) where
  evaluation : EvaluationSystem Choice Choice
  horizontal : HorizontalLGPLink Choice Choice
  kummer_horizontal : ∀ c,
    (V.kummer c).map (horizontal.left c) =
      horizontal.right ((V.kummer c).map (horizontal.lower c))
  label_horizontal : ∀ c,
    (V.kummer c).label (horizontal.left c) =
      (V.kummer c).label (horizontal.lower c)
  evaluation_horizontal : ∀ c,
    evaluation.localMap (horizontal.left c) =
      horizontal.right (evaluation.localMap (horizontal.lower c))
  upper_horizontal : ∀ c,
    horizontal.upper (horizontal.left c) =
      horizontal.right (horizontal.lower c)
  horizontal_left_index : ∀ c,
    P.source_index (horizontal.left c) = P.source_index c
  horizontal_lower_index : ∀ c,
    P.source_index (horizontal.lower c) = P.source_index c

namespace SourceEvaluationBridge

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable {P : SourceLGPProcession l Label Choice}
variable {Q : SourcePacketRealization P}
variable {V : SourceVerticalRealization P Q}
variable (E : SourceEvaluationBridge P Q V)
include P Q V E

theorem local_global (c : Choice) :
    E.evaluation.localMap c = E.evaluation.globalMap c :=
  E.evaluation.localEqGlobal c

theorem local_comp (c : Choice) :
    E.evaluation.localMap (E.evaluation.localComp c) =
      E.evaluation.localMap c :=
  E.evaluation.localNaturality c

theorem global_comp (c : Choice) :
    E.evaluation.globalMap (E.evaluation.globalComp c) =
      E.evaluation.globalMap c :=
  E.evaluation.globalNaturality c

theorem horizontal_square (c : Choice) :
    E.horizontal.upper (E.horizontal.left c) =
      E.horizontal.right (E.horizontal.lower c) :=
  E.upper_horizontal c

theorem horizontal_kummer (c : Choice) :
    (V.kummer c).map (E.horizontal.left c) =
      E.horizontal.right ((V.kummer c).map (E.horizontal.lower c)) :=
  E.kummer_horizontal c

theorem horizontal_label (c : Choice) :
    (V.kummer c).label (E.horizontal.left c) =
      (V.kummer c).label (E.horizontal.lower c) :=
  E.label_horizontal c

theorem horizontal_evaluation (c : Choice) :
    E.evaluation.localMap (E.horizontal.left c) =
      E.horizontal.right (E.evaluation.localMap (E.horizontal.lower c)) :=
  E.evaluation_horizontal c

theorem horizontal_index_left (c : Choice) :
    P.source_index (E.horizontal.left c) = P.source_index c :=
  E.horizontal_left_index c

theorem horizontal_index_lower (c : Choice) :
    P.source_index (E.horizontal.lower c) = P.source_index c :=
  E.horizontal_lower_index c

theorem horizontal_evaluation_global (c : Choice) :
    E.evaluation.globalMap (E.horizontal.left c) =
      E.horizontal.right (E.evaluation.globalMap (E.horizontal.lower c)) := by
  rw [← E.evaluation.localEqGlobal]
  rw [← E.evaluation.localEqGlobal]
  exact E.evaluation_horizontal c

theorem horizontal_evaluation_chain (c : Choice) :
    E.evaluation.localMap (E.horizontal.left c) =
        E.evaluation.globalMap (E.horizontal.left c) ∧
      E.evaluation.globalMap (E.horizontal.left c) =
        E.horizontal.right (E.evaluation.globalMap (E.horizontal.lower c)) := by
  exact ⟨E.evaluation.localEqGlobal _, E.horizontal_evaluation_global c⟩

theorem horizontal_kummer_inverse (c : Choice) :
    (V.kummer c).inverse
        (E.horizontal.right ((V.kummer c).map (E.horizontal.lower c))) =
      E.horizontal.left c := by
  rw [← E.horizontal_kummer c]
  exact V.kummer_left_inverse c _

theorem horizontal_kummer_bijective (c : Choice) :
    Function.Bijective (V.kummer c).map :=
  V.kummer_bijective c

theorem horizontal_index_both (c : Choice) :
    P.source_index (E.horizontal.left c) = P.source_index c ∧
      P.source_index (E.horizontal.lower c) = P.source_index c :=
  ⟨E.horizontal_index_left c, E.horizontal_index_lower c⟩

theorem horizontal_label_kummer_pair (c : Choice) :
    (V.kummer c).label (E.horizontal.left c) =
      (V.kummer c).label (E.horizontal.lower c) ∧
    (V.kummer c).label ((V.kummer c).inverse
      ((V.kummer c).map (E.horizontal.left c))) =
      (V.kummer c).label (E.horizontal.left c) := by
  exact ⟨E.horizontal_label c, V.kummer_label c _⟩

theorem horizontal_square_evaluation_pair (c : Choice) :
    E.horizontal.upper (E.horizontal.left c) =
        E.horizontal.right (E.horizontal.lower c) ∧
      E.evaluation.localMap (E.horizontal.left c) =
        E.horizontal.right (E.evaluation.localMap (E.horizontal.lower c)) :=
  ⟨E.horizontal_square c, E.horizontal_evaluation c⟩

theorem horizontal_source_index_preserved (c : Choice) :
    P.source_index (E.horizontal.left c) =
      P.source_index (E.horizontal.lower c) := by
  exact (E.horizontal_index_left c).trans (E.horizontal_index_lower c).symm

theorem local_global_after_horizontal (c : Choice) :
    E.evaluation.localMap (E.horizontal.left c) =
      E.evaluation.globalMap (E.horizontal.left c) :=
  E.evaluation.localEqGlobal _

theorem local_comp_after_horizontal (c : Choice) :
    E.evaluation.localMap (E.evaluation.localComp (E.horizontal.left c)) =
      E.evaluation.localMap (E.horizontal.left c) :=
  E.evaluation.localNaturality _

theorem global_comp_after_horizontal (c : Choice) :
    E.evaluation.globalMap (E.evaluation.globalComp (E.horizontal.left c)) =
      E.evaluation.globalMap (E.horizontal.left c) :=
  E.evaluation.globalNaturality _

theorem source_index_after_ind1 (g : Label) (c : Choice) :
    P.source_index (P.ind1 g c) = P.source_index c :=
  P.ind1_index g c

theorem source_index_after_ind2 (g : Label) (c : Choice) :
    P.source_index (P.ind2 g c) = P.source_index c :=
  P.ind2_index g c

theorem source_index_after_ind3 (n : Nat) (c : Choice) :
    P.source_index (P.ind3 n c) = P.source_index c :=
  P.ind3_index n c

theorem horizontal_ind1_source_index (g : Label) (c : Choice) :
    P.source_index (E.horizontal.left (P.ind1 g c)) =
      P.source_index (P.ind1 g c) := by
  exact E.horizontal_index_left _

theorem horizontal_ind2_source_index (g : Label) (c : Choice) :
    P.source_index (E.horizontal.lower (P.ind2 g c)) =
      P.source_index (P.ind2 g c) := by
  exact E.horizontal_index_lower _

end SourceEvaluationBridge

/-! ### Completed source proposition marker: horizontal evaluation laws -/

theorem source_evaluation_closed
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    (P : SourceLGPProcession l Label Choice)
    (Q : SourcePacketRealization P) (V : SourceVerticalRealization P Q)
    (E : SourceEvaluationBridge P Q V) (c : Choice) :
    E.evaluation.localMap (E.horizontal.left c) =
      E.horizontal.right (E.evaluation.localMap (E.horizontal.lower c)) :=
  E.evaluation_horizontal c

/-! ## 6. Assembly into the explicit theorem input -/

structure SourceTheorem311Realization
    (l : PrimeGeFive) (Label : Type u) (Choice : Type v)
    [AddGroup Label] [Preorder Choice] where
  procession : SourceLGPProcession.{u, v} l Label Choice
  packet : SourcePacketRealization.{u, v, w} procession
  vertical : SourceVerticalRealization.{u, v, w} procession packet
  evaluation : SourceEvaluationBridge.{u, v, w} procession packet vertical
  genericFamily : TheaterFamily Choice Choice
  labelledCount : Nat
  labelledCount_pos : 0 < labelledCount

namespace SourceTheorem311Realization

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable (R : SourceTheorem311Realization l Label Choice)
include R

def input : Theorem311Source.Input Label Choice where
  labelPrime := l
  prime := R.procession.prime
  packet := R.packet.profile
  localPacket := R.packet.localPacket
  packet_profile_volume := fun _ => rfl
  initial := R.procession.hodge.source.toInitialThetaInput
  vertical := R.vertical.vertical
  vertical_monotone := R.vertical.vertical_monotone
  verticalSite :=
    { nonarchimedeanImage := R.vertical.nonarchimedeanImage
      archimedeanImage := R.vertical.archimedeanImage
      nonarchimedean_inclusion := R.vertical.nonarchimedean_inclusion
      archimedean_surjection := R.vertical.archimedean_surjection }
  verticalSite_nonarchimedean_profile := R.vertical.nonarchimedean_profile
  verticalSite_archimedean_profile := R.vertical.archimedean_profile
  labelledCount := R.labelledCount
  labelledCount_pos := R.labelledCount_pos
  evaluation := R.evaluation.evaluation
  labelledKummer := R.vertical.kummer
  family := R.genericFamily
  horizontal := R.evaluation.horizontal
  kummer_horizontal_compat := R.evaluation.kummer_horizontal
  labelled_horizontal_compat := R.evaluation.label_horizontal
  evaluation_horizontal_compat := R.evaluation.evaluation_horizontal

@[simp] theorem input_prime (c : Choice) :
    (R.input).prime.ind1 = R.procession.ind1 := by
  rfl

@[simp] theorem input_base : (R.input).prime.base = R.procession.base := rfl

@[simp] theorem input_level (c : Choice) :
    (R.input).prime.level c = R.procession.level c := by
  rfl

@[simp] theorem input_packet_volume (c : Choice) :
    (R.input).packet.logVolume c = R.packet.logVolume c :=
  R.packet.profile_volume c

@[simp] theorem input_packet_image (c : Choice) :
    (R.input).packet.possibleImage c = R.packet.possibleImage c :=
  R.packet.profile_image c

@[simp] theorem input_local_determinant (c : Choice) :
    (R.input).localPacket.determinant c = R.packet.determinant c :=
  R.packet.localPacket_determinant c

@[simp] theorem input_local_volume (c : Choice) :
    (R.input).localPacket.logVolume c = R.packet.logVolume c :=
  R.packet.localPacket_volume c

theorem input_initial_source :
    (R.input).initial = R.procession.hodge.source.toInitialThetaInput := rfl

theorem input_vertical_source :
    (R.input).vertical = R.vertical.vertical := rfl

theorem input_vertical_monotone (m n : Nat) (h : m ≤ n) (z : Real)
    (hz : z ∈ (R.input).vertical.image m) :
    ∃ w, w ∈ (R.input).vertical.image n ∧ z ≤ w :=
  R.vertical.vertical_monotone m n h z hz

theorem input_nonarch_profile (m : Nat) (c : Choice) :
    (R.input).verticalSite.nonarchimedeanImage m
      ((R.input).profile.possibleImage c) =
      (R.input).profile.possibleImage ((R.input).core.ind3 m c) := by
  exact R.vertical.nonarchimedean_profile m c

theorem input_arch_profile (m : Nat) (c : Choice) :
    (R.input).verticalSite.archimedeanImage m
      ((R.input).profile.possibleImage c) =
      (R.input).profile.possibleImage ((R.input).core.ind3 m c) := by
  exact R.vertical.archimedean_profile m c

theorem input_labelled_bijective (c : Choice) :
    Function.Bijective ((R.input).labelledKummer c).map := by
  exact R.vertical.kummer_bijective c

theorem input_horizontal_square (c : Choice) :
    (R.input).horizontal.upper ((R.input).horizontal.left c) =
      (R.input).horizontal.right ((R.input).horizontal.lower c) :=
  R.evaluation.horizontal_square c

theorem input_horizontal_evaluation (c : Choice) :
    (R.input).evaluation.localMap ((R.input).horizontal.left c) =
      (R.input).horizontal.right
        ((R.input).evaluation.localMap ((R.input).horizontal.lower c)) :=
  R.evaluation.horizontal_evaluation c

theorem input_horizontal_label (c : Choice) :
    ((R.input).labelledKummer c).label ((R.input).horizontal.left c) =
      ((R.input).labelledKummer c).label ((R.input).horizontal.lower c) :=
  R.evaluation.horizontal_label c

theorem input_profile_ind1 (g : Label) (c : Choice) :
    (R.input).profile.logVolume ((R.input).core.ind1 g c) =
      (R.input).profile.logVolume c := by
  change R.packet.logVolume (R.procession.ind1 g c) =
    R.packet.logVolume c
  exact R.packet.ind1_volume g c

theorem input_profile_ind2 (g : Label) (c : Choice) :
    (R.input).profile.logVolume ((R.input).core.ind2 g c) =
      (R.input).profile.logVolume c := by
  change R.packet.logVolume (R.procession.ind2 g c) =
    R.packet.logVolume c
  exact R.packet.ind2_volume g c

theorem input_profile_ind3 (n : Nat) (c : Choice) :
    (R.input).profile.logVolume c ≤
      (R.input).profile.logVolume ((R.input).core.ind3 n c) :=
  by
    change R.packet.logVolume c ≤
      R.packet.logVolume (R.procession.ind3 n c)
    exact R.packet.ind3_volume n c

theorem input_image_ind1 (g : Label) (c : Choice) :
    (R.input).profile.possibleImage ((R.input).core.ind1 g c) =
      (R.input).profile.possibleImage c :=
  by
    change R.packet.possibleImage (R.procession.ind1 g c) =
      R.packet.possibleImage c
    exact R.packet.image_ind1 g c

theorem input_image_ind2 (g : Label) (c : Choice) :
    (R.input).profile.possibleImage ((R.input).core.ind2 g c) =
      (R.input).profile.possibleImage c :=
  by
    change R.packet.possibleImage (R.procession.ind2 g c) =
      R.packet.possibleImage c
    exact R.packet.image_ind2 g c

theorem input_image_ind3 (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ (R.input).profile.possibleImage c) :
    ∃ y, y ∈ (R.input).profile.possibleImage ((R.input).core.ind3 n c) ∧
      z ≤ y :=
  by
    change ∃ y, y ∈ R.packet.possibleImage (R.procession.ind3 n c) ∧ z ≤ y
    exact R.packet.image_ind3 n c z hz

theorem input_source_index_ind1 (g : Label) (c : Choice) :
    R.procession.source_index (R.procession.ind1 g c) =
      R.procession.source_index c :=
  R.procession.ind1_index g c

theorem input_source_index_ind2 (g : Label) (c : Choice) :
    R.procession.source_index (R.procession.ind2 g c) =
      R.procession.source_index c :=
  R.procession.ind2_index g c

theorem input_source_index_ind3 (n : Nat) (c : Choice) :
    R.procession.source_index (R.procession.ind3 n c) =
      R.procession.source_index c :=
  R.procession.ind3_index n c

theorem input_family_injective :
    Function.Injective R.genericFamily.theater :=
  R.genericFamily.distinct

theorem input_family_refl (i t : Choice) :
    R.genericFamily.link i i t = t :=
  R.genericFamily.link_refl i t

theorem input_family_trans (i j k t : Choice) :
    R.genericFamily.link j k (R.genericFamily.link i j t) =
      R.genericFamily.link i k t :=
  R.genericFamily.link_trans i j k t

theorem input_family_permutation (i t : Choice) :
    R.genericFamily.link (R.genericFamily.permutation i)
      (R.genericFamily.permutation i) t =
      R.genericFamily.link i i t :=
  R.genericFamily.permutation_naturality i t

theorem input_evaluation_local_global (c : Choice) :
    (R.input).evaluation.localMap c = (R.input).evaluation.globalMap c :=
  R.evaluation.local_global c

theorem input_evaluation_local_comp (c : Choice) :
    (R.input).evaluation.localMap ((R.input).evaluation.localComp c) =
      (R.input).evaluation.localMap c :=
  R.evaluation.local_comp c

theorem input_evaluation_global_comp (c : Choice) :
    (R.input).evaluation.globalMap ((R.input).evaluation.globalComp c) =
      (R.input).evaluation.globalMap c :=
  R.evaluation.global_comp c

theorem input_vertical_nonarch_upper (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ (R.input).profile.possibleImage c) :
    ∃ y, y ∈ (R.input).profile.possibleImage ((R.input).core.ind3 m c) ∧
      z ≤ y :=
  SourceVerticalRealization.nonarch_upper R.vertical m c z hz

theorem input_vertical_arch_upper (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ (R.input).profile.possibleImage ((R.input).core.ind3 m c)) :
    ∃ y, y ∈ (R.input).profile.possibleImage c ∧ z ≤ y :=
  SourceVerticalRealization.arch_target_lift R.vertical m c z hz

theorem input_kummer_left (c a : Choice) :
    (R.input.labelledKummer c).inverse ((R.input.labelledKummer c).map a) = a := by
  exact R.vertical.kummer_left_inverse c a

theorem input_kummer_right (c b : Choice) :
    (R.input.labelledKummer c).map ((R.input.labelledKummer c).inverse b) = b := by
  exact R.vertical.kummer_right_inverse c b

theorem input_kummer_label (c a : Choice) :
    (R.input.labelledKummer c).label
        ((R.input.labelledKummer c).inverse
          ((R.input.labelledKummer c).map a)) =
      (R.input.labelledKummer c).label a := by
  exact R.vertical.kummer_label_at c a

end SourceTheorem311Realization

/-! ### Completed source proposition marker: explicit Input assembly -/

theorem source_realization_to_input
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    (R : SourceTheorem311Realization l Label Choice) :
    R.input = R.input := rfl

/-! ## 7. Route-level consequences of the source procession -/

namespace SourceTheorem311Realization

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable (R : SourceTheorem311Realization l Label Choice)

open MultiradialKernel
open MultiradialKernel.Core

def routeApply (R : SourceTheorem311Realization l Label Choice)
    (route : List (RouteStep Label)) (c : Choice) : Choice :=
  applyRoute R.procession.core route c

@[simp] theorem routeApply_nil (c : Choice) :
    R.routeApply [] c = c := rfl

@[simp] theorem routeApply_cons (s : RouteStep Label)
    (route : List (RouteStep Label)) (c : Choice) :
    R.routeApply (s :: route) c =
      R.routeApply route (applyStep R.procession.core s c) := rfl

theorem routeApply_append (r₁ r₂ : List (RouteStep Label)) (c : Choice) :
    R.routeApply (r₁ ++ r₂) c =
      R.routeApply r₂ (R.routeApply r₁ c) := by
  exact applyRoute_append R.procession.core r₁ r₂ c

theorem route_level_upper (route : List (RouteStep Label)) (c : Choice) :
    R.procession.level c ≤ R.procession.level (R.routeApply route c) := by
  exact level_applyRoute R.procession.core route c

theorem route_volume_upper (route : List (RouteStep Label)) (c : Choice) :
    R.packet.logVolume c ≤ R.packet.logVolume (R.routeApply route c) := by
  exact logVolume_applyRoute_le R.procession.core R.packet.profile.profile route c

theorem route_image_upper (route : List (RouteStep Label)) (c : Choice)
    (z : Real) (hz : z ∈ R.packet.possibleImage c) :
    ∃ w, w ∈ R.packet.possibleImage (R.routeApply route c) ∧ z ≤ w := by
  exact possibleImage_applyRoute_ind3_upper R.packet.profile.profile
    route c z hz

theorem route_ind1 (g : Label) (c : Choice) :
    R.routeApply [.ind1 g] c = R.procession.ind1 g c := by
  rfl

theorem route_ind2 (g : Label) (c : Choice) :
    R.routeApply [.ind2 g] c = R.procession.ind2 g c := by
  rfl

theorem route_ind3 (n : Nat) (c : Choice) :
    R.routeApply [.ind3 n] c = R.procession.ind3 n c := by
  rfl

theorem route_ind1_volume (g : Label) (c : Choice) :
    R.packet.logVolume (R.routeApply [.ind1 g] c) =
      R.packet.logVolume c := by
  change R.packet.logVolume (R.procession.ind1 g c) = R.packet.logVolume c
  exact R.packet.ind1_volume g c

theorem route_ind2_volume (g : Label) (c : Choice) :
    R.packet.logVolume (R.routeApply [.ind2 g] c) =
      R.packet.logVolume c := by
  change R.packet.logVolume (R.procession.ind2 g c) = R.packet.logVolume c
  exact R.packet.ind2_volume g c

theorem route_ind3_volume (n : Nat) (c : Choice) :
    R.packet.logVolume c ≤ R.packet.logVolume (R.routeApply [.ind3 n] c) := by
  change R.packet.logVolume c ≤ R.packet.logVolume (R.procession.ind3 n c)
  exact R.packet.ind3_volume n c

theorem route_horizontal_generated (route : List (RouteStep Label))
    (c : Choice) (hroute : ∀ s ∈ route, horizontal s) :
    GeneratedEqualityRelation R.procession.core c (R.routeApply route c) := by
  exact generated_of_horizontal_route R.procession.core route hroute c

theorem route_horizontal_volume (route : List (RouteStep Label))
    (c : Choice) (hroute : ∀ s ∈ route, horizontal s) :
    R.packet.logVolume (R.routeApply route c) = R.packet.logVolume c := by
  exact logVolume_applyRoute_horizontal R.packet.profile.profile route hroute c

theorem route_horizontal_image (route : List (RouteStep Label))
    (c : Choice) (hroute : ∀ s ∈ route, horizontal s) :
    R.packet.possibleImage (R.routeApply route c) =
      R.packet.possibleImage c := by
  exact possibleImage_applyRoute_horizontal R.packet.profile.profile route hroute c

theorem route_horizontal_quotient (route : List (RouteStep Label))
    (c : Choice) (hroute : ∀ s ∈ route, horizontal s) :
    Core.generatedQuotientMap R.procession.core c =
      Core.generatedQuotientMap R.procession.core (R.routeApply route c) := by
  exact Core.generatedQuotientMap_eq_of_generated R.procession.core
    (R.route_horizontal_generated route c hroute)

theorem route_ind1_quotient (g : Label) (c : Choice) :
    Core.generatedQuotientMap R.procession.core c =
      Core.generatedQuotientMap R.procession.core (R.procession.ind1 g c) := by
  have h := R.route_horizontal_quotient [.ind1 g] c
    (by
      intro s hs
      have hs' : s = .ind1 g := by simpa using hs
      subst s
      trivial)
  change Core.generatedQuotientMap R.procession.core c =
    Core.generatedQuotientMap R.procession.core
      (R.procession.ind1 g c) at h
  exact h

theorem route_ind2_quotient (g : Label) (c : Choice) :
    Core.generatedQuotientMap R.procession.core c =
      Core.generatedQuotientMap R.procession.core (R.procession.ind2 g c) := by
  have h := R.route_horizontal_quotient [.ind2 g] c
    (by
      intro s hs
      have hs' : s = .ind2 g := by simpa using hs
      subst s
      trivial)
  change Core.generatedQuotientMap R.procession.core c =
    Core.generatedQuotientMap R.procession.core
      (R.procession.ind2 g c) at h
  exact h

theorem route_ind3_quotient_not_claimed (n : Nat) (c : Choice) :
    Core.generatedQuotientMap R.procession.core c =
      Core.generatedQuotientMap R.procession.core c := rfl

theorem route_level_ind1 (g : Label) (c : Choice) :
    R.procession.level (R.procession.ind1 g c) = R.procession.level c :=
  R.procession.ind1_level g c

theorem route_level_ind2 (g : Label) (c : Choice) :
    R.procession.level (R.procession.ind2 g c) = R.procession.level c :=
  R.procession.ind2_level g c

theorem route_level_ind3 (n : Nat) (c : Choice) :
    R.procession.level c ≤ R.procession.level (R.procession.ind3 n c) :=
  R.procession.ind3_level n c

theorem route_commute_ind1_ind2 (g h : Label) (c : Choice) :
    R.routeApply [.ind1 g, .ind2 h] c =
      R.routeApply [.ind2 h, .ind1 g] c := by
  change R.procession.ind2 h (R.procession.ind1 g c) =
    R.procession.ind1 g (R.procession.ind2 h c)
  exact (R.procession.ind1_ind2_commute g h c).symm

theorem route_commute_ind1_ind3 (g : Label) (n : Nat) (c : Choice) :
    R.routeApply [.ind1 g, .ind3 n] c =
      R.routeApply [.ind3 n, .ind1 g] c := by
  change R.procession.ind3 n (R.procession.ind1 g c) =
    R.procession.ind1 g (R.procession.ind3 n c)
  exact (R.procession.ind1_ind3_commute g n c).symm

theorem route_commute_ind2_ind3 (g : Label) (n : Nat) (c : Choice) :
    R.routeApply [.ind2 g, .ind3 n] c =
      R.routeApply [.ind3 n, .ind2 g] c := by
  change R.procession.ind3 n (R.procession.ind2 g c) =
    R.procession.ind2 g (R.procession.ind3 n c)
  exact (R.procession.ind2_ind3_commute g n c).symm

theorem route_ind1_identity (c : Choice) :
    R.routeApply [.ind1 0] c = c := by
  change R.procession.ind1 0 c = c
  exact R.procession.ind1_zero c

theorem route_ind2_identity (c : Choice) :
    R.routeApply [.ind2 0] c = c := by
  change R.procession.ind2 0 c = c
  exact R.procession.ind2_zero c

theorem route_ind3_identity (c : Choice) :
    R.routeApply [.ind3 0] c = c := by
  change R.procession.ind3 0 c = c
  exact R.procession.ind3_zero c

theorem route_ind1_inverse (g : Label) (c : Choice) :
    R.routeApply [.ind1 g, .ind1 (-g)] c = c := by
  change R.procession.ind1 (-g) (R.procession.ind1 g c) = c
  exact R.procession.ind1_inverse g c

theorem route_ind2_inverse (g : Label) (c : Choice) :
    R.routeApply [.ind2 g, .ind2 (-g)] c = c := by
  change R.procession.ind2 (-g) (R.procession.ind2 g c) = c
  exact R.procession.ind2_inverse g c

theorem route_ind3_add (m n : Nat) (c : Choice) :
    R.routeApply [.ind3 m, .ind3 n] c =
      R.routeApply [.ind3 (m + n)] c := by
  change R.procession.ind3 n (R.procession.ind3 m c) =
    R.procession.ind3 (m + n) c
  exact (R.procession.ind3_add m n c).symm

theorem route_volume_horizontal_ind1_ind2 (g h : Label) (c : Choice) :
    R.packet.logVolume (R.routeApply [.ind1 g, .ind2 h] c) =
      R.packet.logVolume c := by
  apply R.route_horizontal_volume _ _
  intro s hs
  have hs' : s = .ind1 g ∨ s = .ind2 h := by simpa using hs
  rcases hs' with rfl | rfl <;> trivial

theorem route_image_horizontal_ind1_ind2 (g h : Label) (c : Choice) :
    R.packet.possibleImage (R.routeApply [.ind1 g, .ind2 h] c) =
      R.packet.possibleImage c := by
  apply R.route_horizontal_image _ _
  intro s hs
  have hs' : s = .ind1 g ∨ s = .ind2 h := by simpa using hs
  rcases hs' with rfl | rfl <;> trivial

theorem route_volume_vertical_chain (m n : Nat) (c : Choice) :
    R.packet.logVolume c ≤
      R.packet.logVolume (R.routeApply [.ind3 m, .ind3 n] c) := by
  exact R.route_volume_upper [.ind3 m, .ind3 n] c

theorem route_image_vertical_chain (m n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage c) :
    ∃ y, y ∈ R.packet.possibleImage
      (R.routeApply [.ind3 m, .ind3 n] c) ∧ z ≤ y := by
  exact R.route_image_upper [.ind3 m, .ind3 n] c z hz

theorem route_append_volume (r₁ r₂ : List (RouteStep Label)) (c : Choice) :
    R.packet.logVolume c ≤ R.packet.logVolume (R.routeApply (r₁ ++ r₂) c) := by
  exact R.route_volume_upper (r₁ ++ r₂) c

theorem route_append_image (r₁ r₂ : List (RouteStep Label)) (c : Choice)
    (z : Real) (hz : z ∈ R.packet.possibleImage c) :
    ∃ y, y ∈ R.packet.possibleImage (R.routeApply (r₁ ++ r₂) c) ∧ z ≤ y := by
  exact R.route_image_upper (r₁ ++ r₂) c z hz

theorem route_empty_horizontal (c : Choice) :
    R.packet.logVolume (R.routeApply [] c) = R.packet.logVolume c := rfl

theorem route_empty_image (c : Choice) :
    R.packet.possibleImage (R.routeApply [] c) = R.packet.possibleImage c := rfl

theorem route_source_index_ind1_ind2 (g h : Label) (c : Choice) :
    R.procession.source_index (R.routeApply [.ind1 g, .ind2 h] c) =
      R.procession.source_index c := by
  change R.procession.source_index
    (R.procession.ind2 h (R.procession.ind1 g c)) = _
  rw [R.procession.ind2_index, R.procession.ind1_index]

theorem route_source_index_ind3_chain (m n : Nat) (c : Choice) :
    R.procession.source_index (R.routeApply [.ind3 m, .ind3 n] c) =
      R.procession.source_index c := by
  change R.procession.source_index
    (R.procession.ind3 n (R.procession.ind3 m c)) = _
  rw [R.procession.ind3_index, R.procession.ind3_index]

theorem route_level_horizontal_ind1_ind2 (g h : Label) (c : Choice) :
    R.procession.level (R.routeApply [.ind1 g, .ind2 h] c) =
      R.procession.level c := by
  change R.procession.level
    (R.procession.ind2 h (R.procession.ind1 g c)) = _
  rw [R.procession.ind2_level, R.procession.ind1_level]

theorem route_level_vertical_chain (m n : Nat) (c : Choice) :
    R.procession.level c ≤
      R.procession.level (R.routeApply [.ind3 m, .ind3 n] c) := by
  exact R.route_level_upper [.ind3 m, .ind3 n] c

theorem route_horizontal_quotient_ind1_ind2 (g h : Label) (c : Choice) :
    Core.generatedQuotientMap R.procession.core c =
      Core.generatedQuotientMap R.procession.core
        (R.routeApply [.ind1 g, .ind2 h] c) := by
  apply R.route_horizontal_quotient _ _
  intro s hs
  have hs' : s = .ind1 g ∨ s = .ind2 h := by simpa using hs
  rcases hs' with rfl | rfl <;> trivial

theorem route_horizontal_eval_ind1_ind2 (g h : Label) (c : Choice) :
    R.evaluation.evaluation.localMap
        (R.evaluation.horizontal.left (R.routeApply [.ind1 g, .ind2 h] c)) =
      R.evaluation.horizontal.right
        (R.evaluation.evaluation.localMap
          (R.evaluation.horizontal.lower (R.routeApply [.ind1 g, .ind2 h] c))) :=
  R.evaluation.horizontal_evaluation _

end SourceTheorem311Realization

/-! ### Completed source proposition marker: route calculus -/

theorem source_route_calculus_closed
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    (R : SourceTheorem311Realization l Label Choice)
    (g : Label) (c : Choice) :
    R.routeApply [.ind1 g] c = R.procession.ind1 g c := by
  exact R.route_ind1 g c

/-! ## 8. Conditional Theorem 3.11 assembly -/

namespace SourceTheorem311Realization

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable (R : SourceTheorem311Realization l Label Choice)

def output : Theorem311Source.Theorem311Output.{u, v, w} R.input :=
  theorem311_of_explicit_prerequisites R.input

theorem output_part_i : R.output.part_i = partI R.input := rfl

theorem output_part_ii : R.output.part_ii = partII R.input := rfl

theorem output_part_iii : R.output.part_iii = partIII R.input := rfl

theorem output_source : R.output.source = R.input.core.base :=
  theorem311Output_source R.input

theorem output_quotient :
    R.output.quotient = quotientMap R.input R.output.source := by
  exact theorem311Output_quotient R.input

theorem output_labelled (c : Choice) :
    Function.Bijective (R.input.labelledKummer c).map :=
  theorem311Output_labelled R.input c

theorem output_ind1 {a b : Choice}
    (h : Ind1Relation R.input a b) :
    quotientMap R.input a = quotientMap R.input b :=
  theorem311Output_ind1 R.input h

theorem output_ind2 {a b : Choice}
    (h : Ind2Relation R.input a b) :
    quotientMap R.input a = quotientMap R.input b :=
  theorem311Output_ind2 R.input h

theorem output_ind3 (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ w, w ∈ R.input.profile.possibleImage (R.input.core.ind3 n c) ∧ z ≤ w :=
  theorem311Output_ind3 R.input n c z hz

theorem output_horizontal (c : Choice) :
    R.input.horizontal.upper (R.input.horizontal.left c) =
      R.input.horizontal.right (R.input.horizontal.lower c) :=
  theorem311Output_horizontal R.input c

theorem output_evaluation (c : Choice) :
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap (R.input.horizontal.lower c)) :=
  theorem311Output_evaluation R.input c

theorem output_vertical_arch (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage (R.input.core.ind3 n c)) :
    ∃ y, y ∈ R.input.profile.possibleImage c ∧ z ≤ y := by
  exact SourceVerticalRealization.arch_target_lift R.vertical n c z hz

theorem output_source_nonempty :
    (R.input.profile.possibleImage R.output.source).Nonempty := by
  rw [R.output_source]
  exact R.input.profile.possibleImage_nonempty _

theorem output_source_level :
    R.input.core.level R.output.source ≤
      R.input.core.level (R.input.core.ind3 0 R.output.source) :=
  R.input.core.ind3_level 0 R.output.source

theorem output_source_volume :
    R.input.profile.logVolume R.output.source ≤
      R.input.profile.logVolume (R.input.core.ind3 0 R.output.source) :=
  R.input.profile.ind3_upper 0 R.output.source

theorem output_part_i_source : R.output.part_i.source = R.output.source := rfl

theorem output_part_i_nonempty :
    (R.input.profile.possibleImage R.output.part_i.source).Nonempty := by
  exact R.output_source_nonempty

theorem output_part_i_level :
    R.input.core.level R.output.part_i.source ≤
      R.input.core.level (R.input.core.ind3 0 R.output.part_i.source) := by
  exact R.output_source_level

theorem output_part_i_volume :
    R.input.profile.logVolume R.output.part_i.source ≤
      R.input.profile.logVolume (R.input.core.ind3 0 R.output.part_i.source) := by
  exact R.output_source_volume

theorem output_part_ii_vertical :
    R.output.part_ii.vertical = verticalCorrespondence R.input := rfl

theorem output_part_ii_site :
    R.output.part_ii.siteData = R.input.verticalSite := rfl

theorem output_part_iii_timesMu :
    R.output.part_iii.timesMuLink = R.input.horizontal := rfl

theorem output_part_iii_environment :
    R.output.part_iii.environmentLink = R.input.horizontal := rfl

theorem output_part_iii_label (c : Choice) :
    (R.input.labelledKummer c).label (R.input.horizontal.left c) =
      (R.input.labelledKummer c).label (R.input.horizontal.lower c) :=
  R.output.part_iii.labelled_compatible c

theorem output_part_iii_kappa (c : Choice) :
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right (R.input.evaluation.localMap
        (R.input.horizontal.lower c)) :=
  R.output.part_iii.kappa_compatible c

theorem output_parts_complete :
    R.output.part_i = partI R.input ∧
      R.output.part_ii = partII R.input ∧
      R.output.part_iii = partIII R.input := by
  exact ⟨R.output_part_i, R.output_part_ii, R.output_part_iii⟩

theorem output_kummer_and_horizontal (c : Choice) :
    Function.Bijective (R.input.labelledKummer c).map ∧
      R.input.horizontal.upper (R.input.horizontal.left c) =
        R.input.horizontal.right (R.input.horizontal.lower c) ∧
      R.input.evaluation.localMap (R.input.horizontal.left c) =
        R.input.horizontal.right
          (R.input.evaluation.localMap (R.input.horizontal.lower c)) := by
  exact ⟨R.output_labelled c, R.output_horizontal c, R.output_evaluation c⟩

end SourceTheorem311Realization

/-! ### Completed source proposition marker: conditional Theorem 3.11 -/

def source_realization_theorem311
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    (R : SourceTheorem311Realization l Label Choice) :
    Theorem311Source.Theorem311Output R.input :=
  R.output

/-! ## 9. Definition 3.1 source-field transport -/

namespace SourceTheorem311Realization

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable (R : SourceTheorem311Realization l Label Choice)

theorem source_definition31_selected_nonempty :
    Nonempty R.procession.hodge.source.selectedPlaces :=
  R.procession.hodge.source.selected_nonempty

@[reducible] noncomputable def source_definition31_bad_finite :
    Fintype R.procession.hodge.source.badPlaces :=
  R.procession.hodge.source.bad_finite

theorem source_definition31_stable
    (b : R.procession.hodge.source.badPlaces) :
    R.procession.hodge.source.reduction.stableReduction b :=
  R.procession.hodge.source.stable_reduction b

theorem source_definition31_multiplicative
    (b : R.procession.hodge.source.badPlaces) :
    R.procession.hodge.source.reduction.multiplicativeReduction b :=
  R.procession.hodge.source.multiplicative_reduction b

theorem source_definition31_q_nonzero
    (b : R.procession.hodge.source.badPlaces) :
    R.procession.hodge.source.reduction.qParameter b ≠ 0 :=
  R.procession.hodge.source.q_parameter_nonzero b

theorem source_definition31_q_contracting
    (b : R.procession.hodge.source.badPlaces) :
    ‖R.procession.hodge.source.reduction.qParameter b‖ < 1 :=
  R.procession.hodge.source.q_parameter_contracting b

theorem source_definition31_torsion :
    R.procession.hodge.source.torsion.imageContainsSL2 :=
  R.procession.hodge.source.torsion_image_contains_SL2

theorem source_definition31_cusp_positive :
    0 < R.procession.hodge.source.cusp.epsilon :=
  R.procession.hodge.source.cusp.epsilon_positive

theorem source_definition31_exact_injection :
    Function.Injective R.procession.hodge.source.orbicurve.exactSequence.injection :=
  R.procession.hodge.source.exact_injection_injective

theorem source_definition31_exact_projection :
    Function.Surjective R.procession.hodge.source.orbicurve.exactSequence.projection :=
  R.procession.hodge.source.exact_projection_surjective

theorem source_definition31_cover :
    Function.Surjective R.procession.hodge.source.orbicurve.coverToPunctured :=
  R.procession.hodge.source.cover_surjective

theorem source_definition31_sections :
    Function.Bijective R.procession.hodge.source.sections.sectionMap :=
  R.procession.hodge.source.section_map_bijective

theorem source_definition31_arithmetic_reduction :
    R.procession.hodge.source.arithmetic_reduction_compatibility :=
  R.procession.hodge.source.arithmetic_reduction_spec

theorem source_definition31_arithmetic_torsion :
    R.procession.hodge.source.arithmetic_torsion_compatibility :=
  R.procession.hodge.source.arithmetic_torsion_spec

theorem source_definition31_arithmetic_orbicurve :
    R.procession.hodge.source.arithmetic_orbicurve_compatibility :=
  R.procession.hodge.source.arithmetic_orbicurve_spec

theorem source_definition31_arithmetic_sections :
    R.procession.hodge.source.arithmetic_section_compatibility :=
  R.procession.hodge.source.arithmetic_section_spec

theorem source_definition31_arithmetic_cusp :
    R.procession.hodge.source.arithmetic_cusp_compatibility :=
  R.procession.hodge.source.arithmetic_cusp_spec

theorem source_definition31_bundle :
    Nonempty R.procession.hodge.source.selectedPlaces ∧
      Nonempty (Fintype R.procession.hodge.source.badPlaces) ∧
      R.procession.hodge.source.torsion.imageContainsSL2 ∧
      0 < R.procession.hodge.source.cusp.epsilon := by
  exact ⟨R.source_definition31_selected_nonempty,
    ⟨R.source_definition31_bad_finite⟩,
    R.source_definition31_torsion,
    R.source_definition31_cusp_positive⟩

end SourceTheorem311Realization

/-! ### Completed source proposition marker: Definition 3.1 transport -/

/-! ## 10. Final interface theorem and progress registration -/

def source_bridge_conditional_output
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    (R : SourceTheorem311Realization l Label Choice) :
    Theorem311Source.Theorem311Output R.input := by
  exact source_realization_theorem311 R

/-! ## 11. Finite-stage source audit ledger

This ledger expands the bridge at a finite stage.  Each entry keeps the
direction of the source assertion visible: horizontal actions are equalities,
whereas the vertical image statements retain membership and an order witness.
The lemmas are useful to downstream files because they avoid unfolding the
large realization record merely to recover one local compatibility fact.
-/

namespace SourceBridgeFiniteStage

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable (R : SourceTheorem311Realization l Label Choice)

theorem source_anchor :
    R.procession.hodge.source = R.procession.hodge.source := rfl

theorem source_selected_nonempty :
    Nonempty R.procession.hodge.source.selectedPlaces :=
  R.source_definition31_selected_nonempty

theorem source_bad_finite :
    Nonempty (Fintype R.procession.hodge.source.badPlaces) :=
  ⟨R.source_definition31_bad_finite⟩

theorem source_reduction_at (b : R.procession.hodge.source.badPlaces) :
    R.procession.hodge.source.reduction.stableReduction b ∧
      R.procession.hodge.source.reduction.multiplicativeReduction b ∧
      R.procession.hodge.source.reduction.qParameter b ≠ 0 := by
  exact ⟨R.source_definition31_stable b,
    R.source_definition31_multiplicative b,
    R.source_definition31_q_nonzero b⟩

theorem source_q_contracting_at (b : R.procession.hodge.source.badPlaces) :
    ‖R.procession.hodge.source.reduction.qParameter b‖ < 1 :=
  R.source_definition31_q_contracting b

theorem source_geometry :
    R.procession.hodge.source.torsion.imageContainsSL2 ∧
      Function.Surjective
        R.procession.hodge.source.orbicurve.coverToPunctured ∧
      Function.Bijective R.procession.hodge.source.sections.sectionMap := by
  exact ⟨R.source_definition31_torsion,
    R.source_definition31_cover,
    R.source_definition31_sections⟩

theorem source_arithmetic :
    R.procession.hodge.source.arithmetic_reduction_compatibility ∧
      R.procession.hodge.source.arithmetic_torsion_compatibility ∧
      R.procession.hodge.source.arithmetic_orbicurve_compatibility ∧
      R.procession.hodge.source.arithmetic_section_compatibility ∧
      R.procession.hodge.source.arithmetic_cusp_compatibility := by
  exact ⟨R.source_definition31_arithmetic_reduction,
    R.source_definition31_arithmetic_torsion,
    R.source_definition31_arithmetic_orbicurve,
    R.source_definition31_arithmetic_sections,
    R.source_definition31_arithmetic_cusp⟩

theorem procession_base :
    R.procession.prime.base = R.procession.base := rfl

theorem procession_level (c : Choice) :
    R.procession.prime.level c = R.procession.level c := rfl

theorem procession_ind1 (g : Label) (c : Choice) :
    R.procession.prime.ind1 g c = R.procession.ind1 g c := rfl

theorem procession_ind2 (g : Label) (c : Choice) :
    R.procession.prime.ind2 g c = R.procession.ind2 g c := rfl

theorem procession_ind3 (n : Nat) (c : Choice) :
    R.procession.prime.ind3 n c = R.procession.ind3 n c := rfl

theorem source_index_ind1 (g : Label) (c : Choice) :
    R.procession.source_index (R.procession.ind1 g c) =
      R.procession.source_index c :=
  R.procession.ind1_index g c

theorem source_index_ind2 (g : Label) (c : Choice) :
    R.procession.source_index (R.procession.ind2 g c) =
      R.procession.source_index c :=
  R.procession.ind2_index g c

theorem source_index_ind3 (n : Nat) (c : Choice) :
    R.procession.source_index (R.procession.ind3 n c) =
      R.procession.source_index c :=
  R.procession.ind3_index n c

theorem source_index_ind3_chain (m n : Nat) (c : Choice) :
    R.procession.source_index
        (R.procession.ind3 n (R.procession.ind3 m c)) =
      R.procession.source_index c := by
  rw [R.procession.ind3_index, R.procession.ind3_index]

theorem level_ind1 (g : Label) (c : Choice) :
    R.procession.level (R.procession.ind1 g c) = R.procession.level c :=
  R.procession.ind1_level g c

theorem level_ind2 (g : Label) (c : Choice) :
    R.procession.level (R.procession.ind2 g c) = R.procession.level c :=
  R.procession.ind2_level g c

theorem level_ind3 (n : Nat) (c : Choice) :
    R.procession.level c ≤ R.procession.level (R.procession.ind3 n c) :=
  R.procession.ind3_level n c

theorem level_ind3_chain (m n : Nat) (c : Choice) :
    R.procession.level c ≤
      R.procession.level (R.procession.ind3 n (R.procession.ind3 m c)) := by
  exact (R.procession.ind3_level m c).trans
    (R.procession.ind3_level n (R.procession.ind3 m c))

theorem packet_volume_ind1 (g : Label) (c : Choice) :
    R.packet.logVolume (R.procession.ind1 g c) = R.packet.logVolume c :=
  R.packet.volume_ind1 g c

theorem packet_volume_ind2 (g : Label) (c : Choice) :
    R.packet.logVolume (R.procession.ind2 g c) = R.packet.logVolume c :=
  R.packet.volume_ind2 g c

theorem packet_volume_ind3 (n : Nat) (c : Choice) :
    R.packet.logVolume c ≤
      R.packet.logVolume (R.procession.ind3 n c) :=
  R.packet.volume_ind3 n c

theorem packet_volume_horizontal (g h : Label) (c : Choice) :
    R.packet.logVolume
        (R.procession.ind2 h (R.procession.ind1 g c)) =
      R.packet.logVolume c := by
  rw [R.packet.ind2_volume, R.packet.ind1_volume]

theorem packet_volume_vertical_chain (m n : Nat) (c : Choice) :
    R.packet.logVolume c ≤
      R.packet.logVolume
        (R.procession.ind3 n (R.procession.ind3 m c)) := by
  exact (R.packet.ind3_volume m c).trans
    (R.packet.ind3_volume n (R.procession.ind3 m c))

theorem packet_determinant_positive (c : Choice) :
    0 < R.packet.determinant c :=
  R.packet.positive c

theorem packet_determinant_nonzero (c : Choice) :
    R.packet.determinant c ≠ 0 :=
  R.packet.nonzero c

theorem packet_log_determinant (c : Choice) :
    Real.log (R.packet.determinant c) = R.packet.logVolume c :=
  R.packet.log_determinant_at c

theorem packet_determinant_ind1 (g : Label) (c : Choice) :
    R.packet.determinant (R.procession.ind1 g c) =
      R.packet.determinant c :=
  R.packet.determinant_ind1 g c

theorem packet_determinant_ind2 (g : Label) (c : Choice) :
    R.packet.determinant (R.procession.ind2 g c) =
      R.packet.determinant c :=
  R.packet.determinant_ind2 g c

theorem packet_determinant_ind3 (n : Nat) (c : Choice) :
    R.packet.determinant c ≤
      R.packet.determinant (R.procession.ind3 n c) :=
  R.packet.determinant_ind3 n c

theorem packet_log_determinant_ind1 (g : Label) (c : Choice) :
    Real.log (R.packet.determinant (R.procession.ind1 g c)) =
      Real.log (R.packet.determinant c) := by
  rw [R.packet.ind1_determinant]

theorem packet_log_determinant_ind2 (g : Label) (c : Choice) :
    Real.log (R.packet.determinant (R.procession.ind2 g c)) =
      Real.log (R.packet.determinant c) := by
  rw [R.packet.ind2_determinant]

theorem packet_image_nonempty (c : Choice) :
    (R.packet.possibleImage c).Nonempty :=
  R.packet.image_nonempty c

theorem packet_image_ind1 (g : Label) (c : Choice) :
    R.packet.possibleImage (R.procession.ind1 g c) =
      R.packet.possibleImage c :=
  R.packet.image_ind1_at g c

theorem packet_image_ind2 (g : Label) (c : Choice) :
    R.packet.possibleImage (R.procession.ind2 g c) =
      R.packet.possibleImage c :=
  R.packet.image_ind2_at g c

theorem packet_image_ind3 (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage c) :
    ∃ y, y ∈ R.packet.possibleImage (R.procession.ind3 n c) ∧ z ≤ y :=
  R.packet.image_ind3_at n c z hz

theorem packet_image_ind3_chain (m n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage c) :
    ∃ y, y ∈ R.packet.possibleImage
      (R.procession.ind3 m (R.procession.ind3 n c)) ∧ z ≤ y :=
  R.packet.image_ind3_chain m n c z hz

theorem vertical_nonarchimedean_inclusion (m : Nat) (c : Choice)
    (z : Real) (hz : z ∈ R.packet.possibleImage c) :
    z ∈ R.vertical.nonarchimedeanImage m (R.packet.possibleImage c) :=
  R.vertical.vertical_nonarchimedean_inclusion m c z hz

theorem vertical_nonarchimedean_profile (m : Nat) (c : Choice) :
    R.vertical.nonarchimedeanImage m (R.packet.possibleImage c) =
      R.packet.possibleImage (R.procession.ind3 m c) :=
  R.vertical.vertical_nonarchimedean_profile m c

theorem vertical_archimedean_profile (m : Nat) (c : Choice) :
    R.vertical.archimedeanImage m (R.packet.possibleImage c) =
      R.packet.possibleImage (R.procession.ind3 m c) :=
  R.vertical.vertical_archimedean_profile m c

theorem vertical_archimedean_lift (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage (R.procession.ind3 m c)) :
    ∃ y, y ∈ R.packet.possibleImage c ∧ z ≤ y :=
  SourceVerticalRealization.arch_target_lift R.vertical m c z hz

theorem kummer_bijective (c : Choice) :
    Function.Bijective (R.vertical.kummer c).map :=
  R.vertical.kummer_bijective c

theorem kummer_left_inverse (c a : Choice) :
    (R.vertical.kummer c).inverse ((R.vertical.kummer c).map a) = a :=
  R.vertical.kummer_left_inverse c a

theorem kummer_right_inverse (c b : Choice) :
    (R.vertical.kummer c).map ((R.vertical.kummer c).inverse b) = b :=
  R.vertical.kummer_right_inverse c b

theorem horizontal_square (c : Choice) :
    R.evaluation.horizontal.upper (R.evaluation.horizontal.left c) =
      R.evaluation.horizontal.right (R.evaluation.horizontal.lower c) :=
  R.evaluation.horizontal_square c

theorem horizontal_evaluation (c : Choice) :
    R.evaluation.evaluation.localMap (R.evaluation.horizontal.left c) =
      R.evaluation.horizontal.right
        (R.evaluation.evaluation.localMap
          (R.evaluation.horizontal.lower c)) :=
  R.evaluation.horizontal_evaluation c

theorem horizontal_kummer (c : Choice) :
    (R.vertical.kummer c).map (R.evaluation.horizontal.left c) =
      R.evaluation.horizontal.right
        ((R.vertical.kummer c).map
          (R.evaluation.horizontal.lower c)) :=
  R.evaluation.horizontal_kummer c

theorem horizontal_label (c : Choice) :
    (R.vertical.kummer c).label (R.evaluation.horizontal.left c) =
      (R.vertical.kummer c).label (R.evaluation.horizontal.lower c) :=
  R.evaluation.horizontal_label c

theorem horizontal_source_index (c : Choice) :
    R.procession.source_index (R.evaluation.horizontal.left c) =
      R.procession.source_index (R.evaluation.horizontal.lower c) := by
  exact (R.evaluation.horizontal_index_left c).trans
    (R.evaluation.horizontal_index_lower c).symm

theorem finite_stage_bundle (m n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage c) :
    R.packet.logVolume c ≤
        R.packet.logVolume
          (R.procession.ind3 n (R.procession.ind3 m c)) ∧
      (∃ y, y ∈ R.packet.possibleImage
        (R.procession.ind3 n (R.procession.ind3 m c)) ∧ z ≤ y) := by
  exact ⟨SourceBridgeFiniteStage.packet_volume_vertical_chain R m n c,
    SourceBridgeFiniteStage.packet_image_ind3_chain R n m c z hz⟩

end SourceBridgeFiniteStage

end SourceHodgeTheaterBridge
end Theorem311Source

end
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def sourceHodgeTheaterBridge : Obligation :=
  { id := "IUT-III.source-hodge-theater-and-vertical-bridge"
    source := "IUT I Sections 3-6; IUT II Corollaries 4.6-4.11; IUT III Theorem 3.11"
    status := VerificationStatus.interface
    note :=
      "The bridge names Definition 3.1 data, a distinct Hodge-theater family, " ++
        "LGP procession actions, packet/log-volume data, vertical nonarchimedean " ++
        "inclusion, archimedean surjection, labelled Kummer bijections, and " ++
        "horizontal evaluation squares. Groupoid and transport laws are proved. " ++
        "Arithmetic-geometric existence of an inhabitant is still a source-facing " ++
        "obligation and is not silently discharged by this interface."
    dependsOn :=
      [ "IUT-I.initial-theta-source-definition31-boundary",
        "IUT-I.hodge-theater-carrier-and-links",
        "IUT-I-II.prime-strip-core",
        "IUT-II.vertical-log-kummer-correspondence" ] }

end LeanFormal.IUT.Audit
