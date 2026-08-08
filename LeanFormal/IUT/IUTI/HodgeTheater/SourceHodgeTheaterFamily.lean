import LeanFormal.IUT.IUTI.HodgeTheater.History
import Mathlib.Tactic

/-!
  # Source Hodge-theater families and dependent histories

  This module is the source-facing family layer between an initial Theta-data
  object and the procession contracts used by IUT III.  A family is indexed by
  an arbitrary type, carries actual `HodgeTheater` objects, and carries actual
  `HodgeTheaterLink`s between every pair of members.  Distinctness is an
  injectivity field; it is never inferred from a finite test carrier.

  The route type below is dependent in its endpoint.  Consequently a route
  cannot silently compose links with mismatched source or target theaters.  All
  q-parameter and scale transport statements are obtained from the link data,
  while permutation statements use an explicit naturality square.  The final
  audit declaration remains an interface for arithmetic-geometric existence:
  the algebra of a supplied family is proved here, but no family is selected
  from an arbitrary number field.
-/

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon ui

/-! ## 1. Families of actual Hodge theaters -/

structure SourceHodgeTheaterFamily
    (l : PrimeGeFive) (V : Type uv) where
  index : Type ui
  theater : index → HodgeTheater.{ua, uv, upi, umon} l V
  distinct : Function.Injective theater
  link : ∀ i j, HodgeTheaterLink (theater i) (theater j)
  link_refl : ∀ i,
    link i i = HodgeTheaterLink.refl (theater i)
  link_symm : ∀ i j,
    HodgeTheaterLink.symm (link i j) = link j i
  link_trans : ∀ i j k,
    HodgeTheaterLink.trans (link i j) (link j k) = link i k
  permutation : Equiv.Perm index
  permutationLink : ∀ i,
    HodgeTheaterLink (theater (permutation i)) (theater i)
  permutation_naturality : ∀ i j,
    HodgeTheaterLink.trans (link (permutation i) (permutation j))
        (permutationLink j) =
      HodgeTheaterLink.trans (permutationLink i) (link i j)

namespace SourceHodgeTheaterFamily

variable {l : PrimeGeFive} {V : Type uv}
variable (F : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V)

theorem theater_injective : Function.Injective F.theater :=
  F.distinct

theorem theater_eq_iff {i j : F.index} :
    F.theater i = F.theater j ↔ i = j := by
  constructor
  · exact F.distinct
  · intro h
    simpa [h]

theorem link_refl_at (i : F.index) :
    F.link i i = HodgeTheaterLink.refl (F.theater i) :=
  F.link_refl i

theorem link_symm_at (i j : F.index) :
    HodgeTheaterLink.symm (F.link i j) = F.link j i :=
  F.link_symm i j

theorem link_trans_at (i j k : F.index) :
    HodgeTheaterLink.trans (F.link i j) (F.link j k) = F.link i k :=
  F.link_trans i j k

theorem link_q (i j : F.index) :
    (F.theater i).thetaPacket.q = (F.theater j).thetaPacket.q :=
  (F.link i j).theta_q_eq

theorem link_scale (i j : F.index) (r : SignedLabel l.value) :
    (F.theater i).thetaPacket.scale r =
      (F.theater j).thetaPacket.scale r :=
  (F.link i j).theta_scale_eq r

theorem link_q_symm (i j : F.index) :
    (F.theater j).thetaPacket.q = (F.theater i).thetaPacket.q := by
  exact (F.link_q i j).symm

theorem link_scale_symm (i j : F.index) (r : SignedLabel l.value) :
    (F.theater j).thetaPacket.scale r =
      (F.theater i).thetaPacket.scale r := by
  exact (F.link_scale i j r).symm

theorem link_q_trans (i j k : F.index) :
    (F.theater i).thetaPacket.q = (F.theater k).thetaPacket.q := by
  exact (F.link_q i j).trans (F.link_q j k)

theorem link_scale_trans (i j k : F.index) (r : SignedLabel l.value) :
    (F.theater i).thetaPacket.scale r =
      (F.theater k).thetaPacket.scale r := by
  exact (F.link_scale i j r).trans (F.link_scale j k r)

theorem permutation_link_at (i : F.index) :
    HodgeTheaterLink (F.theater (F.permutation i)) (F.theater i) :=
  F.permutationLink i

theorem permutation_q (i : F.index) :
    (F.theater (F.permutation i)).thetaPacket.q =
      (F.theater i).thetaPacket.q :=
  (F.permutationLink i).theta_q_eq

theorem permutation_scale (i : F.index) (r : SignedLabel l.value) :
    (F.theater (F.permutation i)).thetaPacket.scale r =
      (F.theater i).thetaPacket.scale r :=
  (F.permutationLink i).theta_scale_eq r

theorem permutation_naturality_at (i j : F.index) :
    HodgeTheaterLink.trans (F.link (F.permutation i) (F.permutation j))
        (F.permutationLink j) =
      HodgeTheaterLink.trans (F.permutationLink i) (F.link i j) :=
  F.permutation_naturality i j

theorem permutation_theater_injective :
    Function.Injective (fun i => F.theater (F.permutation i)) := by
  intro i j h
  apply F.permutation.injective
  exact F.distinct h

theorem permutation_q_trans (i j : F.index) :
    (F.theater (F.permutation i)).thetaPacket.q =
      (F.theater (F.permutation j)).thetaPacket.q := by
  exact (F.permutation_q i).trans ((F.link_q i j).trans (F.permutation_q j).symm)

theorem permutation_scale_trans (i j : F.index) (r : SignedLabel l.value) :
    (F.theater (F.permutation i)).thetaPacket.scale r =
      (F.theater (F.permutation j)).thetaPacket.scale r := by
  exact (F.permutation_scale i r).trans
    ((F.link_scale i j r).trans (F.permutation_scale j r).symm)

theorem link_trans_q (i j k : F.index) :
    (HodgeTheaterLink.trans (F.link i j) (F.link j k)).theta_q_eq := by
  simpa using F.link_q_trans i j k

theorem link_trans_scale (i j k : F.index) (r : SignedLabel l.value) :
    (HodgeTheaterLink.trans (F.link i j) (F.link j k)).theta_scale_eq r := by
  simpa using F.link_scale_trans i j k r

theorem link_refl_q (i : F.index) :
    (F.theater i).thetaPacket.q = (F.theater i).thetaPacket.q := rfl

theorem link_refl_scale (i : F.index) (r : SignedLabel l.value) :
    (F.theater i).thetaPacket.scale r =
      (F.theater i).thetaPacket.scale r := rfl

theorem link_symm_q (i j : F.index) :
    (HodgeTheaterLink.symm (F.link i j)).theta_q_eq := by
  simpa using F.link_q_symm i j

theorem link_symm_scale (i j : F.index) (r : SignedLabel l.value) :
    (HodgeTheaterLink.symm (F.link i j)).theta_scale_eq r := by
  simpa using F.link_scale_symm i j r

theorem link_refl_id (i : F.index) :
    HodgeTheaterLink.refl (F.theater i) = F.link i i := by
  exact (F.link_refl_at i).symm

theorem link_symm_involutive (i j : F.index) :
    HodgeTheaterLink.symm (HodgeTheaterLink.symm (F.link i j)) =
      F.link i j := by
  exact HodgeTheaterLink.symm_symm (F.link i j)

theorem link_trans_refl_left (i j : F.index) :
    HodgeTheaterLink.trans (F.link i i) (F.link i j) = F.link i j := by
  rw [F.link_refl_at]
  exact HodgeTheaterLink.refl_trans (F.link i j)

theorem link_trans_refl_right (i j : F.index) :
    HodgeTheaterLink.trans (F.link i j) (F.link j j) = F.link i j := by
  rw [F.link_refl_at]
  exact HodgeTheaterLink.trans_refl (F.link i j)

theorem link_trans_assoc (i j k m : F.index) :
    HodgeTheaterLink.trans
        (HodgeTheaterLink.trans (F.link i j) (F.link j k))
        (F.link k m) =
      HodgeTheaterLink.trans (F.link i j)
        (HodgeTheaterLink.trans (F.link j k) (F.link k m)) := by
  rw [F.link_trans_at, F.link_trans_at]

theorem permutation_naturality_q (i j : F.index) :
    (F.theater (F.permutation i)).thetaPacket.q =
      (F.theater j).thetaPacket.q := by
  exact (F.permutation_q i).trans (F.link_q i j)

theorem permutation_naturality_scale (i j : F.index)
    (r : SignedLabel l.value) :
    (F.theater (F.permutation i)).thetaPacket.scale r =
      (F.theater j).thetaPacket.scale r := by
  exact (F.permutation_scale i r).trans (F.link_scale i j r)

theorem permutation_inverse_q (i : F.index) :
    (F.theater (F.permutation.symm i)).thetaPacket.q =
      (F.theater i).thetaPacket.q := by
  obtain ⟨j, rfl⟩ := F.permutation.surjective i
  simpa using F.permutation_q j

theorem permutation_inverse_scale (i : F.index) (r : SignedLabel l.value) :
    (F.theater (F.permutation.symm i)).thetaPacket.scale r =
      (F.theater i).thetaPacket.scale r := by
  obtain ⟨j, rfl⟩ := F.permutation.surjective i
  simpa using F.permutation_scale j r

end SourceHodgeTheaterFamily

/-! ## 2. Dependent routes whose links have matching endpoints -/

inductive SourceHodgeTheaterRoute
    (F : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V)
    (start : F.index) : Type (max ui 1)
  | singleton : SourceHodgeTheaterRoute F start
  | cons (next : F.index) (rest : SourceHodgeTheaterRoute F next) :
      SourceHodgeTheaterRoute F start

namespace SourceHodgeTheaterRoute

variable {l : PrimeGeFive} {V : Type uv}
variable {F : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V}

def consLink (start next : F.index)
    (rest : SourceHodgeTheaterRoute F next) :
    SourceHodgeTheaterRoute F start :=
  .cons next rest

def terminal {start : F.index} :
    SourceHodgeTheaterRoute F start → F.index
  | .singleton => start
  | .cons next rest => rest.terminal

def length {start : F.index} :
    SourceHodgeTheaterRoute F start → Nat
  | .singleton => 1
  | .cons _ rest => rest.length + 1

def composite {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    HodgeTheaterLink (F.theater start) (F.theater route.terminal) := by
  induction route with
  | singleton => exact HodgeTheaterLink.refl (F.theater start)
  | cons next rest ih =>
      exact HodgeTheaterLink.trans (F.link start next) rest.composite

theorem terminal_singleton (start : F.index) :
    (SourceHodgeTheaterRoute.singleton :
      SourceHodgeTheaterRoute F start).terminal = start := rfl

theorem length_singleton (start : F.index) :
    (SourceHodgeTheaterRoute.singleton :
      SourceHodgeTheaterRoute F start).length = 1 := rfl

theorem length_pos {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    0 < route.length := by
  induction route with
  | singleton => simp [length]
  | cons next rest ih => simp [length, ih]

theorem composite_singleton (start : F.index) :
    (SourceHodgeTheaterRoute.singleton :
      SourceHodgeTheaterRoute F start).composite =
      HodgeTheaterLink.refl (F.theater start) := rfl

theorem composite_q {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    (F.theater start).thetaPacket.q =
      (F.theater route.terminal).thetaPacket.q := by
  induction route with
  | singleton => rfl
  | cons next rest ih =>
      exact (F.link_q start next).trans ih

theorem composite_scale {start : F.index}
    (route : SourceHodgeTheaterRoute F start)
    (r : SignedLabel l.value) :
    (F.theater start).thetaPacket.scale r =
      (F.theater route.terminal).thetaPacket.scale r := by
  induction route with
  | singleton => rfl
  | cons next rest ih =>
      exact (F.link_scale start next r).trans ih

theorem composite_is_trans_link {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    route.composite.theta_q_eq := by
  exact route.composite_q

theorem composite_is_trans_scale {start : F.index}
    (route : SourceHodgeTheaterRoute F start)
    (r : SignedLabel l.value) :
    route.composite.theta_scale_eq r := by
  exact route.composite_scale r

def append {start : F.index}
  (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal) :
    SourceHodgeTheaterRoute F start :=
  match left with
  | .singleton => right
  | .cons next rest => .cons next (append rest right)

theorem append_terminal {start : F.index}
    (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal) :
    (left.append right).terminal = right.terminal := by
  induction left with
  | singleton => rfl
  | cons next rest ih => exact ih right

theorem append_length {start : F.index}
    (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal) :
    (left.append right).length = left.length + right.length - 1 := by
  induction left with
  | singleton => simp [append, length]
  | cons next rest ih =>
      simp [append, length, ih, Nat.add_assoc, Nat.add_sub_assoc]

theorem append_composite {start : F.index}
    (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal) :
    (left.append right).composite =
      HodgeTheaterLink.trans left.composite right.composite := by
  induction left with
  | singleton =>
      simp [append, composite]
  | cons next rest ih =>
      simp [append, composite, ih, HodgeTheaterLink.trans]

theorem append_q {start : F.index}
    (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal) :
    (F.theater start).thetaPacket.q =
      (F.theater right.terminal).thetaPacket.q := by
  exact (left.composite_q).trans right.composite_q

theorem append_scale {start : F.index}
    (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal)
    (r : SignedLabel l.value) :
    (F.theater start).thetaPacket.scale r =
      (F.theater right.terminal).thetaPacket.scale r := by
  exact (left.composite_scale r).trans (right.composite_scale r)

theorem route_length_ne_zero {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    route.length ≠ 0 := Nat.ne_of_gt route.length_pos

theorem route_q_eq_start {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    (F.theater route.terminal).thetaPacket.q =
      (F.theater start).thetaPacket.q :=
  route.composite_q.symm

theorem route_scale_eq_start {start : F.index}
    (route : SourceHodgeTheaterRoute F start)
    (r : SignedLabel l.value) :
    (F.theater route.terminal).thetaPacket.scale r =
      (F.theater start).thetaPacket.scale r :=
  (route.composite_scale r).symm

end SourceHodgeTheaterRoute

/-! ## 3. Three-theater systems and route transport -/

structure SourceThreeTheaterSystem
    (F : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V) where
  source : F.index
  middle : F.index
  target : F.index
  source_to_middle : F.link source middle
  middle_to_target : F.link middle target

namespace SourceThreeTheaterSystem

variable {l : PrimeGeFive} {V : Type uv}
variable {F : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V}
variable (S : SourceThreeTheaterSystem F)

def source_to_target : HodgeTheaterLink (F.theater S.source) (F.theater S.target) :=
  HodgeTheaterLink.trans S.source_to_middle S.middle_to_target

theorem source_to_target_q :
    (F.theater S.source).thetaPacket.q =
      (F.theater S.target).thetaPacket.q :=
  (F.link_q S.source S.middle).trans (F.link_q S.middle S.target)

theorem source_to_target_scale (r : SignedLabel l.value) :
    (F.theater S.source).thetaPacket.scale r =
      (F.theater S.target).thetaPacket.scale r :=
  (F.link_scale S.source S.middle r).trans
    (F.link_scale S.middle S.target r)

theorem source_to_target_link :
    S.source_to_target = F.link S.source S.target := by
  exact F.link_trans_at S.source S.middle S.target

theorem source_to_target_link_q : S.source_to_target.theta_q_eq := by
  simpa [source_to_target] using S.source_to_target_q

theorem source_to_target_link_scale (r : SignedLabel l.value) :
    S.source_to_target.theta_scale_eq r := by
  simpa [source_to_target] using S.source_to_target_scale r

theorem source_to_target_index_eq_of_link_target
    {j : F.index} (h : S.source_to_target.target = F.theater j) :
    S.target = j := by
  exact F.distinct h

end SourceThreeTheaterSystem

/-! ## 4. Source-faithful bundles used by the dependency chain -/

structure SourceHodgeTheaterFamilyBundle
    (l : PrimeGeFive) (V : Type uv) where
  family : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V
  anchor : family.index
  route : SourceHodgeTheaterRoute family anchor

namespace SourceHodgeTheaterFamilyBundle

variable {l : PrimeGeFive} {V : Type uv}
variable (B : SourceHodgeTheaterFamilyBundle.{ua, uv, upi, umon, ui} l V)

theorem anchor_q :
    (B.family.theater B.anchor).thetaPacket.q =
      (B.family.theater B.route.terminal).thetaPacket.q :=
  B.route.composite_q

theorem anchor_scale (r : SignedLabel l.value) :
    (B.family.theater B.anchor).thetaPacket.scale r =
      (B.family.theater B.route.terminal).thetaPacket.scale r :=
  B.route.composite_scale r

theorem route_length_positive : 0 < B.route.length :=
  B.route.length_pos

theorem route_terminal_index :
    B.route.composite.theta_q_eq :=
  B.route.composite_q

theorem route_source_target_q :
    (B.family.theater B.anchor).thetaPacket.q =
      (B.family.theater B.route.terminal).thetaPacket.q := by
  exact B.anchor_q

theorem route_source_target_scale (r : SignedLabel l.value) :
    (B.family.theater B.anchor).thetaPacket.scale r =
      (B.family.theater B.route.terminal).thetaPacket.scale r := by
  exact B.anchor_scale r

theorem route_terminal_eq_of_target {j : B.family.index}
    (h : B.family.theater B.route.terminal = B.family.theater j) :
    B.route.terminal = j := by
  exact B.family.distinct h

end SourceHodgeTheaterFamilyBundle

/-! ## 5. Reusable theorem bundles and audit marker -/

namespace SourceHodgeTheaterFamily

variable {l : PrimeGeFive} {V : Type uv}
variable (F : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V)

theorem source_family_bundle (i j k : F.index)
    (r : SignedLabel l.value) :
    F.theater i = F.theater i ∧
      F.link i i = HodgeTheaterLink.refl (F.theater i) ∧
      F.link i j = F.link i j ∧
      HodgeTheaterLink.trans (F.link i j) (F.link j k) = F.link i k ∧
      (F.theater i).thetaPacket.q = (F.theater j).thetaPacket.q ∧
      (F.theater i).thetaPacket.scale r =
        (F.theater j).thetaPacket.scale r := by
  exact ⟨rfl, F.link_refl i, rfl, F.link_trans i j k,
    F.link_q i j, F.link_scale i j r⟩

theorem source_family_permutation_bundle (i : F.index)
    (r : SignedLabel l.value) :
    (F.theater (F.permutation i)).thetaPacket.q =
        (F.theater i).thetaPacket.q ∧
      (F.theater (F.permutation i)).thetaPacket.scale r =
        (F.theater i).thetaPacket.scale r := by
  exact ⟨F.permutation_q i, F.permutation_scale i r⟩

theorem source_family_distinct_bundle {i j : F.index}
    (h : F.theater i = F.theater j) : i = j :=
  F.distinct h

theorem source_family_route_bundle {start : F.index}
    (route : SourceHodgeTheaterRoute F start)
    (r : SignedLabel l.value) :
    0 < route.length ∧
      (F.theater start).thetaPacket.q =
        (F.theater route.terminal).thetaPacket.q ∧
      (F.theater start).thetaPacket.scale r =
        (F.theater route.terminal).thetaPacket.scale r := by
  exact ⟨route.length_pos, route.composite_q, route.composite_scale r⟩

end SourceHodgeTheaterFamily

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def sourceHodgeTheaterFamily : Obligation :=
  { id := "IUT-I.hodge-theater-family-source-laws"
    source := "IUT I, Sections 3--5; IUT III Theorem 3.11"
    status := VerificationStatus.interface
    note :=
      "A source-facing family of actual HodgeTheater objects is indexed by " ++
        "an arbitrary type with explicit injectivity, pairwise links, " ++
        "identity/symmetry/composition laws, and permutation naturality. " ++
        "Dependent routes, terminal indices, composite links, q/scale " ++
        "transport, and three-theater composition are proved. Construction " ++
        "of such a family from arbitrary Definition 3.1 arithmetic data remains " ++
        "a separate source obligation."
    dependsOn := [ "IUT-I.hodge-theater-carrier-and-links",
      "IUT-I.hodge-theater-history-composition" ] }

end LeanFormal.IUT.Audit
