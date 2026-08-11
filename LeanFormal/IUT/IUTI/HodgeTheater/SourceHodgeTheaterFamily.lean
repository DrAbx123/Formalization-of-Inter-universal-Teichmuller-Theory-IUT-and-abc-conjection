import LeanFormal.IUT.IUTI.HodgeTheater.History
import Init.Omega

set_option linter.checkUnivs false

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
  · intro h
    exact F.distinct h
  · intro h
    simp [h]

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

def permutation_link_at (i : F.index) :
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
    (F.theater i).thetaPacket.q = (F.theater k).thetaPacket.q := by
  simpa using F.link_q_trans i j k

theorem link_trans_scale (i j k : F.index) (r : SignedLabel l.value) :
    (F.theater i).thetaPacket.scale r =
      (F.theater k).thetaPacket.scale r := by
  simpa using F.link_scale_trans i j k r

theorem link_refl_q (i : F.index) :
    (F.theater i).thetaPacket.q = (F.theater i).thetaPacket.q := rfl

theorem link_refl_scale (i : F.index) (r : SignedLabel l.value) :
    (F.theater i).thetaPacket.scale r =
      (F.theater i).thetaPacket.scale r := rfl

theorem link_symm_q (i j : F.index) :
    (F.theater j).thetaPacket.q = (F.theater i).thetaPacket.q := by
  simpa using F.link_q_symm i j

theorem link_symm_scale (i j : F.index) (r : SignedLabel l.value) :
    (F.theater j).thetaPacket.scale r =
      (F.theater i).thetaPacket.scale r := by
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
  rw [F.link_trans_at i j k, F.link_trans_at j k m,
    F.link_trans_at i k m, F.link_trans_at i j m]

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
  simpa using (F.permutation_q j).symm

theorem permutation_inverse_scale (i : F.index) (r : SignedLabel l.value) :
    (F.theater (F.permutation.symm i)).thetaPacket.scale r =
      (F.theater i).thetaPacket.scale r := by
  obtain ⟨j, rfl⟩ := F.permutation.surjective i
  simpa using (F.permutation_scale j r).symm

end SourceHodgeTheaterFamily

/-! ## 2. Strictly positive route codes -/

set_option linter.unusedVariables false in
abbrev SourceHodgeTheaterRoute
    (F : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V)
    (start : F.index) := List F.index

namespace SourceHodgeTheaterRoute

variable {l : PrimeGeFive} {V : Type uv}
variable {F : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V}

def singleton {start : F.index} : SourceHodgeTheaterRoute F start := []

def cons {start : F.index} (next : F.index)
    (rest : SourceHodgeTheaterRoute F next) :
    SourceHodgeTheaterRoute F start := next :: rest

def consLink (_start next : F.index)
    (rest : SourceHodgeTheaterRoute F next) :
    SourceHodgeTheaterRoute F _start := cons next rest

def terminalFrom (start : F.index) : List F.index → F.index
  | [] => start
  | next :: rest => terminalFrom next rest

def terminal {start : F.index} :
    SourceHodgeTheaterRoute F start → F.index := terminalFrom start

def length {start : F.index} (route : SourceHodgeTheaterRoute F start) : Nat :=
  List.length route + 1

def compositeFrom (start : F.index) :
    (route : List F.index) →
      HodgeTheaterLink (F.theater start)
        (F.theater (terminalFrom start route))
  | [] => HodgeTheaterLink.refl (F.theater start)
  | next :: rest =>
      HodgeTheaterLink.trans (F.link start next)
        (compositeFrom next rest)

def composite {start : F.index} (route : SourceHodgeTheaterRoute F start) :
    HodgeTheaterLink (F.theater start) (F.theater route.terminal) :=
  compositeFrom start route

def append {start : F.index}
    (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal) :
    SourceHodgeTheaterRoute F start := left ++ right

def transportTarget {S T U : HodgeTheater.{ua, uv, upi, umon} l V}
    (h : T = U) (link : HodgeTheaterLink S T) :
    HodgeTheaterLink S U := by
  cases h
  exact link

theorem transportTarget_trans {S T U W : HodgeTheater.{ua, uv, upi, umon} l V}
    (first : HodgeTheaterLink S T) (second : HodgeTheaterLink T U)
    (h : U = W) :
    transportTarget h (HodgeTheaterLink.trans first second) =
      HodgeTheaterLink.trans first (transportTarget h second) := by
  cases h
  rfl

theorem heq_eq_transport
    {S T U : HodgeTheater.{ua, uv, upi, umon} l V}
    {first : HodgeTheaterLink S T} {second : HodgeTheaterLink S U}
    (h : T = U) (heq : HEq first second) :
    first = transportTarget h.symm second := by
  cases h
  exact eq_of_heq heq

theorem transportTarget_heq
    {S T U : HodgeTheater.{ua, uv, upi, umon} l V}
    (h : T = U) (link : HodgeTheaterLink S U) :
    HEq (transportTarget h.symm link) link := by
  cases h
  rfl

theorem transport_family_link {i j k : F.index} (h : i = j) :
    transportTarget (congrArg F.theater h) (F.link k i) = F.link k j := by
  cases h
  rfl

theorem terminal_singleton (start : F.index) :
    (singleton (F := F) : SourceHodgeTheaterRoute F start).terminal = start := rfl

theorem length_singleton (start : F.index) :
    (singleton (F := F) : SourceHodgeTheaterRoute F start).length = 1 := rfl

theorem terminal_cons {start next : F.index}
    (rest : SourceHodgeTheaterRoute F next) :
    (cons next rest : SourceHodgeTheaterRoute F start).terminal = rest.terminal := rfl

theorem length_cons {start next : F.index}
    (rest : SourceHodgeTheaterRoute F next) :
    (cons next rest : SourceHodgeTheaterRoute F start).length = rest.length + 1 := by
  simp [cons, length, Nat.add_comm]

theorem length_pos {start : F.index}
    (route : SourceHodgeTheaterRoute F start) : 0 < route.length := by
  simp [length]

theorem composite_singleton (start : F.index) :
    (singleton (F := F) : SourceHodgeTheaterRoute F start).composite =
      HodgeTheaterLink.refl (F.theater start) := rfl

theorem composite_q_from (route : List F.index) :
    ∀ start : F.index,
      (F.theater start).thetaPacket.q =
        (F.theater (terminalFrom start route)).thetaPacket.q := by
  induction route with
  | nil => intro start; rfl
  | cons next rest ih =>
      intro start
      exact (F.link_q start next).trans (ih next)

theorem composite_q {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    (F.theater start).thetaPacket.q =
      (F.theater route.terminal).thetaPacket.q :=
  composite_q_from (F := F) route start

theorem composite_scale_from (route : List F.index) (r : SignedLabel l.value) :
    ∀ start : F.index,
      (F.theater start).thetaPacket.scale r =
        (F.theater (terminalFrom start route)).thetaPacket.scale r := by
  induction route with
  | nil => intro start; rfl
  | cons next rest ih =>
      intro start
      exact (F.link_scale start next r).trans (ih next)

theorem composite_scale {start : F.index}
    (route : SourceHodgeTheaterRoute F start)
    (r : SignedLabel l.value) :
    (F.theater start).thetaPacket.scale r =
      (F.theater route.terminal).thetaPacket.scale r :=
  composite_scale_from (F := F) route r start

theorem composite_is_trans_link {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    (F.theater start).thetaPacket.q =
      (F.theater route.terminal).thetaPacket.q := route.composite_q

theorem composite_is_trans_scale {start : F.index}
    (route : SourceHodgeTheaterRoute F start)
    (r : SignedLabel l.value) :
    (F.theater start).thetaPacket.scale r =
      (F.theater route.terminal).thetaPacket.scale r := route.composite_scale r

theorem terminal_append_from (left : List F.index) :
    ∀ (start : F.index) (right : List F.index),
      terminalFrom start (left ++ right) =
        terminalFrom (terminalFrom start left) right := by
  induction left with
  | nil => intro start right; rfl
  | cons next rest ih =>
      intro start right
      exact ih next right

theorem terminal_append {start : F.index}
    (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal) :
    (left.append right).terminal = right.terminal :=
  terminal_append_from (F := F) left start right

theorem append_terminal {start : F.index}
    (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal) :
    (left.append right).terminal = right.terminal :=
  terminal_append left right

theorem append_length {start : F.index}
    (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal) :
    (left.append right).length = left.length + right.length - 1 := by
  simp [append, length, List.length_append]
  omega

theorem composite_eq_family_link_from (route : List F.index) :
    ∀ start : F.index,
      compositeFrom start route = F.link start (terminalFrom start route) := by
  induction route with
  | nil =>
      intro start
      exact (F.link_refl_at start).symm
  | cons next rest ih =>
      intro start
      change HodgeTheaterLink.trans (F.link start next)
        (compositeFrom next rest) = F.link start (terminalFrom next rest)
      rw [ih next]
      exact F.link_trans_at start next (terminalFrom next rest)

theorem composite_eq_family_link {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    route.composite = F.link start route.terminal :=
  composite_eq_family_link_from (F := F) route start

theorem append_composite {start : F.index}
    (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal) :
    (left.append right).composite =
      SourceHodgeTheaterRoute.transportTarget
        (congrArg F.theater (terminal_append left right)).symm
        (HodgeTheaterLink.trans left.composite right.composite) := by
  have hterminal := terminal_append left right
  have htrans :
      HodgeTheaterLink.trans left.composite right.composite =
        F.link start right.terminal := by
    rw [left.composite_eq_family_link, right.composite_eq_family_link]
    exact F.link_trans_at start left.terminal right.terminal
  calc
    (left.append right).composite =
        F.link start (left.append right).terminal :=
      composite_eq_family_link (F := F) (left.append right)
    _ = SourceHodgeTheaterRoute.transportTarget
          (congrArg F.theater hterminal.symm)
          (F.link start right.terminal) := by
      symm
      exact SourceHodgeTheaterRoute.transport_family_link (F := F) hterminal.symm
    _ = SourceHodgeTheaterRoute.transportTarget
          (congrArg F.theater hterminal.symm)
          (HodgeTheaterLink.trans left.composite right.composite) := by
      rw [htrans]

theorem append_q {start : F.index}
    (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal) :
    (F.theater start).thetaPacket.q =
      (F.theater right.terminal).thetaPacket.q :=
  (left.composite_q).trans right.composite_q

theorem append_scale {start : F.index}
    (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal)
    (r : SignedLabel l.value) :
    (F.theater start).thetaPacket.scale r =
      (F.theater right.terminal).thetaPacket.scale r :=
  (left.composite_scale r).trans (right.composite_scale r)

theorem route_length_ne_zero {start : F.index}
    (route : SourceHodgeTheaterRoute F start) : route.length ≠ 0 :=
  Nat.ne_of_gt route.length_pos

theorem route_q_eq_start {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    (F.theater route.terminal).thetaPacket.q =
      (F.theater start).thetaPacket.q := route.composite_q.symm

theorem route_scale_eq_start {start : F.index}
    (route : SourceHodgeTheaterRoute F start)
    (r : SignedLabel l.value) :
    (F.theater route.terminal).thetaPacket.scale r =
      (F.theater start).thetaPacket.scale r := (route.composite_scale r).symm

def reverseSteps (start : F.index) : List F.index → List F.index
  | [] => []
  | next :: rest => reverseSteps next rest ++ [start]

def reverse {start : F.index} (route : SourceHodgeTheaterRoute F start) :
    SourceHodgeTheaterRoute F route.terminal := reverseSteps start route

theorem terminalFrom_append_last_from (steps : List F.index) (last : F.index) :
    ∀ base : F.index, terminalFrom base (steps ++ [last]) = last := by
  induction steps with
  | nil => intro base; rfl
  | cons next rest ih =>
      intro base
      exact ih next

theorem terminalFrom_append_last (base : F.index)
    (steps : List F.index) (last : F.index) :
    terminalFrom base (steps ++ [last]) = last :=
  terminalFrom_append_last_from (F := F) steps last base

theorem reverseSteps_terminal_from (route : List F.index) :
    ∀ start : F.index,
      terminalFrom (terminalFrom start route) (reverseSteps start route) = start := by
  induction route with
  | nil => intro start; rfl
  | cons next rest ih =>
      intro start
      exact terminalFrom_append_last_from (F := F) (reverseSteps next rest)
        start (terminalFrom next rest)

theorem reverseSteps_terminal (start : F.index)
    (route : List F.index) :
    terminalFrom (terminalFrom start route) (reverseSteps start route) = start :=
  reverseSteps_terminal_from (F := F) route start

theorem reverse_terminal {start : F.index}
    (route : SourceHodgeTheaterRoute F start) : route.reverse.terminal = start := by
  exact reverseSteps_terminal start route

theorem reverseSteps_length_from (route : List F.index) :
    ∀ start : F.index, (reverseSteps start route).length = route.length := by
  induction route with
  | nil => intro start; rfl
  | cons next rest ih =>
      intro start
      simp [reverseSteps, List.length_append, ih next]

theorem reverseSteps_length (start : F.index) (route : List F.index) :
    (reverseSteps start route).length = route.length :=
  reverseSteps_length_from (F := F) route start

theorem reverse_length {start : F.index}
    (route : SourceHodgeTheaterRoute F start) : route.reverse.length = route.length := by
  exact congrArg (fun n => n + 1) (reverseSteps_length start route)

theorem reverse_composite {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    route.reverse.composite =
      SourceHodgeTheaterRoute.transportTarget
        (congrArg F.theater route.reverse_terminal).symm
        (HodgeTheaterLink.symm route.composite) := by
  have hterminal := route.reverse_terminal
  have hcomp : route.reverse.composite =
      F.link route.terminal route.reverse.terminal := by
    simpa using route.reverse.composite_eq_family_link
  calc
    route.reverse.composite = F.link route.terminal route.reverse.terminal := hcomp
    _ = SourceHodgeTheaterRoute.transportTarget
          (congrArg F.theater hterminal.symm)
          (F.link route.terminal start) := by
      symm
      exact SourceHodgeTheaterRoute.transport_family_link (F := F) hterminal.symm
    _ = SourceHodgeTheaterRoute.transportTarget
          (congrArg F.theater hterminal.symm)
          (HodgeTheaterLink.symm (F.link start route.terminal)) := by
      rw [F.link_symm_at]
    _ = SourceHodgeTheaterRoute.transportTarget
          (congrArg F.theater hterminal.symm)
          (HodgeTheaterLink.symm route.composite) := by
      rw [route.composite_eq_family_link]

theorem reverse_q {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    (F.theater route.reverse.terminal).thetaPacket.q =
      (F.theater route.terminal).thetaPacket.q := by
  rw [route.reverse_terminal]
  exact route.composite_q

theorem reverse_scale {start : F.index}
    (route : SourceHodgeTheaterRoute F start) (r : SignedLabel l.value) :
    (F.theater route.reverse.terminal).thetaPacket.scale r =
      (F.theater route.terminal).thetaPacket.scale r := by
  rw [route.reverse_terminal]
  exact route.composite_scale r

def mapList (p : Equiv.Perm F.index) : List F.index → List F.index
  | [] => []
  | next :: rest => p next :: mapList p rest

def map (p : Equiv.Perm F.index) {start : F.index} :
    SourceHodgeTheaterRoute F start → SourceHodgeTheaterRoute F (p start) :=
  mapList p

theorem terminalFrom_map_from (p : Equiv.Perm F.index)
    (route : List F.index) :
    ∀ start : F.index,
      terminalFrom (p start) (mapList p route) = p (terminalFrom start route) := by
  induction route with
  | nil => intro start; rfl
  | cons next rest ih =>
      intro start
      simpa [mapList, terminalFrom] using ih next

theorem terminalFrom_map (p : Equiv.Perm F.index) (start : F.index)
    (route : List F.index) :
    terminalFrom (p start) (mapList p route) = p (terminalFrom start route) :=
  terminalFrom_map_from p route start

theorem map_terminal (p : Equiv.Perm F.index) {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    (route.map p).terminal = p route.terminal := by
  exact terminalFrom_map_from p route start

theorem mapList_length (p : Equiv.Perm F.index) (route : List F.index) :
    List.length (mapList p route) = List.length route := by
  induction route with
  | nil => rfl
  | cons next rest ih => simp [mapList, ih]

theorem map_length (p : Equiv.Perm F.index) {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    (route.map p).length = route.length := by
  change List.length (mapList p route) + 1 = List.length route + 1
  rw [mapList_length]

theorem map_composite_eq_family_link (p : Equiv.Perm F.index)
    {start : F.index} (route : SourceHodgeTheaterRoute F start) :
    (route.map p).composite = F.link (p start) (route.map p).terminal :=
  by
    exact composite_eq_family_link (F := F) (route.map p)

theorem map_q (p : Equiv.Perm F.index) {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    (F.theater (p start)).thetaPacket.q =
      (F.theater (p route.terminal)).thetaPacket.q := F.link_q _ _

theorem map_scale (p : Equiv.Perm F.index) {start : F.index}
    (route : SourceHodgeTheaterRoute F start) (r : SignedLabel l.value) :
    (F.theater (p start)).thetaPacket.scale r =
      (F.theater (p route.terminal)).thetaPacket.scale r := F.link_scale _ _ _

theorem permutation_map_composite_naturality {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
  HodgeTheaterLink.trans (F.permutationLink start) route.composite =
      HodgeTheaterLink.trans
        (SourceHodgeTheaterRoute.transportTarget
          (congrArg F.theater
            (SourceHodgeTheaterRoute.map_terminal F.permutation route))
          (route.map F.permutation).composite)
        (F.permutationLink route.terminal) := by
  have hmap := SourceHodgeTheaterRoute.map_terminal F.permutation route
  have hmapComp :
      (route.map F.permutation).composite =
        F.link (F.permutation start) (route.map F.permutation).terminal :=
    (route.map F.permutation).composite_eq_family_link
  have hcast :
      SourceHodgeTheaterRoute.transportTarget
          (congrArg F.theater hmap) (route.map F.permutation).composite =
        F.link (F.permutation start) (F.permutation route.terminal) := by
    calc
      SourceHodgeTheaterRoute.transportTarget
          (congrArg F.theater hmap) (route.map F.permutation).composite =
          SourceHodgeTheaterRoute.transportTarget
            (congrArg F.theater hmap)
            (F.link (F.permutation start) (route.map F.permutation).terminal) := by
        rw [hmapComp]
      _ = F.link (F.permutation start) (F.permutation route.terminal) :=
        SourceHodgeTheaterRoute.transport_family_link (F := F) hmap
  calc
    HodgeTheaterLink.trans (F.permutationLink start) route.composite =
        HodgeTheaterLink.trans (F.permutationLink start)
          (F.link start route.terminal) := by rw [route.composite_eq_family_link]
    _ = HodgeTheaterLink.trans
          (F.link (F.permutation start) (F.permutation route.terminal))
          (F.permutationLink route.terminal) :=
      (F.permutation_naturality start route.terminal).symm
    _ = HodgeTheaterLink.trans
          (SourceHodgeTheaterRoute.transportTarget
            (congrArg F.theater hmap) (route.map F.permutation).composite)
          (F.permutationLink route.terminal) := by rw [hcast]

theorem append_reverse_composite {start : F.index}
    (left : SourceHodgeTheaterRoute F start) :
    (left.append left.reverse).composite =
      SourceHodgeTheaterRoute.transportTarget
        (congrArg F.theater
          ((terminal_append left left.reverse).trans left.reverse_terminal)).symm
        (HodgeTheaterLink.refl (F.theater start)) := by
  have hterminal := (terminal_append left left.reverse).trans left.reverse_terminal
  have hcomp : (left.append left.reverse).composite =
      F.link start (left.append left.reverse).terminal :=
    (left.append left.reverse).composite_eq_family_link
  calc
    (left.append left.reverse).composite =
        F.link start (left.append left.reverse).terminal := hcomp
    _ = SourceHodgeTheaterRoute.transportTarget
          (congrArg F.theater hterminal.symm)
          (F.link start start) := by
      symm
      exact SourceHodgeTheaterRoute.transport_family_link (F := F) hterminal.symm
    _ = SourceHodgeTheaterRoute.transportTarget
          (congrArg F.theater hterminal.symm)
          (HodgeTheaterLink.refl (F.theater start)) := by
      rw [F.link_refl_at]

theorem append_singleton_left {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    (singleton (F := F) : SourceHodgeTheaterRoute F start).append route = route := rfl

theorem append_q_full {start : F.index}
    (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal) :
    (F.theater start).thetaPacket.q =
      (F.theater (left.append right).terminal).thetaPacket.q := by
  rw [terminal_append]
  exact left.append_q right

theorem append_scale_full {start : F.index}
    (left : SourceHodgeTheaterRoute F start)
    (right : SourceHodgeTheaterRoute F left.terminal)
    (r : SignedLabel l.value) :
    (F.theater start).thetaPacket.scale r =
      (F.theater (left.append right).terminal).thetaPacket.scale r := by
  rw [terminal_append]
  exact left.append_scale right r

end SourceHodgeTheaterRoute

/-! ## 3a. Translation to the carrier-independent history type -/

namespace SourceHodgeTheaterFamily

variable {l : PrimeGeFive} {V : Type uv}
variable (F : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V)

def route_to_history_from (start : F.index) : List F.index →
    HodgeTheaterHistory l V (F.theater start)
  | [] => .singleton (F.theater start)
  | next :: rest =>
      .cons (F.link start next) (route_to_history_from next rest)

def route_to_history {start : F.index} :
    SourceHodgeTheaterRoute F start →
      HodgeTheaterHistory l V (F.theater start) :=
  route_to_history_from F start

@[simp] theorem route_to_history_nil {start : F.index} :
    F.route_to_history (start := start) ([] : List F.index) =
      .singleton (F.theater start) := by
  rfl

@[simp] theorem route_to_history_cons {start next : F.index}
    (rest : List F.index) :
    F.route_to_history (start := start) (next :: rest) =
      .cons (F.link start next) (F.route_to_history (start := next) rest) := by
  rfl

theorem route_to_history_terminal_from (route : List F.index) :
    ∀ start : F.index,
      (F.route_to_history_from start route).terminal =
        F.theater (SourceHodgeTheaterRoute.terminalFrom start route) := by
  induction route with
  | nil =>
      intro start
      simp [route_to_history_from,
        SourceHodgeTheaterRoute.terminalFrom]
  | cons next rest ih =>
      intro start
      change (F.route_to_history_from next rest).terminal =
        F.theater (SourceHodgeTheaterRoute.terminalFrom next rest)
      exact ih next

theorem route_to_history_terminal {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    (F.route_to_history route).terminal = F.theater route.terminal :=
  route_to_history_terminal_from (F := F) route start

theorem route_to_history_length_from (route : List F.index) :
    ∀ start : F.index,
      (F.route_to_history_from start route).length =
        List.length route + 1 := by
  induction route with
  | nil =>
      intro start
      simp [route_to_history_from]
  | cons next rest ih =>
      intro start
      change (F.route_to_history_from next rest).length + 1 =
        List.length rest + 2
      rw [ih next]

theorem route_to_history_length {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    (F.route_to_history route).length = route.length :=
  route_to_history_length_from (F := F) route start

theorem route_to_history_composite_from (route : List F.index) :
    ∀ start : F.index,
      HEq (F.route_to_history (start := start) route).composite
        (SourceHodgeTheaterRoute.compositeFrom start route) := by
  induction route with
  | nil =>
      intro start
      rw [route_to_history_nil]
      have hterm := route_to_history_terminal_from (F := F) ([] : List F.index) start
      have hbase :
          (HodgeTheaterHistory.singleton (F.theater start)).composite =
            SourceHodgeTheaterRoute.transportTarget hterm.symm
              (HodgeTheaterLink.refl (F.theater start)) := by
        simp [HodgeTheaterHistory.composite,
          SourceHodgeTheaterRoute.transportTarget]
      have hcast : HEq
          (SourceHodgeTheaterRoute.transportTarget hterm.symm
            (HodgeTheaterLink.refl (F.theater start)))
          (HodgeTheaterLink.refl (F.theater start)) := by
        exact SourceHodgeTheaterRoute.transportTarget_heq hterm _
      exact HEq.trans (heq_of_eq hbase) hcast
  | cons next rest ih =>
      intro start
      rw [route_to_history_cons]
      have hih := ih next
      have hterm := route_to_history_terminal_from (F := F) rest next
      have hrest := SourceHodgeTheaterRoute.heq_eq_transport hterm hih
      have htrans := congrArg
        (fun L => HodgeTheaterLink.trans (F.link start next) L) hrest
      have htrans_cast := SourceHodgeTheaterRoute.transportTarget_trans
        (F.link start next)
        (SourceHodgeTheaterRoute.compositeFrom next rest)
        hterm.symm
      have hright :
          HEq (HodgeTheaterLink.trans (F.link start next)
              (SourceHodgeTheaterRoute.transportTarget hterm.symm
                (SourceHodgeTheaterRoute.compositeFrom next rest)))
            (HodgeTheaterLink.trans (F.link start next)
              (SourceHodgeTheaterRoute.compositeFrom next rest)) := by
        exact HEq.trans (heq_of_eq htrans_cast.symm)
          (SourceHodgeTheaterRoute.transportTarget_heq hterm _)
      exact HEq.trans (heq_of_eq htrans) hright

theorem route_to_history_composite {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    HEq (F.route_to_history route).composite route.composite := by
  exact route_to_history_composite_from (F := F) route start

theorem route_to_history_q {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    (F.theater start).thetaPacket.q =
      (F.route_to_history route).terminal.thetaPacket.q := by
  rw [F.route_to_history_terminal]
  exact route.composite_q

theorem route_to_history_scale {start : F.index}
    (route : SourceHodgeTheaterRoute F start)
    (r : SignedLabel l.value) :
    (F.theater start).thetaPacket.scale r =
      (F.route_to_history route).terminal.thetaPacket.scale r := by
  rw [F.route_to_history_terminal]
  exact route.composite_scale r

theorem route_to_history_composite_q {start : F.index}
    (route : SourceHodgeTheaterRoute F start) :
    (F.theater start).thetaPacket.q =
      (F.route_to_history route).terminal.thetaPacket.q := by
  exact F.route_to_history_q route

theorem route_to_history_composite_scale {start : F.index}
    (route : SourceHodgeTheaterRoute F start)
    (r : SignedLabel l.value) :
    (F.theater start).thetaPacket.scale r =
      (F.route_to_history route).terminal.thetaPacket.scale r := by
  exact F.route_to_history_scale route r

end SourceHodgeTheaterFamily

/-! ## 3. Three-theater systems and route transport -/

structure SourceThreeTheaterSystem
    (F : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V) where
  source : F.index
  middle : F.index
  target : F.index
  source_to_middle :
    HodgeTheaterLink (F.theater source) (F.theater middle)
  middle_to_target :
    HodgeTheaterLink (F.theater middle) (F.theater target)
  source_to_middle_eq_family : source_to_middle = F.link source middle
  middle_to_target_eq_family : middle_to_target = F.link middle target

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
  rw [source_to_target, S.source_to_middle_eq_family,
    S.middle_to_target_eq_family]
  exact F.link_trans_at S.source S.middle S.target

theorem source_to_target_link_q :
    (F.theater S.source).thetaPacket.q =
      (F.theater S.target).thetaPacket.q := by
  simpa [source_to_target] using S.source_to_target_q

theorem source_to_target_link_scale (r : SignedLabel l.value) :
    (F.theater S.source).thetaPacket.scale r =
      (F.theater S.target).thetaPacket.scale r := by
  simpa [source_to_target] using S.source_to_target_scale r

theorem source_to_target_index_eq_of_link_target
    {j : F.index} (h : F.theater S.target = F.theater j) :
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
    B.route.terminal = B.route.terminal := rfl

theorem route_composite_q :
    (B.family.theater B.anchor).thetaPacket.q =
      (B.family.theater B.route.terminal).thetaPacket.q :=
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
