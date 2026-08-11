import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamily

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # The original input of IUT III Theorem 3.11

  The statement of Theorem 3.11 starts with initial Theta-data and a
  collection `{n,m HT}` of distinct Hodge theaters.  It does not start with
  packet profiles, a procession, vertical Kummer maps, evaluation maps, or a
  completed multiradial output.  Those objects are produced by the cited
  IUT I--II propositions.

  This file keeps that quantifier boundary explicit.  `OriginalInput` is the
  only input contract in this module.  The lemmas below use only its source
  fields and the algebra of the already constructed links.  In particular,
  no field in this structure carries a conclusion of Theorem 3.11.

  The older `Theorem311Source.Input` type remains in the boundary module as a
  deliberately named *derived-prerequisite* package.  It is not accepted as
  the original input and is not used by this file.
 -/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe ua uv upi umon ui

namespace Theorem311Source

/-! ## 1. The source index and the input contract -/

abbrev SourceTheorem311Index := Int × Int

structure OriginalInput (l : PrimeGeFive) (V : Type uv) where
  initial : SourceDefinition31Data.{ua} l
  family : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V
  index_equiv : family.index ≃ SourceTheorem311Index
  arithmetic_alignment :
    ∀ i, (family.theater i).arithmetic = initial.arithmetic

namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

def indexOf (n m : Int) : I.family.index :=
  I.index_equiv.symm (n, m)

def theaterAt (n m : Int) :
    HodgeTheater.{ua, uv, upi, umon} l V :=
  I.family.theater (I.indexOf n m)

def linkAt (n m n' m' : Int) :
    HodgeTheaterLink (I.theaterAt n m) (I.theaterAt n' m') :=
  I.family.link (I.indexOf n m) (I.indexOf n' m')

theorem indexOf_apply (n m : Int) :
    I.index_equiv (I.indexOf n m) = (n, m) := by
  exact I.index_equiv.apply_symm_apply (n, m)

theorem indexOf_injective :
    Function.Injective (fun p : SourceTheorem311Index =>
      I.indexOf p.1 p.2) := by
  intro a b h
  apply Prod.ext
  · have hp := congrArg I.index_equiv h
    exact congrArg Prod.fst (by simpa [indexOf] using hp)
  · have hp := congrArg I.index_equiv h
    exact congrArg Prod.snd (by simpa [indexOf] using hp)

theorem indexOf_injective_pair {n m n' m' : Int}
    (h : I.indexOf n m = I.indexOf n' m') :
    n = n' ∧ m = m' := by
  have hp : (n, m) = (n', m') := by
    simpa [indexOf] using congrArg I.index_equiv h
  exact Prod.ext_iff.mp hp

theorem theaterAt_eq_iff {n m n' m' : Int} :
    I.theaterAt n m = I.theaterAt n' m' ↔
      n = n' ∧ m = m' := by
  constructor
  · intro h
    apply I.indexOf_injective_pair
    exact I.family.distinct h
  · rintro ⟨rfl, rfl⟩
    rfl

theorem theaterAt_injective :
    Function.Injective (fun p : SourceTheorem311Index =>
      I.theaterAt p.1 p.2) := by
  intro a b h
  exact Prod.ext_iff.mpr (I.theaterAt_eq_iff.mp h)

theorem theaterAt_arithmetic (n m : Int) :
    (I.theaterAt n m).arithmetic = I.initial.arithmetic :=
  I.arithmetic_alignment (I.indexOf n m)

theorem theaterAt_initial_arithmetic (n m : Int) :
    (I.theaterAt n m).arithmetic =
      I.initial.arithmetic := by
  exact I.theaterAt_arithmetic n m

theorem initial_arithmetic_eq_theaterAt (n m : Int) :
    I.initial.arithmetic = (I.theaterAt n m).arithmetic :=
  (I.theaterAt_arithmetic n m).symm

theorem linkAt_refl (n m : Int) :
    I.linkAt n m n m = HodgeTheaterLink.refl (I.theaterAt n m) :=
  I.family.link_refl (I.indexOf n m)

theorem linkAt_symm (n m n' m' : Int) :
    HodgeTheaterLink.symm (I.linkAt n m n' m') =
      I.linkAt n' m' n m :=
  I.family.link_symm _ _

theorem linkAt_trans (n m n' m' n'' m'' : Int) :
    HodgeTheaterLink.trans (I.linkAt n m n' m')
        (I.linkAt n' m' n'' m'') =
      I.linkAt n m n'' m'' :=
  I.family.link_trans _ _ _

theorem linkAt_q (n m n' m' : Int) :
    (I.theaterAt n m).thetaPacket.q =
      (I.theaterAt n' m').thetaPacket.q :=
  (I.linkAt n m n' m').theta_q_eq

theorem linkAt_scale (n m n' m' : Int) (j : SignedLabel l.value) :
    (I.theaterAt n m).thetaPacket.scale j =
      (I.theaterAt n' m').thetaPacket.scale j :=
  (I.linkAt n m n' m').theta_scale_eq j

def horizontalLink (n m : Int) :
    HodgeTheaterLink (I.theaterAt n m) (I.theaterAt (n + 1) m) :=
  I.linkAt n m (n + 1) m

def verticalLink (n m : Int) :
    HodgeTheaterLink (I.theaterAt n m) (I.theaterAt n (m + 1)) :=
  I.linkAt n m n (m + 1)

theorem horizontal_q (n m : Int) :
    (I.theaterAt n m).thetaPacket.q =
      (I.theaterAt (n + 1) m).thetaPacket.q :=
  I.linkAt_q n m (n + 1) m

theorem vertical_q (n m : Int) :
    (I.theaterAt n m).thetaPacket.q =
      (I.theaterAt n (m + 1)).thetaPacket.q :=
  I.linkAt_q n m n (m + 1)

theorem horizontal_scale (n m : Int) (j : SignedLabel l.value) :
    (I.theaterAt n m).thetaPacket.scale j =
      (I.theaterAt (n + 1) m).thetaPacket.scale j :=
  I.linkAt_scale n m (n + 1) m j

theorem vertical_scale (n m : Int) (j : SignedLabel l.value) :
    (I.theaterAt n m).thetaPacket.scale j =
      (I.theaterAt n (m + 1)).thetaPacket.scale j :=
  I.linkAt_scale n m n (m + 1) j

theorem horizontal_then_vertical (n m : Int) :
    HodgeTheaterLink.trans (I.horizontalLink n m)
        (I.verticalLink (n + 1) m) =
      I.linkAt n m (n + 1) (m + 1) :=
  by simpa [horizontalLink, verticalLink] using
    I.linkAt_trans n m (n + 1) m (n + 1) (m + 1)

theorem vertical_then_horizontal (n m : Int) :
    HodgeTheaterLink.trans (I.verticalLink n m)
        (I.horizontalLink n (m + 1)) =
      I.linkAt n m (n + 1) (m + 1) :=
  by simpa [horizontalLink, verticalLink] using
    I.linkAt_trans n m n (m + 1) (n + 1) (m + 1)

theorem square_link_eq (n m : Int) :
    HodgeTheaterLink.trans (I.horizontalLink n m)
        (I.verticalLink (n + 1) m) =
      HodgeTheaterLink.trans (I.verticalLink n m)
        (I.horizontalLink n (m + 1)) := by
  rw [I.horizontal_then_vertical, I.vertical_then_horizontal]

theorem square_q (n m : Int) :
    (I.theaterAt n m).thetaPacket.q =
      (I.theaterAt (n + 1) (m + 1)).thetaPacket.q :=
  I.linkAt_q n m (n + 1) (m + 1)

theorem square_scale (n m : Int) (j : SignedLabel l.value) :
    (I.theaterAt n m).thetaPacket.scale j =
      (I.theaterAt (n + 1) (m + 1)).thetaPacket.scale j :=
  I.linkAt_scale n m (n + 1) (m + 1) j

/-! ## 2. Arbitrary finite routes in the original lattice -/

def route (p : SourceTheorem311Index) (q : SourceTheorem311Index) :
    SourceHodgeTheaterRoute I.family (I.indexOf p.1 p.2) :=
  SourceHodgeTheaterRoute.consLink (I.indexOf p.1 p.2)
    (I.indexOf q.1 q.2) SourceHodgeTheaterRoute.singleton

theorem route_terminal (p q : SourceTheorem311Index) :
    (I.route p q).terminal = I.indexOf q.1 q.2 := rfl

theorem route_composite (p q : SourceTheorem311Index) :
    (I.route p q).composite = I.linkAt p.1 p.2 q.1 q.2 := by
  rfl

theorem route_q (p q : SourceTheorem311Index) :
    (I.theaterAt p.1 p.2).thetaPacket.q =
      (I.theaterAt q.1 q.2).thetaPacket.q :=
  I.linkAt_q p.1 p.2 q.1 q.2

theorem route_scale (p q : SourceTheorem311Index)
    (j : SignedLabel l.value) :
    (I.theaterAt p.1 p.2).thetaPacket.scale j =
      (I.theaterAt q.1 q.2).thetaPacket.scale j :=
  I.linkAt_scale p.1 p.2 q.1 q.2 j

theorem route_length (p q : SourceTheorem311Index) :
    0 < (I.route p q).length :=
  (I.route p q).length_pos

theorem route_refl (p : SourceTheorem311Index) :
    I.route p p = I.route p p := rfl

theorem route_q_refl (p : SourceTheorem311Index) :
    (I.theaterAt p.1 p.2).thetaPacket.q =
      (I.theaterAt p.1 p.2).thetaPacket.q := rfl

theorem route_scale_refl (p : SourceTheorem311Index)
    (j : SignedLabel l.value) :
    (I.theaterAt p.1 p.2).thetaPacket.scale j =
      (I.theaterAt p.1 p.2).thetaPacket.scale j := rfl

/-! ## 3. Source projections -/

def initialArithmetic : InitialThetaArithmeticData.{ua} l := I.initial.arithmetic

def familyData : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V := I.family

theorem initialArithmetic_eq (n m : Int) :
    I.initialArithmetic = (I.theaterAt n m).arithmetic :=
  I.initial_arithmetic_eq_theaterAt n m

theorem family_theater_injective :
    Function.Injective I.family.theater :=
  I.family.distinct

theorem family_link_q (i j : I.family.index) :
    (I.family.theater i).thetaPacket.q =
      (I.family.theater j).thetaPacket.q :=
  I.family.link_q i j

theorem family_link_scale (i j : I.family.index)
    (r : SignedLabel l.value) :
    (I.family.theater i).thetaPacket.scale r =
      (I.family.theater j).thetaPacket.scale r :=
  I.family.link_scale i j r

theorem family_permutation_q (i : I.family.index) :
    (I.family.theater (I.family.permutation i)).thetaPacket.q =
      (I.family.theater i).thetaPacket.q :=
  I.family.permutation_q i

theorem family_permutation_scale (i : I.family.index)
    (r : SignedLabel l.value) :
    (I.family.theater (I.family.permutation i)).thetaPacket.scale r =
      (I.family.theater i).thetaPacket.scale r :=
  I.family.permutation_scale i r

/-! ## 4. The lattice translations supplied by the original indexing -/

def horizontalIndex (p : SourceTheorem311Index) : SourceTheorem311Index :=
  (p.1 + 1, p.2)

def verticalIndex (p : SourceTheorem311Index) : SourceTheorem311Index :=
  (p.1, p.2 + 1)

def horizontalIndexInv (p : SourceTheorem311Index) : SourceTheorem311Index :=
  (p.1 - 1, p.2)

def verticalIndexInv (p : SourceTheorem311Index) : SourceTheorem311Index :=
  (p.1, p.2 - 1)

theorem horizontalIndexInv_left (p : SourceTheorem311Index) :
    horizontalIndexInv (horizontalIndex p) = p := by
  rcases p with ⟨n, m⟩
  simp [horizontalIndex, horizontalIndexInv]

theorem horizontalIndexInv_right (p : SourceTheorem311Index) :
    horizontalIndex (horizontalIndexInv p) = p := by
  rcases p with ⟨n, m⟩
  simp [horizontalIndex, horizontalIndexInv]

theorem verticalIndexInv_left (p : SourceTheorem311Index) :
    verticalIndexInv (verticalIndex p) = p := by
  rcases p with ⟨n, m⟩
  simp [verticalIndex, verticalIndexInv]

theorem verticalIndexInv_right (p : SourceTheorem311Index) :
    verticalIndex (verticalIndexInv p) = p := by
  rcases p with ⟨n, m⟩
  simp [verticalIndex, verticalIndexInv]

theorem horizontalIndex_bijective :
    Function.Bijective horizontalIndex := by
  refine ⟨?_, ?_⟩
  · intro p q h
    have := congrArg horizontalIndexInv h
    simpa [horizontalIndexInv_left] using this
  · intro p
    exact ⟨horizontalIndexInv p, horizontalIndexInv_right p⟩

theorem verticalIndex_bijective :
    Function.Bijective verticalIndex := by
  refine ⟨?_, ?_⟩
  · intro p q h
    have := congrArg verticalIndexInv h
    simpa [verticalIndexInv_left] using this
  · intro p
    exact ⟨verticalIndexInv p, verticalIndexInv_right p⟩

def horizontalIndexEquiv : SourceTheorem311Index ≃ SourceTheorem311Index :=
  Equiv.ofBijective horizontalIndex horizontalIndex_bijective

def verticalIndexEquiv : SourceTheorem311Index ≃ SourceTheorem311Index :=
  Equiv.ofBijective verticalIndex verticalIndex_bijective

def horizontalShift : I.family.index → I.family.index := fun i =>
  I.indexOf (horizontalIndex (I.index_equiv i)).1
    (horizontalIndex (I.index_equiv i)).2

def verticalShift : I.family.index → I.family.index := fun i =>
  I.indexOf (verticalIndex (I.index_equiv i)).1
    (verticalIndex (I.index_equiv i)).2

def horizontalShiftInv : I.family.index → I.family.index := fun i =>
  I.indexOf (horizontalIndexInv (I.index_equiv i)).1
    (horizontalIndexInv (I.index_equiv i)).2

def verticalShiftInv : I.family.index → I.family.index := fun i =>
  I.indexOf (verticalIndexInv (I.index_equiv i)).1
    (verticalIndexInv (I.index_equiv i)).2

theorem horizontalShift_index (i : I.family.index) :
    I.index_equiv (I.horizontalShift i) =
      horizontalIndex (I.index_equiv i) := by
  unfold horizontalShift
  exact I.indexOf_apply _ _

theorem verticalShift_index (i : I.family.index) :
    I.index_equiv (I.verticalShift i) =
      verticalIndex (I.index_equiv i) := by
  unfold verticalShift
  exact I.indexOf_apply _ _

theorem horizontalShiftInv_index (i : I.family.index) :
    I.index_equiv (I.horizontalShiftInv i) =
      horizontalIndexInv (I.index_equiv i) := by
  unfold horizontalShiftInv
  exact I.indexOf_apply _ _

theorem verticalShiftInv_index (i : I.family.index) :
    I.index_equiv (I.verticalShiftInv i) =
      verticalIndexInv (I.index_equiv i) := by
  unfold verticalShiftInv
  exact I.indexOf_apply _ _

theorem horizontalShiftInv_left (i : I.family.index) :
    I.horizontalShiftInv (I.horizontalShift i) = i := by
  apply I.index_equiv.injective
  rw [I.horizontalShiftInv_index, I.horizontalShift_index]
  exact horizontalIndexInv_left (I.index_equiv i)

theorem horizontalShiftInv_right (i : I.family.index) :
    I.horizontalShift (I.horizontalShiftInv i) = i := by
  apply I.index_equiv.injective
  rw [I.horizontalShift_index, I.horizontalShiftInv_index]
  exact horizontalIndexInv_right (I.index_equiv i)

theorem verticalShiftInv_left (i : I.family.index) :
    I.verticalShiftInv (I.verticalShift i) = i := by
  apply I.index_equiv.injective
  rw [I.verticalShiftInv_index, I.verticalShift_index]
  exact verticalIndexInv_left (I.index_equiv i)

theorem verticalShiftInv_right (i : I.family.index) :
    I.verticalShift (I.verticalShiftInv i) = i := by
  apply I.index_equiv.injective
  rw [I.verticalShift_index, I.verticalShiftInv_index]
  exact verticalIndexInv_right (I.index_equiv i)

theorem horizontalShift_bijective :
    Function.Bijective I.horizontalShift := by
  refine ⟨?_, ?_⟩
  · intro i j h
    have := congrArg I.horizontalShiftInv h
    simpa [I.horizontalShiftInv_left] using this
  · intro i
    exact ⟨I.horizontalShiftInv i, I.horizontalShiftInv_right i⟩

theorem verticalShift_bijective :
    Function.Bijective I.verticalShift := by
  refine ⟨?_, ?_⟩
  · intro i j h
    have := congrArg I.verticalShiftInv h
    simpa [I.verticalShiftInv_left] using this
  · intro i
    exact ⟨I.verticalShiftInv i, I.verticalShiftInv_right i⟩

def horizontalShiftEquiv : I.family.index ≃ I.family.index :=
  Equiv.ofBijective I.horizontalShift I.horizontalShift_bijective

def verticalShiftEquiv : I.family.index ≃ I.family.index :=
  Equiv.ofBijective I.verticalShift I.verticalShift_bijective

theorem horizontal_shift_theater (n m : Int) :
    I.horizontalShift (I.indexOf n m) = I.indexOf (n + 1) m := by
  apply I.index_equiv.injective
  rw [I.horizontalShift_index, I.indexOf_apply, I.indexOf_apply]
  rfl

theorem vertical_shift_theater (n m : Int) :
    I.verticalShift (I.indexOf n m) = I.indexOf n (m + 1) := by
  apply I.index_equiv.injective
  rw [I.verticalShift_index, I.indexOf_apply, I.indexOf_apply]
  rfl

theorem horizontal_shift_inverse_theater (n m : Int) :
    I.horizontalShiftInv (I.indexOf n m) = I.indexOf (n - 1) m := by
  apply I.index_equiv.injective
  rw [I.horizontalShiftInv_index, I.indexOf_apply, I.indexOf_apply]
  rfl

theorem vertical_shift_inverse_theater (n m : Int) :
    I.verticalShiftInv (I.indexOf n m) = I.indexOf n (m - 1) := by
  apply I.index_equiv.injective
  rw [I.verticalShiftInv_index, I.indexOf_apply, I.indexOf_apply]
  rfl

theorem horizontal_vertical_index_commute (p : SourceTheorem311Index) :
    horizontalIndex (verticalIndex p) = verticalIndex (horizontalIndex p) := by
  rcases p with ⟨n, m⟩
  simp [horizontalIndex, verticalIndex]

theorem horizontal_vertical_shift_commute (i : I.family.index) :
    I.horizontalShift (I.verticalShift i) =
      I.verticalShift (I.horizontalShift i) := by
  apply I.index_equiv.injective
  rw [I.horizontalShift_index (I.verticalShift i),
    I.verticalShift_index i,
    I.verticalShift_index (I.horizontalShift i),
    I.horizontalShift_index i]
  exact horizontal_vertical_index_commute (I.index_equiv i)

theorem horizontal_vertical_link_commute (n m : Int) :
    HodgeTheaterLink.trans (I.horizontalLink n m)
        (I.verticalLink (n + 1) m) =
      HodgeTheaterLink.trans (I.verticalLink n m)
        (I.horizontalLink n (m + 1)) :=
  I.square_link_eq n m

theorem horizontal_vertical_q_commute (n m : Int) :
    (I.theaterAt (n + 1) m).thetaPacket.q =
      (I.theaterAt n (m + 1)).thetaPacket.q :=
  I.linkAt_q (n + 1) m n (m + 1)

theorem horizontal_vertical_scale_commute (n m : Int)
    (j : SignedLabel l.value) :
    (I.theaterAt (n + 1) m).thetaPacket.scale j =
      (I.theaterAt n (m + 1)).thetaPacket.scale j :=
  I.linkAt_scale (n + 1) m n (m + 1) j

theorem shift_q_invariant (i : I.family.index) :
    (I.family.theater i).thetaPacket.q =
      (I.family.theater (I.horizontalShift i)).thetaPacket.q := by
  exact I.family_link_q i (I.horizontalShift i)

theorem shift_scale_invariant (i : I.family.index)
    (j : SignedLabel l.value) :
    (I.family.theater i).thetaPacket.scale j =
      (I.family.theater (I.horizontalShift i)).thetaPacket.scale j := by
  exact I.family_link_scale i (I.horizontalShift i) j

theorem vertical_shift_q_invariant (i : I.family.index) :
    (I.family.theater i).thetaPacket.q =
      (I.family.theater (I.verticalShift i)).thetaPacket.q := by
  exact I.family_link_q i (I.verticalShift i)

theorem vertical_shift_scale_invariant (i : I.family.index)
    (j : SignedLabel l.value) :
    (I.family.theater i).thetaPacket.scale j =
      (I.family.theater (I.verticalShift i)).thetaPacket.scale j := by
  exact I.family_link_scale i (I.verticalShift i) j

/-! ## 5. Two-dimensional translations and their naturality -/

def translateIndex (a b : Int) (p : SourceTheorem311Index) :
    SourceTheorem311Index :=
  (p.1 + a, p.2 + b)

def translateIndexInv (a b : Int) (p : SourceTheorem311Index) :
    SourceTheorem311Index :=
  (p.1 - a, p.2 - b)

theorem translateIndexInv_left (a b : Int)
    (p : SourceTheorem311Index) :
    translateIndexInv a b (translateIndex a b p) = p := by
  rcases p with ⟨n, m⟩
  simp [translateIndex, translateIndexInv]

theorem translateIndexInv_right (a b : Int)
    (p : SourceTheorem311Index) :
    translateIndex a b (translateIndexInv a b p) = p := by
  rcases p with ⟨n, m⟩
  simp [translateIndex, translateIndexInv]

theorem translateIndex_injective (a b : Int) :
    Function.Injective (translateIndex a b) := by
  intro p q h
  have h' := congrArg (translateIndexInv a b) h
  simpa [translateIndexInv_left] using h'

theorem translateIndex_surjective (a b : Int) :
    Function.Surjective (translateIndex a b) := by
  intro p
  exact ⟨translateIndexInv a b p, translateIndexInv_right a b p⟩

theorem translateIndex_bijective (a b : Int) :
    Function.Bijective (translateIndex a b) :=
  ⟨translateIndex_injective a b, translateIndex_surjective a b⟩

def translateIndexEquiv (a b : Int) :
    SourceTheorem311Index ≃ SourceTheorem311Index :=
  Equiv.ofBijective (translateIndex a b) (translateIndex_bijective a b)

theorem translateIndex_zero (p : SourceTheorem311Index) :
    translateIndex 0 0 p = p := by
  rcases p with ⟨n, m⟩
  simp [translateIndex]

theorem translateIndex_add (a b c d : Int)
    (p : SourceTheorem311Index) :
    translateIndex a b (translateIndex c d p) =
      translateIndex (c + a) (d + b) p := by
  rcases p with ⟨n, m⟩
  simp [translateIndex, add_assoc]

theorem translateIndex_commute (a b c d : Int)
    (p : SourceTheorem311Index) :
    translateIndex a b (translateIndex c d p) =
      translateIndex c d (translateIndex a b p) := by
  rcases p with ⟨n, m⟩
  simp [translateIndex, add_comm, add_left_comm]

def translate (a b : Int) (i : I.family.index) : I.family.index :=
  I.indexOf (translateIndex a b (I.index_equiv i)).1
    (translateIndex a b (I.index_equiv i)).2

def translateInv (a b : Int) (i : I.family.index) : I.family.index :=
  I.indexOf (translateIndexInv a b (I.index_equiv i)).1
    (translateIndexInv a b (I.index_equiv i)).2

theorem translate_index (a b : Int) (i : I.family.index) :
    I.index_equiv (I.translate a b i) =
      translateIndex a b (I.index_equiv i) := by
  unfold translate
  exact I.indexOf_apply _ _

theorem translate_inv_index (a b : Int) (i : I.family.index) :
    I.index_equiv (I.translateInv a b i) =
      translateIndexInv a b (I.index_equiv i) := by
  unfold translateInv
  exact I.indexOf_apply _ _

theorem translateInv_left (a b : Int) (i : I.family.index) :
    I.translateInv a b (I.translate a b i) = i := by
  apply I.index_equiv.injective
  rw [I.translate_inv_index, I.translate_index]
  exact translateIndexInv_left a b (I.index_equiv i)

theorem translateInv_right (a b : Int) (i : I.family.index) :
    I.translate a b (I.translateInv a b i) = i := by
  apply I.index_equiv.injective
  rw [I.translate_index, I.translate_inv_index]
  exact translateIndexInv_right a b (I.index_equiv i)

theorem translate_bijective (a b : Int) :
    Function.Bijective (I.translate a b) := by
  refine ⟨?_, ?_⟩
  · intro i j h
    have h' := congrArg (I.translateInv a b) h
    simpa [I.translateInv_left] using h'
  · intro i
    exact ⟨I.translateInv a b i, I.translateInv_right a b i⟩

def translateEquiv (a b : Int) : I.family.index ≃ I.family.index :=
  Equiv.ofBijective (I.translate a b) (I.translate_bijective a b)

theorem translate_zero (i : I.family.index) :
    I.translate 0 0 i = i := by
  apply I.index_equiv.injective
  rw [I.translate_index]
  exact translateIndex_zero (I.index_equiv i)

theorem translate_add (a b c d : Int) (i : I.family.index) :
    I.translate a b (I.translate c d i) =
      I.translate (c + a) (d + b) i := by
  apply I.index_equiv.injective
  rw [I.translate_index, I.translate_index, I.translate_index]
  exact translateIndex_add a b c d (I.index_equiv i)

theorem translate_commute (a b c d : Int) (i : I.family.index) :
    I.translate a b (I.translate c d i) =
      I.translate c d (I.translate a b i) := by
  apply I.index_equiv.injective
  rw [I.translate_index, I.translate_index, I.translate_index,
    I.translate_index]
  exact translateIndex_commute a b c d (I.index_equiv i)

theorem translate_theater (a b n m : Int) :
    I.translate a b (I.indexOf n m) =
      I.indexOf (n + a) (m + b) := by
  apply I.index_equiv.injective
  rw [I.translate_index, I.indexOf_apply, I.indexOf_apply]
  rfl

theorem translateInv_theater (a b n m : Int) :
    I.translateInv a b (I.indexOf n m) =
      I.indexOf (n - a) (m - b) := by
  apply I.index_equiv.injective
  rw [I.translate_inv_index, I.indexOf_apply, I.indexOf_apply]
  rfl

theorem translate_q (a b n m : Int) :
    (I.theaterAt n m).thetaPacket.q =
      (I.theaterAt (n + a) (m + b)).thetaPacket.q :=
  I.linkAt_q n m (n + a) (m + b)

theorem translate_scale (a b n m : Int) (j : SignedLabel l.value) :
    (I.theaterAt n m).thetaPacket.scale j =
      (I.theaterAt (n + a) (m + b)).thetaPacket.scale j :=
  I.linkAt_scale n m (n + a) (m + b) j

theorem translate_q_symmetric (a b n m : Int) :
    (I.theaterAt (n + a) (m + b)).thetaPacket.q =
      (I.theaterAt n m).thetaPacket.q :=
  (I.translate_q a b n m).symm

theorem translate_scale_symmetric (a b n m : Int)
    (j : SignedLabel l.value) :
    (I.theaterAt (n + a) (m + b)).thetaPacket.scale j =
      (I.theaterAt n m).thetaPacket.scale j :=
  (I.translate_scale a b n m j).symm

theorem translate_link_q (a b n m n' m' : Int) :
    (I.theaterAt (n + a) (m + b)).thetaPacket.q =
      (I.theaterAt (n' + a) (m' + b)).thetaPacket.q :=
  I.linkAt_q (n + a) (m + b) (n' + a) (m' + b)

theorem translate_link_scale (a b n m n' m' : Int)
    (j : SignedLabel l.value) :
    (I.theaterAt (n + a) (m + b)).thetaPacket.scale j =
      (I.theaterAt (n' + a) (m' + b)).thetaPacket.scale j :=
  I.linkAt_scale (n + a) (m + b) (n' + a) (m' + b) j

theorem translate_square_q (a b n m : Int) :
    (I.theaterAt n m).thetaPacket.q =
      (I.theaterAt (n + a + 1) (m + b + 1)).thetaPacket.q := by
  exact I.linkAt_q n m (n + a + 1) (m + b + 1)

theorem translate_square_scale (a b n m : Int)
    (j : SignedLabel l.value) :
    (I.theaterAt n m).thetaPacket.scale j =
      (I.theaterAt (n + a + 1) (m + b + 1)).thetaPacket.scale j := by
  exact I.linkAt_scale n m (n + a + 1) (m + b + 1) j

/-! ## 6. Explicit finite paths in the indexed lattice -/

def path (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) :
    SourceHodgeTheaterRoute I.family (I.indexOf p.1 p.2) :=
  tail.map (fun q => I.indexOf q.1 q.2)

theorem path_terminal (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) :
    (I.path p tail).terminal =
      SourceHodgeTheaterRoute.terminalFrom
        (I.indexOf p.1 p.2) (tail.map (fun q => I.indexOf q.1 q.2)) := rfl

theorem path_length (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) :
    0 < (I.path p tail).length :=
  (I.path p tail).length_pos

theorem path_composite_q (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) :
    (I.theaterAt p.1 p.2).thetaPacket.q =
      (I.family.theater (I.path p tail).terminal).thetaPacket.q :=
  (I.path p tail).composite_q

theorem path_composite_scale (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) (j : SignedLabel l.value) :
    (I.theaterAt p.1 p.2).thetaPacket.scale j =
      (I.family.theater (I.path p tail).terminal).thetaPacket.scale j :=
  (I.path p tail).composite_scale j

def pathAppend (p : SourceTheorem311Index)
    (left right : List SourceTheorem311Index) :
    SourceHodgeTheaterRoute I.family (I.indexOf p.1 p.2) :=
  I.path p (left ++ right)

theorem pathAppend_length (p : SourceTheorem311Index)
    (left right : List SourceTheorem311Index) :
    0 < (I.pathAppend p left right).length :=
  (I.pathAppend p left right).length_pos

theorem pathAppend_q (p : SourceTheorem311Index)
    (left right : List SourceTheorem311Index) :
    (I.theaterAt p.1 p.2).thetaPacket.q =
      (I.family.theater (I.pathAppend p left right).terminal).thetaPacket.q :=
  (I.pathAppend p left right).composite_q

theorem pathAppend_scale (p : SourceTheorem311Index)
    (left right : List SourceTheorem311Index) (j : SignedLabel l.value) :
    (I.theaterAt p.1 p.2).thetaPacket.scale j =
      (I.family.theater (I.pathAppend p left right).terminal).thetaPacket.scale j :=
  (I.pathAppend p left right).composite_scale j

theorem path_singleton_q (p q : SourceTheorem311Index) :
    (I.theaterAt p.1 p.2).thetaPacket.q =
      (I.theaterAt q.1 q.2).thetaPacket.q :=
  I.route_q p q

theorem path_singleton_scale (p q : SourceTheorem311Index)
    (j : SignedLabel l.value) :
    (I.theaterAt p.1 p.2).thetaPacket.scale j =
      (I.theaterAt q.1 q.2).thetaPacket.scale j :=
  I.route_scale p q j

theorem path_to_path_q (p q r : SourceTheorem311Index) :
    (I.theaterAt p.1 p.2).thetaPacket.q =
      (I.theaterAt r.1 r.2).thetaPacket.q := by
  exact (I.path_singleton_q p q).trans (I.path_singleton_q q r)

theorem path_to_path_scale (p q r : SourceTheorem311Index)
    (j : SignedLabel l.value) :
    (I.theaterAt p.1 p.2).thetaPacket.scale j =
      (I.theaterAt r.1 r.2).thetaPacket.scale j := by
  exact (I.path_singleton_scale p q j).trans
    (I.path_singleton_scale q r j)

theorem path_q_independent_of_tail (p : SourceTheorem311Index)
    (tail₁ tail₂ : List SourceTheorem311Index)
    (hterminal : (I.path p tail₁).terminal =
      (I.path p tail₂).terminal) :
    (I.family.theater (I.path p tail₁).terminal).thetaPacket.q =
      (I.family.theater (I.path p tail₂).terminal).thetaPacket.q := by
  rw [hterminal]

theorem path_scale_independent_of_tail (p : SourceTheorem311Index)
    (tail₁ tail₂ : List SourceTheorem311Index)
    (hterminal : (I.path p tail₁).terminal =
      (I.path p tail₂).terminal) (j : SignedLabel l.value) :
    (I.family.theater (I.path p tail₁).terminal).thetaPacket.scale j =
      (I.family.theater (I.path p tail₂).terminal).thetaPacket.scale j := by
  rw [hterminal]

theorem path_composite_eq_family_link (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) :
    (I.path p tail).composite =
      I.family.link (I.indexOf p.1 p.2) (I.path p tail).terminal :=
  (I.path p tail).composite_eq_family_link

/-! ## 7. Prime-strip projections of the original source family

The preceding route lemmas concern the theta packet carried by a theater.  The
other part of a source theater is its prime strip.  This section exposes that
part without changing the input contract: every definition is a projection of
`OriginalInput.family`, and every compatibility statement is a projection of a
field of an already supplied `HodgeTheaterLink`.
-/

def primeStripAt (n m : Int) : FPrimeStrip.{umon, uv, upi} V :=
  (I.theaterAt n m).primeStrip

def dPrimeStripAt (n m : Int) : DPrimeStrip.{upi, uv} V :=
  (I.primeStripAt n m).toDPrimeStrip

def monoAnalyticAt (n m : Int) : V → Type upi :=
  (I.primeStripAt n m).monoAnalytic

def geometricAt (n m : Int) (v : V) :
    Subgroup ((I.primeStripAt n m).toDPrimeStrip.Pi v) :=
  (I.primeStripAt n m).toDPrimeStrip.geometric v

def valueMonoidAt (n m : Int) (v : V) : Type umon :=
  (I.primeStripAt n m).Mon v

def primeStripLinkAt (n m n' m' : Int) :
    FPrimeStripEquiv (I.primeStripAt n m) (I.primeStripAt n' m') :=
  (I.linkAt n m n' m').primeStripEquiv

def dPrimeStripLinkAt (n m n' m' : Int) :
    DPrimeStripEquiv (I.dPrimeStripAt n m) (I.dPrimeStripAt n' m') :=
  (I.primeStripLinkAt n m n' m').toD

theorem primeStripAt_eq_family (n m : Int) :
    I.primeStripAt n m =
      (I.family.theater (I.indexOf n m)).primeStrip := rfl

theorem dPrimeStripAt_eq_toD (n m : Int) :
    I.dPrimeStripAt n m = (I.primeStripAt n m).toDPrimeStrip := rfl

theorem monoAnalyticAt_eq (n m : Int) (v : V) :
    I.monoAnalyticAt n m v = (I.primeStripAt n m).G v := rfl

theorem geometricAt_eq_kernel (n m : Int) (v : V) :
    I.geometricAt n m v = (I.primeStripAt n m).toDPrimeStrip.geometric v := rfl

theorem primeStripLinkAt_eq (n m n' m' : Int) :
    I.primeStripLinkAt n m n' m' =
      (I.linkAt n m n' m').primeStripEquiv := rfl

theorem dPrimeStripLinkAt_eq_toD (n m n' m' : Int) :
    I.dPrimeStripLinkAt n m n' m' =
      (I.primeStripLinkAt n m n' m').toD := rfl

theorem primeStripLinkAt_compatProj (n m n' m' : Int)
    (v : V) (x : (I.primeStripAt n m).toDPrimeStrip.Pi v) :
    (I.primeStripAt n' m').proj v
        ((I.primeStripLinkAt n m n' m').isoPi v x) =
      (I.primeStripLinkAt n m n' m').isoG v
        ((I.primeStripAt n m).proj v x) := by
  exact (I.primeStripLinkAt n m n' m').compatProj_apply v x

theorem primeStripLinkAt_compatAction (n m n' m' : Int)
    (v : V) (g : (I.primeStripAt n m).toDPrimeStrip.Pi v)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripLinkAt n m n' m').isoMon v
        ((I.primeStripAt n m).action v g x) =
      (I.primeStripAt n' m').action v
        ((I.primeStripLinkAt n m n' m').isoPi v g)
        ((I.primeStripLinkAt n m n' m').isoMon v x) := by
  exact (I.primeStripLinkAt n m n' m').compatAction v g x

theorem primeStripLinkAt_compatDegree (n m n' m' : Int)
    (v : V) (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripAt n' m').degree v
        ((I.primeStripLinkAt n m n' m').isoMon v x) =
      (I.primeStripAt n m).degree v x := by
  exact (I.primeStripLinkAt n m n' m').compatDegree v x

theorem dPrimeStripLinkAt_compatProj (n m n' m' : Int)
    (v : V) (x : (I.dPrimeStripAt n m).Pi v) :
    (I.dPrimeStripAt n' m').proj v
        ((I.dPrimeStripLinkAt n m n' m').isoPi v x) =
      (I.dPrimeStripLinkAt n m n' m').isoG v
        ((I.dPrimeStripAt n m).proj v x) := by
  exact (I.dPrimeStripLinkAt n m n' m').compat_apply v x

theorem primeStripLinkAt_isoPi_bijective (n m n' m' : Int) (v : V) :
    Function.Bijective ((I.primeStripLinkAt n m n' m').isoPi v) := by
  exact (I.primeStripLinkAt n m n' m').isoPi v |>.bijective

theorem primeStripLinkAt_isoG_bijective (n m n' m' : Int) (v : V) :
    Function.Bijective ((I.primeStripLinkAt n m n' m').isoG v) := by
  exact (I.primeStripLinkAt n m n' m').isoG v |>.bijective

theorem primeStripLinkAt_isoMon_bijective (n m n' m' : Int) (v : V) :
    Function.Bijective ((I.primeStripLinkAt n m n' m').isoMon v) := by
  exact (I.primeStripLinkAt n m n' m').isoMon v |>.bijective

theorem dPrimeStripLinkAt_isoPi_bijective (n m n' m' : Int) (v : V) :
    Function.Bijective ((I.dPrimeStripLinkAt n m n' m').isoPi v) := by
  exact (I.dPrimeStripLinkAt n m n' m').isoPi v |>.bijective

theorem dPrimeStripLinkAt_isoG_bijective (n m n' m' : Int) (v : V) :
    Function.Bijective ((I.dPrimeStripLinkAt n m n' m').isoG v) := by
  exact (I.dPrimeStripLinkAt n m n' m').isoG v |>.bijective

theorem primeStripLinkAt_isoPi_apply_mul (n m n' m' : Int) (v : V)
    (x y : (I.primeStripAt n m).toDPrimeStrip.Pi v) :
    (I.primeStripLinkAt n m n' m').isoPi v (x * y) =
      (I.primeStripLinkAt n m n' m').isoPi v x *
        (I.primeStripLinkAt n m n' m').isoPi v y := by
  exact (I.primeStripLinkAt n m n' m').isoPi v |>.map_mul x y

theorem primeStripLinkAt_isoG_apply_mul (n m n' m' : Int) (v : V)
    (x y : (I.primeStripAt n m).G v) :
    (I.primeStripLinkAt n m n' m').isoG v (x * y) =
      (I.primeStripLinkAt n m n' m').isoG v x *
        (I.primeStripLinkAt n m n' m').isoG v y := by
  exact (I.primeStripLinkAt n m n' m').isoG v |>.map_mul x y

theorem primeStripLinkAt_isoMon_apply_mul (n m n' m' : Int) (v : V)
    (x y : (I.primeStripAt n m).Mon v) :
    (I.primeStripLinkAt n m n' m').isoMon v (x * y) =
      (I.primeStripLinkAt n m n' m').isoMon v x *
        (I.primeStripLinkAt n m n' m').isoMon v y := by
  exact (I.primeStripLinkAt n m n' m').isoMon v |>.map_mul x y

theorem primeStripLinkAt_isoPi_apply_one (n m n' m' : Int) (v : V) :
    (I.primeStripLinkAt n m n' m').isoPi v 1 = 1 := by
  exact (I.primeStripLinkAt n m n' m').isoPi v |>.map_one

theorem primeStripLinkAt_isoG_apply_one (n m n' m' : Int) (v : V) :
    (I.primeStripLinkAt n m n' m').isoG v 1 = 1 := by
  exact (I.primeStripLinkAt n m n' m').isoG v |>.map_one

theorem primeStripLinkAt_isoMon_apply_one (n m n' m' : Int) (v : V) :
    (I.primeStripLinkAt n m n' m').isoMon v 1 = 1 := by
  exact (I.primeStripLinkAt n m n' m').isoMon v |>.map_one

theorem primeStripLinkAt_isoPi_apply_inv (n m n' m' : Int) (v : V)
    (x : (I.primeStripAt n m).toDPrimeStrip.Pi v) :
    (I.primeStripLinkAt n m n' m').isoPi v x⁻¹ =
      ((I.primeStripLinkAt n m n' m').isoPi v x)⁻¹ := by
  exact (I.primeStripLinkAt n m n' m').isoPi v |>.map_inv x

theorem primeStripLinkAt_isoG_apply_inv (n m n' m' : Int) (v : V)
    (x : (I.primeStripAt n m).G v) :
    (I.primeStripLinkAt n m n' m').isoG v x⁻¹ =
      ((I.primeStripLinkAt n m n' m').isoG v x)⁻¹ := by
  exact (I.primeStripLinkAt n m n' m').isoG v |>.map_inv x

theorem primeStripLinkAt_degree_preserves_one (n m n' m' : Int) (v : V) :
    (I.primeStripAt n m').degree v 1 =
      (I.primeStripAt n m').degree v 1 := rfl

theorem primeStrip_degree_one (n m : Int) (v : V) :
    (I.primeStripAt n m).degree v 1 = 1 := by
  exact (I.primeStripAt n m).degree v |>.map_one

theorem primeStrip_degree_mul (n m : Int) (v : V)
    (x y : (I.primeStripAt n m).Mon v) :
    (I.primeStripAt n m).degree v (x * y) =
      (I.primeStripAt n m).degree v x *
        (I.primeStripAt n m).degree v y := by
  exact (I.primeStripAt n m).degree v |>.map_mul x y

theorem primeStrip_action_one (n m : Int) (v : V)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripAt n m).action v 1 x = x :=
  (I.primeStripAt n m).action_one v x

theorem primeStrip_action_mul (n m : Int) (v : V)
    (g h : (I.primeStripAt n m).toDPrimeStrip.Pi v)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripAt n m).action v (g * h) x =
      (I.primeStripAt n m).action v g
        ((I.primeStripAt n m).action v h x) :=
  (I.primeStripAt n m).action_mul v g h x

theorem geometricAt_one_mem (n m : Int) (v : V) :
    (1 : (I.dPrimeStripAt n m).Pi v) ∈ I.geometricAt n m v := by
  change (1 : (I.dPrimeStripAt n m).Pi v) ∈
    (I.dPrimeStripAt n m).geometric v
  rw [(I.dPrimeStripAt n m).geometric_carrier]
  exact (I.dPrimeStripAt n m).proj v |>.map_one

theorem geometricAt_mem_iff (n m : Int) (v : V)
    (x : (I.dPrimeStripAt n m).Pi v) :
    x ∈ I.geometricAt n m v ↔ (I.dPrimeStripAt n m).proj v x = 1 :=
  (I.dPrimeStripAt n m).geometric_carrier v x

theorem geometricAt_subgroup_mul (n m : Int) (v : V)
    {x y : (I.dPrimeStripAt n m).Pi v}
    (hx : x ∈ I.geometricAt n m v)
    (hy : y ∈ I.geometricAt n m v) :
    x * y ∈ I.geometricAt n m v := by
  rw [I.geometricAt_mem_iff] at hx hy ⊢
  calc
    (I.dPrimeStripAt n m).proj v (x * y) =
      (I.dPrimeStripAt n m).proj v x *
          (I.dPrimeStripAt n m).proj v y :=
      ((I.dPrimeStripAt n m).proj v).map_mul x y
    _ = 1 := by rw [hx, hy, one_mul]

theorem geometricAt_subgroup_inv (n m : Int) (v : V)
    {x : (I.dPrimeStripAt n m).Pi v}
    (hx : x ∈ I.geometricAt n m v) :
    x⁻¹ ∈ I.geometricAt n m v := by
  rw [I.geometricAt_mem_iff] at hx ⊢
  calc
    (I.dPrimeStripAt n m).proj v x⁻¹ =
        ((I.dPrimeStripAt n m).proj v x)⁻¹ :=
      ((I.dPrimeStripAt n m).proj v).map_inv x
    _ = 1 := by rw [hx, inv_one]

theorem dPrimeStripLinkAt_compat_geometric (n m n' m' : Int) (v : V)
    (x : (I.dPrimeStripAt n m).Pi v) :
    x ∈ I.geometricAt n m v ↔
      (I.dPrimeStripLinkAt n m n' m').isoPi v x ∈
        I.geometricAt n' m' v := by
  rw [I.geometricAt_mem_iff, I.geometricAt_mem_iff,
    I.dPrimeStripLinkAt_compatProj]
  constructor
  · intro h
    rw [h, map_one]
  · intro h
    apply (I.dPrimeStripLinkAt n m n' m').isoG v |>.injective
    simpa using h

theorem primeStripLinkAt_degree_naturality (n m n' m' : Int) (v : V)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripAt n' m').degree v
        ((I.primeStripLinkAt n m n' m').isoMon v x) =
      (I.primeStripAt n m).degree v x :=
  I.primeStripLinkAt_compatDegree n m n' m' v x

theorem primeStripLinkAt_action_naturality (n m n' m' : Int) (v : V)
    (g : (I.primeStripAt n m).toDPrimeStrip.Pi v)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripLinkAt n m n' m').isoMon v
        ((I.primeStripAt n m).action v g x) =
      (I.primeStripAt n' m').action v
        ((I.primeStripLinkAt n m n' m').isoPi v g)
        ((I.primeStripLinkAt n m n' m').isoMon v x) :=
  I.primeStripLinkAt_compatAction n m n' m' v g x

theorem dPrimeStripLinkAt_projection_naturality (n m n' m' : Int)
    (v : V) (x : (I.dPrimeStripAt n m).Pi v) :
    (I.dPrimeStripAt n' m').proj v
        ((I.dPrimeStripLinkAt n m n' m').isoPi v x) =
      (I.dPrimeStripLinkAt n m n' m').isoG v
        ((I.dPrimeStripAt n m).proj v x) :=
  I.dPrimeStripLinkAt_compatProj n m n' m' v x

theorem primeStripLinkAt_isoPi_surjective (n m n' m' : Int) (v : V)
    (y : (I.primeStripAt n' m').toDPrimeStrip.Pi v) :
    ∃ x, (I.primeStripLinkAt n m n' m').isoPi v x = y := by
  exact (I.primeStripLinkAt_isoPi_bijective n m n' m' v).2 y

theorem primeStripLinkAt_isoG_surjective (n m n' m' : Int) (v : V)
    (y : (I.primeStripAt n' m').G v) :
    ∃ x, (I.primeStripLinkAt n m n' m').isoG v x = y := by
  exact (I.primeStripLinkAt_isoG_bijective n m n' m' v).2 y

theorem primeStripLinkAt_isoMon_surjective (n m n' m' : Int) (v : V)
    (y : (I.primeStripAt n' m').Mon v) :
    ∃ x, (I.primeStripLinkAt n m n' m').isoMon v x = y := by
  exact (I.primeStripLinkAt_isoMon_bijective n m n' m' v).2 y

theorem dPrimeStripLinkAt_isoPi_surjective (n m n' m' : Int) (v : V)
    (y : (I.dPrimeStripAt n' m').Pi v) :
    ∃ x, (I.dPrimeStripLinkAt n m n' m').isoPi v x = y := by
  exact (I.dPrimeStripLinkAt_isoPi_bijective n m n' m' v).2 y

theorem dPrimeStripLinkAt_isoG_surjective (n m n' m' : Int) (v : V)
    (y : (I.dPrimeStripAt n' m').G v) :
    ∃ x, (I.dPrimeStripLinkAt n m n' m').isoG v x = y := by
  exact (I.dPrimeStripLinkAt_isoG_bijective n m n' m' v).2 y

theorem primeStripLinkAt_isoPi_injective (n m n' m' : Int) (v : V) :
    Function.Injective ((I.primeStripLinkAt n m n' m').isoPi v) := by
  exact (I.primeStripLinkAt_isoPi_bijective n m n' m' v).1

theorem primeStripLinkAt_isoG_injective (n m n' m' : Int) (v : V) :
    Function.Injective ((I.primeStripLinkAt n m n' m').isoG v) := by
  exact (I.primeStripLinkAt_isoG_bijective n m n' m' v).1

theorem primeStripLinkAt_isoMon_injective (n m n' m' : Int) (v : V) :
    Function.Injective ((I.primeStripLinkAt n m n' m').isoMon v) := by
  exact (I.primeStripLinkAt_isoMon_bijective n m n' m' v).1

/-! The endpoint-indexed link laws are stated at the prime-strip level as
well.  They are useful when a later construction forgets theta packets but
keeps the source geometric or value-group data. -/

theorem primeStripLinkAt_refl (n m : Int) :
    I.primeStripLinkAt n m n m =
      FPrimeStripEquiv.refl (I.primeStripAt n m) := by
  exact congrArg HodgeTheaterLink.primeStripEquiv
    (I.linkAt_refl n m)

theorem primeStripLinkAt_symm (n m n' m' : Int) :
    FPrimeStripEquiv.symm (I.primeStripLinkAt n m n' m') =
      I.primeStripLinkAt n' m' n m := by
  exact congrArg HodgeTheaterLink.primeStripEquiv
    (I.linkAt_symm n m n' m')

theorem primeStripLinkAt_trans (n m n' m' n'' m'' : Int) :
    FPrimeStripEquiv.trans (I.primeStripLinkAt n m n' m')
        (I.primeStripLinkAt n' m' n'' m'') =
      I.primeStripLinkAt n m n'' m'' := by
  exact congrArg HodgeTheaterLink.primeStripEquiv
    (I.linkAt_trans n m n' m' n'' m'')

theorem dPrimeStripLinkAt_refl (n m : Int) :
    I.dPrimeStripLinkAt n m n m =
      DPrimeStripEquiv.refl (I.dPrimeStripAt n m) := by
  exact congrArg FPrimeStripEquiv.toD
    (I.primeStripLinkAt_refl n m)

theorem dPrimeStripLinkAt_symm (n m n' m' : Int) :
    DPrimeStripEquiv.symm (I.dPrimeStripLinkAt n m n' m') =
      I.dPrimeStripLinkAt n' m' n m := by
  exact congrArg FPrimeStripEquiv.toD
    (I.primeStripLinkAt_symm n m n' m')

theorem dPrimeStripLinkAt_trans (n m n' m' n'' m'' : Int) :
    DPrimeStripEquiv.trans (I.dPrimeStripLinkAt n m n' m')
        (I.dPrimeStripLinkAt n' m' n'' m'') =
      I.dPrimeStripLinkAt n m n'' m'' := by
  exact congrArg FPrimeStripEquiv.toD
    (I.primeStripLinkAt_trans n m n' m' n'' m'')

theorem primeStripLinkAt_trans_isoPi (n m n' m' n'' m'' : Int)
    (v : V) (x : (I.primeStripAt n m).toDPrimeStrip.Pi v) :
    (I.primeStripLinkAt n m n'' m'').isoPi v x =
      (I.primeStripLinkAt n' m' n'' m'').isoPi v
        ((I.primeStripLinkAt n m n' m').isoPi v x) := by
  rw [← I.primeStripLinkAt_trans]
  rfl

theorem primeStripLinkAt_trans_isoG (n m n' m' n'' m'' : Int)
    (v : V) (x : (I.primeStripAt n m).G v) :
    (I.primeStripLinkAt n m n'' m'').isoG v x =
      (I.primeStripLinkAt n' m' n'' m'').isoG v
        ((I.primeStripLinkAt n m n' m').isoG v x) := by
  rw [← I.primeStripLinkAt_trans]
  rfl

theorem primeStripLinkAt_trans_isoMon (n m n' m' n'' m'' : Int)
    (v : V) (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripLinkAt n m n'' m'').isoMon v x =
      (I.primeStripLinkAt n' m' n'' m'').isoMon v
        ((I.primeStripLinkAt n m n' m').isoMon v x) := by
  rw [← I.primeStripLinkAt_trans]
  rfl

theorem dPrimeStripLinkAt_trans_isoPi (n m n' m' n'' m'' : Int)
    (v : V) (x : (I.dPrimeStripAt n m).Pi v) :
    (I.dPrimeStripLinkAt n m n'' m'').isoPi v x =
      (I.dPrimeStripLinkAt n' m' n'' m'').isoPi v
        ((I.dPrimeStripLinkAt n m n' m').isoPi v x) := by
  rw [← I.dPrimeStripLinkAt_trans]
  rfl

theorem dPrimeStripLinkAt_trans_isoG (n m n' m' n'' m'' : Int)
    (v : V) (x : (I.dPrimeStripAt n m).G v) :
    (I.dPrimeStripLinkAt n m n'' m'').isoG v x =
      (I.dPrimeStripLinkAt n' m' n'' m'').isoG v
        ((I.dPrimeStripLinkAt n m n' m').isoG v x) := by
  rw [← I.dPrimeStripLinkAt_trans]
  rfl

theorem primeStripLinkAt_symm_isoPi_apply (n m n' m' : Int) (v : V)
    (x : (I.primeStripAt n m).toDPrimeStrip.Pi v) :
    (I.primeStripLinkAt n' m' n m).isoPi v
        ((I.primeStripLinkAt n m n' m').isoPi v x) = x := by
  rw [← I.primeStripLinkAt_symm]
  exact (I.primeStripLinkAt n m n' m').isoPi v |>.symm_apply_apply x

theorem primeStripLinkAt_symm_isoG_apply (n m n' m' : Int) (v : V)
    (x : (I.primeStripAt n m).G v) :
    (I.primeStripLinkAt n' m' n m).isoG v
        ((I.primeStripLinkAt n m n' m').isoG v x) = x := by
  rw [← I.primeStripLinkAt_symm]
  exact (I.primeStripLinkAt n m n' m').isoG v |>.symm_apply_apply x

theorem primeStripLinkAt_symm_isoMon_apply (n m n' m' : Int) (v : V)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripLinkAt n' m' n m).isoMon v
        ((I.primeStripLinkAt n m n' m').isoMon v x) = x := by
  rw [← I.primeStripLinkAt_symm]
  exact (I.primeStripLinkAt n m n' m').isoMon v |>.symm_apply_apply x

theorem dPrimeStripLinkAt_symm_isoPi_apply (n m n' m' : Int) (v : V)
    (x : (I.dPrimeStripAt n m).Pi v) :
    (I.dPrimeStripLinkAt n' m' n m).isoPi v
        ((I.dPrimeStripLinkAt n m n' m').isoPi v x) = x := by
  rw [← I.dPrimeStripLinkAt_symm]
  exact (I.dPrimeStripLinkAt n m n' m').isoPi v |>.symm_apply_apply x

theorem dPrimeStripLinkAt_symm_isoG_apply (n m n' m' : Int) (v : V)
    (x : (I.dPrimeStripAt n m).G v) :
    (I.dPrimeStripLinkAt n' m' n m).isoG v
        ((I.dPrimeStripLinkAt n m n' m').isoG v x) = x := by
  rw [← I.dPrimeStripLinkAt_symm]
  exact (I.dPrimeStripLinkAt n m n' m').isoG v |>.symm_apply_apply x

theorem route_primeStripEquiv (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) :
    (I.path p tail).composite.primeStripEquiv =
      (I.family.link (I.indexOf p.1 p.2) (I.path p tail).terminal).primeStripEquiv := by
  rw [I.path_composite_eq_family_link]

theorem route_dPrimeStripEquiv (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) :
    (I.path p tail).composite.primeStripEquiv.toD =
      (I.family.link (I.indexOf p.1 p.2) (I.path p tail).terminal).primeStripEquiv.toD := by
  exact congrArg FPrimeStripEquiv.toD (I.route_primeStripEquiv p tail)

/-! ## 8. Route transport at each prime place -/

theorem route_compatProj (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) (v : V)
    (x : (I.primeStripAt p.1 p.2).toDPrimeStrip.Pi v) :
    ((I.family.theater (I.path p tail).terminal).primeStrip.proj v)
        ((I.path p tail).composite.primeStripEquiv.isoPi v x) =
      (I.path p tail).composite.primeStripEquiv.isoG v
        ((I.primeStripAt p.1 p.2).proj v x) := by
  exact (I.path p tail).composite.primeStripEquiv.compatProj_apply v x

theorem route_compatAction (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) (v : V)
    (g : (I.primeStripAt p.1 p.2).toDPrimeStrip.Pi v)
    (x : (I.primeStripAt p.1 p.2).Mon v) :
    (I.path p tail).composite.primeStripEquiv.isoMon v
        ((I.primeStripAt p.1 p.2).action v g x) =
      ((I.family.theater (I.path p tail).terminal).primeStrip.action v)
        ((I.path p tail).composite.primeStripEquiv.isoPi v g)
        ((I.path p tail).composite.primeStripEquiv.isoMon v x) := by
  exact (I.path p tail).composite.primeStripEquiv.compatAction v g x

theorem route_compatDegree (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) (v : V)
    (x : (I.primeStripAt p.1 p.2).Mon v) :
    ((I.family.theater (I.path p tail).terminal).primeStrip.degree v)
        ((I.path p tail).composite.primeStripEquiv.isoMon v x) =
      (I.primeStripAt p.1 p.2).degree v x := by
  exact (I.path p tail).composite.primeStripEquiv.compatDegree v x

theorem route_degree_preserves_totalDegree (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) (s : Finset V)
    (x : ∀ v, (I.primeStripAt p.1 p.2).Mon v) :
    ((I.family.theater (I.path p tail).terminal).primeStrip.totalDegree s)
        (fun v => (I.path p tail).composite.primeStripEquiv.isoMon v (x v)) =
      (I.primeStripAt p.1 p.2).totalDegree s x := by
  apply Finset.sum_congr rfl
  intro v hv
  exact I.route_compatDegree p tail v (x v)

theorem route_primeStrip_isoPi_bijective (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) (v : V) :
    Function.Bijective ((I.path p tail).composite.primeStripEquiv.isoPi v) := by
  exact ((I.path p tail).composite.primeStripEquiv.isoPi v).bijective

theorem route_primeStrip_isoG_bijective (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) (v : V) :
    Function.Bijective ((I.path p tail).composite.primeStripEquiv.isoG v) := by
  exact ((I.path p tail).composite.primeStripEquiv.isoG v).bijective

theorem route_primeStrip_isoMon_bijective (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) (v : V) :
    Function.Bijective ((I.path p tail).composite.primeStripEquiv.isoMon v) := by
  exact ((I.path p tail).composite.primeStripEquiv.isoMon v).bijective

theorem route_primeStrip_isoPi_surjective (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) (v : V)
    (y : ((I.family.theater (I.path p tail).terminal).primeStrip.toDPrimeStrip).Pi v) :
    ∃ x, (I.path p tail).composite.primeStripEquiv.isoPi v x = y := by
  exact (I.route_primeStrip_isoPi_bijective p tail v).2 y

theorem route_primeStrip_isoG_surjective (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) (v : V)
    (y : ((I.family.theater (I.path p tail).terminal).primeStrip).G v) :
    ∃ x, (I.path p tail).composite.primeStripEquiv.isoG v x = y := by
  exact (I.route_primeStrip_isoG_bijective p tail v).2 y

theorem route_primeStrip_isoMon_surjective (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) (v : V)
    (y : ((I.family.theater (I.path p tail).terminal).primeStrip).Mon v) :
    ∃ x, (I.path p tail).composite.primeStripEquiv.isoMon v x = y := by
  exact (I.route_primeStrip_isoMon_bijective p tail v).2 y

theorem route_primeStrip_isoPi_injective (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) (v : V) :
    Function.Injective ((I.path p tail).composite.primeStripEquiv.isoPi v) := by
  exact (I.route_primeStrip_isoPi_bijective p tail v).1

theorem route_primeStrip_isoG_injective (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) (v : V) :
    Function.Injective ((I.path p tail).composite.primeStripEquiv.isoG v) := by
  exact (I.route_primeStrip_isoG_bijective p tail v).1

theorem route_primeStrip_isoMon_injective (p : SourceTheorem311Index)
    (tail : List SourceTheorem311Index) (v : V) :
    Function.Injective ((I.path p tail).composite.primeStripEquiv.isoMon v) := by
  exact (I.route_primeStrip_isoMon_bijective p tail v).1

/-! ## 9. Definition 3.1 clauses at the original-input root

These lemmas deliberately have `initial` on the left of every statement.  In
this way the later dependency modules can use a named source fact without
confusing a projection with a construction.  In particular, no theorem here
turns an arbitrary field, curve, or place partition into a Definition 3.1
datum; it only reuses the datum which the theorem's opening quantifier gives.
-/

def initialThetaInput : InitialThetaInput.{ua} l :=
  I.initial.toInitialThetaInput

theorem initialThetaInput_eq_projection :
    I.initialThetaInput = I.initial.toInitialThetaInput := rfl

theorem initial_selected_nonempty : Nonempty I.initial.selectedPlaces :=
  I.initial.selected_nonempty

@[reducible] noncomputable def initial_bad_finite : Fintype I.initial.badPlaces :=
  I.initial.bad_finite

def initial_bad_included (b : I.initial.badPlaces) :
    I.initial.selectedPlaces :=
  I.initial.reduction.partition.badIncluded b

theorem initial_bad_label_compatibility (b : I.initial.badPlaces) :
    I.initial.reduction.partition.selectedLabel
        (I.initial.reduction.partition.badIncluded b) =
      I.initial.reduction.partition.badLabel b :=
  I.initial.reduction.partition.labels_agree b

theorem initial_stable_reduction (b : I.initial.badPlaces) :
    I.initial.reduction.stableReduction b :=
  I.initial.stable_reduction b

theorem initial_multiplicative_reduction (b : I.initial.badPlaces) :
    I.initial.reduction.multiplicativeReduction b :=
  I.initial.multiplicative_reduction b

theorem initial_split_multiplicative_reduction (b : I.initial.badPlaces) :
    I.initial.reduction.splitMultiplicativeReduction b :=
  I.initial.split_multiplicative_reduction b

theorem initial_q_parameter_nonzero (b : I.initial.badPlaces) :
    I.initial.reduction.qParameter b ≠ 0 :=
  I.initial.q_parameter_nonzero b

theorem initial_q_parameter_contracting (b : I.initial.badPlaces) :
    ‖I.initial.reduction.qParameter b‖ < 1 :=
  I.initial.q_parameter_contracting b

theorem initial_q_parameter_neq_one (b : I.initial.badPlaces) :
    I.initial.reduction.qParameter b ≠ 1 :=
  I.initial.reduction.q_ne_one b

theorem initial_q_parameter_nonnegative_norm (b : I.initial.badPlaces) :
    0 ≤ ‖I.initial.reduction.qParameter b‖ :=
  norm_nonneg _

theorem initial_q_parameter_in_unit_interval (b : I.initial.badPlaces) :
    ‖I.initial.reduction.qParameter b‖ ∈ Set.Ioo (0 : Real) 1 := by
  exact ⟨norm_pos_iff.mpr (I.initial.q_parameter_nonzero b),
    I.initial.q_parameter_contracting b⟩

theorem initial_q_parameter_power_nonzero (b : I.initial.badPlaces)
    (n : Nat) : I.initial.reduction.qParameter b ^ n ≠ 0 :=
  pow_ne_zero n (I.initial.q_parameter_nonzero b)

theorem initial_q_parameter_power_contracting (b : I.initial.badPlaces)
    (n : Nat) (hn : 0 < n) :
    ‖I.initial.reduction.qParameter b‖ ^ n < 1 := by
  exact pow_lt_one₀ (I.initial_q_parameter_nonnegative_norm b)
    (I.initial.q_parameter_contracting b) (Nat.ne_of_gt hn)

theorem initial_torsion_nonempty :
    Nonempty I.initial.torsion.torsionCarrier :=
  I.initial.torsion_nonempty

theorem initial_torsion_representation_surjective :
    Function.Surjective I.initial.torsion.representation :=
  I.initial.torsion.representation_surjective_spec

theorem initial_torsion_image_contains_SL2 :
    I.initial.torsion.imageContainsSL2 :=
  I.initial.torsion_image_contains_SL2

theorem initial_torsion_six_independent :
    I.initial.torsion.sixTorsionIndependent :=
  I.initial.torsion_six_independent

theorem initial_torsion_l_compatible :
    I.initial.torsion.lTorsionCompatible :=
  I.initial.torsion_l_compatible

theorem initial_torsion_all_clauses :
    I.initial.torsion.imageContainsSL2 ∧
      I.initial.torsion.sixTorsionIndependent ∧
      I.initial.torsion.lTorsionCompatible := by
  exact ⟨I.initial_torsion_image_contains_SL2,
    I.initial_torsion_six_independent,
    I.initial_torsion_l_compatible⟩

theorem initial_cover_surjective :
    Function.Surjective I.initial.orbicurve.coverToPunctured :=
  I.initial.cover_surjective

theorem initial_cover_cusp_count_pos : 0 < I.initial.orbicurve.cuspCount :=
  I.initial.cover_cusp_count_pos

theorem initial_exact_injection_injective :
    Function.Injective I.initial.orbicurve.exactSequence.injection :=
  I.initial.exact_injection_injective

theorem initial_exact_projection_surjective :
    Function.Surjective I.initial.orbicurve.exactSequence.projection :=
  I.initial.exact_projection_surjective

theorem initial_exact_at_cover (x : I.initial.orbicurve.exactSequence.coverGroup) :
    I.initial.orbicurve.exactSequence.projection x = 1 ↔
      ∃ y, I.initial.orbicurve.exactSequence.injection y = x :=
  I.initial.orbicurve.exactSequence.exact_at_cover_iff x

theorem initial_section_right_inverse
    (x : I.initial.orbicurve.exactSequence.baseGroup) :
    I.initial.orbicurve.exactSequence.projection
        (I.initial.orbicurve.exactSequence.sectionMap x) = x :=
  I.initial.orbicurve.exactSequence.section_right_inverse_spec x

theorem initial_section_bijective :
    Function.Bijective I.initial.sections.sectionMap :=
  I.initial.section_map_bijective

theorem initial_finite_place_data : I.initial.sections.finitePlaceData :=
  I.initial.finite_place_data

theorem initial_infinite_place_data : I.initial.sections.infinitePlaceData :=
  I.initial.infinite_place_data

theorem initial_cusp_positive : 0 < I.initial.cusp.epsilon :=
  I.initial.cusp_positive

theorem initial_cusp_nonzero : I.initial.cusp.epsilon ≠ 0 :=
  I.initial.cusp_nonzero

theorem initial_cusp_compatibility : I.initial.cusp.epsilon_compatibility :=
  I.initial.cusp_compatibility

theorem initial_compatibility_bundle :
    I.initial.arithmetic_reduction_compatibility ∧
      I.initial.arithmetic_torsion_compatibility ∧
      I.initial.arithmetic_orbicurve_compatibility ∧
      I.initial.arithmetic_section_compatibility ∧
      I.initial.arithmetic_cusp_compatibility := by
  exact ⟨I.initial.arithmetic_reduction_spec,
    I.initial.arithmetic_torsion_spec,
    I.initial.arithmetic_orbicurve_spec,
    I.initial.arithmetic_section_spec,
    I.initial.arithmetic_cusp_spec⟩

theorem initial_source_condition_bundle :
    Nonempty I.initial.selectedPlaces ∧
      Nonempty (Fintype I.initial.badPlaces) ∧
      (∀ b, I.initial.reduction.stableReduction b) ∧
      (∀ b, I.initial.reduction.splitMultiplicativeReduction b) ∧
      I.initial.torsion.imageContainsSL2 ∧
      I.initial.torsion.sixTorsionIndependent ∧
      I.initial.torsion.lTorsionCompatible ∧
      Function.Surjective I.initial.orbicurve.coverToPunctured ∧
      Function.Injective I.initial.orbicurve.exactSequence.injection ∧
      Function.Surjective I.initial.orbicurve.exactSequence.projection ∧
      Function.Bijective I.initial.sections.sectionMap ∧
      0 < I.initial.cusp.epsilon := by
  exact I.initial.source_condition_bundle

theorem initial_toInitialThetaInput_arithmetic :
    I.initialThetaInput.arithmetic = I.initial.arithmetic := rfl

theorem initial_toInitialThetaInput_selectedPlaces :
    I.initialThetaInput.selectedPlaces = I.initial.selectedPlaces := rfl

theorem initial_toInitialThetaInput_badPlaces :
    I.initialThetaInput.badPlaces = I.initial.badPlaces := rfl

theorem initial_toInitialThetaInput_badIncluded (b : I.initial.badPlaces) :
    I.initialThetaInput.badIncluded b =
      I.initial.reduction.partition.badIncluded b := rfl

theorem initial_toInitialThetaInput_stableReduction
    (b : I.initial.badPlaces) :
    I.initialThetaInput.stableReduction b =
      I.initial.reduction.stableReduction b := rfl

theorem initial_toInitialThetaInput_torsionImage :
    I.initialThetaInput.torsionImage =
      I.initial.torsion.imageContainsSL2 := rfl

theorem initial_toInitialThetaInput_cuspParameter :
    I.initialThetaInput.cuspParameter = I.initial.cusp.epsilon := rfl

theorem initial_arithmetic_sqrt_neg_one :
    HasSqrtNegOne I.initial.arithmetic.F :=
  I.initial.arithmetic.tower.sqrtNegOne

theorem initial_arithmetic_degree_prime_to_l :
    Nat.Coprime (Module.finrank I.initial.arithmetic.Fmod
      I.initial.arithmetic.F) l.value :=
  I.initial.arithmetic.tower.degreePrimeToL

theorem initial_arithmetic_galois_Fmod_F :
    IsGalois I.initial.arithmetic.Fmod I.initial.arithmetic.F := inferInstance

theorem initial_arithmetic_galois_F_K :
    IsGalois I.initial.arithmetic.F I.initial.arithmetic.K := inferInstance

theorem initial_arithmetic_finite_Fmod_F :
    FiniteDimensional I.initial.arithmetic.Fmod I.initial.arithmetic.F :=
  inferInstance

theorem initial_arithmetic_finite_F_K :
    FiniteDimensional I.initial.arithmetic.F I.initial.arithmetic.K :=
  inferInstance

def initial_arithmetic_curve :
    PuncturedEllipticCurve I.initial.arithmetic.F :=
  I.initial.arithmetic.curve

theorem family_arithmetic_alignment (i : I.family.index) :
    (I.family.theater i).arithmetic = I.initial.arithmetic :=
  I.arithmetic_alignment i

theorem family_arithmetic_alignment_symm (i : I.family.index) :
    I.initial.arithmetic = (I.family.theater i).arithmetic :=
  (I.family_arithmetic_alignment i).symm

theorem theaterAt_arithmetic_alignment (n m : Int) :
    (I.theaterAt n m).arithmetic = I.initial.arithmetic :=
  I.theaterAt_arithmetic n m

theorem theaterAt_arithmetic_alignment_symm (n m : Int) :
    I.initial.arithmetic = (I.theaterAt n m).arithmetic :=
  (I.theaterAt_arithmetic n m).symm

theorem initial_reduction_for_theater (n m : Int) :
    Nonempty I.initial.selectedPlaces :=
  I.initial_selected_nonempty

theorem initial_torsion_for_theater (n m : Int) :
    I.initial.torsion.imageContainsSL2 :=
  I.initial_torsion_image_contains_SL2

theorem initial_exact_sequence_for_theater (n m : Int) :
    Function.Surjective I.initial.orbicurve.exactSequence.projection :=
  I.initial_exact_projection_surjective

theorem initial_cusp_for_theater (n m : Int) :
    0 < I.initial.cusp.epsilon :=
  I.initial_cusp_positive

theorem arithmetic_alignment_trans (i j : I.family.index) :
    (I.family.theater i).arithmetic = (I.family.theater j).arithmetic := by
  exact (I.family_arithmetic_alignment i).trans
    (I.family_arithmetic_alignment j).symm

theorem arithmetic_alignment_of_theater_eq (i j : I.family.index)
    (h : I.family.theater i = I.family.theater j) :
    (I.family.theater i).arithmetic = (I.family.theater j).arithmetic := by
  rw [h]

theorem source_root_bundle (n m : Int) :
    (I.theaterAt n m).arithmetic = I.initial.arithmetic ∧
      Nonempty I.initial.selectedPlaces ∧
      I.initial.torsion.imageContainsSL2 ∧
      Function.Surjective I.initial.orbicurve.exactSequence.projection ∧
      0 < I.initial.cusp.epsilon := by
  exact ⟨I.theaterAt_arithmetic_alignment n m,
    I.initial_selected_nonempty,
    I.initial_torsion_image_contains_SL2,
    I.initial_exact_projection_surjective,
    I.initial_cusp_positive⟩

/-! ## 10. Explicit endpoint data for arbitrary source links -/

def link_source_primeStrip (n m n' m' : Int) :
    ∀ v, (I.primeStripAt n m).toDPrimeStrip.Pi v ≃*
      (I.primeStripAt n' m').toDPrimeStrip.Pi v := by
  intro v
  exact (I.primeStripLinkAt n m n' m').isoPi v

def link_target_primeStrip (n m n' m' : Int) :
    ∀ v, (I.primeStripAt n m).G v ≃* (I.primeStripAt n' m').G v := by
  intro v
  exact (I.primeStripLinkAt n m n' m').isoG v

def link_value_monoid (n m n' m' : Int) :
    ∀ v, (I.primeStripAt n m).Mon v ≃*
      (I.primeStripAt n' m').Mon v := by
  intro v
  exact (I.primeStripLinkAt n m n' m').isoMon v

theorem link_projection_commutes (n m n' m' : Int) (v : V)
    (x : (I.primeStripAt n m).toDPrimeStrip.Pi v) :
    (I.primeStripAt n' m').proj v
        ((I.primeStripLinkAt n m n' m').isoPi v x) =
      (I.primeStripLinkAt n m n' m').isoG v
        ((I.primeStripAt n m).proj v x) :=
  I.primeStripLinkAt_compatProj n m n' m' v x

theorem link_action_commutes (n m n' m' : Int) (v : V)
    (g : (I.primeStripAt n m).toDPrimeStrip.Pi v)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripLinkAt n m n' m').isoMon v
        ((I.primeStripAt n m).action v g x) =
      (I.primeStripAt n' m').action v
        ((I.primeStripLinkAt n m n' m').isoPi v g)
        ((I.primeStripLinkAt n m n' m').isoMon v x) :=
  I.primeStripLinkAt_compatAction n m n' m' v g x

theorem link_degree_commutes (n m n' m' : Int) (v : V)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripAt n' m').degree v
        ((I.primeStripLinkAt n m n' m').isoMon v x) =
      (I.primeStripAt n m).degree v x :=
  I.primeStripLinkAt_compatDegree n m n' m' v x

theorem link_geometric_commutes (n m n' m' : Int) (v : V)
    (x : (I.dPrimeStripAt n m).Pi v) :
    x ∈ I.geometricAt n m v ↔
      (I.dPrimeStripLinkAt n m n' m').isoPi v x ∈
        I.geometricAt n' m' v :=
  I.dPrimeStripLinkAt_compat_geometric n m n' m' v x

theorem link_q_and_primeStrip (n m n' m' : Int) :
    (I.theaterAt n m).thetaPacket.q =
        (I.theaterAt n' m').thetaPacket.q ∧
      Nonempty (FPrimeStripEquiv (I.primeStripAt n m)
        (I.primeStripAt n' m')) := by
  exact ⟨I.linkAt_q n m n' m',
    ⟨I.primeStripLinkAt n m n' m'⟩⟩

theorem link_scale_and_primeStrip (n m n' m' : Int)
    (j : SignedLabel l.value) :
    (I.theaterAt n m).thetaPacket.scale j =
        (I.theaterAt n' m').thetaPacket.scale j ∧
      Nonempty (DPrimeStripEquiv (I.dPrimeStripAt n m)
        (I.dPrimeStripAt n' m')) := by
  exact ⟨I.linkAt_scale n m n' m' j,
    ⟨I.dPrimeStripLinkAt n m n' m'⟩⟩

end OriginalInput

end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def sourceOriginalInputBoundary : Obligation :=
  { id := "IUT-III.theorem-3.11-original-input-boundary"
    source := "IUT III, Theorem 3.11 (opening quantifiers)"
    status := VerificationStatus.interface
    note :=
      "OriginalInput contains only Definition 3.1 data, a family of actual " ++
        "distinct Hodge theaters indexed up to equivalence by Z x Z, and the " ++
        "relative arithmetic alignment stated by the phrase 'relative to the " ++
        "given initial Theta-data'. Packet profiles, D-prime-strip processions, " ++
        "vertical log-Kummer maps, evaluations, and Theorem 3.11 outputs are " ++
        "deliberately absent. The projections and lattice-link squares are " ++
        "proved; the cited IUT I--II construction of the derived objects remains " ++
        "the next obligation."
    dependsOn :=
      [ "IUT-I.initial-theta-data",
        "IUT-I.hodge-theater-family-source-laws" ] }

end LeanFormal.IUT.Audit
