import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2OriginalArrows
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # The source-constructed D-shadow of the H1/H2 input

  The opening data of Theorem 3.11 contains the family of distinct
  `Theta+-ell-NF-Hodge theaters`.  Each member already carries an
  `FPrimeStrip`; its `toD` image and every source link therefore give a
  concrete D-prime-strip shadow.  This file packages that construction before
  any packet, Frobenioid, or Kummer object is introduced.

  The word `shadow` is deliberate.  IUT III Theorem 1.5(i) constructs a
  D-Theta-Hodge theater by vertical coricity and supplies more structure than
  the bare `toD` image.  We construct all data that follows from the supplied
  family, and state the remaining coricity realization as a separate gate.
  No theorem below identifies the shadow with that coric theater without the
  corresponding source theorem.

  Source references: IUT III Theorem 3.11 opening paragraph; Theorem 1.5(i);
  IUT I Definition 5.2 and Proposition 6.9(ii).
-/

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

open OriginalInputArrows

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. D-shadow family -/

structure DThetaShadow where
  index : Type ui
  dStrip : index -> DPrimeStrip.{upi, uv} V
  dStrip_source : forall i, dStrip i =
    (I.family.theater i).primeStrip.toD
  dLink : forall i j, DPrimeStripEquiv (dStrip i) (dStrip j)
  dLink_source : forall i j,
    dLink i j = (I.family.link i j).primeStripEquiv.toD

def dThetaShadow : I.DThetaShadow where
  index := I.family.index
  dStrip := fun i => (I.family.theater i).primeStrip.toD
  dStrip_source := by intro i; rfl
  dLink := fun i j => (I.family.link i j).primeStripEquiv.toD
  dLink_source := by intro i j; rfl

@[simp] theorem dThetaShadow_index :
    (I.dThetaShadow).index = I.family.index := rfl

@[simp] theorem dThetaShadow_strip (i : I.family.index) :
    (I.dThetaShadow).dStrip i =
      (I.family.theater i).primeStrip.toD := rfl

@[simp] theorem dThetaShadow_link (i j : I.family.index) :
    (I.dThetaShadow).dLink i j =
      (I.family.link i j).primeStripEquiv.toD := rfl

theorem dThetaShadow_source (i : I.family.index) :
    (I.dThetaShadow).dStrip i =
      (I.family.theater i).primeStrip.toD :=
  (I.dThetaShadow).dStrip_source i

theorem dThetaShadow_link_source (i j : I.family.index) :
    (I.dThetaShadow).dLink i j =
      (I.family.link i j).primeStripEquiv.toD :=
  (I.dThetaShadow).dLink_source i j

theorem dThetaShadow_family_distinct :
    Function.Injective I.family.theater :=
  I.family.distinct

/-! ## 2. D-link groupoid laws -/

theorem dThetaShadow_link_refl (i : I.family.index) :
    (I.dThetaShadow).dLink i i =
      DPrimeStripEquiv.refl ((I.dThetaShadow).dStrip i) := by
  change (I.family.link i i).primeStripEquiv.toD = _
  rw [I.family.link_refl]
  rfl

theorem dThetaShadow_link_symm (i j : I.family.index) :
    DPrimeStripEquiv.symm ((I.dThetaShadow).dLink i j) =
      (I.dThetaShadow).dLink j i := by
  change DPrimeStripEquiv.symm
      ((I.family.link i j).primeStripEquiv.toD) = _
  rw [FPrimeStripEquiv.toD_symm]
  exact congrArg FPrimeStripEquiv.toD
    (congrArg HodgeTheaterLink.primeStripEquiv
      (I.family.link_symm i j))

theorem dThetaShadow_link_trans (i j k : I.family.index) :
    DPrimeStripEquiv.trans ((I.dThetaShadow).dLink i j)
        ((I.dThetaShadow).dLink j k) =
      (I.dThetaShadow).dLink i k := by
  change DPrimeStripEquiv.trans
      ((I.family.link i j).primeStripEquiv.toD)
      ((I.family.link j k).primeStripEquiv.toD) = _
  rw [FPrimeStripEquiv.toD_trans]
  exact congrArg FPrimeStripEquiv.toD
    (congrArg HodgeTheaterLink.primeStripEquiv
      (I.family.link_trans i j k))

theorem dThetaShadow_link_inverse (i j : I.family.index) :
    DPrimeStripEquiv.trans ((I.dThetaShadow).dLink i j)
        ((I.dThetaShadow).dLink j i) =
      DPrimeStripEquiv.refl ((I.dThetaShadow).dStrip i) := by
  calc
    DPrimeStripEquiv.trans ((I.dThetaShadow).dLink i j)
        ((I.dThetaShadow).dLink j i) =
        (I.dThetaShadow).dLink i i :=
      I.dThetaShadow_link_trans i j i
    _ = DPrimeStripEquiv.refl ((I.dThetaShadow).dStrip i) :=
      I.dThetaShadow_link_refl i

theorem dThetaShadow_link_inverse_right (i j : I.family.index) :
    DPrimeStripEquiv.trans ((I.dThetaShadow).dLink j i)
        ((I.dThetaShadow).dLink i j) =
      DPrimeStripEquiv.refl ((I.dThetaShadow).dStrip j) := by
  calc
    DPrimeStripEquiv.trans ((I.dThetaShadow).dLink j i)
        ((I.dThetaShadow).dLink i j) =
        (I.dThetaShadow).dLink j j :=
      I.dThetaShadow_link_trans j i j
    _ = DPrimeStripEquiv.refl ((I.dThetaShadow).dStrip j) :=
      I.dThetaShadow_link_refl j

theorem dThetaShadow_link_bijective_pi (i j : I.family.index) (v : V) :
    Function.Bijective
      (((I.dThetaShadow).dLink i j).isoPi v) := by
  exact (((I.dThetaShadow).dLink i j).isoPi v).bijective

theorem dThetaShadow_link_bijective_g (i j : I.family.index) (v : V) :
    Function.Bijective
      (((I.dThetaShadow).dLink i j).isoG v) := by
  exact (((I.dThetaShadow).dLink i j).isoG v).bijective

theorem dThetaShadow_link_projection (i j : I.family.index) (v : V)
    (x : ((I.dThetaShadow).dStrip i).Pi v) :
    (I.dThetaShadow.dStrip j).proj v
        ((I.dThetaShadow.dLink i j).isoPi v x) =
      (I.dThetaShadow.dLink i j).isoG v
        ((I.dThetaShadow.dStrip i).proj v x) := by
  exact (I.dThetaShadow.dLink i j).compat_apply v x

theorem dThetaShadow_link_refl_pi (i : I.family.index) (v : V)
    (x : ((I.dThetaShadow).dStrip i).Pi v) :
    ((I.dThetaShadow).dLink i i).isoPi v x = x := by
  rw [I.dThetaShadow_link_refl]
  rfl

theorem dThetaShadow_link_refl_g (i : I.family.index) (v : V)
    (x : ((I.dThetaShadow).dStrip i).G v) :
    ((I.dThetaShadow).dLink i i).isoG v x = x := by
  rw [I.dThetaShadow_link_refl]
  rfl

/-! ## 3. D-theater shadow at lattice coordinates -/

def dThetaShadowAt (n m : Int) : DPrimeStrip.{upi, uv} V :=
  (I.theaterAt n m).primeStrip.toD

def dThetaShadowLinkAt (n m n' m' : Int) :
    DPrimeStripEquiv (I.dThetaShadowAt n m) (I.dThetaShadowAt n' m') :=
  (I.linkAt n m n' m').primeStripEquiv.toD

@[simp] theorem dThetaShadowAt_eq (n m : Int) :
    I.dThetaShadowAt n m =
      (I.family.theater (I.indexOf n m)).primeStrip.toD := rfl

@[simp] theorem dThetaShadowLinkAt_eq (n m n' m' : Int) :
    I.dThetaShadowLinkAt n m n' m' =
      (I.family.link (I.indexOf n m) (I.indexOf n' m')).primeStripEquiv.toD := rfl

theorem dThetaShadowLinkAt_refl (n m : Int) :
    I.dThetaShadowLinkAt n m n m =
      DPrimeStripEquiv.refl (I.dThetaShadowAt n m) := by
  change (I.linkAt n m n m).primeStripEquiv.toD = _
  rw [I.linkAt_refl]
  rfl

theorem dThetaShadowLinkAt_symm (n m n' m' : Int) :
    DPrimeStripEquiv.symm (I.dThetaShadowLinkAt n m n' m') =
      I.dThetaShadowLinkAt n' m' n m := by
  change DPrimeStripEquiv.symm
      ((I.linkAt n m n' m').primeStripEquiv.toD) = _
  rw [FPrimeStripEquiv.toD_symm]
  exact congrArg FPrimeStripEquiv.toD
    (congrArg HodgeTheaterLink.primeStripEquiv
      (I.linkAt_symm n m n' m'))

theorem dThetaShadowLinkAt_trans (n m n' m' n'' m'' : Int) :
    DPrimeStripEquiv.trans (I.dThetaShadowLinkAt n m n' m')
        (I.dThetaShadowLinkAt n' m' n'' m'') =
      I.dThetaShadowLinkAt n m n'' m'' := by
  change DPrimeStripEquiv.trans
      ((I.linkAt n m n' m').primeStripEquiv.toD)
      ((I.linkAt n' m' n'' m'').primeStripEquiv.toD) = _
  rw [FPrimeStripEquiv.toD_trans]
  exact congrArg FPrimeStripEquiv.toD
    (congrArg HodgeTheaterLink.primeStripEquiv
      (I.linkAt_trans n m n' m' n'' m''))

theorem dThetaShadowLinkAt_projection (n m n' m' : Int) (v : V)
    (x : (I.dThetaShadowAt n m).Pi v) :
    (I.dThetaShadowAt n' m').proj v
        ((I.dThetaShadowLinkAt n m n' m').isoPi v x) =
      (I.dThetaShadowLinkAt n m n' m').isoG v
        ((I.dThetaShadowAt n m).proj v x) := by
  exact (I.dThetaShadowLinkAt n m n' m').compat_apply v x

theorem dThetaShadowAt_q (n m n' m' : Int) :
    (I.theaterAt n m).thetaPacket.q =
      (I.theaterAt n' m').thetaPacket.q :=
  I.linkAt_q n m n' m'

theorem dThetaShadowAt_scale (n m n' m' : Int)
    (j : SignedLabel l.value) :
    (I.theaterAt n m).thetaPacket.scale j =
      (I.theaterAt n' m').thetaPacket.scale j :=
  I.linkAt_scale n m n' m' j

/-! ## 4. The source-constructed vertical D-prime-strip core

The opening family supplies a D-prime-strip at every pair `(n,m)` and a link
between every two such pairs.  For a fixed horizontal coordinate `n`, choose
the `m = 0` member as a base and transport to every other member.  This is a
genuine construction from the source links; it does not assert the extra
holomorphic, mono-analytic, log-shell, or Frobenioid data used by the full
vertical coricity theorem.
-/

structure DPrimeStripVerticalCore where
  core : Int -> DPrimeStrip.{upi, uv} V
  toMember : forall n m,
    DPrimeStripEquiv (core n) (I.dThetaShadowAt n m)
  core_source : forall n, core n = I.dThetaShadowAt n 0
  member_zero : forall n,
    toMember n 0 = DPrimeStripEquiv.refl (core n)
  vertical_link : forall n m m',
    DPrimeStripEquiv (I.dThetaShadowAt n m) (I.dThetaShadowAt n m')
  vertical_link_source : forall n m m',
    vertical_link n m m' = I.dThetaShadowLinkAt n m n m'
  vertical_transport : forall n m m',
    DPrimeStripEquiv.trans (DPrimeStripEquiv.symm (toMember n m))
        (toMember n m') = vertical_link n m m'
  core_link : forall n n', DPrimeStripEquiv (core n) (core n')
  core_link_source : forall n n',
    core_link n n' = I.dThetaShadowLinkAt n 0 n' 0
  core_naturality : forall n n' m m',
    DPrimeStripEquiv.trans (core_link n n') (toMember n' m') =
      DPrimeStripEquiv.trans (toMember n m)
        (I.dThetaShadowLinkAt n m n' m')

def dPrimeStripVerticalCore : I.DPrimeStripVerticalCore where
  core := fun n => I.dThetaShadowAt n 0
  toMember := fun n m => I.dThetaShadowLinkAt n 0 n m
  core_source := by
    intro n
    rfl
  member_zero := by
    intro n
    simpa using I.dThetaShadowLinkAt_refl n 0
  vertical_link := fun n m m' => I.dThetaShadowLinkAt n m n m'
  vertical_link_source := by
    intro n m m'
    rfl
  vertical_transport := by
    intro n m m'
    rw [I.dThetaShadowLinkAt_symm]
    exact I.dThetaShadowLinkAt_trans n m n 0 n m'
  core_link := fun n n' => I.dThetaShadowLinkAt n 0 n' 0
  core_link_source := by
    intro n n'
    rfl
  core_naturality := by
    intro n n' m m'
    rw [I.dThetaShadowLinkAt_trans, I.dThetaShadowLinkAt_trans]

@[simp] theorem dPrimeStripVerticalCore_core (n : Int) :
    (I.dPrimeStripVerticalCore).core n = I.dThetaShadowAt n 0 := rfl

@[simp] theorem dPrimeStripVerticalCore_toMember (n m : Int) :
    (I.dPrimeStripVerticalCore).toMember n m =
      I.dThetaShadowLinkAt n 0 n m := rfl

@[simp] theorem dPrimeStripVerticalCore_vertical_link (n m m' : Int) :
    (I.dPrimeStripVerticalCore).vertical_link n m m' =
      I.dThetaShadowLinkAt n m n m' := rfl

@[simp] theorem dPrimeStripVerticalCore_core_link (n n' : Int) :
    (I.dPrimeStripVerticalCore).core_link n n' =
      I.dThetaShadowLinkAt n 0 n' 0 := rfl

theorem dPrimeStripVerticalCore_core_source (n : Int) :
    (I.dPrimeStripVerticalCore).core n = I.dThetaShadowAt n 0 :=
  (I.dPrimeStripVerticalCore).core_source n

theorem dPrimeStripVerticalCore_member_zero (n : Int) :
    (I.dPrimeStripVerticalCore).toMember n 0 =
      DPrimeStripEquiv.refl ((I.dPrimeStripVerticalCore).core n) :=
  (I.dPrimeStripVerticalCore).member_zero n

theorem dPrimeStripVerticalCore_vertical_link_source
    (n m m' : Int) :
    (I.dPrimeStripVerticalCore).vertical_link n m m' =
      I.dThetaShadowLinkAt n m n m' :=
  (I.dPrimeStripVerticalCore).vertical_link_source n m m'

theorem dPrimeStripVerticalCore_transport
    (n m m' : Int) :
    DPrimeStripEquiv.trans
        (DPrimeStripEquiv.symm ((I.dPrimeStripVerticalCore).toMember n m))
        ((I.dPrimeStripVerticalCore).toMember n m') =
      (I.dPrimeStripVerticalCore).vertical_link n m m' :=
  (I.dPrimeStripVerticalCore).vertical_transport n m m'

theorem dPrimeStripVerticalCore_core_link_source (n n' : Int) :
    (I.dPrimeStripVerticalCore).core_link n n' =
      I.dThetaShadowLinkAt n 0 n' 0 :=
  (I.dPrimeStripVerticalCore).core_link_source n n'

theorem dPrimeStripVerticalCore_naturality
    (n n' m m' : Int) :
    DPrimeStripEquiv.trans
        ((I.dPrimeStripVerticalCore).core_link n n')
        ((I.dPrimeStripVerticalCore).toMember n' m') =
      DPrimeStripEquiv.trans
        ((I.dPrimeStripVerticalCore).toMember n m)
        (I.dThetaShadowLinkAt n m n' m') :=
  (I.dPrimeStripVerticalCore).core_naturality n n' m m'

theorem dPrimeStripVerticalCore_toMember_bijective_pi
    (n m : Int) (v : V) :
    Function.Bijective
      (((I.dPrimeStripVerticalCore).toMember n m).isoPi v) := by
  exact (((I.dPrimeStripVerticalCore).toMember n m).isoPi v).bijective

theorem dPrimeStripVerticalCore_toMember_bijective_g
    (n m : Int) (v : V) :
    Function.Bijective
      (((I.dPrimeStripVerticalCore).toMember n m).isoG v) := by
  exact (((I.dPrimeStripVerticalCore).toMember n m).isoG v).bijective

theorem dPrimeStripVerticalCore_vertical_link_refl (n m : Int) :
    (I.dPrimeStripVerticalCore).vertical_link n m m =
      DPrimeStripEquiv.refl (I.dThetaShadowAt n m) := by
  rw [dPrimeStripVerticalCore_vertical_link_source,
    I.dThetaShadowLinkAt_refl]

theorem dPrimeStripVerticalCore_vertical_link_symm
    (n m m' : Int) :
    DPrimeStripEquiv.symm
        ((I.dPrimeStripVerticalCore).vertical_link n m m') =
      (I.dPrimeStripVerticalCore).vertical_link n m' m := by
  rw [dPrimeStripVerticalCore_vertical_link_source,
    dPrimeStripVerticalCore_vertical_link_source,
    I.dThetaShadowLinkAt_symm]

theorem dPrimeStripVerticalCore_vertical_link_trans
    (n m m' m'' : Int) :
    DPrimeStripEquiv.trans
        ((I.dPrimeStripVerticalCore).vertical_link n m m')
        ((I.dPrimeStripVerticalCore).vertical_link n m' m'') =
      (I.dPrimeStripVerticalCore).vertical_link n m m'' := by
  rw [dPrimeStripVerticalCore_vertical_link_source,
    dPrimeStripVerticalCore_vertical_link_source,
    dPrimeStripVerticalCore_vertical_link_source,
    I.dThetaShadowLinkAt_trans]

theorem dPrimeStripVerticalCore_vertical_link_projection
    (n m m' : Int) (v : V)
    (x : (I.dThetaShadowAt n m).Pi v) :
    (I.dThetaShadowAt n m').proj v
        (((I.dPrimeStripVerticalCore).vertical_link n m m').isoPi v x) =
      ((I.dPrimeStripVerticalCore).vertical_link n m m').isoG v
        ((I.dThetaShadowAt n m).proj v x) := by
  rw [dPrimeStripVerticalCore_vertical_link_source]
  exact I.dThetaShadowLinkAt_projection n m n m' v x

theorem dPrimeStripVerticalCore_core_link_refl (n : Int) :
    (I.dPrimeStripVerticalCore).core_link n n =
      DPrimeStripEquiv.refl ((I.dPrimeStripVerticalCore).core n) := by
  rw [dPrimeStripVerticalCore_core_link_source,
    dThetaShadowLinkAt_refl]

theorem dPrimeStripVerticalCore_core_link_symm
    (n n' : Int) :
    DPrimeStripEquiv.symm ((I.dPrimeStripVerticalCore).core_link n n') =
      (I.dPrimeStripVerticalCore).core_link n' n := by
  rw [dPrimeStripVerticalCore_core_link_source,
    dPrimeStripVerticalCore_core_link_source,
    dThetaShadowLinkAt_symm]

theorem dPrimeStripVerticalCore_core_link_trans
    (n n' n'' : Int) :
    DPrimeStripEquiv.trans
        ((I.dPrimeStripVerticalCore).core_link n n')
        ((I.dPrimeStripVerticalCore).core_link n' n'') =
      (I.dPrimeStripVerticalCore).core_link n n'' := by
  rw [dPrimeStripVerticalCore_core_link_source,
    dPrimeStripVerticalCore_core_link_source,
    dPrimeStripVerticalCore_core_link_source,
    dThetaShadowLinkAt_trans]

/-! ## 4b. The source-constructed vertical F-prime-strip core

The D core above is the image of the actual F-prime-strip family.  The value
monoids, actions, and degrees are also already present in every source
theater, so the same source links construct an F-level core.  Keeping this
record separate from the full coricity gate is important: the construction
uses only the fields present in `OriginalInput`, while the paper's vertical
coricity theorem adds arithmetic and analytic structures not present there.
-/

structure FPrimeStripVerticalCore where
  core : Int -> FPrimeStrip.{umon, uv, upi} V
  toMember : forall n m,
    FPrimeStripEquiv (core n) (I.fPrimeStripAt n m)
  core_source : forall n, core n = I.fPrimeStripAt n 0
  member_zero : forall n,
    toMember n 0 = FPrimeStripEquiv.refl (core n)
  vertical_link : forall n m m',
    FPrimeStripEquiv (I.fPrimeStripAt n m) (I.fPrimeStripAt n m')
  vertical_link_source : forall n m m',
    vertical_link n m m' = I.fLinkAt n m n m'
  vertical_transport : forall n m m',
    FPrimeStripEquiv.trans (FPrimeStripEquiv.symm (toMember n m))
        (toMember n m') = vertical_link n m m'
  core_link : forall n n', FPrimeStripEquiv (core n) (core n')
  core_link_source : forall n n',
    core_link n n' = I.fLinkAt n 0 n' 0
  core_naturality : forall n n' m m',
    FPrimeStripEquiv.trans (core_link n n') (toMember n' m') =
      FPrimeStripEquiv.trans (toMember n m)
        (I.fLinkAt n m n' m')

def fPrimeStripVerticalCore : I.FPrimeStripVerticalCore where
  core := fun n => I.fPrimeStripAt n 0
  toMember := fun n m => I.fLinkAt n 0 n m
  core_source := by
    intro n
    rfl
  member_zero := by
    intro n
    simpa using I.fLinkAt_refl n 0
  vertical_link := fun n m m' => I.fLinkAt n m n m'
  vertical_link_source := by
    intro n m m'
    rfl
  vertical_transport := by
    intro n m m'
    rw [I.fLinkAt_symm]
    exact I.fLinkAt_trans n m n 0 n m'
  core_link := fun n n' => I.fLinkAt n 0 n' 0
  core_link_source := by
    intro n n'
    rfl
  core_naturality := by
    intro n n' m m'
    rw [I.fLinkAt_trans, I.fLinkAt_trans]

@[simp] theorem fPrimeStripVerticalCore_core (n : Int) :
    (I.fPrimeStripVerticalCore).core n = I.fPrimeStripAt n 0 := rfl

@[simp] theorem fPrimeStripVerticalCore_toMember (n m : Int) :
    (I.fPrimeStripVerticalCore).toMember n m =
      I.fLinkAt n 0 n m := rfl

@[simp] theorem fPrimeStripVerticalCore_vertical_link (n m m' : Int) :
    (I.fPrimeStripVerticalCore).vertical_link n m m' =
      I.fLinkAt n m n m' := rfl

@[simp] theorem fPrimeStripVerticalCore_core_link (n n' : Int) :
    (I.fPrimeStripVerticalCore).core_link n n' =
      I.fLinkAt n 0 n' 0 := rfl

theorem fPrimeStripVerticalCore_core_source (n : Int) :
    (I.fPrimeStripVerticalCore).core n = I.fPrimeStripAt n 0 :=
  (I.fPrimeStripVerticalCore).core_source n

theorem fPrimeStripVerticalCore_member_zero (n : Int) :
    (I.fPrimeStripVerticalCore).toMember n 0 =
      FPrimeStripEquiv.refl ((I.fPrimeStripVerticalCore).core n) :=
  (I.fPrimeStripVerticalCore).member_zero n

theorem fPrimeStripVerticalCore_vertical_link_source
    (n m m' : Int) :
    (I.fPrimeStripVerticalCore).vertical_link n m m' =
      I.fLinkAt n m n m' :=
  (I.fPrimeStripVerticalCore).vertical_link_source n m m'

theorem fPrimeStripVerticalCore_transport
    (n m m' : Int) :
    FPrimeStripEquiv.trans
        (FPrimeStripEquiv.symm ((I.fPrimeStripVerticalCore).toMember n m))
        ((I.fPrimeStripVerticalCore).toMember n m') =
      (I.fPrimeStripVerticalCore).vertical_link n m m' :=
  (I.fPrimeStripVerticalCore).vertical_transport n m m'

theorem fPrimeStripVerticalCore_core_link_source (n n' : Int) :
    (I.fPrimeStripVerticalCore).core_link n n' =
      I.fLinkAt n 0 n' 0 :=
  (I.fPrimeStripVerticalCore).core_link_source n n'

theorem fPrimeStripVerticalCore_naturality
    (n n' m m' : Int) :
    FPrimeStripEquiv.trans
        ((I.fPrimeStripVerticalCore).core_link n n')
        ((I.fPrimeStripVerticalCore).toMember n' m') =
      FPrimeStripEquiv.trans
        ((I.fPrimeStripVerticalCore).toMember n m)
        (I.fLinkAt n m n' m') :=
  (I.fPrimeStripVerticalCore).core_naturality n n' m m'

theorem fPrimeStripVerticalCore_toMember_bijective_pi
    (n m : Int) (v : V) :
    Function.Bijective
      (((I.fPrimeStripVerticalCore).toMember n m).isoPi v) := by
  exact (((I.fPrimeStripVerticalCore).toMember n m).isoPi v).bijective

theorem fPrimeStripVerticalCore_toMember_bijective_g
    (n m : Int) (v : V) :
    Function.Bijective
      (((I.fPrimeStripVerticalCore).toMember n m).isoG v) := by
  exact (((I.fPrimeStripVerticalCore).toMember n m).isoG v).bijective

theorem fPrimeStripVerticalCore_toMember_bijective_mon
    (n m : Int) (v : V) :
    Function.Bijective
      (((I.fPrimeStripVerticalCore).toMember n m).isoMon v) := by
  exact (((I.fPrimeStripVerticalCore).toMember n m).isoMon v).bijective

theorem fPrimeStripVerticalCore_vertical_link_refl (n m : Int) :
    (I.fPrimeStripVerticalCore).vertical_link n m m =
      FPrimeStripEquiv.refl (I.fPrimeStripAt n m) := by
  rw [fPrimeStripVerticalCore_vertical_link_source, I.fLinkAt_refl]

theorem fPrimeStripVerticalCore_vertical_link_symm
    (n m m' : Int) :
    FPrimeStripEquiv.symm
        ((I.fPrimeStripVerticalCore).vertical_link n m m') =
      (I.fPrimeStripVerticalCore).vertical_link n m' m := by
  rw [fPrimeStripVerticalCore_vertical_link_source,
    fPrimeStripVerticalCore_vertical_link_source,
    I.fLinkAt_symm]

theorem fPrimeStripVerticalCore_vertical_link_trans
    (n m m' m'' : Int) :
    FPrimeStripEquiv.trans
        ((I.fPrimeStripVerticalCore).vertical_link n m m')
        ((I.fPrimeStripVerticalCore).vertical_link n m' m'') =
      (I.fPrimeStripVerticalCore).vertical_link n m m'' := by
  rw [fPrimeStripVerticalCore_vertical_link_source,
    fPrimeStripVerticalCore_vertical_link_source,
    fPrimeStripVerticalCore_vertical_link_source,
    I.fLinkAt_trans]

theorem fPrimeStripVerticalCore_vertical_link_projection
    (n m m' : Int) (v : V)
    (x : (I.fPrimeStripAt n m).toDPrimeStrip.Pi v) :
    (I.fPrimeStripAt n m').proj v
        (((I.fPrimeStripVerticalCore).vertical_link n m m').isoPi v x) =
      ((I.fPrimeStripVerticalCore).vertical_link n m m').isoG v
        ((I.fPrimeStripAt n m).proj v x) := by
  rw [fPrimeStripVerticalCore_vertical_link_source]
  exact I.fLinkAt_compatibility n m n m' v x

theorem fPrimeStripVerticalCore_vertical_link_action
    (n m m' : Int) (v : V)
    (g : (I.fPrimeStripAt n m).toDPrimeStrip.Pi v)
    (x : (I.fPrimeStripAt n m).Mon v) :
    ((I.fPrimeStripVerticalCore).vertical_link n m m').isoMon v
        ((I.fPrimeStripAt n m).action v g x) =
      (I.fPrimeStripAt n m').action v
        ((I.fPrimeStripVerticalCore).vertical_link n m m').isoPi v g
        (((I.fPrimeStripVerticalCore).vertical_link n m m').isoMon v x) := by
  rw [fPrimeStripVerticalCore_vertical_link_source]
  exact I.fLinkAt_action n m n m' v g x

theorem fPrimeStripVerticalCore_vertical_link_degree
    (n m m' : Int) (v : V)
    (x : (I.fPrimeStripAt n m).Mon v) :
    (I.fPrimeStripAt n m').degree v
        (((I.fPrimeStripVerticalCore).vertical_link n m m').isoMon v x) =
      (I.fPrimeStripAt n m).degree v x := by
  rw [fPrimeStripVerticalCore_vertical_link_source]
  exact I.fLinkAt_degree n m n m' v x

theorem fPrimeStripVerticalCore_vertical_link_total_degree
    (n m m' : Int) (s : Finset V)
    (x : ∀ v, (I.fPrimeStripAt n m).Mon v) :
    (I.fPrimeStripAt n m').totalDegree s
        (fun v =>
          ((I.fPrimeStripVerticalCore).vertical_link n m m').isoMon v
            (x v)) =
      (I.fPrimeStripAt n m).totalDegree s x := by
  apply Finset.sum_congr rfl
  intro v hv
  exact I.fPrimeStripVerticalCore_vertical_link_degree n m m' v (x v)

theorem fPrimeStripVerticalCore_core_link_refl (n : Int) :
    (I.fPrimeStripVerticalCore).core_link n n =
      FPrimeStripEquiv.refl ((I.fPrimeStripVerticalCore).core n) := by
  rw [fPrimeStripVerticalCore_core_link_source, I.fLinkAt_refl]

theorem fPrimeStripVerticalCore_core_link_symm
    (n n' : Int) :
    FPrimeStripEquiv.symm ((I.fPrimeStripVerticalCore).core_link n n') =
      (I.fPrimeStripVerticalCore).core_link n' n := by
  rw [fPrimeStripVerticalCore_core_link_source,
    fPrimeStripVerticalCore_core_link_source, I.fLinkAt_symm]

theorem fPrimeStripVerticalCore_core_link_trans
    (n n' n'' : Int) :
    FPrimeStripEquiv.trans
        ((I.fPrimeStripVerticalCore).core_link n n')
        ((I.fPrimeStripVerticalCore).core_link n' n'') =
      (I.fPrimeStripVerticalCore).core_link n n'' := by
  rw [fPrimeStripVerticalCore_core_link_source,
    fPrimeStripVerticalCore_core_link_source,
    fPrimeStripVerticalCore_core_link_source, I.fLinkAt_trans]

/-! ## 4c. Coupling the F and D vertical cores

The coupling records exactly what survives the forgetful map.  It is a
source-derived bridge, not a new theorem about vertical coricity.
-/

structure FDPrimeStripVerticalCore where
  fCore : I.FPrimeStripVerticalCore
  dCore : I.DPrimeStripVerticalCore
  core_toD : forall n, (fCore.core n).toD = dCore.core n
  member_toD : forall n m,
    (fCore.toMember n m).toD = dCore.toMember n m
  vertical_link_toD : forall n m m',
    (fCore.vertical_link n m m').toD = dCore.vertical_link n m m'
  core_link_toD : forall n n',
    (fCore.core_link n n').toD = dCore.core_link n n'

def fdPrimeStripVerticalCore : I.FDPrimeStripVerticalCore where
  fCore := I.fPrimeStripVerticalCore
  dCore := I.dPrimeStripVerticalCore
  core_toD := by
    intro n
    rfl
  member_toD := by
    intro n m
    rfl
  vertical_link_toD := by
    intro n m m'
    rfl
  core_link_toD := by
    intro n n'
    rfl

@[simp] theorem fdPrimeStripVerticalCore_fCore :
    (I.fdPrimeStripVerticalCore).fCore = I.fPrimeStripVerticalCore := rfl

@[simp] theorem fdPrimeStripVerticalCore_dCore :
    (I.fdPrimeStripVerticalCore).dCore = I.dPrimeStripVerticalCore := rfl

theorem fdPrimeStripVerticalCore_core_toD (n : Int) :
    ((I.fdPrimeStripVerticalCore).fCore.core n).toD =
      (I.fdPrimeStripVerticalCore).dCore.core n :=
  (I.fdPrimeStripVerticalCore).core_toD n

theorem fdPrimeStripVerticalCore_member_toD (n m : Int) :
    ((I.fdPrimeStripVerticalCore).fCore.toMember n m).toD =
      (I.fdPrimeStripVerticalCore).dCore.toMember n m :=
  (I.fdPrimeStripVerticalCore).member_toD n m

theorem fdPrimeStripVerticalCore_vertical_link_toD (n m m' : Int) :
    ((I.fdPrimeStripVerticalCore).fCore.vertical_link n m m').toD =
      (I.fdPrimeStripVerticalCore).dCore.vertical_link n m m' :=
  (I.fdPrimeStripVerticalCore).vertical_link_toD n m m'

theorem fdPrimeStripVerticalCore_core_link_toD (n n' : Int) :
    ((I.fdPrimeStripVerticalCore).fCore.core_link n n').toD =
      (I.fdPrimeStripVerticalCore).dCore.core_link n n' :=
  (I.fdPrimeStripVerticalCore).core_link_toD n n'

theorem fdPrimeStripVerticalCore_member_projection
    (n m : Int) (v : V)
    (x : ((I.fdPrimeStripVerticalCore).fCore.core n).toD.Pi v) :
    (I.fdPrimeStripVerticalCore).dCore.toMember n m |>.isoPi v x =
      (I.fdPrimeStripVerticalCore).fCore.toMember n m |>.isoPi v x := rfl

theorem fdPrimeStripVerticalCore_link_projection
    (n m m' : Int) (v : V)
    (x : ((I.fdPrimeStripVerticalCore).fCore.vertical_link n m m').toD.Pi v) :
    x = x := rfl

/-! The last theorem is intentionally a typed identity: a D-link has no value
    monoid or degree component.  The F-link lemmas above are the ones that
    carry the action and degree data, while this bridge certifies that their
    D projection is the exact D core used by H1/H2. -/

theorem fdPrimeStripVerticalCore_closed :
    (I.fdPrimeStripVerticalCore).fCore = I.fPrimeStripVerticalCore ∧
      (I.fdPrimeStripVerticalCore).dCore = I.dPrimeStripVerticalCore :=
  ⟨rfl, rfl⟩

/-! ## 4. A complete source D-shadow family package -/

structure DThetaShadowFamily where
  shadow : I.DThetaShadow
  coordinate : SourceTheorem311Index -> I.family.index
  coordinate_recovery : forall p,
    I.index_equiv (coordinate p) = p
  strip_at : SourceTheorem311Index -> DPrimeStrip.{upi, uv} V
  strip_at_eq : forall p, strip_at p = shadow.dStrip (coordinate p)
  link_at : forall p q,
    DPrimeStripEquiv (strip_at p) (strip_at q)
  link_at_eq : forall p q,
    link_at p q = shadow.dLink (coordinate p) (coordinate q)

def dThetaShadowFamily : I.DThetaShadowFamily where
  shadow := I.dThetaShadow
  coordinate := fun p => I.indexOf p.1 p.2
  coordinate_recovery := by
    intro p
    exact I.indexOf_apply p.1 p.2
  strip_at := fun p => I.dThetaShadowAt p.1 p.2
  strip_at_eq := by
    intro p
    rfl
  link_at := fun p q => I.dThetaShadowLinkAt p.1 p.2 q.1 q.2
  link_at_eq := by
    intro p q
    rfl

@[simp] theorem dThetaShadowFamily_coordinate (p : SourceTheorem311Index) :
    (I.dThetaShadowFamily).coordinate p = I.indexOf p.1 p.2 := rfl

@[simp] theorem dThetaShadowFamily_strip_at (p : SourceTheorem311Index) :
    (I.dThetaShadowFamily).strip_at p = I.dThetaShadowAt p.1 p.2 := rfl

@[simp] theorem dThetaShadowFamily_link_at
    (p q : SourceTheorem311Index) :
    (I.dThetaShadowFamily).link_at p q =
      I.dThetaShadowLinkAt p.1 p.2 q.1 q.2 := rfl

theorem dThetaShadowFamily_coordinate_recovery
    (p : SourceTheorem311Index) :
    I.index_equiv ((I.dThetaShadowFamily).coordinate p) = p :=
  (I.dThetaShadowFamily).coordinate_recovery p

theorem dThetaShadowFamily_strip_recovery
    (p : SourceTheorem311Index) :
    (I.dThetaShadowFamily).strip_at p =
      (I.dThetaShadowFamily).shadow.dStrip
        ((I.dThetaShadowFamily).coordinate p) :=
  (I.dThetaShadowFamily).strip_at_eq p

theorem dThetaShadowFamily_link_recovery
    (p q : SourceTheorem311Index) :
    (I.dThetaShadowFamily).link_at p q =
      (I.dThetaShadowFamily).shadow.dLink
        ((I.dThetaShadowFamily).coordinate p)
        ((I.dThetaShadowFamily).coordinate q) :=
  (I.dThetaShadowFamily).link_at_eq p q

theorem dThetaShadowFamily_coordinate_injective :
    Function.Injective (I.dThetaShadowFamily).coordinate := by
  intro p q h
  exact I.indexOf_injective h

/-!
  The `toD` projection forgets the value-monoid, action, and degree fields of an
  F-prime-strip.  Consequently equality of the projected D-strips cannot be
  used to recover the lattice coordinate (or the complete Hodge theater).
  The source input does give injectivity of the coordinate map itself; any
  stronger D-strip injectivity belongs to a later coricity/source theorem and
  is therefore not asserted here.
-/
theorem dThetaShadowFamily_coordinate_recovery_iff
    {p q : SourceTheorem311Index} :
    (I.dThetaShadowFamily).coordinate p =
        (I.dThetaShadowFamily).coordinate q ↔ p = q := by
  constructor
  · intro h
    exact I.dThetaShadowFamily_coordinate_injective h
  · intro h
    cases h
    rfl

/-! ## 5. D fixed-column capsules -/

structure DColumnStage (n : Int) (k : Nat) where
  source : Fin (k + 1) -> I.family.index
  source_eq : forall i, source i = I.indexOf n (i.1 : Int)
  source_injective : Function.Injective source
  strip : Fin (k + 1) -> DPrimeStrip.{upi, uv} V
  strip_eq : forall i, strip i = I.dThetaShadowAt n (i.1 : Int)
  link : forall i j, DPrimeStripEquiv (strip i) (strip j)
  link_eq : forall i j,
    link i j = I.dThetaShadowLinkAt n (i.1 : Int) n (j.1 : Int)

def dColumnStage (n : Int) (k : Nat) : I.DColumnStage n k where
  source := fun i => I.indexOf n (i.1 : Int)
  source_eq := by intro i; rfl
  source_injective := I.columnSource_injective n k
  strip := fun i => I.dThetaShadowAt n (i.1 : Int)
  strip_eq := by intro i; rfl
  link := fun i j => I.dThetaShadowLinkAt n (i.1 : Int) n (j.1 : Int)
  link_eq := by intro i j; rfl

@[simp] theorem dColumnStage_source (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.dColumnStage n k).source i = I.indexOf n (i.1 : Int) := rfl

@[simp] theorem dColumnStage_strip (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.dColumnStage n k).strip i = I.dThetaShadowAt n (i.1 : Int) := rfl

@[simp] theorem dColumnStage_link (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    (I.dColumnStage n k).link i j =
      I.dThetaShadowLinkAt n (i.1 : Int) n (j.1 : Int) := rfl

theorem dColumnStage_source_injective (n : Int) (k : Nat) :
    Function.Injective (I.dColumnStage n k).source :=
  (I.dColumnStage n k).source_injective

theorem dColumnStage_link_refl (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.dColumnStage n k).link i i =
      DPrimeStripEquiv.refl ((I.dColumnStage n k).strip i) := by
  change I.dThetaShadowLinkAt n (i.1 : Int) n (i.1 : Int) = _
  rw [I.dThetaShadowLinkAt_refl]
  rfl

theorem dColumnStage_link_symm (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    DPrimeStripEquiv.symm ((I.dColumnStage n k).link i j) =
      (I.dColumnStage n k).link j i := by
  change DPrimeStripEquiv.symm
      (I.dThetaShadowLinkAt n (i.1 : Int) n (j.1 : Int)) = _
  rw [I.dThetaShadowLinkAt_symm]
  rfl

theorem dColumnStage_link_trans (n : Int) (k : Nat)
    (i j h : Fin (k + 1)) :
    DPrimeStripEquiv.trans ((I.dColumnStage n k).link i j)
        ((I.dColumnStage n k).link j h) =
      (I.dColumnStage n k).link i h := by
  change DPrimeStripEquiv.trans
      (I.dThetaShadowLinkAt n (i.1 : Int) n (j.1 : Int))
      (I.dThetaShadowLinkAt n (j.1 : Int) n (h.1 : Int)) = _
  rw [I.dThetaShadowLinkAt_trans]
  rfl

/-! ## 6. D column inclusions and procession laws -/

structure DColumnInclusion (n : Int) {k r : Nat} (h : k <= r) where
  map : Fin (k + 1) -> Fin (r + 1)
  map_eq : forall i, map i = finStageMap h i
  map_injective : Function.Injective map
  component : forall i,
    DPrimeStripEquiv ((I.dColumnStage n k).strip i)
      ((I.dColumnStage n r).strip (map i))
  component_eq : forall i,
    component i = I.dThetaShadowLinkAt n (i.1 : Int) n ((map i).1 : Int)
  naturality : forall i j,
    DPrimeStripEquiv.trans ((I.dColumnStage n k).link i j)
      (component j) =
    DPrimeStripEquiv.trans (component i)
      ((I.dColumnStage n r).link (map i) (map j))

def dColumnInclusion (n : Int) {k r : Nat} (h : k <= r) :
    I.DColumnInclusion n h where
  map := finStageMap h
  map_eq := by intro i; rfl
  map_injective := finStageMap_injective h
  component := fun i =>
    I.dThetaShadowLinkAt n (i.1 : Int) n ((finStageMap h i).1 : Int)
  component_eq := by intro i; rfl
  naturality := by
    intro i j
    change DPrimeStripEquiv.trans
        (I.dThetaShadowLinkAt n (i.1 : Int) n (j.1 : Int))
        (I.dThetaShadowLinkAt n (j.1 : Int) n ((finStageMap h j).1 : Int)) =
      DPrimeStripEquiv.trans
        (I.dThetaShadowLinkAt n (i.1 : Int) n ((finStageMap h i).1 : Int))
        (I.dThetaShadowLinkAt n ((finStageMap h i).1 : Int) n
          ((finStageMap h j).1 : Int))
    rw [I.dThetaShadowLinkAt_trans, I.dThetaShadowLinkAt_trans]

@[simp] theorem dColumnInclusion_map (n : Int) {k r : Nat} (h : k <= r)
    (i : Fin (k + 1)) :
    (I.dColumnInclusion n h).map i = finStageMap h i := rfl

@[simp] theorem dColumnInclusion_component (n : Int) {k r : Nat}
    (h : k <= r) (i : Fin (k + 1)) :
    (I.dColumnInclusion n h).component i =
      I.dThetaShadowLinkAt n (i.1 : Int) n
        ((finStageMap h i).1 : Int) := rfl

theorem dColumnInclusion_injective (n : Int) {k r : Nat} (h : k <= r) :
    Function.Injective (I.dColumnInclusion n h).map :=
  (I.dColumnInclusion n h).map_injective

theorem dColumnInclusion_natural (n : Int) {k r : Nat} (h : k <= r)
    (i j : Fin (k + 1)) :
    DPrimeStripEquiv.trans ((I.dColumnStage n k).link i j)
      ((I.dColumnInclusion n h).component j) =
    DPrimeStripEquiv.trans ((I.dColumnInclusion n h).component i)
      ((I.dColumnStage n r).link
        ((I.dColumnInclusion n h).map i)
        ((I.dColumnInclusion n h).map j)) :=
  (I.dColumnInclusion n h).naturality i j

theorem dColumnInclusion_refl (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.dColumnInclusion n (Nat.le_refl k)).map i = i := by
  rw [dColumnInclusion_map]
  exact finStageMap_refl k i

theorem dColumnInclusion_trans (n : Int) {k r s : Nat}
    (h₁ : k <= r) (h₂ : r <= s) (i : Fin (k + 1)) :
    (I.dColumnInclusion n (Nat.le_trans h₁ h₂)).map i =
      (I.dColumnInclusion n h₂).map ((I.dColumnInclusion n h₁).map i) := by
  rw [dColumnInclusion_map, dColumnInclusion_map, dColumnInclusion_map]
  exact (finStageMap_trans h₁ h₂ i).symm

structure DColumnProcession (n : Int) where
  stage : (k : Nat) -> I.DColumnStage n k
  inclusion : forall {k r : Nat} (h : k <= r), I.DColumnInclusion n h
  inclusion_refl : forall (k : Nat) (i : Fin (k + 1)),
    (inclusion (Nat.le_refl k)).map i = i
  inclusion_trans : forall {k r s : Nat} (h₁ : k <= r) (h₂ : r <= s)
    (i : Fin (k + 1)),
    (inclusion (Nat.le_trans h₁ h₂)).map i =
      (inclusion h₂).map ((inclusion h₁).map i)

def dColumnProcession (n : Int) : I.DColumnProcession n where
  stage := I.dColumnStage n
  inclusion := fun {_ _} h => I.dColumnInclusion n h
  inclusion_refl := by
    intro k i
    exact I.dColumnInclusion_refl n k i
  inclusion_trans := by
    intro k r s h₁ h₂ i
    exact I.dColumnInclusion_trans n h₁ h₂ i

@[simp] theorem dColumnProcession_stage (n : Int) (k : Nat) :
    (I.dColumnProcession n).stage k = I.dColumnStage n k := rfl

@[simp] theorem dColumnProcession_inclusion (n : Int) {k r : Nat}
    (h : k <= r) :
    (I.dColumnProcession n).inclusion h = I.dColumnInclusion n h := rfl

theorem dColumnProcession_stage_source (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    ((I.dColumnProcession n).stage k).source i =
      I.indexOf n (i.1 : Int) := rfl

theorem dColumnProcession_stage_strip (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    ((I.dColumnProcession n).stage k).strip i =
      I.dThetaShadowAt n (i.1 : Int) := rfl

theorem dColumnProcession_stage_link (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    ((I.dColumnProcession n).stage k).link i j =
      I.dThetaShadowLinkAt n (i.1 : Int) n (j.1 : Int) := rfl

theorem dColumnProcession_stage_injective (n : Int) (k : Nat) :
    Function.Injective ((I.dColumnProcession n).stage k).source :=
  (I.dColumnProcession n).stage k |>.source_injective

theorem dColumnProcession_stage_cardinality (n : Int) (k : Nat) :
    Fintype.card (Fin (k + 1)) = k + 1 := by simp

theorem dColumnProcession_inclusion_natural (n : Int)
    {k r : Nat} (h : k <= r) (i j : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        (((I.dColumnProcession n).stage k).link i j)
        (((I.dColumnProcession n).inclusion h).component j) =
      DPrimeStripEquiv.trans
        (((I.dColumnProcession n).inclusion h).component i)
        (((I.dColumnProcession n).stage r).link
          (((I.dColumnProcession n).inclusion h).map i)
          (((I.dColumnProcession n).inclusion h).map j)) :=
  (I.dColumnProcession n).inclusion h |>.naturality i j

/-! ## 7. Conversion to the existing D-stage API -/

def dColumnStageAsExisting (n : Int) (k : Nat) : DStageCapsule I k where
  source := (I.dColumnStage n k).source
  source_injective := (I.dColumnStage n k).source_injective

@[simp] theorem dColumnStageAsExisting_source (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.dColumnStageAsExisting n k).source i =
      I.indexOf n (i.1 : Int) := rfl

@[simp] theorem dColumnStageAsExisting_strip (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.dColumnStageAsExisting n k).strip i =
      I.dPrimeStripAt n (i.1 : Int) := rfl

@[simp] theorem dColumnStageAsExisting_link (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    (I.dColumnStageAsExisting n k).link i j =
      I.dLinkAt n (i.1 : Int) n (j.1 : Int) := rfl

theorem dColumnStage_existing_eq (n : Int) (k : Nat) :
    I.dColumnStageAsExisting n k = I.columnDStage n k := by
  cases I.dColumnStage n k
  rfl

def dColumnProcessionAsExisting (n : Int) : I.ColumnDProcession where
  stage := I.dColumnStageAsExisting n
  inclusion := fun {_ _} h => I.columnDInclusion n h
  inclusion_refl := by
    intro k i
    exact finStageMap_refl k i
  inclusion_trans := by
    intro k r s h₁ h₂ i
    exact (finStageMap_trans h₁ h₂ i).symm

@[simp] theorem dColumnProcessionAsExisting_stage (n : Int) (k : Nat) :
    (I.dColumnProcessionAsExisting n).stage k = I.columnDStage n k := rfl

theorem dColumnProcessionAsExisting_source (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    ((I.dColumnProcessionAsExisting n).stage k).source i =
      I.indexOf n (i.1 : Int) := rfl

theorem dColumnProcessionAsExisting_injective (n : Int) {k r : Nat}
    (h : k <= r) :
    Function.Injective ((I.dColumnProcessionAsExisting n).inclusion h).map :=
  ((I.dColumnProcessionAsExisting n).inclusion h).map_injective

theorem dColumnProcessionAsExisting_natural (n : Int) {k r : Nat}
    (h : k <= r) (i j : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        (((I.dColumnProcessionAsExisting n).stage k).link i j)
        (((I.dColumnProcessionAsExisting n).inclusion h).component j) =
      DPrimeStripEquiv.trans
        (((I.dColumnProcessionAsExisting n).inclusion h).component i)
        (((I.dColumnProcessionAsExisting n).stage r).link
          (((I.dColumnProcessionAsExisting n).inclusion h).map i)
          (((I.dColumnProcessionAsExisting n).inclusion h).map j)) := by
  exact ((I.dColumnProcessionAsExisting n).inclusion h).naturality i j

/-! ## 8. The source D-shadow ledger -/

structure DThetaShadowLedger where
  h1 : I.DThetaShadowFamily
  column : Int -> I.DColumnProcession
  top_cardinality : forall n,
    Fintype.card (Fin (lStar l.value + 1)) = lStar l.value + 1
  top_source_injective : forall n,
    Function.Injective ((column n).stage (lStar l.value)).source
  top_strip : forall n (i : Fin (lStar l.value + 1)),
    ((column n).stage (lStar l.value)).strip i =
      I.dThetaShadowAt n (i.1 : Int)
  top_link : forall n (i j : Fin (lStar l.value + 1)),
    ((column n).stage (lStar l.value)).link i j =
      I.dThetaShadowLinkAt n (i.1 : Int) n (j.1 : Int)

def dThetaShadowLedger : I.DThetaShadowLedger where
  h1 := I.dThetaShadowFamily
  column := I.dColumnProcession
  top_cardinality := by intro n; simp
  top_source_injective := by
    intro n
    exact I.dColumnProcession_stage_injective n (lStar l.value)
  top_strip := by intro n i; rfl
  top_link := by intro n i j; rfl

@[simp] theorem dThetaShadowLedger_h1 :
    (I.dThetaShadowLedger).h1 = I.dThetaShadowFamily := rfl

@[simp] theorem dThetaShadowLedger_column (n : Int) :
    (I.dThetaShadowLedger).column n = I.dColumnProcession n := rfl

theorem dThetaShadowLedger_cardinality (n : Int) :
    Fintype.card (Fin (lStar l.value + 1)) = lStar l.value + 1 :=
  (I.dThetaShadowLedger).top_cardinality n

theorem dThetaShadowLedger_source_injective (n : Int) :
    Function.Injective
      (((I.dThetaShadowLedger).column n).stage (lStar l.value)).source :=
  (I.dThetaShadowLedger).top_source_injective n

theorem dThetaShadowLedger_top_strip (n : Int)
    (i : Fin (lStar l.value + 1)) :
    (((I.dThetaShadowLedger).column n).stage (lStar l.value)).strip i =
      I.dThetaShadowAt n (i.1 : Int) :=
  (I.dThetaShadowLedger).top_strip n i

theorem dThetaShadowLedger_top_link (n : Int)
    (i j : Fin (lStar l.value + 1)) :
    (((I.dThetaShadowLedger).column n).stage (lStar l.value)).link i j =
      I.dThetaShadowLinkAt n (i.1 : Int) n (j.1 : Int) :=
  (I.dThetaShadowLedger).top_link n i j

/-! ## 9. What is and is not supplied by this construction -/

structure VerticalCoricityGate where
  dTheater : I.family.index -> DPrimeStrip.{upi, uv} V
  verticalLink : forall i j, DPrimeStripEquiv (dTheater i) (dTheater j)
  bridge : forall i,
    DPrimeStripEquiv (dTheater i) ((I.dThetaShadow).dStrip i)
  source_dTheater : forall i,
    dTheater i = (I.dThetaShadow).dStrip i
  link_source : forall i j,
    verticalLink i j = (I.dThetaShadow).dLink i j

def verticalCoricityGate_of_shadow (G : I.VerticalCoricityGate) :
    I.DThetaRealizationGate where
  dTheater := G.dTheater
  bridge := G.bridge

theorem verticalCoricityGate_of_shadow_bridge (G : I.VerticalCoricityGate)
    (i : I.family.index) :
    (verticalCoricityGate_of_shadow G).bridge i = G.bridge i := rfl

theorem verticalCoricityGate_shadow_recovery (G : I.VerticalCoricityGate)
    (i : I.family.index) :
    (verticalCoricityGate_of_shadow G).dTheater i =
      (I.dThetaShadow).dStrip i :=
  G.source_dTheater i

theorem verticalCoricityGate_link_recovery (G : I.VerticalCoricityGate)
    (i j : I.family.index) :
    G.verticalLink i j = (I.dThetaShadow).dLink i j :=
  G.link_source i j

/-! The following exact shadow gate is constructible, but it is intentionally
    not declared to be `VerticalCoricityGate`: the latter names the theorem
    1.5(i) coricity output and must retain its source theorem fields. -/

structure DShadowSelfGate where
  dTheater : I.family.index -> DPrimeStrip.{upi, uv} V
  bridge : forall i,
    DPrimeStripEquiv (dTheater i) ((I.dThetaShadow).dStrip i)
  source : forall i, dTheater i = (I.dThetaShadow).dStrip i

def dShadowSelfGate : I.DShadowSelfGate where
  dTheater := (I.dThetaShadow).dStrip
  bridge := fun i => DPrimeStripEquiv.refl ((I.dThetaShadow).dStrip i)
  source := by intro i; rfl

@[simp] theorem dShadowSelfGate_dTheater (i : I.family.index) :
    (I.dShadowSelfGate).dTheater i = (I.dThetaShadow).dStrip i := rfl

@[simp] theorem dShadowSelfGate_bridge (i : I.family.index) :
    (I.dShadowSelfGate).bridge i =
      DPrimeStripEquiv.refl ((I.dThetaShadow).dStrip i) := rfl

theorem dShadowSelfGate_to_gate :
    I.dShadowSelfGate.dTheater = (I.dThetaShadow).dStrip := rfl

/-! ## 10. Reusable transport lemmas for later P1/P2 layers -/

theorem dShadow_link_component_bijective (i j : I.family.index) (v : V) :
    Function.Bijective
      ((I.dThetaShadow.dLink i j).isoPi v) := by
  exact (I.dThetaShadow_link_bijective_pi i j v)

theorem dShadow_link_component_projection (i j : I.family.index) (v : V)
    (x : (I.dThetaShadow.dStrip i).Pi v) :
    (I.dThetaShadow.dStrip j).proj v
        ((I.dThetaShadow.dLink i j).isoPi v x) =
      (I.dThetaShadow.dLink i j).isoG v
        ((I.dThetaShadow.dStrip i).proj v x) := by
  exact I.dThetaShadow_link_projection i j v x

theorem dShadow_column_component_bijective (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V) :
    Function.Bijective
      (((I.dColumnStage n k).link i i).isoPi v) := by
  exact (((I.dColumnStage n k).link i i).isoPi v).bijective

theorem dShadow_column_inclusion_component_bijective (n : Int)
    {k r : Nat} (h : k <= r) (i : Fin (k + 1)) (v : V) :
    Function.Bijective
      (((I.dColumnInclusion n h).component i).isoPi v) := by
  exact (((I.dColumnInclusion n h).component i).isoPi v).bijective

theorem dShadow_column_inclusion_projection (n : Int)
    {k r : Nat} (h : k <= r) (i : Fin (k + 1)) (v : V)
    (x : ((I.dColumnStage n k).strip i).Pi v) :
    ((I.dColumnStage n r).strip
      ((I.dColumnInclusion n h).map i)).proj v
        (((I.dColumnInclusion n h).component i).isoPi v x) =
      ((I.dColumnInclusion n h).component i).isoG v
        (((I.dColumnStage n k).strip i).proj v x) := by
  exact ((I.dColumnInclusion n h).component i).compat_apply v x

theorem dShadow_column_spoke_component_bijective
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V) :
    Function.Bijective
      ((P.dSpokeLink ((I.dColumnStage n k).source i)).isoPi v) := by
  exact ((P.dSpokeLink ((I.dColumnStage n k).source i)).isoPi v).bijective

theorem dShadow_column_spoke_projection
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (x : (I.family.theater
      (P.permutation ((I.dColumnStage n k).source i))).primeStrip.toD.Pi v) :
    (I.family.theater ((I.dColumnStage n k).source i)).primeStrip.toD.proj v
        ((P.dSpokeLink ((I.dColumnStage n k).source i)).isoPi v x) =
      (P.dSpokeLink ((I.dColumnStage n k).source i)).isoG v
        ((I.family.theater
          (P.permutation ((I.dColumnStage n k).source i))).primeStrip.toD.proj v x) := by
  exact (P.dSpokeLink ((I.dColumnStage n k).source i)).compat_apply v x

theorem dShadow_column_spoke_q
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.family.theater (P.permutation ((I.dColumnStage n k).source i))).thetaPacket.q =
      (I.family.theater ((I.dColumnStage n k).source i)).thetaPacket.q :=
  P.spoke_q ((I.dColumnStage n k).source i)

theorem dShadow_column_spoke_scale
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) (j : SignedLabel l.value) :
    (I.family.theater (P.permutation ((I.dColumnStage n k).source i))).thetaPacket.scale j =
      (I.family.theater ((I.dColumnStage n k).source i)).thetaPacket.scale j :=
  P.spoke_scale ((I.dColumnStage n k).source i) j

/-! ## 11. Explicit source closure marker -/

theorem dThetaShadow_closed :
    (Function.Injective I.family.theater) ∧
      (forall i, (I.dThetaShadow).dLink i i =
        DPrimeStripEquiv.refl ((I.dThetaShadow).dStrip i)) ∧
      (forall i j k, DPrimeStripEquiv.trans
        ((I.dThetaShadow).dLink i j)
        ((I.dThetaShadow).dLink j k) =
          (I.dThetaShadow).dLink i k) := by
  exact ⟨I.dThetaShadow_family_distinct, I.dThetaShadow_link_refl,
    I.dThetaShadow_link_trans⟩

end OriginalInput
end Theorem311Source
end
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def theorem311DThetaShadow : Obligation :=
  { id := "IUT-III.theorem-3.11-d-theta-shadow"
    source := "IUT III, Theorem 3.11 opening paragraph; Theorem 1.5(i); IUT I Prop. 6.9(ii)"
     status := VerificationStatus.interface
     note :=
       "Constructs the D-prime-strip shadow, a fixed-horizontal-coordinate " ++
         "vertical D-prime-strip core, D-links, fixed-column finite processions, " ++
         "inclusions, and spoke transport directly from the given OriginalInput " ++
         "family. The core is source-faithful at the D-prime-strip level. Theorem " ++
         "1.5(i) still requires the paper's full vertical coricity output: " ++
         "arithmetic holomorphic/mono-analytic log-shell data and its full " ++
         "D-Theta-Hodge-theater poly-isomorphisms; no shadow identity is promoted " ++
         "to that theorem."
     dependsOn := ["IUT-III.theorem-3.11-H1-H2-original-input-arrows",
       "IUT-I-II.prime-strip-core",
       "IUT-III.theorem-3.11-source-packet-degree-ledger"] }

end LeanFormal.IUT.Audit
