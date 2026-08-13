import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.SourceDThetaConstruction
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false

/-!
  # Source projection of the vertical D-Theta theater

  The opening data of Theorem 3.11 contains actual Theta-plus ell NF Hodge
  theaters and actual links between them.  The vertical-coricit object in the
  paper is a further object determined from this data by Theorem 1.5(i).  A
  useful part of that determination is nevertheless completely visible in the
  input: forget the F-prime-strip value monoids and retain the D-prime-strip,
  arithmetic record, and finite theta packet.  This file constructs that
  projection field by field.

  The construction is intentionally named a projection.  It proves all laws
  that follow from the supplied source links, including full D-Theta link
  equivalences, fixed-column finite stages, and lattice naturality.  It does
  not claim the arithmetic holomorphic, mono-analytic log-shell, or full
  poly-isomorphism data supplied by Theorem 1.5(i).  Those source-specific
  fields remain a separate gate in the audit.

  Source references: IUT III, Theorem 3.11 opening paragraph and (i);
  IUT III, Theorem 1.5(i); IUT I, Definition 5.2 and Proposition 6.9(ii).
 -/

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

/-! ## 1. The projected D-Theta theater and its full link -/

structure DThetaHodgeTheater (l : PrimeGeFive) (V : Type uv) where
  arithmetic : InitialThetaArithmeticData.{ua} l
  dPrimeStrip : DPrimeStrip.{upi, uv} V
  thetaPacket : FiniteThetaPacket l

namespace DThetaHodgeTheater

variable {l : PrimeGeFive} {V : Type uv}
variable (T : DThetaHodgeTheater.{ua, uv, upi} l V)

@[simp] theorem arithmetic_source : T.arithmetic = T.arithmetic := rfl

@[simp] theorem dPrimeStrip_source : T.dPrimeStrip = T.dPrimeStrip := rfl

@[simp] theorem thetaPacket_source : T.thetaPacket = T.thetaPacket := rfl

end DThetaHodgeTheater

structure DThetaHodgeTheaterLink
    {l : PrimeGeFive} {V : Type uv}
    (source target : DThetaHodgeTheater.{ua, uv, upi} l V) where
  dPrimeStripEquiv : DPrimeStripEquiv source.dPrimeStrip target.dPrimeStrip
  arithmetic_eq : source.arithmetic = target.arithmetic
  theta_q_eq : source.thetaPacket.q = target.thetaPacket.q
  theta_scale_eq : ∀ j,
    source.thetaPacket.scale j = target.thetaPacket.scale j

namespace DThetaHodgeTheaterLink

variable {l : PrimeGeFive} {V : Type uv}
variable {S T U : DThetaHodgeTheater.{ua, uv, upi} l V}

def refl (S : DThetaHodgeTheater.{ua, uv, upi} l V) :
    DThetaHodgeTheaterLink S S where
  dPrimeStripEquiv := DPrimeStripEquiv.refl S.dPrimeStrip
  arithmetic_eq := rfl
  theta_q_eq := rfl
  theta_scale_eq := by intro j; rfl

def symm (link : DThetaHodgeTheaterLink S T) :
    DThetaHodgeTheaterLink T S where
  dPrimeStripEquiv := DPrimeStripEquiv.symm link.dPrimeStripEquiv
  arithmetic_eq := link.arithmetic_eq.symm
  theta_q_eq := link.theta_q_eq.symm
  theta_scale_eq := by
    intro j
    exact (link.theta_scale_eq j).symm

def trans (first : DThetaHodgeTheaterLink S T)
    (second : DThetaHodgeTheaterLink T U) :
    DThetaHodgeTheaterLink S U where
  dPrimeStripEquiv := DPrimeStripEquiv.trans
    first.dPrimeStripEquiv second.dPrimeStripEquiv
  arithmetic_eq := first.arithmetic_eq.trans second.arithmetic_eq
  theta_q_eq := first.theta_q_eq.trans second.theta_q_eq
  theta_scale_eq := by
    intro j
    exact (first.theta_scale_eq j).trans (second.theta_scale_eq j)

theorem symm_symm (link : DThetaHodgeTheaterLink S T) :
    (link.symm).symm = link := by
  cases link
  rfl

theorem refl_trans (first : DThetaHodgeTheaterLink S T) :
    trans (refl S) first = first := by
  cases first
  rfl

theorem trans_refl (first : DThetaHodgeTheaterLink S T) :
    trans first (refl T) = first := by
  cases first
  rfl

theorem trans_assoc
    (first : DThetaHodgeTheaterLink S T)
    (second : DThetaHodgeTheaterLink T U)
    {W : DThetaHodgeTheater.{ua, uv, upi} l V}
    (third : DThetaHodgeTheaterLink U W) :
    trans (trans first second) third =
      trans first (trans second third) := by
  cases first
  cases second
  cases third
  rfl

theorem dPrimeStrip_bijective (link : DThetaHodgeTheaterLink S T)
    (v : V) : Function.Bijective (link.dPrimeStripEquiv.isoPi v) := by
  exact (link.dPrimeStripEquiv.isoPi v).bijective

theorem geometric_bijective (link : DThetaHodgeTheaterLink S T)
    (v : V) : Function.Bijective (link.dPrimeStripEquiv.isoG v) := by
  exact (link.dPrimeStripEquiv.isoG v).bijective

theorem projection_compat (link : DThetaHodgeTheaterLink S T)
    (v : V) (x : S.dPrimeStrip.Pi v) :
    T.dPrimeStrip.proj v (link.dPrimeStripEquiv.isoPi v x) =
      link.dPrimeStripEquiv.isoG v (S.dPrimeStrip.proj v x) := by
  exact link.dPrimeStripEquiv.compat_apply v x

theorem arithmetic_trans
    (first : DThetaHodgeTheaterLink S T)
    (second : DThetaHodgeTheaterLink T U) :
    S.arithmetic = U.arithmetic :=
  first.arithmetic_eq.trans second.arithmetic_eq

theorem q_trans
    (first : DThetaHodgeTheaterLink S T)
    (second : DThetaHodgeTheaterLink T U) :
    S.thetaPacket.q = U.thetaPacket.q :=
  first.theta_q_eq.trans second.theta_q_eq

theorem scale_trans
    (first : DThetaHodgeTheaterLink S T)
    (second : DThetaHodgeTheaterLink T U)
    (j : SignedLabel l.value) :
    S.thetaPacket.scale j = U.thetaPacket.scale j :=
  (first.theta_scale_eq j).trans (second.theta_scale_eq j)

theorem inverse_left (link : DThetaHodgeTheaterLink S T) :
    trans link (symm link) = refl S := by
  cases link
  rfl

theorem inverse_right (link : DThetaHodgeTheaterLink S T) :
    trans (symm link) link = refl T := by
  cases link
  rfl

end DThetaHodgeTheaterLink

/-! ## 2. Canonical projection at lattice coordinates -/

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

def dThetaTheaterAt (n m : Int) : DThetaHodgeTheater.{ua, uv, upi} l V where
  arithmetic := (I.theaterAt n m).arithmetic
  dPrimeStrip := (I.theaterAt n m).primeStrip.toD
  thetaPacket := (I.theaterAt n m).thetaPacket

@[simp] theorem dThetaTheaterAt_arithmetic (n m : Int) :
    (I.dThetaTheaterAt n m).arithmetic =
      (I.theaterAt n m).arithmetic := rfl

@[simp] theorem dThetaTheaterAt_dPrimeStrip (n m : Int) :
    (I.dThetaTheaterAt n m).dPrimeStrip =
      (I.theaterAt n m).primeStrip.toD := rfl

@[simp] theorem dThetaTheaterAt_thetaPacket (n m : Int) :
    (I.dThetaTheaterAt n m).thetaPacket =
      (I.theaterAt n m).thetaPacket := rfl

theorem dThetaTheaterAt_source_arithmetic (n m : Int) :
    (I.dThetaTheaterAt n m).arithmetic = I.initial.arithmetic :=
  I.theaterAt_arithmetic n m

theorem dThetaTheaterAt_source_arithmetic_symm (n m : Int) :
    I.initial.arithmetic = (I.dThetaTheaterAt n m).arithmetic :=
  (I.dThetaTheaterAt_source_arithmetic n m).symm

theorem dThetaTheaterAt_theta_q (n m : Int) :
    0 < (I.dThetaTheaterAt n m).thetaPacket.q :=
  (I.dThetaTheaterAt n m).thetaPacket.q_pos

theorem dThetaTheaterAt_scale_pos (n m : Int)
    (j : SignedLabel l.value) :
    0 < (I.dThetaTheaterAt n m).thetaPacket.scale j :=
  (I.dThetaTheaterAt n m).thetaPacket.scale_pos j

theorem dThetaTheaterAt_scale_ne_zero (n m : Int)
    (j : SignedLabel l.value) :
    (I.dThetaTheaterAt n m).thetaPacket.scale j ≠ 0 :=
  (I.dThetaTheaterAt n m).thetaPacket.scale_ne_zero j

def dThetaLinkAt (n m n' m' : Int) :
    DThetaHodgeTheaterLink (I.dThetaTheaterAt n m)
      (I.dThetaTheaterAt n' m') where
  dPrimeStripEquiv := (I.linkAt n m n' m').primeStripEquiv.toD
  arithmetic_eq := by
    exact (I.theaterAt_arithmetic n m).trans
      (I.theaterAt_arithmetic n' m').symm
  theta_q_eq := I.linkAt_q n m n' m'
  theta_scale_eq := I.linkAt_scale n m n' m'

@[simp] theorem dThetaLinkAt_dPrimeStrip (n m n' m' : Int) :
    (I.dThetaLinkAt n m n' m').dPrimeStripEquiv =
      (I.linkAt n m n' m').primeStripEquiv.toD := rfl

@[simp] theorem dThetaLinkAt_arithmetic (n m n' m' : Int) :
    (I.dThetaLinkAt n m n' m').arithmetic_eq =
      (I.dThetaLinkAt n m n' m').arithmetic_eq := rfl

theorem dThetaLinkAt_projection (n m n' m' : Int) (v : V)
    (x : (I.dThetaTheaterAt n m).dPrimeStrip.Pi v) :
    (I.dThetaTheaterAt n' m').dPrimeStrip.proj v
        ((I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoPi v x) =
      (I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoG v
        ((I.dThetaTheaterAt n m).dPrimeStrip.proj v x) := by
  exact (I.dThetaLinkAt n m n' m').projection_compat v x

theorem dThetaLinkAt_bijective_pi (n m n' m' : Int) (v : V) :
    Function.Bijective
      ((I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoPi v) := by
  exact (I.dThetaLinkAt n m n' m').dPrimeStrip_bijective v

theorem dThetaLinkAt_bijective_g (n m n' m' : Int) (v : V) :
    Function.Bijective
      ((I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoG v) := by
  exact (I.dThetaLinkAt n m n' m').geometric_bijective v

theorem dThetaLinkAt_arithmetic_eq (n m n' m' : Int) :
    (I.dThetaTheaterAt n m).arithmetic =
      (I.dThetaTheaterAt n' m').arithmetic :=
  (I.dThetaLinkAt n m n' m').arithmetic_eq

theorem dThetaLinkAt_q_eq (n m n' m' : Int) :
    (I.dThetaTheaterAt n m).thetaPacket.q =
      (I.dThetaTheaterAt n' m').thetaPacket.q :=
  (I.dThetaLinkAt n m n' m').theta_q_eq

theorem dThetaLinkAt_scale_eq (n m n' m' : Int)
    (j : SignedLabel l.value) :
    (I.dThetaTheaterAt n m).thetaPacket.scale j =
      (I.dThetaTheaterAt n' m').thetaPacket.scale j :=
  (I.dThetaLinkAt n m n' m').theta_scale_eq j

theorem dThetaLinkAt_refl (n m : Int) :
    I.dThetaLinkAt n m n m =
      DThetaHodgeTheaterLink.refl (I.dThetaTheaterAt n m) := by
  have h := I.linkAt_refl n m
  cases h
  rfl

theorem dThetaLinkAt_symm (n m n' m' : Int) :
    DThetaHodgeTheaterLink.symm (I.dThetaLinkAt n m n' m') =
      I.dThetaLinkAt n' m' n m := by
  have h := I.linkAt_symm n m n' m'
  cases h
  rfl

theorem dThetaLinkAt_trans (n m n' m' n'' m'' : Int) :
    DThetaHodgeTheaterLink.trans
        (I.dThetaLinkAt n m n' m')
        (I.dThetaLinkAt n' m' n'' m'') =
      I.dThetaLinkAt n m n'' m'' := by
  have h := I.linkAt_trans n m n' m' n'' m''
  cases h
  rfl

theorem dThetaLinkAt_inverse (n m n' m' : Int) :
    DThetaHodgeTheaterLink.trans
        (I.dThetaLinkAt n m n' m')
        (I.dThetaLinkAt n' m' n m) =
      DThetaHodgeTheaterLink.refl (I.dThetaTheaterAt n m) := by
  rw [← I.dThetaLinkAt_symm n m n' m']
  exact (I.dThetaLinkAt n m n' m').inverse_left

theorem dThetaLinkAt_inverse_right (n m n' m' : Int) :
    DThetaHodgeTheaterLink.trans
        (I.dThetaLinkAt n' m' n m)
        (I.dThetaLinkAt n m n' m') =
      DThetaHodgeTheaterLink.refl (I.dThetaTheaterAt n' m') := by
  rw [← I.dThetaLinkAt_symm n m n' m']
  exact (I.dThetaLinkAt n m n' m').inverse_right

/-! ## 3. Source trace and exact recovery of the shadow projection -/

theorem dThetaTheaterAt_source (n m : Int) :
    (I.dThetaTheaterAt n m).dPrimeStrip =
      (I.dThetaShadowAt n m) := rfl

theorem dThetaTheaterAt_source_fPrime (n m : Int) :
    (I.dThetaTheaterAt n m).dPrimeStrip =
      (I.theaterAt n m).primeStrip.toD := rfl

theorem dThetaLinkAt_source (n m n' m' : Int) :
    (I.dThetaLinkAt n m n' m').dPrimeStripEquiv =
      I.dThetaShadowLinkAt n m n' m' := rfl

theorem dThetaLinkAt_source_fLink (n m n' m' : Int) :
    (I.dThetaLinkAt n m n' m').dPrimeStripEquiv =
      (I.linkAt n m n' m').primeStripEquiv.toD := rfl

theorem dThetaTheaterAt_source_index (n m : Int) :
    I.theaterAt n m = I.family.theater (I.indexOf n m) := rfl

theorem dThetaLinkAt_source_link (n m n' m' : Int) :
    (I.dThetaLinkAt n m n' m').dPrimeStripEquiv =
      (I.family.link (I.indexOf n m) (I.indexOf n' m')).primeStripEquiv.toD := rfl

theorem dThetaTheaterAt_arithmetic_initial (n m : Int) :
    (I.dThetaTheaterAt n m).arithmetic = I.initial.arithmetic :=
  I.dThetaTheaterAt_source_arithmetic n m

theorem dThetaTheaterAt_arithmetic_pair (n m n' m' : Int) :
    (I.dThetaTheaterAt n m).arithmetic =
      (I.dThetaTheaterAt n' m').arithmetic :=
  I.dThetaLinkAt_arithmetic_eq n m n' m'

theorem dThetaTheaterAt_q_pair (n m n' m' : Int) :
    (I.dThetaTheaterAt n m).thetaPacket.q =
      (I.dThetaTheaterAt n' m').thetaPacket.q :=
  I.dThetaLinkAt_q_eq n m n' m'

theorem dThetaTheaterAt_scale_pair (n m n' m' : Int)
    (j : SignedLabel l.value) :
    (I.dThetaTheaterAt n m).thetaPacket.scale j =
      (I.dThetaTheaterAt n' m').thetaPacket.scale j :=
  I.dThetaLinkAt_scale_eq n m n' m' j

theorem dThetaTheaterAt_q_vertical (n m : Int) :
    (I.dThetaTheaterAt n m).thetaPacket.q =
      (I.dThetaTheaterAt n (m + 1)).thetaPacket.q :=
  I.dThetaTheaterAt_q_pair n m n (m + 1)

theorem dThetaTheaterAt_scale_vertical (n m : Int)
    (j : SignedLabel l.value) :
    (I.dThetaTheaterAt n m).thetaPacket.scale j =
      (I.dThetaTheaterAt n (m + 1)).thetaPacket.scale j :=
  I.dThetaTheaterAt_scale_pair n m n (m + 1) j

theorem dThetaTheaterAt_q_horizontal (n m : Int) :
    (I.dThetaTheaterAt n m).thetaPacket.q =
      (I.dThetaTheaterAt (n + 1) m).thetaPacket.q :=
  I.dThetaTheaterAt_q_pair n m (n + 1) m

theorem dThetaTheaterAt_scale_horizontal (n m : Int)
    (j : SignedLabel l.value) :
    (I.dThetaTheaterAt n m).thetaPacket.scale j =
      (I.dThetaTheaterAt (n + 1) m).thetaPacket.scale j :=
  I.dThetaTheaterAt_scale_pair n m (n + 1) m j

/-! ## 4. Fixed-n vertical lines -/

structure DThetaVerticalLine (n : Int) where
  member : Int → DThetaHodgeTheater.{ua, uv, upi} l V
  member_source : ∀ m, member m = I.dThetaTheaterAt n m
  link : ∀ m m', DThetaHodgeTheaterLink (member m) (member m')
  link_source : ∀ m m', link m m' = I.dThetaLinkAt n m n m'
  link_refl : ∀ m, link m m = DThetaHodgeTheaterLink.refl (member m)
  link_symm : ∀ m m',
    DThetaHodgeTheaterLink.symm (link m m') = link m' m
  link_trans : ∀ m m' m'',
    DThetaHodgeTheaterLink.trans (link m m') (link m' m'') = link m m''

def dThetaVerticalLine (n : Int) : I.DThetaVerticalLine n where
  member := I.dThetaTheaterAt n
  member_source := by intro m; rfl
  link := fun m m' => I.dThetaLinkAt n m n m'
  link_source := by intro m m'; rfl
  link_refl := by
    intro m
    exact I.dThetaLinkAt_refl n m
  link_symm := by
    intro m m'
    exact I.dThetaLinkAt_symm n m n m'
  link_trans := by
    intro m m' m''
    exact I.dThetaLinkAt_trans n m n m' n m''

@[simp] theorem dThetaVerticalLine_member (n m : Int) :
    (I.dThetaVerticalLine n).member m = I.dThetaTheaterAt n m := rfl

@[simp] theorem dThetaVerticalLine_link (n m m' : Int) :
    (I.dThetaVerticalLine n).link m m' = I.dThetaLinkAt n m n m' := rfl

theorem dThetaVerticalLine_member_source (n m : Int) :
    (I.dThetaVerticalLine n).member m = I.dThetaTheaterAt n m :=
  (I.dThetaVerticalLine n).member_source m

theorem dThetaVerticalLine_link_source (n m m' : Int) :
    (I.dThetaVerticalLine n).link m m' = I.dThetaLinkAt n m n m' :=
  (I.dThetaVerticalLine n).link_source m m'

theorem dThetaVerticalLine_link_refl (n m : Int) :
    (I.dThetaVerticalLine n).link m m =
      DThetaHodgeTheaterLink.refl
        ((I.dThetaVerticalLine n).member m) :=
  (I.dThetaVerticalLine n).link_refl m

theorem dThetaVerticalLine_link_symm (n m m' : Int) :
    DThetaHodgeTheaterLink.symm
        ((I.dThetaVerticalLine n).link m m') =
      (I.dThetaVerticalLine n).link m' m :=
  (I.dThetaVerticalLine n).link_symm m m'

theorem dThetaVerticalLine_link_trans (n m m' m'' : Int) :
    DThetaHodgeTheaterLink.trans
        ((I.dThetaVerticalLine n).link m m')
        ((I.dThetaVerticalLine n).link m' m'') =
      (I.dThetaVerticalLine n).link m m'' :=
  (I.dThetaVerticalLine n).link_trans m m' m''

theorem dThetaVerticalLine_member_arithmetic (n m : Int) :
    ((I.dThetaVerticalLine n).member m).arithmetic = I.initial.arithmetic := by
  rw [I.dThetaVerticalLine_member]
  exact I.dThetaTheaterAt_source_arithmetic n m

theorem dThetaVerticalLine_member_q (n m : Int) :
    ((I.dThetaVerticalLine n).member m).thetaPacket.q =
      (I.dThetaVerticalLine n).member 0 |>.thetaPacket.q := by
  rw [I.dThetaVerticalLine_member, I.dThetaVerticalLine_member]
  exact I.dThetaTheaterAt_q_pair n m n 0

theorem dThetaVerticalLine_member_scale (n m : Int)
    (j : SignedLabel l.value) :
    ((I.dThetaVerticalLine n).member m).thetaPacket.scale j =
      (I.dThetaVerticalLine n).member 0 |>.thetaPacket.scale j := by
  rw [I.dThetaVerticalLine_member, I.dThetaVerticalLine_member]
  exact I.dThetaTheaterAt_scale_pair n m n 0 j

theorem dThetaVerticalLine_link_bijective_pi (n m m' : Int) (v : V) :
    Function.Bijective
      (((I.dThetaVerticalLine n).link m m').dPrimeStripEquiv.isoPi v) := by
  rw [I.dThetaVerticalLine_link]
  exact I.dThetaLinkAt_bijective_pi n m n m' v

theorem dThetaVerticalLine_link_bijective_g (n m m' : Int) (v : V) :
    Function.Bijective
      (((I.dThetaVerticalLine n).link m m').dPrimeStripEquiv.isoG v) := by
  rw [I.dThetaVerticalLine_link]
  exact I.dThetaLinkAt_bijective_g n m n m' v

theorem dThetaVerticalLine_link_projection (n m m' : Int) (v : V)
    (x : ((I.dThetaVerticalLine n).member m).dPrimeStrip.Pi v) :
    ((I.dThetaVerticalLine n).member m').dPrimeStrip.proj v
        (((I.dThetaVerticalLine n).link m m').dPrimeStripEquiv.isoPi v x) =
      ((I.dThetaVerticalLine n).link m m').dPrimeStripEquiv.isoG v
        (((I.dThetaVerticalLine n).member m).dPrimeStrip.proj v x) := by
  rw [I.dThetaVerticalLine_link, I.dThetaVerticalLine_member,
    I.dThetaVerticalLine_member]
  exact I.dThetaLinkAt_projection n m n m' v x

theorem dThetaVerticalLine_link_arithmetic (n m m' : Int) :
    ((I.dThetaVerticalLine n).member m).arithmetic =
      ((I.dThetaVerticalLine n).member m').arithmetic := by
  rw [I.dThetaVerticalLine_link]
  exact I.dThetaLinkAt_arithmetic_eq n m n m'

theorem dThetaVerticalLine_link_q (n m m' : Int) :
    ((I.dThetaVerticalLine n).member m).thetaPacket.q =
      ((I.dThetaVerticalLine n).member m').thetaPacket.q := by
  rw [I.dThetaVerticalLine_link]
  exact I.dThetaLinkAt_q_eq n m n m'

theorem dThetaVerticalLine_link_scale (n m m' : Int)
    (j : SignedLabel l.value) :
    ((I.dThetaVerticalLine n).member m).thetaPacket.scale j =
      ((I.dThetaVerticalLine n).member m').thetaPacket.scale j := by
  rw [I.dThetaVerticalLine_link]
  exact I.dThetaLinkAt_scale_eq n m n m' j

/-! ## 5. The source-visible full vertical isomorphism -/

def verticalFullIso (n m : Int) :
    DThetaHodgeTheaterLink
      ((I.dThetaVerticalLine n).member m)
      ((I.dThetaVerticalLine n).member (m + 1)) :=
  (I.dThetaVerticalLine n).link m (m + 1)

@[simp] theorem verticalFullIso_source (n m : Int) :
    I.verticalFullIso n m = I.dThetaLinkAt n m n (m + 1) := rfl

theorem verticalFullIso_bijective_pi (n m : Int) (v : V) :
    Function.Bijective
      ((I.verticalFullIso n m).dPrimeStripEquiv.isoPi v) := by
  exact I.dThetaVerticalLine_link_bijective_pi n m (m + 1) v

theorem verticalFullIso_bijective_g (n m : Int) (v : V) :
    Function.Bijective
      ((I.verticalFullIso n m).dPrimeStripEquiv.isoG v) := by
  exact I.dThetaVerticalLine_link_bijective_g n m (m + 1) v

theorem verticalFullIso_projection (n m : Int) (v : V)
    (x : ((I.dThetaVerticalLine n).member m).dPrimeStrip.Pi v) :
    ((I.dThetaVerticalLine n).member (m + 1)).dPrimeStrip.proj v
        ((I.verticalFullIso n m).dPrimeStripEquiv.isoPi v x) =
      (I.verticalFullIso n m).dPrimeStripEquiv.isoG v
        (((I.dThetaVerticalLine n).member m).dPrimeStrip.proj v x) := by
  exact I.dThetaVerticalLine_link_projection n m (m + 1) v x

theorem verticalFullIso_arithmetic (n m : Int) :
    ((I.dThetaVerticalLine n).member m).arithmetic =
      ((I.dThetaVerticalLine n).member (m + 1)).arithmetic :=
  I.dThetaVerticalLine_link_arithmetic n m (m + 1)

theorem verticalFullIso_q (n m : Int) :
    ((I.dThetaVerticalLine n).member m).thetaPacket.q =
      ((I.dThetaVerticalLine n).member (m + 1)).thetaPacket.q :=
  I.dThetaVerticalLine_link_q n m (m + 1)

theorem verticalFullIso_scale (n m : Int) (j : SignedLabel l.value) :
    ((I.dThetaVerticalLine n).member m).thetaPacket.scale j =
      ((I.dThetaVerticalLine n).member (m + 1)).thetaPacket.scale j :=
  I.dThetaVerticalLine_link_scale n m (m + 1) j

theorem verticalFullIso_inverse (n m : Int) :
    DThetaHodgeTheaterLink.trans (I.verticalFullIso n m)
        (I.dThetaVerticalLine n).link (m + 1) m =
      DThetaHodgeTheaterLink.refl
        ((I.dThetaVerticalLine n).member m) :=
  (I.dThetaVerticalLine n).link m (m + 1) |>.inverse_left

theorem verticalFullIso_inverse_right (n m : Int) :
    DThetaHodgeTheaterLink.trans
        ((I.dThetaVerticalLine n).link (m + 1) m)
        (I.verticalFullIso n m) =
      DThetaHodgeTheaterLink.refl
        ((I.dThetaVerticalLine n).member (m + 1)) :=
  (I.dThetaVerticalLine n).link m (m + 1) |>.inverse_right

theorem verticalFullIso_two_step (n m : Int) :
    DThetaHodgeTheaterLink.trans (I.verticalFullIso n m)
        ((I.dThetaVerticalLine n).link (m + 1) (m + 2)) =
      (I.dThetaVerticalLine n).link m (m + 2) :=
  (I.dThetaVerticalLine n).link_trans m (m + 1) (m + 2)

theorem verticalFullIso_n_step (n m : Int) (k : Nat) :
    DThetaHodgeTheaterLink.trans
        ((I.dThetaVerticalLine n).link m (m + k))
        ((I.dThetaVerticalLine n).link (m + k) (m + k + 1)) =
      (I.dThetaVerticalLine n).link m (m + k + 1) := by
  exact (I.dThetaVerticalLine n).link_trans m (m + k) (m + k + 1)

theorem verticalFullIso_chain (n m : Int) :
    ∀ k : Nat,
      DThetaHodgeTheaterLink.trans
          ((I.dThetaVerticalLine n).link m (m + k))
          ((I.dThetaVerticalLine n).link (m + k) (m + k + 1)) =
        (I.dThetaVerticalLine n).link m (m + k + 1) := by
  intro k
  exact I.verticalFullIso_n_step n m k

/-! ## 6. Finite vertical stages -/

structure DThetaVerticalStage (n : Int) (k : Nat) where
  source : Fin (k + 1) → I.family.index
  source_eq : ∀ i, source i = I.indexOf n (i.1 : Int)
  source_injective : Function.Injective source
  theater : Fin (k + 1) → DThetaHodgeTheater.{ua, uv, upi} l V
  theater_eq : ∀ i, theater i = I.dThetaTheaterAt n (i.1 : Int)
  link : ∀ i j, DThetaHodgeTheaterLink (theater i) (theater j)
  link_eq : ∀ i j, link i j = I.dThetaLinkAt n (i.1 : Int) n (j.1 : Int)

def dThetaVerticalStage (n : Int) (k : Nat) : I.DThetaVerticalStage n k where
  source := fun i => I.indexOf n (i.1 : Int)
  source_eq := by intro i; rfl
  source_injective := I.columnSource_injective n k
  theater := fun i => I.dThetaTheaterAt n (i.1 : Int)
  theater_eq := by intro i; rfl
  link := fun i j => I.dThetaLinkAt n (i.1 : Int) n (j.1 : Int)
  link_eq := by intro i j; rfl

@[simp] theorem dThetaVerticalStage_source (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.dThetaVerticalStage n k).source i = I.indexOf n (i.1 : Int) := rfl

@[simp] theorem dThetaVerticalStage_theater (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.dThetaVerticalStage n k).theater i =
      I.dThetaTheaterAt n (i.1 : Int) := rfl

@[simp] theorem dThetaVerticalStage_link (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    (I.dThetaVerticalStage n k).link i j =
      I.dThetaLinkAt n (i.1 : Int) n (j.1 : Int) := rfl

theorem dThetaVerticalStage_source_injective (n : Int) (k : Nat) :
    Function.Injective (I.dThetaVerticalStage n k).source :=
  (I.dThetaVerticalStage n k).source_injective

theorem dThetaVerticalStage_link_refl (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.dThetaVerticalStage n k).link i i =
      DThetaHodgeTheaterLink.refl
        ((I.dThetaVerticalStage n k).theater i) := by
  rw [I.dThetaVerticalStage_link, I.dThetaLinkAt_refl]
  rfl

theorem dThetaVerticalStage_link_symm (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    DThetaHodgeTheaterLink.symm
        ((I.dThetaVerticalStage n k).link i j) =
      (I.dThetaVerticalStage n k).link j i := by
  rw [I.dThetaVerticalStage_link, I.dThetaLinkAt_symm]
  rfl

theorem dThetaVerticalStage_link_trans (n : Int) (k : Nat)
    (i j h : Fin (k + 1)) :
    DThetaHodgeTheaterLink.trans
        ((I.dThetaVerticalStage n k).link i j)
        ((I.dThetaVerticalStage n k).link j h) =
      (I.dThetaVerticalStage n k).link i h := by
  rw [I.dThetaVerticalStage_link, I.dThetaLinkAt_trans]
  rfl

theorem dThetaVerticalStage_cardinality (n : Int) (k : Nat) :
    Fintype.card (Fin (k + 1)) = k + 1 := by
  simp

theorem dThetaVerticalStage_source_pair (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    (I.dThetaVerticalStage n k).source i =
      (I.dThetaVerticalStage n k).source j ↔ i = j := by
  constructor
  · intro h
    exact I.dThetaVerticalStage_source_injective n k h
  · intro h
    cases h
    rfl

theorem dThetaVerticalStage_q_pair (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    ((I.dThetaVerticalStage n k).theater i).thetaPacket.q =
      ((I.dThetaVerticalStage n k).theater j).thetaPacket.q := by
  rw [I.dThetaVerticalStage_theater, I.dThetaVerticalStage_theater]
  exact I.dThetaTheaterAt_q_pair n (i.1 : Int) n (j.1 : Int)

theorem dThetaVerticalStage_scale_pair (n : Int) (k : Nat)
    (i j : Fin (k + 1)) (r : SignedLabel l.value) :
    ((I.dThetaVerticalStage n k).theater i).thetaPacket.scale r =
      ((I.dThetaVerticalStage n k).theater j).thetaPacket.scale r := by
  rw [I.dThetaVerticalStage_theater, I.dThetaVerticalStage_theater]
  exact I.dThetaTheaterAt_scale_pair n (i.1 : Int) n (j.1 : Int) r

theorem dThetaVerticalStage_arithmetic_pair (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    ((I.dThetaVerticalStage n k).theater i).arithmetic =
      ((I.dThetaVerticalStage n k).theater j).arithmetic := by
  rw [I.dThetaVerticalStage_theater, I.dThetaVerticalStage_theater]
  exact I.dThetaTheaterAt_arithmetic_pair n (i.1 : Int) n (j.1 : Int)

theorem dThetaVerticalStage_link_bijective (n : Int) (k : Nat)
    (i j : Fin (k + 1)) (v : V) :
    Function.Bijective
      (((I.dThetaVerticalStage n k).link i j).dPrimeStripEquiv.isoPi v) := by
  rw [I.dThetaVerticalStage_link]
  exact I.dThetaLinkAt_bijective_pi n (i.1 : Int) n (j.1 : Int) v

theorem dThetaVerticalStage_link_projection (n : Int) (k : Nat)
    (i j : Fin (k + 1)) (v : V)
    (x : ((I.dThetaVerticalStage n k).theater i).dPrimeStrip.Pi v) :
    ((I.dThetaVerticalStage n k).theater j).dPrimeStrip.proj v
        (((I.dThetaVerticalStage n k).link i j).dPrimeStripEquiv.isoPi v x) =
      ((I.dThetaVerticalStage n k).link i j).dPrimeStripEquiv.isoG v
        (((I.dThetaVerticalStage n k).theater i).dPrimeStrip.proj v x) := by
  rw [I.dThetaVerticalStage_link, I.dThetaVerticalStage_theater,
    I.dThetaVerticalStage_theater]
  exact I.dThetaLinkAt_projection n (i.1 : Int) n (j.1 : Int) v x

/-! ## 7. Stage inclusions and procession -/

structure DThetaVerticalInclusion (n : Int) {k r : Nat} (h : k ≤ r) where
  map : Fin (k + 1) → Fin (r + 1)
  map_eq : ∀ i, map i = finStageMap h i
  map_injective : Function.Injective map
  component : ∀ i,
    DThetaHodgeTheaterLink
      ((I.dThetaVerticalStage n k).theater i)
      ((I.dThetaVerticalStage n r).theater (map i))
  component_eq : ∀ i,
    component i = I.dThetaLinkAt n (i.1 : Int) n ((map i).1 : Int)
  naturality : ∀ i j,
    DThetaHodgeTheaterLink.trans
        ((I.dThetaVerticalStage n k).link i j)
        (component j) =
      DThetaHodgeTheaterLink.trans
        (component i)
        ((I.dThetaVerticalStage n r).link (map i) (map j))

def dThetaVerticalInclusion (n : Int) {k r : Nat} (h : k ≤ r) :
    I.DThetaVerticalInclusion n h where
  map := finStageMap h
  map_eq := by intro i; rfl
  map_injective := finStageMap_injective h
  component := fun i =>
    I.dThetaLinkAt n (i.1 : Int) n ((finStageMap h i).1 : Int)
  component_eq := by intro i; rfl
  naturality := by
    intro i j
    change DThetaHodgeTheaterLink.trans
        (I.dThetaLinkAt n (i.1 : Int) n (j.1 : Int))
        (I.dThetaLinkAt n (j.1 : Int) n
          ((finStageMap h j).1 : Int)) =
      DThetaHodgeTheaterLink.trans
        (I.dThetaLinkAt n (i.1 : Int) n
          ((finStageMap h i).1 : Int))
        (I.dThetaLinkAt n ((finStageMap h i).1 : Int) n
          ((finStageMap h j).1 : Int))
    rw [I.dThetaLinkAt_trans, I.dThetaLinkAt_trans]

@[simp] theorem dThetaVerticalInclusion_map (n : Int) {k r : Nat}
    (h : k ≤ r) (i : Fin (k + 1)) :
    (I.dThetaVerticalInclusion n h).map i = finStageMap h i := rfl

@[simp] theorem dThetaVerticalInclusion_component (n : Int)
    {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)) :
    (I.dThetaVerticalInclusion n h).component i =
      I.dThetaLinkAt n (i.1 : Int) n
        ((finStageMap h i).1 : Int) := rfl

theorem dThetaVerticalInclusion_injective (n : Int) {k r : Nat}
    (h : k ≤ r) :
    Function.Injective (I.dThetaVerticalInclusion n h).map :=
  (I.dThetaVerticalInclusion n h).map_injective

theorem dThetaVerticalInclusion_natural (n : Int) {k r : Nat}
    (h : k ≤ r) (i j : Fin (k + 1)) :
    DThetaHodgeTheaterLink.trans
        ((I.dThetaVerticalStage n k).link i j)
        ((I.dThetaVerticalInclusion n h).component j) =
      DThetaHodgeTheaterLink.trans
        ((I.dThetaVerticalInclusion n h).component i)
        ((I.dThetaVerticalStage n r).link
          ((I.dThetaVerticalInclusion n h).map i)
          ((I.dThetaVerticalInclusion n h).map j)) :=
  (I.dThetaVerticalInclusion n h).naturality i j

theorem dThetaVerticalInclusion_refl (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.dThetaVerticalInclusion n (Nat.le_refl k)).map i = i := by
  rw [dThetaVerticalInclusion_map]
  exact finStageMap_refl k i

theorem dThetaVerticalInclusion_trans (n : Int) {k r s : Nat}
    (h₁ : k ≤ r) (h₂ : r ≤ s) (i : Fin (k + 1)) :
    (I.dThetaVerticalInclusion n (Nat.le_trans h₁ h₂)).map i =
      (I.dThetaVerticalInclusion n h₂).map
        ((I.dThetaVerticalInclusion n h₁).map i) := by
  rw [dThetaVerticalInclusion_map, dThetaVerticalInclusion_map,
    dThetaVerticalInclusion_map]
  exact (finStageMap_trans h₁ h₂ i).symm

theorem dThetaVerticalInclusion_component_bijective (n : Int)
    {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)) (v : V) :
    Function.Bijective
      (((I.dThetaVerticalInclusion n h).component i).dPrimeStripEquiv.isoPi v) := by
  exact (((I.dThetaVerticalInclusion n h).component i).dPrimeStripEquiv.isoPi v).bijective

theorem dThetaVerticalInclusion_component_projection (n : Int)
    {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)) (v : V)
    (x : ((I.dThetaVerticalStage n k).theater i).dPrimeStrip.Pi v) :
    ((I.dThetaVerticalStage n r).theater
      ((I.dThetaVerticalInclusion n h).map i)).dPrimeStrip.proj v
        (((I.dThetaVerticalInclusion n h).component i).dPrimeStripEquiv.isoPi v x) =
      ((I.dThetaVerticalInclusion n h).component i).dPrimeStripEquiv.isoG v
        (((I.dThetaVerticalStage n k).theater i).dPrimeStrip.proj v x) := by
  rw [dThetaVerticalInclusion_component, dThetaVerticalStage_theater,
    dThetaVerticalStage_theater]
  exact I.dThetaLinkAt_projection n (i.1 : Int) n
    ((finStageMap h i).1 : Int) v x

structure DThetaVerticalProcession (n : Int) where
  stage : (k : Nat) → I.DThetaVerticalStage n k
  inclusion : ∀ {k r : Nat} (h : k ≤ r), I.DThetaVerticalInclusion n h
  inclusion_refl : ∀ (k : Nat) (i : Fin (k + 1)),
    (inclusion (Nat.le_refl k)).map i = i
  inclusion_trans : ∀ {k r s : Nat} (h₁ : k ≤ r) (h₂ : r ≤ s)
    (i : Fin (k + 1)),
    (inclusion (Nat.le_trans h₁ h₂)).map i =
      (inclusion h₂).map ((inclusion h₁).map i)

def dThetaVerticalProcession (n : Int) : I.DThetaVerticalProcession n where
  stage := I.dThetaVerticalStage n
  inclusion := fun {_ _} h => I.dThetaVerticalInclusion n h
  inclusion_refl := by
    intro k i
    exact I.dThetaVerticalInclusion_refl n k i
  inclusion_trans := by
    intro k r s h₁ h₂ i
    exact I.dThetaVerticalInclusion_trans n h₁ h₂ i

@[simp] theorem dThetaVerticalProcession_stage (n : Int) (k : Nat) :
    (I.dThetaVerticalProcession n).stage k =
      I.dThetaVerticalStage n k := rfl

@[simp] theorem dThetaVerticalProcession_inclusion (n : Int)
    {k r : Nat} (h : k ≤ r) :
    (I.dThetaVerticalProcession n).inclusion h =
      I.dThetaVerticalInclusion n h := rfl

theorem dThetaVerticalProcession_stage_source (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    ((I.dThetaVerticalProcession n).stage k).source i =
      I.indexOf n (i.1 : Int) := rfl

theorem dThetaVerticalProcession_stage_theater (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    ((I.dThetaVerticalProcession n).stage k).theater i =
      I.dThetaTheaterAt n (i.1 : Int) := rfl

theorem dThetaVerticalProcession_stage_link (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    ((I.dThetaVerticalProcession n).stage k).link i j =
      I.dThetaLinkAt n (i.1 : Int) n (j.1 : Int) := rfl

theorem dThetaVerticalProcession_stage_cardinality (n : Int) (k : Nat) :
    Fintype.card (Fin (k + 1)) = k + 1 := by
  simp

theorem dThetaVerticalProcession_stage_injective (n : Int) (k : Nat) :
    Function.Injective
      ((I.dThetaVerticalProcession n).stage k).source :=
  (I.dThetaVerticalProcession n).stage k |>.source_injective

theorem dThetaVerticalProcession_inclusion_natural (n : Int)
    {k r : Nat} (h : k ≤ r) (i j : Fin (k + 1)) :
    DThetaHodgeTheaterLink.trans
        (((I.dThetaVerticalProcession n).stage k).link i j)
        (((I.dThetaVerticalProcession n).inclusion h).component j) =
      DThetaHodgeTheaterLink.trans
        (((I.dThetaVerticalProcession n).inclusion h).component i)
        (((I.dThetaVerticalProcession n).stage r).link
          (((I.dThetaVerticalProcession n).inclusion h).map i)
          (((I.dThetaVerticalProcession n).inclusion h).map j)) :=
  (I.dThetaVerticalProcession n).inclusion h |>.naturality i j

theorem dThetaVerticalProcession_top_cardinality (n : Int) :
    Fintype.card (Fin (lStar l.value + 1)) = lStar l.value + 1 := by
  simp

theorem dThetaVerticalProcession_top_injective (n : Int) :
    Function.Injective
      (((I.dThetaVerticalProcession n).stage (lStar l.value)).source) :=
  I.dThetaVerticalProcession_stage_injective n (lStar l.value)

/-! ## 8. Exact source compatibility with the existing D procession -/

theorem dThetaVerticalStage_toD_stage (n : Int) (k : Nat) :
    (I.dThetaVerticalStage n k).theater =
      fun i => I.dThetaTheaterAt n (i.1 : Int) := rfl

theorem dThetaVerticalStage_strip_recovery (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    ((I.dThetaVerticalStage n k).theater i).dPrimeStrip =
      (I.dColumnStage n k).strip i := by
  rfl

theorem dThetaVerticalStage_link_recovery (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    ((I.dThetaVerticalStage n k).link i j).dPrimeStripEquiv =
      (I.dColumnStage n k).link i j := by
  rfl

theorem dThetaVerticalInclusion_component_recovery (n : Int)
    {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)) :
    ((I.dThetaVerticalInclusion n h).component i).dPrimeStripEquiv =
      (I.dColumnInclusion n h).component i := by
  rfl

theorem dThetaVerticalProcession_strip_recovery (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    ((I.dThetaVerticalProcession n).stage k).theater i |>.dPrimeStrip =
      ((I.dColumnProcession n).stage k).strip i := by
  rfl

theorem dThetaVerticalProcession_link_recovery (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    (((I.dThetaVerticalProcession n).stage k).link i j).dPrimeStripEquiv =
      ((I.dColumnProcession n).stage k).link i j := by
  rfl

theorem dThetaVerticalProcession_inclusion_recovery (n : Int)
    {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)) :
    (((I.dThetaVerticalProcession n).inclusion h).component i).dPrimeStripEquiv =
      ((I.dColumnProcession n).inclusion h).component i := by
  rfl

theorem dThetaVerticalProcession_top_strip (n : Int)
    (i : Fin (lStar l.value + 1)) :
    ((I.dThetaVerticalProcession n).stage (lStar l.value)).theater i |>.dPrimeStrip =
      I.dThetaShadowAt n (i.1 : Int) := by
  rfl

theorem dThetaVerticalProcession_top_link (n : Int)
    (i j : Fin (lStar l.value + 1)) :
    (((I.dThetaVerticalProcession n).stage (lStar l.value)).link i j)
      .dPrimeStripEquiv = I.dThetaShadowLinkAt n (i.1 : Int) n (j.1 : Int) := by
  rfl

/-! ## 9. Horizontal and vertical lattice squares -/

def horizontalDThetaLinkAt (n m : Int) :
    DThetaHodgeTheaterLink (I.dThetaTheaterAt n m)
      (I.dThetaTheaterAt (n + 1) m) :=
  I.dThetaLinkAt n m (n + 1) m

def verticalDThetaLinkAt (n m : Int) :
    DThetaHodgeTheaterLink (I.dThetaTheaterAt n m)
      (I.dThetaTheaterAt n (m + 1)) :=
  I.dThetaLinkAt n m n (m + 1)

@[simp] theorem horizontalDThetaLinkAt_source (n m : Int) :
    I.horizontalDThetaLinkAt n m = I.dThetaLinkAt n m (n + 1) m := rfl

@[simp] theorem verticalDThetaLinkAt_source (n m : Int) :
    I.verticalDThetaLinkAt n m = I.dThetaLinkAt n m n (m + 1) := rfl

theorem horizontalDThetaLinkAt_projection (n m : Int) (v : V)
    (x : (I.dThetaTheaterAt n m).dPrimeStrip.Pi v) :
    (I.dThetaTheaterAt (n + 1) m).dPrimeStrip.proj v
        ((I.horizontalDThetaLinkAt n m).dPrimeStripEquiv.isoPi v x) =
      (I.horizontalDThetaLinkAt n m).dPrimeStripEquiv.isoG v
        ((I.dThetaTheaterAt n m).dPrimeStrip.proj v x) :=
  I.dThetaLinkAt_projection n m (n + 1) m v x

theorem verticalDThetaLinkAt_projection (n m : Int) (v : V)
    (x : (I.dThetaTheaterAt n m).dPrimeStrip.Pi v) :
    (I.dThetaTheaterAt n (m + 1)).dPrimeStrip.proj v
        ((I.verticalDThetaLinkAt n m).dPrimeStripEquiv.isoPi v x) =
      (I.verticalDThetaLinkAt n m).dPrimeStripEquiv.isoG v
        ((I.dThetaTheaterAt n m).dPrimeStrip.proj v x) :=
  I.dThetaLinkAt_projection n m n (m + 1) v x

theorem horizontal_then_vertical_dTheta (n m : Int) :
    DThetaHodgeTheaterLink.trans
        (I.horizontalDThetaLinkAt n m)
        (I.verticalDThetaLinkAt (n + 1) m) =
      I.dThetaLinkAt n m (n + 1) (m + 1) := by
  exact I.dThetaLinkAt_trans n m (n + 1) m (n + 1) (m + 1)

theorem vertical_then_horizontal_dTheta (n m : Int) :
    DThetaHodgeTheaterLink.trans
        (I.verticalDThetaLinkAt n m)
        (I.horizontalDThetaLinkAt n (m + 1)) =
      I.dThetaLinkAt n m (n + 1) (m + 1) := by
  exact I.dThetaLinkAt_trans n m n (m + 1) (n + 1) (m + 1)

theorem dTheta_square_link_eq (n m : Int) :
    DThetaHodgeTheaterLink.trans
        (I.horizontalDThetaLinkAt n m)
        (I.verticalDThetaLinkAt (n + 1) m) =
      DThetaHodgeTheaterLink.trans
        (I.verticalDThetaLinkAt n m)
        (I.horizontalDThetaLinkAt n (m + 1)) := by
  rw [I.horizontal_then_vertical_dTheta,
    I.vertical_then_horizontal_dTheta]

theorem dTheta_square_arithmetic (n m : Int) :
    (I.dThetaTheaterAt n m).arithmetic =
      (I.dThetaTheaterAt (n + 1) (m + 1)).arithmetic :=
  I.dThetaLinkAt_arithmetic_eq n m (n + 1) (m + 1)

theorem dTheta_square_q (n m : Int) :
    (I.dThetaTheaterAt n m).thetaPacket.q =
      (I.dThetaTheaterAt (n + 1) (m + 1)).thetaPacket.q :=
  I.dThetaLinkAt_q_eq n m (n + 1) (m + 1)

theorem dTheta_square_scale (n m : Int) (j : SignedLabel l.value) :
    (I.dThetaTheaterAt n m).thetaPacket.scale j =
      (I.dThetaTheaterAt (n + 1) (m + 1)).thetaPacket.scale j :=
  I.dThetaLinkAt_scale_eq n m (n + 1) (m + 1) j

theorem dTheta_square_projection (n m : Int) (v : V)
    (x : (I.dThetaTheaterAt n m).dPrimeStrip.Pi v) :
    (I.dThetaTheaterAt (n + 1) (m + 1)).dPrimeStrip.proj v
        ((I.dThetaLinkAt n m (n + 1) (m + 1)).dPrimeStripEquiv.isoPi v x) =
      (I.dThetaLinkAt n m (n + 1) (m + 1)).dPrimeStripEquiv.isoG v
        ((I.dThetaTheaterAt n m).dPrimeStrip.proj v x) :=
  I.dThetaLinkAt_projection n m (n + 1) (m + 1) v x

/-! ## 10. Permutation transport -/

def permutationDThetaLink (i : I.family.index) :
    DThetaHodgeTheaterLink
      (DThetaHodgeTheater.mk
        (I.family.theater (I.family.permutation i)).arithmetic
        (I.family.theater (I.family.permutation i)).primeStrip.toD
        (I.family.theater (I.family.permutation i)).thetaPacket)
      (DThetaHodgeTheater.mk
        (I.family.theater i).arithmetic
        (I.family.theater i).primeStrip.toD
        (I.family.theater i).thetaPacket) where
  dPrimeStripEquiv := (I.family.permutationLink i).primeStripEquiv.toD
  arithmetic_eq := by
    exact (I.family_arithmetic_alignment (I.family.permutation i)).trans
      (I.family_arithmetic_alignment i).symm
  theta_q_eq := (I.family.permutationLink i).theta_q_eq
  theta_scale_eq := (I.family.permutationLink i).theta_scale_eq

theorem permutationDThetaLink_projection (i : I.family.index) (v : V)
    (x : (I.family.theater (I.family.permutation i)).primeStrip.toD.Pi v) :
    (I.family.theater i).primeStrip.toD.proj v
        ((I.permutationDThetaLink i).dPrimeStripEquiv.isoPi v x) =
      (I.permutationDThetaLink i).dPrimeStripEquiv.isoG v
        ((I.family.theater (I.family.permutation i)).primeStrip.toD.proj v x) := by
  exact (I.permutationDThetaLink i).projection_compat v x

theorem permutationDThetaLink_bijective_pi (i : I.family.index) (v : V) :
    Function.Bijective
      ((I.permutationDThetaLink i).dPrimeStripEquiv.isoPi v) := by
  exact (I.permutationDThetaLink i).dPrimeStrip_bijective v

theorem permutationDThetaLink_bijective_g (i : I.family.index) (v : V) :
    Function.Bijective
      ((I.permutationDThetaLink i).dPrimeStripEquiv.isoG v) := by
  exact (I.permutationDThetaLink i).geometric_bijective v

theorem permutationDThetaLink_q (i : I.family.index) :
    (I.family.theater (I.family.permutation i)).thetaPacket.q =
      (I.family.theater i).thetaPacket.q :=
  (I.permutationDThetaLink i).theta_q_eq

theorem permutationDThetaLink_scale (i : I.family.index)
    (j : SignedLabel l.value) :
    (I.family.theater (I.family.permutation i)).thetaPacket.scale j =
      (I.family.theater i).thetaPacket.scale j :=
  (I.permutationDThetaLink i).theta_scale_eq j

theorem permutationDThetaLink_arithmetic (i : I.family.index) :
    (I.family.theater (I.family.permutation i)).arithmetic =
      (I.family.theater i).arithmetic :=
  (I.permutationDThetaLink i).arithmetic_eq

theorem permutationDThetaLink_natural (i j : I.family.index) :
    DPrimeStripEquiv.trans
        ((I.family.link (I.family.permutation i)
          (I.family.permutation j)).primeStripEquiv.toD)
        ((I.family.permutationLink j).primeStripEquiv.toD) =
      DPrimeStripEquiv.trans
        ((I.family.permutationLink i).primeStripEquiv.toD)
        ((I.family.link i j).primeStripEquiv.toD) := by
  rw [FPrimeStripEquiv.toD_trans, FPrimeStripEquiv.toD_trans]
  exact congrArg FPrimeStripEquiv.toD
    (I.family.permutation_naturality i j)

theorem permutationDThetaLink_natural_q (i j : I.family.index) :
    (I.family.theater (I.family.permutation i)).thetaPacket.q =
      (I.family.theater (I.family.permutation j)).thetaPacket.q := by
  exact (I.family.permutation_q i).trans
    ((I.family.link_q i j).trans (I.family.permutation_q j).symm)

theorem permutationDThetaLink_natural_scale (i j : I.family.index)
    (r : SignedLabel l.value) :
    (I.family.theater (I.family.permutation i)).thetaPacket.scale r =
      (I.family.theater (I.family.permutation j)).thetaPacket.scale r := by
  exact (I.family.permutation_scale i r).trans
    ((I.family.link_scale i j r).trans
      (I.family.permutation_scale j r).symm)

/-! ## 11. Coordinate form of permutation transport -/

def permutationIndex (p : SourceTheorem311Index) : SourceTheorem311Index :=
  I.index_equiv (I.family.permutation (I.indexOf p.1 p.2))

theorem permutationIndex_apply (p : SourceTheorem311Index) :
    I.index_equiv (I.family.permutation (I.indexOf p.1 p.2)) =
      I.permutationIndex p := rfl

theorem permutationIndex_injective :
    Function.Injective I.permutationIndex := by
  intro p q h
  apply I.family.permutation.injective
  apply I.index_equiv.injective
  simpa [permutationIndex] using h

theorem permutationIndex_bijective :
    Function.Bijective I.permutationIndex := by
  refine ⟨I.permutationIndex_injective, ?_⟩
  intro p
  let i := I.family.permutation.symm (I.indexOf p.1 p.2)
  refine ⟨I.index_equiv i, ?_⟩
  apply I.index_equiv.injective
  simp [permutationIndex, i]

theorem permutationIndex_source (p : SourceTheorem311Index) :
    I.indexOf (I.permutationIndex p).1 (I.permutationIndex p).2 =
      I.family.permutation (I.indexOf p.1 p.2) := by
  apply I.index_equiv.injective
  exact I.indexOf_apply _ _

theorem permutationIndex_q (p : SourceTheorem311Index) :
    (I.dThetaTheaterAt (I.permutationIndex p).1
      (I.permutationIndex p).2).thetaPacket.q =
      (I.dThetaTheaterAt p.1 p.2).thetaPacket.q := by
  rw [I.dThetaTheaterAt_thetaPacket, I.dThetaTheaterAt_thetaPacket,
    I.dThetaTheaterAt_source_index, I.dThetaTheaterAt_source_index,
    I.permutationIndex_source]
  exact I.family.permutation_q _

theorem permutationIndex_scale (p : SourceTheorem311Index)
    (j : SignedLabel l.value) :
    (I.dThetaTheaterAt (I.permutationIndex p).1
      (I.permutationIndex p).2).thetaPacket.scale j =
      (I.dThetaTheaterAt p.1 p.2).thetaPacket.scale j := by
  rw [I.dThetaTheaterAt_thetaPacket, I.dThetaTheaterAt_thetaPacket,
    I.dThetaTheaterAt_source_index, I.dThetaTheaterAt_source_index,
    I.permutationIndex_source]
  exact I.family.permutation_scale _ j

theorem permutationIndex_arithmetic (p : SourceTheorem311Index) :
    (I.dThetaTheaterAt (I.permutationIndex p).1
      (I.permutationIndex p).2).arithmetic =
      (I.dThetaTheaterAt p.1 p.2).arithmetic := by
  exact I.dThetaTheaterAt_arithmetic_pair _ _ _ _

/-! ## 12. Source projection ledger -/

structure DThetaProjectionLedger where
  theater : ∀ n m : Int, DThetaHodgeTheater.{ua, uv, upi} l V
  theater_source : ∀ n m, theater n m = I.dThetaTheaterAt n m
  vertical : ∀ n : Int, DThetaVerticalLine I n
  vertical_source : ∀ n, (vertical n).member = I.dThetaTheaterAt n
  procession : ∀ n : Int, DThetaVerticalProcession I n
  procession_source : ∀ n, (procession n).stage = I.dThetaVerticalStage n
  horizontal : ∀ n m : Int,
    DThetaHodgeTheaterLink (theater n m) (theater (n + 1) m)
  horizontal_source : ∀ n m,
    horizontal n m = I.horizontalDThetaLinkAt n m
  vertical_arrow : ∀ n m : Int,
    DThetaHodgeTheaterLink (theater n m) (theater n (m + 1))
  vertical_arrow_source : ∀ n m,
    vertical_arrow n m = I.verticalDThetaLinkAt n m

def dThetaProjectionLedger : I.DThetaProjectionLedger where
  theater := I.dThetaTheaterAt
  theater_source := by intro n m; rfl
  vertical := I.dThetaVerticalLine
  vertical_source := by
    intro n
    funext m
    rfl
  procession := I.dThetaVerticalProcession
  procession_source := by intro n; rfl
  horizontal := I.horizontalDThetaLinkAt
  horizontal_source := by intro n m; rfl
  vertical_arrow := I.verticalDThetaLinkAt
  vertical_arrow_source := by intro n m; rfl

@[simp] theorem dThetaProjectionLedger_theater (n m : Int) :
    (I.dThetaProjectionLedger).theater n m = I.dThetaTheaterAt n m := rfl

@[simp] theorem dThetaProjectionLedger_vertical (n : Int) :
    (I.dThetaProjectionLedger).vertical n = I.dThetaVerticalLine n := rfl

@[simp] theorem dThetaProjectionLedger_procession (n : Int) :
    (I.dThetaProjectionLedger).procession n =
      I.dThetaVerticalProcession n := rfl

@[simp] theorem dThetaProjectionLedger_horizontal (n m : Int) :
    (I.dThetaProjectionLedger).horizontal n m =
      I.horizontalDThetaLinkAt n m := rfl

@[simp] theorem dThetaProjectionLedger_vertical_arrow (n m : Int) :
    (I.dThetaProjectionLedger).vertical_arrow n m =
      I.verticalDThetaLinkAt n m := rfl

theorem dThetaProjectionLedger_theater_arithmetic (n m : Int) :
    (I.dThetaProjectionLedger).theater n m |>.arithmetic =
      I.initial.arithmetic := by
  rw [dThetaProjectionLedger_theater]
  exact I.dThetaTheaterAt_source_arithmetic n m

theorem dThetaProjectionLedger_vertical_bijective (n m : Int) (v : V) :
    Function.Bijective
      (((I.dThetaProjectionLedger).vertical_arrow n m)
        .dPrimeStripEquiv.isoPi v) := by
  rw [dThetaProjectionLedger_vertical_arrow]
  exact (I.verticalDThetaLinkAt n m).dPrimeStrip_bijective v

theorem dThetaProjectionLedger_vertical_projection (n m : Int) (v : V)
    (x : ((I.dThetaProjectionLedger).theater n m).dPrimeStrip.Pi v) :
    ((I.dThetaProjectionLedger).theater n (m + 1)).dPrimeStrip.proj v
        (((I.dThetaProjectionLedger).vertical_arrow n m)
          .dPrimeStripEquiv.isoPi v x) =
      ((I.dThetaProjectionLedger).vertical_arrow n m)
        .dPrimeStripEquiv.isoG v
        (((I.dThetaProjectionLedger).theater n m).dPrimeStrip.proj v x) := by
  rw [dThetaProjectionLedger_theater, dThetaProjectionLedger_vertical_arrow]
  exact I.verticalDThetaLinkAt_projection n m v x

theorem dThetaProjectionLedger_square (n m : Int) :
    DThetaHodgeTheaterLink.trans
        ((I.dThetaProjectionLedger).horizontal n m)
        ((I.dThetaProjectionLedger).vertical_arrow (n + 1) m) =
      DThetaHodgeTheaterLink.trans
        ((I.dThetaProjectionLedger).vertical_arrow n m)
        ((I.dThetaProjectionLedger).horizontal n (m + 1)) := by
  rw [dThetaProjectionLedger_horizontal,
    dThetaProjectionLedger_vertical_arrow,
    dThetaProjectionLedger_vertical_arrow,
    dThetaProjectionLedger_horizontal]
  exact I.dTheta_square_link_eq n m

/-! ## 13. The explicit boundary between projection and coricity -/

structure DThetaCoricityGate where
  theater : ∀ n m : Int, DThetaHodgeTheater.{ua, uv, upi} l V
  verticalIso : ∀ n m : Int,
    DThetaHodgeTheaterLink (theater n m) (theater n (m + 1))
  bridge : ∀ n m, DPrimeStripEquiv
    (theater n m).dPrimeStrip (I.dThetaTheaterAt n m).dPrimeStrip
  bridge_source : ∀ n m, bridge n m = DPrimeStripEquiv.refl
    (I.dThetaTheaterAt n m).dPrimeStrip

def projectionCoricityGate : I.DThetaCoricityGate where
  theater := I.dThetaTheaterAt
  verticalIso := I.verticalDThetaLinkAt
  bridge := fun n m => DPrimeStripEquiv.refl (I.dThetaTheaterAt n m).dPrimeStrip
  bridge_source := by intro n m; rfl

@[simp] theorem projectionCoricityGate_theater (n m : Int) :
    (I.projectionCoricityGate).theater n m = I.dThetaTheaterAt n m := rfl

@[simp] theorem projectionCoricityGate_verticalIso (n m : Int) :
    (I.projectionCoricityGate).verticalIso n m =
      I.verticalDThetaLinkAt n m := rfl

theorem projectionCoricityGate_bridge (n m : Int) :
    (I.projectionCoricityGate).bridge n m =
      DPrimeStripEquiv.refl (I.dThetaTheaterAt n m).dPrimeStrip := rfl

theorem projectionCoricityGate_vertical_bijective (n m : Int) (v : V) :
    Function.Bijective
      (((I.projectionCoricityGate).verticalIso n m)
        .dPrimeStripEquiv.isoPi v) := by
  rw [projectionCoricityGate_verticalIso]
  exact (I.verticalDThetaLinkAt n m).dPrimeStrip_bijective v

theorem projectionCoricityGate_vertical_q (n m : Int) :
    ((I.projectionCoricityGate).theater n m).thetaPacket.q =
      ((I.projectionCoricityGate).theater n (m + 1)).thetaPacket.q := by
  rw [projectionCoricityGate_theater, projectionCoricityGate_theater]
  exact I.dThetaTheaterAt_q_vertical n m

theorem projectionCoricityGate_vertical_scale (n m : Int)
    (j : SignedLabel l.value) :
    ((I.projectionCoricityGate).theater n m).thetaPacket.scale j =
      ((I.projectionCoricityGate).theater n (m + 1)).thetaPacket.scale j := by
  rw [projectionCoricityGate_theater, projectionCoricityGate_theater]
  exact I.dThetaTheaterAt_scale_vertical n m j

/-! ## 14. Reusable source-facing consequences -/

theorem dTheta_vertical_transport_q (n m : Int) (k : Nat) :
    (I.dThetaTheaterAt n m).thetaPacket.q =
      (I.dThetaTheaterAt n (m + k)).thetaPacket.q :=
  I.dThetaTheaterAt_q_pair n m n (m + k)

theorem dTheta_vertical_transport_scale (n m : Int) (k : Nat)
    (j : SignedLabel l.value) :
    (I.dThetaTheaterAt n m).thetaPacket.scale j =
      (I.dThetaTheaterAt n (m + k)).thetaPacket.scale j :=
  I.dThetaTheaterAt_scale_pair n m n (m + k) j

theorem dTheta_vertical_transport_arithmetic (n m : Int) (k : Nat) :
    (I.dThetaTheaterAt n m).arithmetic =
      (I.dThetaTheaterAt n (m + k)).arithmetic :=
  I.dThetaTheaterAt_arithmetic_pair n m n (m + k)

theorem dTheta_any_coordinate_q (n m n' m' : Int) :
    (I.dThetaTheaterAt n m).thetaPacket.q =
      (I.dThetaTheaterAt n' m').thetaPacket.q :=
  I.dThetaTheaterAt_q_pair n m n' m'

theorem dTheta_any_coordinate_scale (n m n' m' : Int)
    (j : SignedLabel l.value) :
    (I.dThetaTheaterAt n m).thetaPacket.scale j =
      (I.dThetaTheaterAt n' m').thetaPacket.scale j :=
  I.dThetaTheaterAt_scale_pair n m n' m' j

theorem dTheta_any_coordinate_arithmetic (n m n' m' : Int) :
    (I.dThetaTheaterAt n m).arithmetic =
      (I.dThetaTheaterAt n' m').arithmetic :=
  I.dThetaTheaterAt_arithmetic_pair n m n' m'

theorem dTheta_link_inverse_pair (n m n' m' : Int) :
    DThetaHodgeTheaterLink.trans
        (I.dThetaLinkAt n m n' m')
        (I.dThetaLinkAt n' m' n m) =
      DThetaHodgeTheaterLink.refl (I.dThetaTheaterAt n m) :=
  I.dThetaLinkAt_inverse n m n' m'

theorem dTheta_link_inverse_pair_right (n m n' m' : Int) :
    DThetaHodgeTheaterLink.trans
        (I.dThetaLinkAt n' m' n m)
        (I.dThetaLinkAt n m n' m') =
      DThetaHodgeTheaterLink.refl (I.dThetaTheaterAt n' m') :=
  I.dThetaLinkAt_inverse_right n m n' m'

theorem dTheta_link_three_coordinate (n m n' m' n'' m'' : Int) :
    DThetaHodgeTheaterLink.trans
        (I.dThetaLinkAt n m n' m')
        (I.dThetaLinkAt n' m' n'' m'') =
      I.dThetaLinkAt n m n'' m'' :=
  I.dThetaLinkAt_trans n m n' m' n'' m''

theorem dTheta_link_projection_bijective (n m n' m' : Int) (v : V) :
    Function.Bijective
      ((I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoPi v) :=
  I.dThetaLinkAt_bijective_pi n m n' m' v

theorem dTheta_link_geometric_bijective (n m n' m' : Int) (v : V) :
    Function.Bijective
      ((I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoG v) :=
  I.dThetaLinkAt_bijective_g n m n' m' v

theorem dTheta_source_root_bundle (n m : Int) :
    (I.dThetaTheaterAt n m).arithmetic = I.initial.arithmetic ∧
      0 < (I.dThetaTheaterAt n m).thetaPacket.q ∧
      (I.dThetaTheaterAt n m).dPrimeStrip = I.dThetaShadowAt n m := by
  exact ⟨I.dThetaTheaterAt_source_arithmetic n m,
    I.dThetaTheaterAt_theta_q n m, I.dThetaTheaterAt_source n m⟩

theorem dTheta_vertical_root_bundle (n m : Int) :
    (I.dThetaVerticalLine n).member m |>.arithmetic = I.initial.arithmetic ∧
      ((I.dThetaVerticalLine n).member m).thetaPacket.q =
        ((I.dThetaVerticalLine n).member 0).thetaPacket.q ∧
      ((I.dThetaVerticalLine n).member m).dPrimeStrip =
        I.dThetaShadowAt n m := by
  rw [I.dThetaVerticalLine_member]
  exact ⟨I.dThetaTheaterAt_source_arithmetic n m,
    I.dThetaVerticalLine_member_q n m, I.dThetaTheaterAt_source n m⟩

theorem dTheta_top_stage_bundle (n : Int)
    (i : Fin (lStar l.value + 1)) :
    ((I.dThetaVerticalProcession n).stage (lStar l.value)).source i =
        I.indexOf n (i.1 : Int) ∧
      ((I.dThetaVerticalProcession n).stage (lStar l.value)).theater i |>.dPrimeStrip =
        I.dThetaShadowAt n (i.1 : Int) := by
  exact ⟨I.dThetaVerticalProcession_stage_source n (lStar l.value) i,
    I.dThetaVerticalProcession_top_strip n i⟩

theorem dTheta_square_bundle (n m : Int) :
    (I.dThetaTheaterAt n m).arithmetic =
        (I.dThetaTheaterAt (n + 1) (m + 1)).arithmetic ∧
      (I.dThetaTheaterAt n m).thetaPacket.q =
        (I.dThetaTheaterAt (n + 1) (m + 1)).thetaPacket.q ∧
      DThetaHodgeTheaterLink.trans
          (I.horizontalDThetaLinkAt n m)
          (I.verticalDThetaLinkAt (n + 1) m) =
        DThetaHodgeTheaterLink.trans
          (I.verticalDThetaLinkAt n m)
          (I.horizontalDThetaLinkAt n (m + 1)) := by
  exact ⟨I.dTheta_square_arithmetic n m, I.dTheta_square_q n m,
    I.dTheta_square_link_eq n m⟩

/-! ## 15. F-prime-strip trace retained by the D projection -/

theorem dThetaLinkAt_isoPi_source (n m n' m' : Int) (v : V) :
    (I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoPi v =
      (I.primeStripLinkAt n m n' m').isoPi v := rfl

theorem dThetaLinkAt_isoG_source (n m n' m' : Int) (v : V) :
    (I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoG v =
      (I.primeStripLinkAt n m n' m').isoG v := rfl

theorem dThetaLinkAt_f_projection (n m n' m' : Int) (v : V)
    (x : (I.primeStripAt n m).toDPrimeStrip.Pi v) :
    (I.primeStripAt n' m').proj v
        ((I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoPi v x) =
      (I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoG v
        ((I.primeStripAt n m).proj v x) := by
  exact I.dThetaLinkAt_projection n m n' m' v x

theorem dThetaLinkAt_f_action (n m n' m' : Int) (v : V)
    (g : (I.primeStripAt n m).toDPrimeStrip.Pi v)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripAt n' m').action v
        ((I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoPi v g)
        ((I.primeStripLinkAt n m n' m').isoMon v x) =
      (I.primeStripLinkAt n m n' m').isoMon v
        ((I.primeStripAt n m).action v g x) := by
  exact (I.link_action_commutes n m n' m' v g x).symm

theorem dThetaLinkAt_f_degree (n m n' m' : Int) (v : V)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripAt n' m').degree v
        ((I.primeStripLinkAt n m n' m').isoMon v x) =
      (I.primeStripAt n m).degree v x := by
  exact I.link_degree_commutes n m n' m' v x

theorem dThetaLinkAt_geometric_iff (n m n' m' : Int) (v : V)
    (x : (I.dThetaTheaterAt n m).dPrimeStrip.Pi v) :
    x ∈ (I.dThetaTheaterAt n m).dPrimeStrip.geometric v ↔
      (I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoPi v x ∈
        (I.dThetaTheaterAt n' m').dPrimeStrip.geometric v := by
  exact I.link_geometric_commutes n m n' m' v x

theorem dThetaLinkAt_geometric_one_mem (n m : Int) (v : V) :
    (1 : (I.dThetaTheaterAt n m).dPrimeStrip.Pi v) ∈
      (I.dThetaTheaterAt n m).dPrimeStrip.geometric v := by
  exact (I.dThetaTheaterAt n m).dPrimeStrip.geometric_carrier v 1 |>.mpr
    (by simp)

theorem dThetaLinkAt_geometric_mul_mem (n m : Int) (v : V)
    {x y : (I.dThetaTheaterAt n m).dPrimeStrip.Pi v}
    (hx : x ∈ (I.dThetaTheaterAt n m).dPrimeStrip.geometric v)
    (hy : y ∈ (I.dThetaTheaterAt n m).dPrimeStrip.geometric v) :
    x * y ∈ (I.dThetaTheaterAt n m).dPrimeStrip.geometric v := by
  exact (I.dThetaTheaterAt n m).geometricAt_subgroup_mul v hx hy

theorem dThetaLinkAt_geometric_inv_mem (n m : Int) (v : V)
    {x : (I.dThetaTheaterAt n m).dPrimeStrip.Pi v}
    (hx : x ∈ (I.dThetaTheaterAt n m).dPrimeStrip.geometric v) :
    x⁻¹ ∈ (I.dThetaTheaterAt n m).dPrimeStrip.geometric v := by
  exact (I.dThetaTheaterAt n m).geometricAt_subgroup_inv v hx

theorem dThetaLinkAt_f_totalDegree (n m n' m' : Int) (s : Finset V)
    (x : ∀ v, (I.primeStripAt n m).Mon v) :
    (I.primeStripAt n' m').totalDegree s
        (fun v => (I.primeStripLinkAt n m n' m').isoMon v (x v)) =
      (I.primeStripAt n m).totalDegree s x := by
  apply Finset.sum_congr rfl
  intro v hv
  exact I.link_degree_commutes n m n' m' v (x v)

theorem dThetaLinkAt_f_totalDegree_mul (n m n' m' : Int) (s : Finset V)
    (x y : ∀ v, (I.primeStripAt n m).Mon v) :
    (I.primeStripAt n' m').totalDegree s
        (fun v => (I.primeStripLinkAt n m n' m').isoMon v
          (x v * y v)) =
      (I.primeStripAt n m).totalDegree s (fun v => x v * y v) := by
  exact I.dThetaLinkAt_f_totalDegree n m n' m' s
    (fun v => x v * y v)

theorem dThetaLinkAt_f_action_degree (n m n' m' : Int) (v : V)
    (g : (I.primeStripAt n m).toDPrimeStrip.Pi v)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripAt n' m').degree v
        ((I.primeStripAt n' m').action v
          ((I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoPi v g)
          ((I.primeStripLinkAt n m n' m').isoMon v x)) =
      (I.primeStripAt n m).degree v ((I.primeStripAt n m).action v g x) := by
  rw [I.dThetaLinkAt_f_action]
  exact I.dThetaLinkAt_f_degree n m n' m' v
    ((I.primeStripAt n m).action v g x)

theorem dThetaLinkAt_d_geometric_transport (n m n' m' : Int) (v : V)
    (x : (I.dThetaTheaterAt n m).dPrimeStrip.Pi v) :
    x ∈ (I.dThetaTheaterAt n m).dPrimeStrip.geometric v ↔
      (I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoPi v x ∈
        (I.dThetaTheaterAt n' m').dPrimeStrip.geometric v :=
  I.dThetaLinkAt_geometric_iff n m n' m' v x

theorem dThetaLinkAt_d_geometric_transport_symm (n m n' m' : Int) (v : V)
    (x : (I.dThetaTheaterAt n' m').dPrimeStrip.Pi v) :
    x ∈ (I.dThetaTheaterAt n' m').dPrimeStrip.geometric v ↔
      (I.dThetaLinkAt n' m' n m).dPrimeStripEquiv.isoPi v x ∈
        (I.dThetaTheaterAt n m).dPrimeStrip.geometric v :=
  I.dThetaLinkAt_geometric_iff n' m' n m v x

theorem dThetaLinkAt_f_action_one (n m n' m' : Int) (v : V)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripLinkAt n m n' m').isoMon v
        ((I.primeStripAt n m).action v 1 x) =
      (I.primeStripAt n' m').action v
        ((I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoPi v 1)
        ((I.primeStripLinkAt n m n' m').isoMon v x) := by
  exact (I.dThetaLinkAt_f_action n m n' m' v 1 x).symm

theorem dThetaLinkAt_f_action_mul (n m n' m' : Int) (v : V)
    (g h : (I.primeStripAt n m).toDPrimeStrip.Pi v)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripLinkAt n m n' m').isoMon v
        ((I.primeStripAt n m).action v (g * h) x) =
      (I.primeStripAt n' m').action v
        ((I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoPi v (g * h))
        ((I.primeStripLinkAt n m n' m').isoMon v x) := by
  exact (I.dThetaLinkAt_f_action n m n' m' v (g * h) x).symm

theorem dThetaLinkAt_degree_preserves_zero (n m n' m' : Int) (v : V) :
    (I.primeStripAt n' m').degree v 1 =
      (I.primeStripAt n m).degree v 1 := by
  obtain ⟨x, hx⟩ := (I.primeStripAt n m).degree_surjective v
  exact (I.dThetaLinkAt_f_degree n m n' m' v x).trans
    (by simpa [hx])

theorem dThetaLinkAt_f_link_trans_action
    (n m n' m' n'' m'' : Int) (v : V)
    (g : (I.primeStripAt n m).toDPrimeStrip.Pi v)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripLinkAt n m n'' m'').isoMon v
        ((I.primeStripAt n m).action v g x) =
      (I.primeStripLinkAt n' m' n'' m'').isoMon v
        ((I.primeStripLinkAt n m n' m').isoMon v
          ((I.primeStripAt n m).action v g x)) := by
  rw [I.primeStripLinkAt_trans]
  rfl

theorem dThetaLinkAt_d_link_trans_pi
    (n m n' m' n'' m'' : Int) (v : V)
    (x : (I.dThetaTheaterAt n m).dPrimeStrip.Pi v) :
    (I.dThetaLinkAt n m n'' m'').dPrimeStripEquiv.isoPi v x =
      (I.dThetaLinkAt n' m' n'' m'').dPrimeStripEquiv.isoPi v
        ((I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoPi v x) := by
  rw [I.dThetaLinkAt_trans]
  rfl

theorem dThetaLinkAt_d_link_trans_g
    (n m n' m' n'' m'' : Int) (v : V)
    (x : (I.dThetaTheaterAt n m).dPrimeStrip.G v) :
    (I.dThetaLinkAt n m n'' m'').dPrimeStripEquiv.isoG v x =
      (I.dThetaLinkAt n' m' n'' m'').dPrimeStripEquiv.isoG v
        ((I.dThetaLinkAt n m n' m').dPrimeStripEquiv.isoG v x) := by
  rw [I.dThetaLinkAt_trans]
  rfl

theorem dThetaLinkAt_f_link_trans_degree
    (n m n' m' n'' m'' : Int) (v : V)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripAt n'' m'').degree v
        ((I.primeStripLinkAt n' m' n'' m'').isoMon v
          ((I.primeStripLinkAt n m n' m').isoMon v x)) =
      (I.primeStripAt n m).degree v x := by
  rw [← I.primeStripLinkAt_trans]
  exact I.link_degree_commutes n m n'' m'' v x

theorem dTheta_vertical_line_f_degree (n m m' : Int) (v : V)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripAt n m').degree v
        ((I.primeStripLinkAt n m n m').isoMon v x) =
      (I.primeStripAt n m).degree v x :=
  I.dThetaLinkAt_f_degree n m n m' v x

theorem dTheta_vertical_line_f_action (n m m' : Int) (v : V)
    (g : (I.primeStripAt n m).toDPrimeStrip.Pi v)
    (x : (I.primeStripAt n m).Mon v) :
    (I.primeStripLinkAt n m n m').isoMon v
        ((I.primeStripAt n m).action v g x) =
      (I.primeStripAt n m').action v
        ((I.dThetaLinkAt n m n m').dPrimeStripEquiv.isoPi v g)
        ((I.primeStripLinkAt n m n m').isoMon v x) := by
  exact I.dThetaLinkAt_f_action n m n m' v g x

theorem dTheta_vertical_line_geometric (n m m' : Int) (v : V)
    (x : (I.dThetaTheaterAt n m).dPrimeStrip.Pi v) :
    x ∈ (I.dThetaTheaterAt n m).dPrimeStrip.geometric v ↔
      (I.dThetaLinkAt n m n m').dPrimeStripEquiv.isoPi v x ∈
        (I.dThetaTheaterAt n m').dPrimeStrip.geometric v :=
  I.dThetaLinkAt_geometric_iff n m n m' v x

theorem dTheta_vertical_line_totalDegree (n m m' : Int) (s : Finset V)
    (x : ∀ v, (I.primeStripAt n m).Mon v) :
    (I.primeStripAt n m').totalDegree s
        (fun v => (I.primeStripLinkAt n m n m').isoMon v (x v)) =
      (I.primeStripAt n m).totalDegree s x :=
  I.dThetaLinkAt_f_totalDegree n m n m' s x

theorem dTheta_vertical_line_link_trans
    (n m m' m'' : Int) :
    DThetaHodgeTheaterLink.trans
        (I.dThetaLinkAt n m n m')
        (I.dThetaLinkAt n m' n m'') =
      I.dThetaLinkAt n m n m'' :=
  I.dThetaLinkAt_trans n m n m' n m''

theorem dTheta_vertical_line_link_symm
    (n m m' : Int) :
    DThetaHodgeTheaterLink.symm (I.dThetaLinkAt n m n m') =
      I.dThetaLinkAt n m' n m :=
  I.dThetaLinkAt_symm n m n m'

theorem dTheta_vertical_line_link_refl (n m : Int) :
    I.dThetaLinkAt n m n m =
      DThetaHodgeTheaterLink.refl (I.dThetaTheaterAt n m) :=
  I.dThetaLinkAt_refl n m

/-! The F trace is deliberately kept separate from the D-theater record.  The
    D projection forgets the value monoid, but these equalities make the
    forgotten source fields available to later packet and degree modules. -/

structure DThetaFSourceTrace (n m n' m' : Int) where
  sourceF : FPrimeStrip.{umon, uv, upi} V
  targetF : FPrimeStrip.{umon, uv, upi} V
  sourceF_eq : sourceF = I.primeStripAt n m
  targetF_eq : targetF = I.primeStripAt n' m'
  fLink : FPrimeStripEquiv sourceF targetF
  fLink_eq : fLink = I.primeStripLinkAt n m n' m'
  dLink_eq : fLink.toD = I.dThetaLinkAt n m n' m' |>.dPrimeStripEquiv

def dThetaFSourceTrace (n m n' m' : Int) : I.DThetaFSourceTrace n m n' m' where
  sourceF := I.primeStripAt n m
  targetF := I.primeStripAt n' m'
  sourceF_eq := rfl
  targetF_eq := rfl
  fLink := I.primeStripLinkAt n m n' m'
  fLink_eq := rfl
  dLink_eq := rfl

@[simp] theorem dThetaFSourceTrace_sourceF (n m n' m' : Int) :
    (I.dThetaFSourceTrace n m n' m').sourceF = I.primeStripAt n m := rfl

@[simp] theorem dThetaFSourceTrace_targetF (n m n' m' : Int) :
    (I.dThetaFSourceTrace n m n' m').targetF = I.primeStripAt n' m' := rfl

@[simp] theorem dThetaFSourceTrace_fLink (n m n' m' : Int) :
    (I.dThetaFSourceTrace n m n' m').fLink =
      I.primeStripLinkAt n m n' m' := rfl

theorem dThetaFSourceTrace_dLink (n m n' m' : Int) :
    (I.dThetaFSourceTrace n m n' m').fLink.toD =
      (I.dThetaFSourceTrace n m n' m').dLink_eq ▸
        (I.dThetaLinkAt n m n' m').dPrimeStripEquiv := by
  rfl

theorem dThetaFSourceTrace_action (n m n' m' : Int) (v : V)
    (g : (I.dThetaFSourceTrace n m n' m').sourceF.toD.Pi v)
    (x : (I.dThetaFSourceTrace n m n' m').sourceF.Mon v) :
    (I.dThetaFSourceTrace n m n' m').fLink.isoMon v
        ((I.dThetaFSourceTrace n m n' m').sourceF.action v g x) =
      (I.dThetaFSourceTrace n m n' m').targetF.action v
        ((I.dThetaFSourceTrace n m n' m').fLink.isoPi v g)
        ((I.dThetaFSourceTrace n m n' m').fLink.isoMon v x) := by
  exact (I.link_action_commutes n m n' m' v g x).symm

theorem dThetaFSourceTrace_degree (n m n' m' : Int) (v : V)
    (x : (I.dThetaFSourceTrace n m n' m').sourceF.Mon v) :
    (I.dThetaFSourceTrace n m n' m').targetF.degree v
        ((I.dThetaFSourceTrace n m n' m').fLink.isoMon v x) =
      (I.dThetaFSourceTrace n m n' m').sourceF.degree v x := by
  exact I.link_degree_commutes n m n' m' v x

theorem dThetaFSourceTrace_geometric (n m n' m' : Int) (v : V)
    (x : (I.dThetaFSourceTrace n m n' m').sourceF.toD.Pi v) :
    x ∈ (I.dThetaFSourceTrace n m n' m').sourceF.toD.geometric v ↔
      (I.dThetaFSourceTrace n m n' m').fLink.isoPi v x ∈
        (I.dThetaFSourceTrace n m n' m').targetF.toD.geometric v := by
  exact I.link_geometric_commutes n m n' m' v x

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def theorem311SourceVerticalDThetaProjection : Obligation :=
  { id := "IUT-III.theorem-3.11-source-vertical-d-theta-projection"
    source :=
      "IUT III, Theorem 3.11 opening paragraph and (i); Theorem 1.5(i); " ++
        "IUT I, Definition 5.2 and Proposition 6.9(ii)"
    status := VerificationStatus.sourceProjection
    note :=
      "For every OriginalInput, constructs the D-Theta theater obtained by " ++
        "forgetting each supplied F-prime-strip to its D-prime-strip while " ++
        "retaining the source arithmetic and finite theta packet. Source links " ++
        "give full D-Theta link equivalences, fixed-n vertical lines, finite " ++
        "stage inclusions, procession laws, lattice squares, and permutation " ++
        "naturality. This is an exact source projection. It does not claim the " ++
        "arithmetic holomorphic, mono-analytic log-shell, or full poly-isomorphism " ++
        "fields of Theorem 1.5(i)."
    dependsOn :=
      [ "IUT-III.theorem-3.11-original-input-boundary",
        "IUT-III.theorem-3.11-d-theta-shadow",
        "IUT-I-II.prime-strip-core",
        "IUT-II.finite-theta-packet" ] }

end LeanFormal.IUT.Audit
