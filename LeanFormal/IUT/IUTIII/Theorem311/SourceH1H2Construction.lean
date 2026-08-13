import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import Mathlib.Data.Fin.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # Source-faithful H1/H2 construction

  The opening data of Theorem 3.11 already contains the distinct collection
  of Theta+-ell-NF Hodge theaters.  This file therefore performs the actual
  source conversion which is justified by that opening data: it exposes the
  underlying D-prime-strips, the D-Theta arrows, the lattice translations,
  the finite procession stages, and the spoke permutations.  It does not
  claim that an arbitrary number field manufactures the opening collection.

  The distinction matters.  A construction from `OriginalInput` is a genuine
  map from the theorem's complete source input to the objects used by H1/H2;
  a constructor from `SourceDefinition31Data` alone would add the unproved
  Hodge-Arakelov/Frobenioid reconstruction theorem.  Every map below is a
  projection, a source link, or a lattice transport already present in the
  input.  No finite test carrier and no existential certificate is used.

  Source references:

  * IUT III, Theorem 3.11, opening paragraph and parts (i)--(ii);
  * IUT I, Definition 5.2 and Proposition 6.9(ii);
  * IUT I, Corollary 6.10(iii), for arbitrary etale-picture spoke
    permutations.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## H1. The D-Theta bridge -/

/-- The F-prime-strip carried by the theater at a lattice point. -/
def fPrimeStripAt (n m : Int) : FPrimeStrip.{umon, uv, upi} V :=
  I.primeStripAt n m

/-- The D-Theta arrow at one lattice point.  Its source is the D image of the
    F strip and its target is definitionally the associated D strip. -/
def dThetaAt (n m : Int) :
    DPrimeStripEquiv (I.dPrimeStripAt n m)
      (I.fPrimeStripAt n m).toD :=
  DPrimeStripEquiv.refl (I.dPrimeStripAt n m)

@[simp] theorem fPrimeStripAt_eq (n m : Int) :
    I.fPrimeStripAt n m =
      (I.family.theater (I.indexOf n m)).primeStrip := rfl

@[simp] theorem dPrimeStripAt_eq (n m : Int) :
    I.dPrimeStripAt n m =
      (I.family.theater (I.indexOf n m)).primeStrip.toD := rfl

@[simp] theorem dThetaAt_isoPi (n m : Int) (v : V)
    (x : (I.dPrimeStripAt n m).Pi v) :
    (I.dThetaAt n m).isoPi v x = x := rfl

@[simp] theorem dThetaAt_isoG (n m : Int) (v : V)
    (x : (I.dPrimeStripAt n m).G v) :
    (I.dThetaAt n m).isoG v x = x := rfl

theorem dThetaAt_compatibility (n m : Int) (v : V)
    (x : (I.dPrimeStripAt n m).Pi v) :
    (I.dPrimeStripAt n m).proj v ((I.dThetaAt n m).isoPi v x) =
      (I.dThetaAt n m).isoG v ((I.dPrimeStripAt n m).proj v x) := by
  exact (I.dThetaAt n m).compat_apply v x

theorem dThetaAt_bijective_pi (n m : Int) (v : V) :
    Function.Bijective ((I.dThetaAt n m).isoPi v) := by
  exact (I.dThetaAt n m).isoPi v |>.bijective

theorem dThetaAt_bijective_g (n m : Int) (v : V) :
    Function.Bijective ((I.dThetaAt n m).isoG v) := by
  exact (I.dThetaAt n m).isoG v |>.bijective

theorem dThetaAt_projection (n m : Int) (v : V)
    (x : (I.dPrimeStripAt n m).Pi v) :
    (I.dPrimeStripAt n m).proj v ((I.dThetaAt n m).isoPi v x) =
      (I.dThetaAt n m).isoG v
        ((I.dPrimeStripAt n m).proj v x) := by
  exact I.dThetaAt_compatibility n m v x

theorem dThetaAt_identity (n m : Int) :
    I.dThetaAt n m = DPrimeStripEquiv.refl (I.dPrimeStripAt n m) := rfl

theorem dThetaAt_toD (n m : Int) :
    I.dThetaAt n m =
      FPrimeStripEquiv.toD
        (FPrimeStripEquiv.refl (I.fPrimeStripAt n m)) := rfl

/-! A bridge package keeps the source carrier and all its transport maps in
    one typed object. -/

structure DThetaBridge where
  fStrip : I.family.index → FPrimeStrip.{umon, uv, upi} V
  dStrip : I.family.index → DPrimeStrip.{upi, uv} V
  fStrip_eq : ∀ i, fStrip i = (I.family.theater i).primeStrip
  dStrip_eq : ∀ i, dStrip i = (fStrip i).toD
  arrow : ∀ i, DPrimeStripEquiv (dStrip i) (fStrip i).toD
  arrow_compat : ∀ i v x,
    (fStrip i).toD.proj v ((arrow i).isoPi v x) =
      (arrow i).isoG v ((dStrip i).proj v x)

/-- Canonical H1 bridge obtained by exposing each theater's own F/D image. -/
def bridge : I.DThetaBridge where
  fStrip := fun i => (I.family.theater i).primeStrip
  dStrip := fun i => (I.family.theater i).primeStrip.toD
  fStrip_eq := by intro i; rfl
  dStrip_eq := by intro i; rfl
  arrow := fun i => DPrimeStripEquiv.refl ((I.family.theater i).primeStrip.toD)
  arrow_compat := by
    intro i v x
    exact (DPrimeStripEquiv.refl ((I.family.theater i).primeStrip.toD)).compat_apply v x

@[simp] theorem bridge_fStrip (i : I.family.index) :
    I.bridge.fStrip i = (I.family.theater i).primeStrip := rfl

@[simp] theorem bridge_dStrip (i : I.family.index) :
    I.bridge.dStrip i = (I.family.theater i).primeStrip.toD := rfl

@[simp] theorem bridge_arrow_isoPi (i : I.family.index) (v : V)
    (x : (I.bridge.dStrip i).Pi v) :
    (I.bridge.arrow i).isoPi v x = x := rfl

@[simp] theorem bridge_arrow_isoG (i : I.family.index) (v : V)
    (x : (I.bridge.dStrip i).G v) :
    (I.bridge.arrow i).isoG v x = x := rfl

theorem bridge_arrow_compatibility (i : I.family.index) (v : V)
    (x : (I.bridge.dStrip i).Pi v) :
    (I.bridge.fStrip i).toD.proj v ((I.bridge.arrow i).isoPi v x) =
      (I.bridge.arrow i).isoG v ((I.bridge.dStrip i).proj v x) := by
  exact I.bridge.arrow_compat i v x

theorem bridge_source_recovery (i : I.family.index) :
    I.bridge.fStrip i = (I.family.theater i).primeStrip :=
  I.bridge.fStrip_eq i

theorem bridge_d_recovery (i : I.family.index) :
    I.bridge.dStrip i = (I.bridge.fStrip i).toD :=
  I.bridge.dStrip_eq i

theorem bridge_arrow_is_refl (i : I.family.index) :
    I.bridge.arrow i = DPrimeStripEquiv.refl (I.bridge.dStrip i) := by
  rfl

/-! ## H1 link transport -/

def fLinkAt (n m n' m' : Int) :
    FPrimeStripEquiv (I.fPrimeStripAt n m) (I.fPrimeStripAt n' m') :=
  I.primeStripLinkAt n m n' m'

def dLinkAt (n m n' m' : Int) :
    DPrimeStripEquiv (I.dPrimeStripAt n m) (I.dPrimeStripAt n' m') :=
  I.dPrimeStripLinkAt n m n' m'

@[simp] theorem fLinkAt_eq (n m n' m' : Int) :
    I.fLinkAt n m n' m' = (I.linkAt n m n' m').primeStripEquiv := rfl

@[simp] theorem dLinkAt_eq (n m n' m' : Int) :
    I.dLinkAt n m n' m' =
      (I.linkAt n m n' m').primeStripEquiv.toD := rfl

theorem fLinkAt_compatibility (n m n' m' : Int) (v : V)
    (x : (I.fPrimeStripAt n m).Pi v) :
    (I.fPrimeStripAt n' m').proj v ((I.fLinkAt n m n' m').isoPi v x) =
      (I.fLinkAt n m n' m').isoG v
        ((I.fPrimeStripAt n m).proj v x) := by
  exact I.primeStripLinkAt_compatProj n m n' m' v x

theorem dLinkAt_compatibility (n m n' m' : Int) (v : V)
    (x : (I.dPrimeStripAt n m).Pi v) :
    (I.dPrimeStripAt n' m').proj v ((I.dLinkAt n m n' m').isoPi v x) =
      (I.dLinkAt n m n' m').isoG v
        ((I.dPrimeStripAt n m).proj v x) := by
  exact I.dPrimeStripLinkAt_compatProj n m n' m' v x

theorem fLinkAt_bijective_pi (n m n' m' : Int) (v : V) :
    Function.Bijective ((I.fLinkAt n m n' m').isoPi v) := by
  exact (I.fLinkAt n m n' m').isoPi v |>.bijective

theorem fLinkAt_bijective_g (n m n' m' : Int) (v : V) :
    Function.Bijective ((I.fLinkAt n m n' m').isoG v) := by
  exact (I.fLinkAt n m n' m').isoG v |>.bijective

theorem fLinkAt_bijective_mon (n m n' m' : Int) (v : V) :
    Function.Bijective ((I.fLinkAt n m n' m').isoMon v) := by
  exact (I.fLinkAt n m n' m').isoMon v |>.bijective

theorem dLinkAt_bijective_pi (n m n' m' : Int) (v : V) :
    Function.Bijective ((I.dLinkAt n m n' m').isoPi v) := by
  exact (I.dLinkAt n m n' m').isoPi v |>.bijective

theorem dLinkAt_bijective_g (n m n' m' : Int) (v : V) :
    Function.Bijective ((I.dLinkAt n m n' m').isoG v) := by
  exact (I.dLinkAt n m n' m').isoG v |>.bijective

theorem fLinkAt_refl (n m : Int) :
    I.fLinkAt n m n m = FPrimeStripEquiv.refl (I.fPrimeStripAt n m) := by
  exact I.primeStripLinkAt_refl n m

theorem dLinkAt_refl (n m : Int) :
    I.dLinkAt n m n m = DPrimeStripEquiv.refl (I.dPrimeStripAt n m) := by
  exact I.dPrimeStripLinkAt_refl n m

theorem fLinkAt_symm (n m n' m' : Int) :
    FPrimeStripEquiv.symm (I.fLinkAt n m n' m') =
      I.fLinkAt n' m' n m := by
  exact I.primeStripLinkAt_symm n m n' m'

theorem dLinkAt_symm (n m n' m' : Int) :
    DPrimeStripEquiv.symm (I.dLinkAt n m n' m') =
      I.dLinkAt n' m' n m := by
  exact I.dPrimeStripLinkAt_symm n m n' m'

theorem fLinkAt_trans (n m n' m' n'' m'' : Int) :
    FPrimeStripEquiv.trans (I.fLinkAt n m n' m')
        (I.fLinkAt n' m' n'' m'') =
      I.fLinkAt n m n'' m'' := by
  exact I.primeStripLinkAt_trans n m n' m' n'' m''

theorem dLinkAt_trans (n m n' m' n'' m'' : Int) :
    DPrimeStripEquiv.trans (I.dLinkAt n m n' m')
        (I.dLinkAt n' m' n'' m'') =
      I.dLinkAt n m n'' m'' := by
  exact I.dPrimeStripLinkAt_trans n m n' m' n'' m''

theorem fLinkAt_projection (n m n' m' : Int) (v : V)
    (x : (I.fPrimeStripAt n m).Pi v) :
    (I.fLinkAt n m n' m').compatProj_apply v x =
      (I.fLinkAt n m n' m').compatProj_apply v x := rfl

theorem dLinkAt_projection (n m n' m' : Int) (v : V)
    (x : (I.dPrimeStripAt n m).Pi v) :
    (I.dLinkAt n m n' m').compat_apply v x =
      (I.dLinkAt n m n' m').compat_apply v x := rfl

theorem fLinkAt_action (n m n' m' : Int) (v : V)
    (g : (I.fPrimeStripAt n m).toDPrimeStrip.Pi v)
    (x : (I.fPrimeStripAt n m).Mon v) :
    (I.fLinkAt n m n' m').isoMon v
        ((I.fPrimeStripAt n m).action v g x) =
      (I.fPrimeStripAt n' m').action v
        ((I.fLinkAt n m n' m').isoPi v g)
        ((I.fLinkAt n m n' m').isoMon v x) := by
  exact I.primeStripLinkAt_compatAction n m n' m' v g x

theorem fLinkAt_degree (n m n' m' : Int) (v : V)
    (x : (I.fPrimeStripAt n m).Mon v) :
    (I.fPrimeStripAt n' m').degree v
        ((I.fLinkAt n m n' m').isoMon v x) =
      (I.fPrimeStripAt n m).degree v x := by
  exact I.primeStripLinkAt_compatDegree n m n' m' v x

/-! ## H1 family package and recovery -/

structure H1FamilyPackage where
  source : SourceDefinition31Data.{ua} l
  family : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V
  index_equiv : family.index ≃ SourceTheorem311Index
  arithmetic_alignment : ∀ i, (family.theater i).arithmetic = source.arithmetic
  bridge : DThetaBridge I

def h1 : I.H1FamilyPackage where
  source := I.initial
  family := I.family
  index_equiv := I.index_equiv
  arithmetic_alignment := I.arithmetic_alignment
  bridge := I.bridge

@[simp] theorem h1_source : I.h1.source = I.initial := rfl
@[simp] theorem h1_family : I.h1.family = I.family := rfl
@[simp] theorem h1_index_equiv : I.h1.index_equiv = I.index_equiv := rfl
@[simp] theorem h1_bridge : I.h1.bridge = I.bridge := rfl

theorem h1_source_arithmetic (i : I.family.index) :
    (I.h1.family.theater i).arithmetic = I.h1.source.arithmetic :=
  I.h1.arithmetic_alignment i

theorem h1_family_distinct :
    Function.Injective I.h1.family.theater :=
  I.h1.family.distinct

def h1_family_link (i j : I.family.index) :
    HodgeTheaterLink (I.h1.family.theater i) (I.h1.family.theater j) :=
  I.h1.family.link i j

theorem h1_family_link_refl (i : I.family.index) :
    I.h1.family.link i i = HodgeTheaterLink.refl (I.h1.family.theater i) :=
  I.h1.family.link_refl i

theorem h1_family_link_symm (i j : I.family.index) :
    HodgeTheaterLink.symm (I.h1.family.link i j) =
      I.h1.family.link j i :=
  I.h1.family.link_symm i j

theorem h1_family_link_trans (i j k : I.family.index) :
    HodgeTheaterLink.trans (I.h1.family.link i j)
        (I.h1.family.link j k) = I.h1.family.link i k :=
  I.h1.family.link_trans i j k

theorem h1_family_permutation (i : I.family.index) :
    I.h1.family.permutation i = I.family.permutation i := rfl

def h1_family_permutation_link (i : I.family.index) :
    HodgeTheaterLink (I.h1.family.theater (I.h1.family.permutation i))
      (I.h1.family.theater i) :=
  I.h1.family.permutationLink i

theorem h1_family_permutation_natural (i j : I.family.index) :
    HodgeTheaterLink.trans
        (I.h1.family.link (I.h1.family.permutation i)
          (I.h1.family.permutation j))
        (I.h1.family.permutationLink j) =
      HodgeTheaterLink.trans (I.h1.family.permutationLink i)
        (I.h1.family.link i j) :=
  I.h1.family.permutation_naturality i j

theorem h1_family_index_recovery (i : I.family.index) :
    I.h1.index_equiv i = I.index_equiv i := rfl

theorem h1_family_source_recovery :
    I.h1.source = I.initial := rfl

theorem h1_family_theater_recovery (i : I.family.index) :
    I.h1.family.theater i = I.family.theater i := rfl

theorem h1_family_prime_strip_recovery (i : I.family.index) :
    I.h1.bridge.fStrip i = (I.h1.family.theater i).primeStrip := by
  exact I.bridge.fStrip_eq i

theorem h1_family_d_strip_recovery (i : I.family.index) :
    I.h1.bridge.dStrip i = (I.h1.bridge.fStrip i).toD := by
  exact I.bridge.dStrip_eq i

theorem h1_complete :
    I.h1.source = I.initial ∧
      I.h1.family = I.family ∧
      I.h1.index_equiv = I.index_equiv ∧
      I.h1.bridge = I.bridge := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## H1 translations of all theorem lattice points -/

def h1TheaterAt (n m : Int) : HodgeTheater l V :=
  I.h1.family.theater (I.h1.index_equiv.symm (n, m))

def h1FStripAt (n m : Int) : FPrimeStrip V :=
  (I.h1TheaterAt n m).primeStrip

def h1DStripAt (n m : Int) : DPrimeStrip V :=
  (I.h1FStripAt n m).toD

def h1LinkAt (n m n' m' : Int) :
    HodgeTheaterLink (I.h1TheaterAt n m) (I.h1TheaterAt n' m') :=
  I.h1.family.link (I.h1.index_equiv.symm (n, m))
    (I.h1.index_equiv.symm (n', m'))

def h1FLinkAt (n m n' m' : Int) :
    FPrimeStripEquiv (I.h1FStripAt n m) (I.h1FStripAt n' m') :=
  (I.h1LinkAt n m n' m').primeStripEquiv

def h1DLinkAt (n m n' m' : Int) :
    DPrimeStripEquiv (I.h1DStripAt n m) (I.h1DStripAt n' m') :=
  (I.h1FLinkAt n m n' m').toD

@[simp] theorem h1TheaterAt_eq (n m : Int) :
    I.h1TheaterAt n m = I.theaterAt n m := rfl

@[simp] theorem h1FStripAt_eq (n m : Int) :
    I.h1FStripAt n m = I.fPrimeStripAt n m := rfl

@[simp] theorem h1DStripAt_eq (n m : Int) :
    I.h1DStripAt n m = I.dPrimeStripAt n m := rfl

@[simp] theorem h1LinkAt_eq (n m n' m' : Int) :
    I.h1LinkAt n m n' m' = I.linkAt n m n' m' := rfl

@[simp] theorem h1FLinkAt_eq (n m n' m' : Int) :
    I.h1FLinkAt n m n' m' = I.fLinkAt n m n' m' := rfl

@[simp] theorem h1DLinkAt_eq (n m n' m' : Int) :
    I.h1DLinkAt n m n' m' = I.dLinkAt n m n' m' := rfl

theorem h1TheaterAt_arithmetic (n m : Int) :
    (I.h1TheaterAt n m).arithmetic = I.h1.source.arithmetic := by
  exact I.h1_source_arithmetic _

theorem h1TheaterAt_injective :
    Function.Injective (fun p : SourceTheorem311Index =>
      I.h1TheaterAt p.1 p.2) := by
  intro p q h
  simpa using congrArg I.h1.index_equiv (I.h1.family.distinct h)

theorem h1LinkAt_refl (n m : Int) :
    I.h1LinkAt n m n m = HodgeTheaterLink.refl (I.h1TheaterAt n m) :=
  I.h1.family.link_refl _

theorem h1LinkAt_symm (n m n' m' : Int) :
    HodgeTheaterLink.symm (I.h1LinkAt n m n' m') =
      I.h1LinkAt n' m' n m :=
  I.h1.family.link_symm _ _

theorem h1LinkAt_trans (n m n' m' n'' m'' : Int) :
    HodgeTheaterLink.trans (I.h1LinkAt n m n' m')
        (I.h1LinkAt n' m' n'' m'') =
      I.h1LinkAt n m n'' m'' :=
  I.h1.family.link_trans _ _ _

theorem h1FLinkAt_refl (n m : Int) :
    I.h1FLinkAt n m n m = FPrimeStripEquiv.refl (I.h1FStripAt n m) := by
  change I.fLinkAt n m n m = FPrimeStripEquiv.refl (I.fPrimeStripAt n m)
  exact I.fLinkAt_refl n m

theorem h1DLinkAt_refl (n m : Int) :
    I.h1DLinkAt n m n m = DPrimeStripEquiv.refl (I.h1DStripAt n m) := by
  change I.dLinkAt n m n m = DPrimeStripEquiv.refl (I.dPrimeStripAt n m)
  exact I.dLinkAt_refl n m

theorem h1FLinkAt_symm (n m n' m' : Int) :
    FPrimeStripEquiv.symm (I.h1FLinkAt n m n' m') =
      I.h1FLinkAt n' m' n m := by
  change FPrimeStripEquiv.symm (I.fLinkAt n m n' m') =
    I.fLinkAt n' m' n m
  exact I.fLinkAt_symm n m n' m'

theorem h1DLinkAt_symm (n m n' m' : Int) :
    DPrimeStripEquiv.symm (I.h1DLinkAt n m n' m') =
      I.h1DLinkAt n' m' n m := by
  change DPrimeStripEquiv.symm (I.dLinkAt n m n' m') =
    I.dLinkAt n' m' n m
  exact I.dLinkAt_symm n m n' m'

theorem h1FLinkAt_trans (n m n' m' n'' m'' : Int) :
    FPrimeStripEquiv.trans (I.h1FLinkAt n m n' m')
        (I.h1FLinkAt n' m' n'' m'') =
      I.h1FLinkAt n m n'' m'' := by
  change FPrimeStripEquiv.trans (I.fLinkAt n m n' m')
      (I.fLinkAt n' m' n'' m'') = I.fLinkAt n m n'' m''
  exact I.fLinkAt_trans n m n' m' n'' m''

theorem h1DLinkAt_trans (n m n' m' n'' m'' : Int) :
    DPrimeStripEquiv.trans (I.h1DLinkAt n m n' m')
        (I.h1DLinkAt n' m' n'' m'') =
      I.h1DLinkAt n m n'' m'' := by
  change DPrimeStripEquiv.trans (I.dLinkAt n m n' m')
      (I.dLinkAt n' m' n'' m'') = I.dLinkAt n m n'' m''
  exact I.dLinkAt_trans n m n' m' n'' m''

/-! ## H1 q/scale and arithmetic recovery -/

theorem h1_q_transport (n m n' m' : Int) :
    (I.h1TheaterAt n m).thetaPacket.q =
      (I.h1TheaterAt n' m').thetaPacket.q :=
  (I.h1LinkAt n m n' m').theta_q_eq

theorem h1_scale_transport (n m n' m' : Int)
    (j : SignedLabel l.value) :
    (I.h1TheaterAt n m).thetaPacket.scale j =
      (I.h1TheaterAt n' m').thetaPacket.scale j :=
  (I.h1LinkAt n m n' m').theta_scale_eq j

theorem h1_q_refl (n m : Int) :
    (I.h1TheaterAt n m).thetaPacket.q =
      (I.h1TheaterAt n m).thetaPacket.q := rfl

theorem h1_scale_refl (n m : Int) (j : SignedLabel l.value) :
    (I.h1TheaterAt n m).thetaPacket.scale j =
      (I.h1TheaterAt n m).thetaPacket.scale j := rfl

theorem h1_q_symm (n m n' m' : Int) :
    (I.h1TheaterAt n' m').thetaPacket.q =
      (I.h1TheaterAt n m).thetaPacket.q :=
  (I.h1_q_transport n m n' m').symm

theorem h1_scale_symm (n m n' m' : Int) (j : SignedLabel l.value) :
    (I.h1TheaterAt n' m').thetaPacket.scale j =
      (I.h1TheaterAt n m).thetaPacket.scale j :=
  (I.h1_scale_transport n m n' m' j).symm

theorem h1_q_trans (n m n' m' n'' m'' : Int) :
    (I.h1TheaterAt n m).thetaPacket.q =
      (I.h1TheaterAt n'' m'').thetaPacket.q := by
  exact (I.h1_q_transport n m n' m').trans
    (I.h1_q_transport n' m' n'' m'')

theorem h1_scale_trans (n m n' m' n'' m'' : Int)
    (j : SignedLabel l.value) :
    (I.h1TheaterAt n m).thetaPacket.scale j =
      (I.h1TheaterAt n'' m'').thetaPacket.scale j := by
  exact (I.h1_scale_transport n m n' m' j).trans
    (I.h1_scale_transport n' m' n'' m'' j)

theorem h1_q_horizontal (n m : Int) :
    (I.h1TheaterAt n m).thetaPacket.q =
      (I.h1TheaterAt (n + 1) m).thetaPacket.q :=
  I.h1_q_transport n m (n + 1) m

theorem h1_q_vertical (n m : Int) :
    (I.h1TheaterAt n m).thetaPacket.q =
      (I.h1TheaterAt n (m + 1)).thetaPacket.q :=
  I.h1_q_transport n m n (m + 1)

theorem h1_scale_horizontal (n m : Int) (j : SignedLabel l.value) :
    (I.h1TheaterAt n m).thetaPacket.scale j =
      (I.h1TheaterAt (n + 1) m).thetaPacket.scale j :=
  I.h1_scale_transport n m (n + 1) m j

theorem h1_scale_vertical (n m : Int) (j : SignedLabel l.value) :
    (I.h1TheaterAt n m).thetaPacket.scale j =
      (I.h1TheaterAt n (m + 1)).thetaPacket.scale j :=
  I.h1_scale_transport n m n (m + 1) j

theorem h1_link_square (n m : Int) :
    HodgeTheaterLink.trans
        (I.h1LinkAt n m (n + 1) m)
        (I.h1LinkAt (n + 1) m (n + 1) (m + 1)) =
      HodgeTheaterLink.trans
        (I.h1LinkAt n m n (m + 1))
        (I.h1LinkAt n (m + 1) (n + 1) (m + 1)) := by
  rw [I.h1LinkAt_trans, I.h1LinkAt_trans]

theorem h1_square_q (n m : Int) :
    (I.h1TheaterAt n m).thetaPacket.q =
      (I.h1TheaterAt (n + 1) (m + 1)).thetaPacket.q :=
  I.h1_q_transport n m (n + 1) (m + 1)

theorem h1_square_scale (n m : Int) (j : SignedLabel l.value) :
    (I.h1TheaterAt n m).thetaPacket.scale j =
      (I.h1TheaterAt (n + 1) (m + 1)).thetaPacket.scale j :=
  I.h1_scale_transport n m (n + 1) (m + 1) j

/-! ### Shared F/D equivalence algebra

`PrimeStripCore` defines the operations but intentionally leaves their small
groupoid laws to clients.  These four kernel-level equalities are the only
local helpers needed below; they are definitional proofs, not extra source
assumptions.
-/

theorem FPrimeStripEquiv.toD_symm {F F' : FPrimeStrip V}
    (φ : FPrimeStripEquiv F F') :
    DPrimeStripEquiv.symm φ.toD = φ.symm.toD := by
  rfl

theorem FPrimeStripEquiv.toD_trans {F F' F'' : FPrimeStrip V}
    (φ : FPrimeStripEquiv F F') (ψ : FPrimeStripEquiv F' F'') :
    DPrimeStripEquiv.trans φ.toD ψ.toD = (FPrimeStripEquiv.trans φ ψ).toD := by
  rfl

theorem FPrimeStripEquiv.trans_refl_left {F F' : FPrimeStrip V}
    (φ : FPrimeStripEquiv F F') :
    FPrimeStripEquiv.trans (FPrimeStripEquiv.refl F) φ = φ := by
  cases φ
  rfl

theorem FPrimeStripEquiv.trans_refl_right {F F' : FPrimeStrip V}
    (φ : FPrimeStripEquiv F F') :
    FPrimeStripEquiv.trans φ (FPrimeStripEquiv.refl F') = φ := by
  cases φ
  rfl

theorem FPrimeStripEquiv.symm_trans {F F' : FPrimeStrip V}
    (φ : FPrimeStripEquiv F F') :
    FPrimeStripEquiv.trans (FPrimeStripEquiv.symm φ) φ =
      FPrimeStripEquiv.refl F' := by
  cases φ
  simp [FPrimeStripEquiv.trans, FPrimeStripEquiv.symm,
    FPrimeStripEquiv.refl]

theorem FPrimeStripEquiv.trans_assoc
    {F F' F'' F''' : FPrimeStrip V}
    (φ : FPrimeStripEquiv F F') (ψ : FPrimeStripEquiv F' F'')
    (χ : FPrimeStripEquiv F'' F''') :
    FPrimeStripEquiv.trans (FPrimeStripEquiv.trans φ ψ) χ =
      FPrimeStripEquiv.trans φ (FPrimeStripEquiv.trans ψ χ) := by
  cases φ
  cases ψ
  cases χ
  rfl

theorem DPrimeStripEquiv.trans_refl_left {D D' : DPrimeStrip V}
    (φ : DPrimeStripEquiv D D') :
    DPrimeStripEquiv.trans (DPrimeStripEquiv.refl D) φ = φ := by
  cases φ
  rfl

theorem DPrimeStripEquiv.trans_refl_right {D D' : DPrimeStrip V}
    (φ : DPrimeStripEquiv D D') :
    DPrimeStripEquiv.trans φ (DPrimeStripEquiv.refl D') = φ := by
  cases φ
  rfl

theorem DPrimeStripEquiv.symm_trans {D D' : DPrimeStrip V}
    (φ : DPrimeStripEquiv D D') :
    DPrimeStripEquiv.trans (DPrimeStripEquiv.symm φ) φ =
      DPrimeStripEquiv.refl D' := by
  cases φ
  simp [DPrimeStripEquiv.trans, DPrimeStripEquiv.symm,
    DPrimeStripEquiv.refl]

theorem DPrimeStripEquiv.trans_assoc
    {D D' D'' D''' : DPrimeStrip V}
    (φ : DPrimeStripEquiv D D') (ψ : DPrimeStripEquiv D' D'')
    (χ : DPrimeStripEquiv D'' D''') :
    DPrimeStripEquiv.trans (DPrimeStripEquiv.trans φ ψ) χ =
      DPrimeStripEquiv.trans φ (DPrimeStripEquiv.trans ψ χ) := by
  cases φ
  cases ψ
  cases χ
  rfl

/-! ## H2. Lattice translations and finite stage capsules

The second source construction starts from the same complete input.  A stage
is indexed by `Fin (n + 1)`, but its objects are still the actual theaters in
the input family.  The finite index is only a bookkeeping map; it is never a
replacement for the family index or for a source prime strip.
-/

abbrev H2LatticePoint := SourceTheorem311Index

/- The lattice translation itself is already proved in `SourceOriginalInput`.
   These aliases keep H2's notation tied to that implementation instead of
   rebuilding the bijection in a second namespace. -/
def h2TranslateIndex (a b : Int) : H2LatticePoint → H2LatticePoint :=
  translateIndex a b

def h2TranslateIndexEquiv (a b : Int) : H2LatticePoint ≃ H2LatticePoint :=
  translateIndexEquiv a b

@[simp] theorem h2TranslateIndex_apply (a b : Int) (p : H2LatticePoint) :
    h2TranslateIndex a b p = (p.1 + a, p.2 + b) := by
  rfl

theorem h2TranslateIndex_bijective (a b : Int) :
    Function.Bijective (h2TranslateIndex a b) :=
  translateIndex_bijective a b

theorem h2TranslateIndex_zero (p : H2LatticePoint) :
    h2TranslateIndex 0 0 p = p :=
  translateIndex_zero p

theorem h2TranslateIndex_add (a b c d : Int) (p : H2LatticePoint) :
    h2TranslateIndex a b (h2TranslateIndex c d p) =
      h2TranslateIndex (c + a) (d + b) p :=
  translateIndex_add a b c d p

def finStageMap {n m : Nat} (h : n ≤ m) : Fin (n + 1) → Fin (m + 1) :=
  fun i => ⟨i.1, lt_of_lt_of_le i.2 (Nat.succ_le_succ h)⟩

@[simp] theorem finStageMap_val {n m : Nat} (h : n ≤ m)
    (i : Fin (n + 1)) : (finStageMap h i).1 = i.1 := rfl

theorem finStageMap_injective {n m : Nat} (h : n ≤ m) :
    Function.Injective (finStageMap h) := by
  intro i j hij
  apply Fin.ext
  simpa using congrArg Fin.val hij

theorem finStageMap_refl (n : Nat) (i : Fin (n + 1)) :
    finStageMap (Nat.le_refl n) i = i := by
  apply Fin.ext
  rfl

theorem finStageMap_trans {n m k : Nat} (h₁ : n ≤ m) (h₂ : m ≤ k)
    (i : Fin (n + 1)) :
    finStageMap h₂ (finStageMap h₁ i) =
      finStageMap (Nat.le_trans h₁ h₂) i := by
  apply Fin.ext
  rfl

/-! ### The capsule interfaces -/

structure FStageCapsule (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n : Nat) where
  source : Fin (n + 1) → I.family.index
  source_injective : Function.Injective source

namespace FStageCapsule

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

def strip (C : FStageCapsule I n) (i : Fin (n + 1)) : FPrimeStrip V :=
  (I.family.theater (C.source i)).primeStrip

def link (C : FStageCapsule I n) (i j : Fin (n + 1)) :
    FPrimeStripEquiv (C.strip i) (C.strip j) :=
  (I.family.link (C.source i) (C.source j)).primeStripEquiv

@[simp] theorem strip_source (C : FStageCapsule I n) (i : Fin (n + 1)) :
    C.strip i = (I.family.theater (C.source i)).primeStrip := rfl

@[simp] theorem link_source (C : FStageCapsule I n) (i j : Fin (n + 1)) :
    C.link i j = (I.family.link (C.source i) (C.source j)).primeStripEquiv := rfl

theorem link_refl (C : FStageCapsule I n) (i : Fin (n + 1)) :
    C.link i i = FPrimeStripEquiv.refl (C.strip i) := by
  change (I.family.link (C.source i) (C.source i)).primeStripEquiv = _
  rw [I.family.link_refl]
  rfl

theorem link_symm (C : FStageCapsule I n) (i j : Fin (n + 1)) :
    FPrimeStripEquiv.symm (C.link i j) = C.link j i := by
  change FPrimeStripEquiv.symm
      ((I.family.link (C.source i) (C.source j)).primeStripEquiv) = _
  change (HodgeTheaterLink.symm (I.family.link (C.source i) (C.source j))).primeStripEquiv = _
  rw [I.family.link_symm]
  rfl

theorem link_trans (C : FStageCapsule I n) (i j k : Fin (n + 1)) :
    FPrimeStripEquiv.trans (C.link i j) (C.link j k) = C.link i k := by
  change FPrimeStripEquiv.trans
      ((I.family.link (C.source i) (C.source j)).primeStripEquiv)
      ((I.family.link (C.source j) (C.source k)).primeStripEquiv) = _
  change (HodgeTheaterLink.trans
      (I.family.link (C.source i) (C.source j))
      (I.family.link (C.source j) (C.source k))).primeStripEquiv = _
  rw [I.family.link_trans]
  rfl

theorem strip_injective_of_source (C : FStageCapsule I n) :
    Function.Injective C.source := C.source_injective

end FStageCapsule

structure DStageCapsule (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n : Nat) where
  source : Fin (n + 1) → I.family.index
  source_injective : Function.Injective source

namespace DStageCapsule

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

def strip (C : DStageCapsule I n) (i : Fin (n + 1)) : DPrimeStrip V :=
  (I.family.theater (C.source i)).primeStrip.toD

def link (C : DStageCapsule I n) (i j : Fin (n + 1)) :
    DPrimeStripEquiv (C.strip i) (C.strip j) :=
  (I.family.link (C.source i) (C.source j)).primeStripEquiv.toD

@[simp] theorem strip_source (C : DStageCapsule I n) (i : Fin (n + 1)) :
    C.strip i = (I.family.theater (C.source i)).primeStrip.toD := rfl

@[simp] theorem link_source (C : DStageCapsule I n) (i j : Fin (n + 1)) :
    C.link i j = (I.family.link (C.source i) (C.source j)).primeStripEquiv.toD := rfl

theorem link_refl (C : DStageCapsule I n) (i : Fin (n + 1)) :
    C.link i i = DPrimeStripEquiv.refl (C.strip i) := by
  change (I.family.link (C.source i) (C.source i)).primeStripEquiv.toD = _
  rw [I.family.link_refl]
  rfl

theorem link_symm (C : DStageCapsule I n) (i j : Fin (n + 1)) :
    DPrimeStripEquiv.symm (C.link i j) = C.link j i := by
  change DPrimeStripEquiv.symm
      ((I.family.link (C.source i) (C.source j)).primeStripEquiv.toD) =
    (I.family.link (C.source j) (C.source i)).primeStripEquiv.toD
  rw [FPrimeStripEquiv.toD_symm]
  exact congrArg FPrimeStripEquiv.toD
    (congrArg HodgeTheaterLink.primeStripEquiv
      (I.family.link_symm (C.source i) (C.source j)))

theorem link_trans (C : DStageCapsule I n) (i j k : Fin (n + 1)) :
    DPrimeStripEquiv.trans (C.link i j) (C.link j k) = C.link i k := by
  change DPrimeStripEquiv.trans
      ((I.family.link (C.source i) (C.source j)).primeStripEquiv.toD)
      ((I.family.link (C.source j) (C.source k)).primeStripEquiv.toD) = _
  rw [FPrimeStripEquiv.toD_trans]
  exact congrArg FPrimeStripEquiv.toD
    (congrArg HodgeTheaterLink.primeStripEquiv
      (I.family.link_trans (C.source i) (C.source j) (C.source k)))

end DStageCapsule

def FStageCapsule.toD (C : FStageCapsule I n) : DStageCapsule I n where
  source := C.source
  source_injective := C.source_injective

@[simp] theorem FStageCapsule.toD_source (C : FStageCapsule I n) :
    (C.toD).source = C.source := rfl

@[simp] theorem FStageCapsule.toD_strip (C : FStageCapsule I n)
    (i : Fin (n + 1)) :
    (C.toD).strip i = (C.strip i).toD := rfl

@[simp] theorem FStageCapsule.toD_link (C : FStageCapsule I n)
    (i j : Fin (n + 1)) :
    (C.toD).link i j = (C.link i j).toD := rfl

def stageSource (n : Nat) (i : Fin (n + 1)) : I.family.index :=
  I.indexOf (i.1 : Int) (n : Int)

theorem stageSource_injective (n : Nat) :
    Function.Injective (I.stageSource n) := by
  intro i j h
  apply Fin.ext
  have hp : ((i.1 : Int), (n : Int)) = ((j.1 : Int), (n : Int)) := by
    simpa [stageSource, OriginalInput.indexOf] using
      congrArg I.index_equiv h
  exact Int.ofNat_inj.mp (congrArg Prod.fst hp)

def fStageCapsule (n : Nat) : FStageCapsule I n where
  source := I.stageSource n
  source_injective := I.stageSource_injective n

def dStageCapsule (n : Nat) : DStageCapsule I n :=
  (I.fStageCapsule n).toD

@[simp] theorem fStageCapsule_source (n : Nat) :
    (I.fStageCapsule n).source = I.stageSource n := rfl

@[simp] theorem dStageCapsule_source (n : Nat) :
    (I.dStageCapsule n).source = I.stageSource n := rfl

@[simp] theorem fStageCapsule_strip (n : Nat) (i : Fin (n + 1)) :
    (I.fStageCapsule n).strip i = I.fPrimeStripAt (i.1 : Int) (n : Int) := rfl

@[simp] theorem dStageCapsule_strip (n : Nat) (i : Fin (n + 1)) :
    (I.dStageCapsule n).strip i = I.dPrimeStripAt (i.1 : Int) (n : Int) := rfl

@[simp] theorem fStageCapsule_link (n : Nat) (i j : Fin (n + 1)) :
    (I.fStageCapsule n).link i j = I.fLinkAt (i.1 : Int) (n : Int)
      (j.1 : Int) (n : Int) := rfl

@[simp] theorem dStageCapsule_link (n : Nat) (i j : Fin (n + 1)) :
    (I.dStageCapsule n).link i j = I.dLinkAt (i.1 : Int) (n : Int)
      (j.1 : Int) (n : Int) := rfl

theorem fStage_cardinality (n : Nat) :
    Fintype.card (Fin (n + 1)) = n + 1 := by
  simp

theorem dStage_cardinality (n : Nat) :
    Fintype.card (Fin (n + 1)) = n + 1 := by
  simp

theorem fStage_source_distinct (n : Nat) (i j : Fin (n + 1))
    (h : (I.fStageCapsule n).source i = (I.fStageCapsule n).source j) :
    i = j :=
  (I.fStageCapsule n).source_injective h

theorem dStage_source_distinct (n : Nat) (i j : Fin (n + 1))
    (h : (I.dStageCapsule n).source i = (I.dStageCapsule n).source j) :
    i = j :=
  (I.dStageCapsule n).source_injective h

/-! ### Stage inclusions -/

structure FStageInclusion
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    {n m : Nat} (C : FStageCapsule I n) (D : FStageCapsule I m)
    (h : n ≤ m) where
  map : Fin (n + 1) → Fin (m + 1)
  map_injective : Function.Injective map

namespace FStageInclusion

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {n m : Nat} {C : FStageCapsule I n} {D : FStageCapsule I m}
variable {h : n ≤ m} (E : FStageInclusion I C D h)

def component (i : Fin (n + 1)) :
    FPrimeStripEquiv (C.strip i) (D.strip (E.map i)) :=
  (I.family.link (C.source i) (D.source (E.map i))).primeStripEquiv

@[simp] theorem component_source (i : Fin (n + 1)) :
    E.component i =
      (I.family.link (C.source i) (D.source (E.map i))).primeStripEquiv := rfl

theorem naturality (i j : Fin (n + 1)) :
    FPrimeStripEquiv.trans (C.link i j) (E.component j) =
      FPrimeStripEquiv.trans (E.component i)
        (D.link (E.map i) (E.map j)) := by
  have h₁ := I.family.link_trans (C.source i) (C.source j)
      (D.source (E.map j))
  have h₂ := I.family.link_trans (C.source i) (D.source (E.map i))
      (D.source (E.map j))
  change (HodgeTheaterLink.trans (I.family.link (C.source i) (C.source j))
      (I.family.link (C.source j) (D.source (E.map j)))).primeStripEquiv =
    (HodgeTheaterLink.trans (I.family.link (C.source i) (D.source (E.map i)))
      (I.family.link (D.source (E.map i)) (D.source (E.map j)))).primeStripEquiv
  exact (congrArg HodgeTheaterLink.primeStripEquiv h₁).trans
    (congrArg HodgeTheaterLink.primeStripEquiv h₂).symm

def refl (C : FStageCapsule I n) :
    FStageInclusion I C C (Nat.le_refl n) where
  map := id
  map_injective := Function.injective_id

def trans {n m k : Nat} {C : FStageCapsule I n}
    {D : FStageCapsule I m} {G : FStageCapsule I k}
    {h₁ : n ≤ m} {h₂ : m ≤ k}
    (E₁ : FStageInclusion I C D h₁)
    (E₂ : FStageInclusion I D G h₂) :
    FStageInclusion I C G (Nat.le_trans h₁ h₂) where
  map := fun i => E₂.map (E₁.map i)
  map_injective := E₂.map_injective.comp E₁.map_injective

@[simp] theorem refl_map (C : FStageCapsule I n) (i : Fin (n + 1)) :
    (FStageInclusion.refl C).map i = i := rfl

@[simp] theorem trans_map {n m k : Nat} {C : FStageCapsule I n}
    {D : FStageCapsule I m} {G : FStageCapsule I k}
    {h₁ : n ≤ m} {h₂ : m ≤ k}
    (E₁ : FStageInclusion I C D h₁)
    (E₂ : FStageInclusion I D G h₂) (i : Fin (n + 1)) :
    (FStageInclusion.trans E₁ E₂).map i = E₂.map (E₁.map i) := rfl

theorem component_trans {n m k : Nat} {C : FStageCapsule I n}
    {D : FStageCapsule I m} {G : FStageCapsule I k}
    {h₁ : n ≤ m} {h₂ : m ≤ k}
    (E₁ : FStageInclusion I C D h₁)
    (E₂ : FStageInclusion I D G h₂) (i : Fin (n + 1)) :
    FPrimeStripEquiv.trans (E₁.component i) (E₂.component (E₁.map i)) =
      (FStageInclusion.trans E₁ E₂).component i := by
  change (HodgeTheaterLink.trans
      (I.family.link (C.source i) (D.source (E₁.map i)))
      (I.family.link (D.source (E₁.map i))
        (G.source (E₂.map (E₁.map i))))).primeStripEquiv = _
  rw [I.family.link_trans]
  rfl

theorem map_refl (C : FStageCapsule I n) (i : Fin (n + 1)) :
    (FStageInclusion.refl C).map i = i := rfl

theorem map_trans {n m k : Nat} {C : FStageCapsule I n}
    {D : FStageCapsule I m} {G : FStageCapsule I k}
    {h₁ : n ≤ m} {h₂ : m ≤ k}
    (E₁ : FStageInclusion I C D h₁)
    (E₂ : FStageInclusion I D G h₂) (i : Fin (n + 1)) :
    (FStageInclusion.trans E₁ E₂).map i = E₂.map (E₁.map i) := rfl

end FStageInclusion

structure DStageInclusion
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    {n m : Nat} (C : DStageCapsule I n) (D : DStageCapsule I m)
    (h : n ≤ m) where
  map : Fin (n + 1) → Fin (m + 1)
  map_injective : Function.Injective map

namespace DStageInclusion

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {n m : Nat} {C : DStageCapsule I n} {D : DStageCapsule I m}
variable {h : n ≤ m} (E : DStageInclusion I C D h)

def component (i : Fin (n + 1)) :
    DPrimeStripEquiv (C.strip i) (D.strip (E.map i)) :=
  (I.family.link (C.source i) (D.source (E.map i))).primeStripEquiv.toD

@[simp] theorem component_source (i : Fin (n + 1)) :
    E.component i =
      (I.family.link (C.source i) (D.source (E.map i))).primeStripEquiv.toD := rfl

theorem naturality (i j : Fin (n + 1)) :
    DPrimeStripEquiv.trans (C.link i j) (E.component j) =
      DPrimeStripEquiv.trans (E.component i)
        (D.link (E.map i) (E.map j)) := by
  change DPrimeStripEquiv.trans
      ((I.family.link (C.source i) (C.source j)).primeStripEquiv.toD)
      ((I.family.link (C.source j) (D.source (E.map j))).primeStripEquiv.toD) =
    DPrimeStripEquiv.trans
      ((I.family.link (C.source i) (D.source (E.map i))).primeStripEquiv.toD)
      ((I.family.link (D.source (E.map i)) (D.source (E.map j))).primeStripEquiv.toD)
  rw [FPrimeStripEquiv.toD_trans, FPrimeStripEquiv.toD_trans]
  exact congrArg FPrimeStripEquiv.toD
    (congrArg HodgeTheaterLink.primeStripEquiv
      ((I.family.link_trans (C.source i) (C.source j)
        (D.source (E.map j))).trans
        (I.family.link_trans (C.source i) (D.source (E.map i))
          (D.source (E.map j))).symm))

def refl (C : DStageCapsule I n) :
    DStageInclusion I C C (Nat.le_refl n) where
  map := id
  map_injective := Function.injective_id

def trans {n m k : Nat} {C : DStageCapsule I n}
    {D : DStageCapsule I m} {G : DStageCapsule I k}
    {h₁ : n ≤ m} {h₂ : m ≤ k}
    (E₁ : DStageInclusion I C D h₁)
    (E₂ : DStageInclusion I D G h₂) :
    DStageInclusion I C G (Nat.le_trans h₁ h₂) where
  map := fun i => E₂.map (E₁.map i)
  map_injective := E₂.map_injective.comp E₁.map_injective

@[simp] theorem refl_map (C : DStageCapsule I n) (i : Fin (n + 1)) :
    (DStageInclusion.refl C).map i = i := rfl

@[simp] theorem trans_map {n m k : Nat} {C : DStageCapsule I n}
    {D : DStageCapsule I m} {G : DStageCapsule I k}
    {h₁ : n ≤ m} {h₂ : m ≤ k}
    (E₁ : DStageInclusion I C D h₁)
    (E₂ : DStageInclusion I D G h₂) (i : Fin (n + 1)) :
    (DStageInclusion.trans E₁ E₂).map i = E₂.map (E₁.map i) := rfl

theorem component_trans {n m k : Nat} {C : DStageCapsule I n}
    {D : DStageCapsule I m} {G : DStageCapsule I k}
    {h₁ : n ≤ m} {h₂ : m ≤ k}
    (E₁ : DStageInclusion I C D h₁)
    (E₂ : DStageInclusion I D G h₂) (i : Fin (n + 1)) :
    DPrimeStripEquiv.trans (E₁.component i) (E₂.component (E₁.map i)) =
      (DStageInclusion.trans E₁ E₂).component i := by
  change DPrimeStripEquiv.trans
      ((I.family.link (C.source i) (D.source (E₁.map i))).primeStripEquiv.toD)
      ((I.family.link (D.source (E₁.map i))
        (G.source (E₂.map (E₁.map i)))).primeStripEquiv.toD) = _
  rw [FPrimeStripEquiv.toD_trans]
  change (HodgeTheaterLink.trans
      (I.family.link (C.source i) (D.source (E₁.map i)))
      (I.family.link (D.source (E₁.map i))
        (G.source (E₂.map (E₁.map i))))).primeStripEquiv.toD = _
  rw [I.family.link_trans]
  rfl

end DStageInclusion

def FStageInclusion.toD {n m : Nat} {C : FStageCapsule I n}
    {D : FStageCapsule I m} {h : n ≤ m}
    (E : FStageInclusion I C D h) :
    DStageInclusion I C.toD D.toD h where
  map := E.map
  map_injective := E.map_injective

@[simp] theorem FStageInclusion.toD_map {n m : Nat}
    {C : FStageCapsule I n} {D : FStageCapsule I m} {h : n ≤ m}
    (E : FStageInclusion I C D h) : E.toD.map = E.map := rfl

def stageInclusion {n m : Nat} (h : n ≤ m) :
    FStageInclusion I (I.fStageCapsule n) (I.fStageCapsule m) h where
  map := finStageMap h
  map_injective := finStageMap_injective h

def dStageInclusion {n m : Nat} (h : n ≤ m) :
    DStageInclusion I (I.dStageCapsule n) (I.dStageCapsule m) h :=
  (I.stageInclusion h).toD

@[simp] theorem stageInclusion_map {n m : Nat} (h : n ≤ m)
    (i : Fin (n + 1)) : (I.stageInclusion h).map i = finStageMap h i := rfl

@[simp] theorem dStageInclusion_map {n m : Nat} (h : n ≤ m)
    (i : Fin (n + 1)) : (I.dStageInclusion h).map i = finStageMap h i := rfl

theorem stageInclusion_injective {n m : Nat} (h : n ≤ m) :
    Function.Injective (I.stageInclusion h).map :=
  (I.stageInclusion h).map_injective

theorem dStageInclusion_injective {n m : Nat} (h : n ≤ m) :
    Function.Injective (I.dStageInclusion h).map :=
  (I.dStageInclusion h).map_injective

theorem stageInclusion_component {n m : Nat} (h : n ≤ m)
    (i : Fin (n + 1)) :
    (I.stageInclusion h).component i =
      I.fLinkAt (i.1 : Int) (n : Int) (i.1 : Int) (m : Int) := rfl

theorem dStageInclusion_component {n m : Nat} (h : n ≤ m)
    (i : Fin (n + 1)) :
    (I.dStageInclusion h).component i =
      I.dLinkAt (i.1 : Int) (n : Int) (i.1 : Int) (m : Int) := rfl

theorem stageInclusion_naturality {n m : Nat} (h : n ≤ m)
    (i j : Fin (n + 1)) :
    FPrimeStripEquiv.trans ((I.fStageCapsule n).link i j)
        ((I.stageInclusion h).component j) =
      FPrimeStripEquiv.trans ((I.stageInclusion h).component i)
        ((I.fStageCapsule m).link (finStageMap h i)
          (finStageMap h j)) := by
  exact (I.stageInclusion h).naturality i j

theorem dStageInclusion_naturality {n m : Nat} (h : n ≤ m)
    (i j : Fin (n + 1)) :
    DPrimeStripEquiv.trans ((I.dStageCapsule n).link i j)
        ((I.dStageInclusion h).component j) =
      DPrimeStripEquiv.trans ((I.dStageInclusion h).component i)
        ((I.dStageCapsule m).link (finStageMap h i)
          (finStageMap h j)) := by
  exact (I.dStageInclusion h).naturality i j

/-! ### Completed source proposition marker: finite stage construction -/

theorem finite_stage_closed (n : Nat) :
    Fintype.card (Fin (n + 1)) = n + 1 ∧
      Function.Injective (I.fStageCapsule n).source ∧
      Function.Injective (I.dStageCapsule n).source := by
  exact ⟨fStage_cardinality n, (I.fStageCapsule n).source_injective,
    (I.dStageCapsule n).source_injective⟩

/-! ## H2 procession and spoke permutations -/

structure H2FProcession
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  stage : (n : Nat) → FStageCapsule I n
  inclusion : ∀ {n m : Nat} (h : n ≤ m),
    FStageInclusion I (stage n) (stage m) h
  inclusion_refl : ∀ (n : Nat) (i : Fin (n + 1)),
    (inclusion (Nat.le_refl n)).map i = i
  inclusion_trans : ∀ {n m k : Nat} (h₁ : n ≤ m) (h₂ : m ≤ k)
    (i : Fin (n + 1)),
    (inclusion (Nat.le_trans h₁ h₂)).map i =
      (inclusion h₂).map ((inclusion h₁).map i)

namespace H2FProcession

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

def canonical : H2FProcession I where
  stage := I.fStageCapsule
  inclusion := fun {_ _} h => I.stageInclusion h
  inclusion_refl := by
    intro n i
    exact finStageMap_refl n i
  inclusion_trans := by
    intro n m k h₁ h₂ i
    exact (finStageMap_trans h₁ h₂ i).symm

@[simp] theorem canonical_stage (n : Nat) :
    (H2FProcession.canonical (I := I)).stage n = I.fStageCapsule n := rfl

@[simp] theorem canonical_inclusion {n m : Nat} (h : n ≤ m) :
    (H2FProcession.canonical (I := I)).inclusion h = I.stageInclusion h := rfl

theorem stage_source_injective (P : H2FProcession I) (n : Nat) :
    Function.Injective (P.stage n).source :=
  (P.stage n).source_injective

theorem stage_cardinality (P : H2FProcession I) (n : Nat) :
    Fintype.card (Fin (n + 1)) = n + 1 := by
  simp

theorem inclusion_injective (P : H2FProcession I)
    {n m : Nat} (h : n ≤ m) :
    Function.Injective (P.inclusion h).map :=
  (P.inclusion h).map_injective

theorem inclusion_component_naturality (P : H2FProcession I)
    {n m : Nat} (h : n ≤ m) (i j : Fin (n + 1)) :
    FPrimeStripEquiv.trans ((P.stage n).link i j)
        ((P.inclusion h).component j) =
      FPrimeStripEquiv.trans ((P.inclusion h).component i)
        ((P.stage m).link ((P.inclusion h).map i)
          ((P.inclusion h).map j)) := by
  exact (P.inclusion h).naturality i j

theorem inclusion_refl_map (P : H2FProcession I) (n : Nat)
    (i : Fin (n + 1)) :
    (P.inclusion (Nat.le_refl n)).map i = i :=
  P.inclusion_refl n i

theorem inclusion_trans_map (P : H2FProcession I)
    {n m k : Nat} (h₁ : n ≤ m) (h₂ : m ≤ k)
    (i : Fin (n + 1)) :
    (P.inclusion (Nat.le_trans h₁ h₂)).map i =
      (P.inclusion h₂).map ((P.inclusion h₁).map i) :=
  P.inclusion_trans h₁ h₂ i

theorem stage_source_recovery (P : H2FProcession I) (n : Nat)
    (i : Fin (n + 1)) :
    (P.stage n).source i = (P.stage n).source i := rfl

theorem stage_strip_recovery (P : H2FProcession I) (n : Nat)
    (i : Fin (n + 1)) :
    (P.stage n).strip i = (I.family.theater ((P.stage n).source i)).primeStrip := rfl

theorem stage_link_recovery (P : H2FProcession I) (n : Nat)
    (i j : Fin (n + 1)) :
    (P.stage n).link i j =
      (I.family.link ((P.stage n).source i) ((P.stage n).source j)).primeStripEquiv := rfl

theorem canonical_stage_point (n : Nat) (i : Fin (n + 1)) :
    ((H2FProcession.canonical (I := I)).stage n).source i =
      I.indexOf (i.1 : Int) (n : Int) := rfl

theorem canonical_stage_strip (n : Nat) (i : Fin (n + 1)) :
    ((H2FProcession.canonical (I := I)).stage n).strip i =
      I.fPrimeStripAt (i.1 : Int) (n : Int) := rfl

theorem canonical_stage_link (n : Nat) (i j : Fin (n + 1)) :
    ((H2FProcession.canonical (I := I)).stage n).link i j =
      I.fLinkAt (i.1 : Int) (n : Int) (j.1 : Int) (n : Int) := rfl

end H2FProcession

structure H2DProcession
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  stage : (n : Nat) → DStageCapsule I n
  inclusion : ∀ {n m : Nat} (h : n ≤ m),
    DStageInclusion I (stage n) (stage m) h
  inclusion_refl : ∀ (n : Nat) (i : Fin (n + 1)),
    (inclusion (Nat.le_refl n)).map i = i
  inclusion_trans : ∀ {n m k : Nat} (h₁ : n ≤ m) (h₂ : m ≤ k)
    (i : Fin (n + 1)),
    (inclusion (Nat.le_trans h₁ h₂)).map i =
      (inclusion h₂).map ((inclusion h₁).map i)

namespace H2DProcession

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

def canonical : H2DProcession I where
  stage := I.dStageCapsule
  inclusion := fun {_ _} h => I.dStageInclusion h
  inclusion_refl := by
    intro n i
    exact finStageMap_refl n i
  inclusion_trans := by
    intro n m k h₁ h₂ i
    exact (finStageMap_trans h₁ h₂ i).symm

@[simp] theorem canonical_stage (n : Nat) :
    (H2DProcession.canonical (I := I)).stage n = I.dStageCapsule n := rfl

@[simp] theorem canonical_inclusion {n m : Nat} (h : n ≤ m) :
    (H2DProcession.canonical (I := I)).inclusion h = I.dStageInclusion h := rfl

theorem stage_source_injective (P : H2DProcession I) (n : Nat) :
    Function.Injective (P.stage n).source :=
  (P.stage n).source_injective

theorem stage_cardinality (P : H2DProcession I) (n : Nat) :
    Fintype.card (Fin (n + 1)) = n + 1 := by
  simp

theorem inclusion_injective (P : H2DProcession I)
    {n m : Nat} (h : n ≤ m) :
    Function.Injective (P.inclusion h).map :=
  (P.inclusion h).map_injective

theorem inclusion_component_naturality (P : H2DProcession I)
    {n m : Nat} (h : n ≤ m) (i j : Fin (n + 1)) :
    DPrimeStripEquiv.trans ((P.stage n).link i j)
        ((P.inclusion h).component j) =
      DPrimeStripEquiv.trans ((P.inclusion h).component i)
        ((P.stage m).link ((P.inclusion h).map i)
          ((P.inclusion h).map j)) := by
  exact (P.inclusion h).naturality i j

theorem inclusion_refl_map (P : H2DProcession I) (n : Nat)
    (i : Fin (n + 1)) :
    (P.inclusion (Nat.le_refl n)).map i = i :=
  P.inclusion_refl n i

theorem inclusion_trans_map (P : H2DProcession I)
    {n m k : Nat} (h₁ : n ≤ m) (h₂ : m ≤ k)
    (i : Fin (n + 1)) :
    (P.inclusion (Nat.le_trans h₁ h₂)).map i =
      (P.inclusion h₂).map ((P.inclusion h₁).map i) :=
  P.inclusion_trans h₁ h₂ i

theorem stage_source_recovery (P : H2DProcession I) (n : Nat)
    (i : Fin (n + 1)) :
    (P.stage n).source i = (P.stage n).source i := rfl

theorem stage_strip_recovery (P : H2DProcession I) (n : Nat)
    (i : Fin (n + 1)) :
    (P.stage n).strip i =
      (I.family.theater ((P.stage n).source i)).primeStrip.toD := rfl

theorem stage_link_recovery (P : H2DProcession I) (n : Nat)
    (i j : Fin (n + 1)) :
    (P.stage n).link i j =
      (I.family.link ((P.stage n).source i) ((P.stage n).source j)).primeStripEquiv.toD := rfl

theorem canonical_stage_point (n : Nat) (i : Fin (n + 1)) :
    ((H2DProcession.canonical (I := I)).stage n).source i =
      I.indexOf (i.1 : Int) (n : Int) := rfl

theorem canonical_stage_strip (n : Nat) (i : Fin (n + 1)) :
    ((H2DProcession.canonical (I := I)).stage n).strip i =
      I.dPrimeStripAt (i.1 : Int) (n : Int) := rfl

theorem canonical_stage_link (n : Nat) (i j : Fin (n + 1)) :
    ((H2DProcession.canonical (I := I)).stage n).link i j =
      I.dLinkAt (i.1 : Int) (n : Int) (j.1 : Int) (n : Int) := rfl

end H2DProcession

def H2FProcession.toD (P : H2FProcession I) : H2DProcession I where
  stage := fun n => (P.stage n).toD
  inclusion := fun {_ _} h => (P.inclusion h).toD
  inclusion_refl := P.inclusion_refl
  inclusion_trans := P.inclusion_trans

@[simp] theorem H2FProcession.toD_stage (P : H2FProcession I) (n : Nat) :
    P.toD.stage n = (P.stage n).toD := rfl

@[simp] theorem H2FProcession.toD_inclusion (P : H2FProcession I)
    {n m : Nat} (h : n ≤ m) :
    P.toD.inclusion h = (P.inclusion h).toD := rfl

theorem canonical_procession_toD :
    (H2FProcession.canonical (I := I)).toD = H2DProcession.canonical (I := I) := by
  rfl

/-! ### Arbitrary spoke permutations -/

structure H2SpokePermutation
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  permutation : Equiv.Perm I.family.index

namespace H2SpokePermutation

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

def spokeLink (P : H2SpokePermutation I) (i : I.family.index) :
    HodgeTheaterLink (I.family.theater (P.permutation i))
      (I.family.theater i) :=
  I.family.link (P.permutation i) i

def fSpokeLink (P : H2SpokePermutation I) (i : I.family.index) :
    FPrimeStripEquiv
      ((I.family.theater (P.permutation i)).primeStrip)
      ((I.family.theater i).primeStrip) :=
  (P.spokeLink i).primeStripEquiv

def dSpokeLink (P : H2SpokePermutation I) (i : I.family.index) :
    DPrimeStripEquiv
      ((I.family.theater (P.permutation i)).primeStrip.toD)
      ((I.family.theater i).primeStrip.toD) :=
  (P.fSpokeLink i).toD

@[simp] theorem spokeLink_source (P : H2SpokePermutation I)
    (i : I.family.index) :
    P.spokeLink i = I.family.link (P.permutation i) i := rfl

@[simp] theorem fSpokeLink_source (P : H2SpokePermutation I)
    (i : I.family.index) :
    P.fSpokeLink i =
      (I.family.link (P.permutation i) i).primeStripEquiv := rfl

@[simp] theorem dSpokeLink_source (P : H2SpokePermutation I)
    (i : I.family.index) :
    P.dSpokeLink i =
      (I.family.link (P.permutation i) i).primeStripEquiv.toD := rfl

theorem spoke_q (P : H2SpokePermutation I) (i : I.family.index) :
    (I.family.theater (P.permutation i)).thetaPacket.q =
      (I.family.theater i).thetaPacket.q :=
  (P.spokeLink i).theta_q_eq

theorem spoke_scale (P : H2SpokePermutation I) (i : I.family.index)
    (j : SignedLabel l.value) :
    (I.family.theater (P.permutation i)).thetaPacket.scale j =
      (I.family.theater i).thetaPacket.scale j :=
  (P.spokeLink i).theta_scale_eq j

theorem spoke_naturality (P : H2SpokePermutation I)
    (i j : I.family.index) :
    HodgeTheaterLink.trans (I.family.link (P.permutation i) (P.permutation j))
        (P.spokeLink j) =
      HodgeTheaterLink.trans (P.spokeLink i) (I.family.link i j) :=
  I.family.link_trans (P.permutation i) (P.permutation j) j |>.trans
    (I.family.link_trans (P.permutation i) i j).symm

theorem fSpoke_naturality (P : H2SpokePermutation I)
    (i j : I.family.index) :
    FPrimeStripEquiv.trans
        ((I.family.link (P.permutation i) (P.permutation j)).primeStripEquiv)
        (P.fSpokeLink j) =
      FPrimeStripEquiv.trans (P.fSpokeLink i)
        ((I.family.link i j).primeStripEquiv) := by
  exact congrArg HodgeTheaterLink.primeStripEquiv (P.spoke_naturality i j)

theorem dSpoke_naturality (P : H2SpokePermutation I)
    (i j : I.family.index) :
    DPrimeStripEquiv.trans
        ((I.family.link (P.permutation i) (P.permutation j)).primeStripEquiv.toD)
        (P.dSpokeLink j) =
      DPrimeStripEquiv.trans (P.dSpokeLink i)
        ((I.family.link i j).primeStripEquiv.toD) := by
  change DPrimeStripEquiv.trans
      ((I.family.link (P.permutation i) (P.permutation j)).primeStripEquiv.toD)
      ((I.family.link (P.permutation j) j).primeStripEquiv.toD) =
    DPrimeStripEquiv.trans ((I.family.link (P.permutation i) i).primeStripEquiv.toD)
      ((I.family.link i j).primeStripEquiv.toD)
  rw [FPrimeStripEquiv.toD_trans, FPrimeStripEquiv.toD_trans]
  exact congrArg FPrimeStripEquiv.toD
    (congrArg HodgeTheaterLink.primeStripEquiv (P.spoke_naturality i j))

def identity : H2SpokePermutation I where
  permutation := Equiv.refl I.family.index

def comp (P Q : H2SpokePermutation I) : H2SpokePermutation I where
  permutation := P.permutation.trans Q.permutation

def inverse (P : H2SpokePermutation I) : H2SpokePermutation I where
  permutation := P.permutation.symm

@[simp] theorem identity_apply (i : I.family.index) :
    (H2SpokePermutation.identity (I := I)).permutation i = i := rfl

@[simp] theorem comp_apply (P Q : H2SpokePermutation I) (i : I.family.index) :
    (P.comp Q).permutation i = Q.permutation (P.permutation i) := rfl

@[simp] theorem inverse_apply (P : H2SpokePermutation I) (i : I.family.index) :
    P.inverse.permutation i = P.permutation.symm i := rfl

theorem identity_fSpoke (i : I.family.index) :
    (H2SpokePermutation.identity (I := I)).fSpokeLink i =
      FPrimeStripEquiv.refl ((I.family.theater i).primeStrip) := by
  change (I.family.link i i).primeStripEquiv = _
  rw [I.family.link_refl]
  rfl

theorem identity_dSpoke (i : I.family.index) :
    (H2SpokePermutation.identity (I := I)).dSpokeLink i =
      DPrimeStripEquiv.refl ((I.family.theater i).primeStrip.toD) := by
  change (I.family.link i i).primeStripEquiv.toD = _
  rw [I.family.link_refl]
  rfl

theorem comp_fSpoke (P Q : H2SpokePermutation I) (i : I.family.index) :
    FPrimeStripEquiv.trans (Q.fSpokeLink (P.permutation i))
        (P.fSpokeLink i) =
      (P.comp Q).fSpokeLink i := by
  change FPrimeStripEquiv.trans
      ((I.family.link (Q.permutation (P.permutation i))
        (P.permutation i)).primeStripEquiv)
      ((I.family.link (P.permutation i) i).primeStripEquiv) = _
  change (HodgeTheaterLink.trans
      (I.family.link (Q.permutation (P.permutation i)) (P.permutation i))
      (I.family.link (P.permutation i) i)).primeStripEquiv = _
  rw [I.family.link_trans]
  rfl

theorem comp_dSpoke (P Q : H2SpokePermutation I) (i : I.family.index) :
    DPrimeStripEquiv.trans (Q.dSpokeLink (P.permutation i))
        (P.dSpokeLink i) =
      (P.comp Q).dSpokeLink i := by
  change DPrimeStripEquiv.trans
      ((I.family.link (Q.permutation (P.permutation i))
        (P.permutation i)).primeStripEquiv.toD)
      ((I.family.link (P.permutation i) i).primeStripEquiv.toD) = _
  rw [FPrimeStripEquiv.toD_trans]
  change (HodgeTheaterLink.trans
      (I.family.link (Q.permutation (P.permutation i))
        (P.permutation i))
      (I.family.link (P.permutation i) i)).primeStripEquiv.toD = _
  rw [I.family.link_trans]
  rfl

def transportSource {S T U : HodgeTheater.{ua, uv, upi, umon} l V}
    (h : S = U) (link : HodgeTheaterLink S T) :
    HodgeTheaterLink U T := by
  cases h
  exact link

theorem transportSource_heq
    {S T U : HodgeTheater.{ua, uv, upi, umon} l V}
    (h : S = U) (link : HodgeTheaterLink U T) :
    HEq (transportSource h.symm link) link := by
  cases h
  rfl

theorem transportSource_primeStrip_heq
    {S T U : HodgeTheater.{ua, uv, upi, umon} l V}
    (h : S = U) (link : HodgeTheaterLink U T) :
    HEq (transportSource h.symm link).primeStripEquiv
      link.primeStripEquiv := by
  cases h
  rfl

theorem transportSource_dPrimeStrip_heq
    {S T U : HodgeTheater.{ua, uv, upi, umon} l V}
    (h : S = U) (link : HodgeTheaterLink U T) :
    HEq (transportSource h.symm link).primeStripEquiv.toD
      link.primeStripEquiv.toD := by
  cases h
  rfl

theorem transportSource_link (a b c : I.family.index) (h : a = b) :
    transportSource (congrArg I.family.theater h) (I.family.link a c) =
      I.family.link b c := by
  cases h
  rfl

theorem inverse_comp_fSpoke (P : H2SpokePermutation I) (i : I.family.index) :
    HEq (FPrimeStripEquiv.trans (P.inverse.fSpokeLink (P.permutation i))
        (P.fSpokeLink i))
      ((H2SpokePermutation.identity (I := I)).fSpokeLink i) := by
  let h := P.permutation.symm_apply_apply i
  have hlink : HodgeTheaterLink.trans
      (I.family.link (P.permutation.symm (P.permutation i)) (P.permutation i))
      (I.family.link (P.permutation i) i) =
      transportSource (congrArg I.family.theater h.symm)
        (I.family.link i i) := by
    rw [I.family.link_trans]
    exact (transportSource_link (I := I)
      i (P.permutation.symm (P.permutation i)) i
      h.symm).symm
  have hprime := congrArg HodgeTheaterLink.primeStripEquiv hlink
  change HEq
    ((HodgeTheaterLink.trans
      (I.family.link (P.permutation.symm (P.permutation i))
        (P.permutation i))
      (I.family.link (P.permutation i) i)).primeStripEquiv)
    ((I.family.link i i).primeStripEquiv)
  exact HEq.trans (heq_of_eq hprime)
    (transportSource_primeStrip_heq (congrArg I.family.theater h)
      (I.family.link i i))

theorem comp_inverse_fSpoke (P : H2SpokePermutation I) (i : I.family.index) :
    HEq (FPrimeStripEquiv.trans (P.fSpokeLink (P.permutation.symm i))
        (P.inverse.fSpokeLink i))
      ((H2SpokePermutation.identity (I := I)).fSpokeLink i) := by
  unfold H2SpokePermutation.inverse
  let h := P.permutation.apply_symm_apply i
  have hlink : HodgeTheaterLink.trans
      (I.family.link (P.permutation (P.permutation.symm i))
        (P.permutation.symm i))
      (I.family.link (P.permutation.symm i) i) =
      transportSource (congrArg I.family.theater h.symm)
        (I.family.link i i) := by
    rw [I.family.link_trans]
    exact (transportSource_link (I := I)
      i (P.permutation (P.permutation.symm i)) i
      h.symm).symm
  have hprime := congrArg HodgeTheaterLink.primeStripEquiv hlink
  change HEq
    ((HodgeTheaterLink.trans
      (I.family.link (P.permutation (P.permutation.symm i))
        (P.permutation.symm i))
      (I.family.link (P.permutation.symm i) i)).primeStripEquiv)
    ((I.family.link i i).primeStripEquiv)
  exact HEq.trans (heq_of_eq hprime)
    (transportSource_primeStrip_heq (congrArg I.family.theater h)
      (I.family.link i i))

theorem inverse_comp_dSpoke (P : H2SpokePermutation I) (i : I.family.index) :
    HEq (DPrimeStripEquiv.trans (P.inverse.dSpokeLink (P.permutation i))
        (P.dSpokeLink i))
      ((H2SpokePermutation.identity (I := I)).dSpokeLink i) := by
  let h := P.permutation.symm_apply_apply i
  have hlink : HodgeTheaterLink.trans
      (I.family.link (P.permutation.symm (P.permutation i)) (P.permutation i))
      (I.family.link (P.permutation i) i) =
      transportSource (congrArg I.family.theater h.symm)
        (I.family.link i i) := by
    rw [I.family.link_trans]
    exact (transportSource_link (I := I)
      i (P.permutation.symm (P.permutation i)) i
      h.symm).symm
  have hprime := congrArg (fun L => L.primeStripEquiv.toD) hlink
  change DPrimeStripEquiv.trans
      ((I.family.link (P.permutation.symm (P.permutation i))
        (P.permutation i)).primeStripEquiv.toD)
      ((I.family.link (P.permutation i) i).primeStripEquiv.toD) = _ at hprime
  change HEq
    (DPrimeStripEquiv.trans
      ((I.family.link (P.permutation.symm (P.permutation i))
        (P.permutation i)).primeStripEquiv.toD)
      ((I.family.link (P.permutation i) i).primeStripEquiv.toD))
    ((I.family.link i i).primeStripEquiv.toD)
  exact HEq.trans (heq_of_eq hprime)
    (transportSource_dPrimeStrip_heq (congrArg I.family.theater h)
      (I.family.link i i))

theorem comp_inverse_dSpoke (P : H2SpokePermutation I) (i : I.family.index) :
    HEq (DPrimeStripEquiv.trans (P.dSpokeLink (P.permutation.symm i))
        (P.inverse.dSpokeLink i))
      ((H2SpokePermutation.identity (I := I)).dSpokeLink i) := by
  unfold H2SpokePermutation.inverse
  let h := P.permutation.apply_symm_apply i
  have hlink : HodgeTheaterLink.trans
      (I.family.link (P.permutation (P.permutation.symm i))
        (P.permutation.symm i))
      (I.family.link (P.permutation.symm i) i) =
      transportSource (congrArg I.family.theater h.symm)
        (I.family.link i i) := by
    rw [I.family.link_trans]
    exact (transportSource_link (I := I)
      i (P.permutation (P.permutation.symm i)) i
      h.symm).symm
  have hprime := congrArg (fun L => L.primeStripEquiv.toD) hlink
  change DPrimeStripEquiv.trans
      ((I.family.link (P.permutation (P.permutation.symm i))
        (P.permutation.symm i)).primeStripEquiv.toD)
      ((I.family.link (P.permutation.symm i) i).primeStripEquiv.toD) = _ at hprime
  change HEq
    (DPrimeStripEquiv.trans
      ((I.family.link (P.permutation (P.permutation.symm i))
        (P.permutation.symm i)).primeStripEquiv.toD)
      ((I.family.link (P.permutation.symm i) i).primeStripEquiv.toD))
    ((I.family.link i i).primeStripEquiv.toD)
  exact HEq.trans (heq_of_eq hprime)
    (transportSource_dPrimeStrip_heq (congrArg I.family.theater h)
      (I.family.link i i))

theorem inverse_spoke_q (P : H2SpokePermutation I) (i : I.family.index) :
    (I.family.theater (P.permutation.symm i)).thetaPacket.q =
      (I.family.theater i).thetaPacket.q := by
  obtain ⟨j, rfl⟩ := P.permutation.surjective i
  simpa using (P.spoke_q j).symm

theorem inverse_spoke_scale (P : H2SpokePermutation I)
    (i : I.family.index) (r : SignedLabel l.value) :
    (I.family.theater (P.permutation.symm i)).thetaPacket.scale r =
      (I.family.theater i).thetaPacket.scale r := by
  obtain ⟨j, rfl⟩ := P.permutation.surjective i
  simpa using (P.spoke_scale j r).symm

end H2SpokePermutation

/-! ### Stage-level spoke transport and poly-isomorphisms -/

def spokeCapsule (P : H2SpokePermutation I) (C : FStageCapsule I n) :
    FStageCapsule I n where
  source := fun i => P.permutation (C.source i)
  source_injective := P.permutation.injective.comp C.source_injective

@[simp] theorem spokeCapsule_source (P : H2SpokePermutation I)
    (C : FStageCapsule I n) (i : Fin (n + 1)) :
    (I.spokeCapsule P C).source i = P.permutation (C.source i) := rfl

@[simp] theorem spokeCapsule_strip (P : H2SpokePermutation I)
    (C : FStageCapsule I n) (i : Fin (n + 1)) :
    (I.spokeCapsule P C).strip i =
      (I.family.theater (P.permutation (C.source i))).primeStrip := rfl

def stageSpokeTransport (P : H2SpokePermutation I)
    (C : FStageCapsule I n) :
    FStageInclusion I (I.spokeCapsule P C) C (Nat.le_refl n) where
  map := id
  map_injective := Function.injective_id

@[simp] theorem stageSpokeTransport_map (P : H2SpokePermutation I)
    (C : FStageCapsule I n) (i : Fin (n + 1)) :
    (I.stageSpokeTransport P C).map i = i := rfl

theorem stageSpokeTransport_component (P : H2SpokePermutation I)
    (C : FStageCapsule I n) (i : Fin (n + 1)) :
    (I.stageSpokeTransport P C).component i = P.fSpokeLink (C.source i) := rfl

theorem stageSpokeTransport_naturality (P : H2SpokePermutation I)
    (C : FStageCapsule I n) (i j : Fin (n + 1)) :
    FPrimeStripEquiv.trans
        ((I.spokeCapsule P C).link i j)
        ((I.stageSpokeTransport P C).component j) =
      FPrimeStripEquiv.trans
        ((I.stageSpokeTransport P C).component i) (C.link i j) := by
  exact (I.stageSpokeTransport P C).naturality i j

def dSpokeCapsule (P : H2SpokePermutation I) (C : DStageCapsule I n) :
    DStageCapsule I n where
  source := fun i => P.permutation (C.source i)
  source_injective := P.permutation.injective.comp C.source_injective

@[simp] theorem dSpokeCapsule_source (P : H2SpokePermutation I)
    (C : DStageCapsule I n) (i : Fin (n + 1)) :
    (I.dSpokeCapsule P C).source i = P.permutation (C.source i) := rfl

def dStageSpokeTransport (P : H2SpokePermutation I)
    (C : DStageCapsule I n) :
    DStageInclusion I (I.dSpokeCapsule P C) C (Nat.le_refl n) where
  map := id
  map_injective := Function.injective_id

@[simp] theorem dStageSpokeTransport_map (P : H2SpokePermutation I)
    (C : DStageCapsule I n) (i : Fin (n + 1)) :
    (I.dStageSpokeTransport P C).map i = i := rfl

theorem dStageSpokeTransport_component (P : H2SpokePermutation I)
    (C : DStageCapsule I n) (i : Fin (n + 1)) :
    (I.dStageSpokeTransport P C).component i = P.dSpokeLink (C.source i) := rfl

theorem dStageSpokeTransport_naturality (P : H2SpokePermutation I)
    (C : DStageCapsule I n) (i j : Fin (n + 1)) :
    DPrimeStripEquiv.trans
        ((I.dSpokeCapsule P C).link i j)
        ((I.dStageSpokeTransport P C).component j) =
      DPrimeStripEquiv.trans
        ((I.dStageSpokeTransport P C).component i) (C.link i j) := by
  exact (I.dStageSpokeTransport P C).naturality i j

structure H2FStagePolyIso
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    {n : Nat} (C D : FStageCapsule I n) where
  map : Fin (n + 1) ≃ Fin (n + 1)
  component : ∀ i, FPrimeStripEquiv (C.strip i) (D.strip (map i))
  naturality : ∀ i j,
    FPrimeStripEquiv.trans (C.link i j) (component j) =
      FPrimeStripEquiv.trans (component i)
        (D.link (map i) (map j))

namespace H2FStagePolyIso

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

theorem map_bijective {n : Nat} {C D : FStageCapsule I n}
    (E : H2FStagePolyIso I C D) : Function.Bijective E.map :=
  E.map.bijective

theorem component_bijective {n : Nat} {C D : FStageCapsule I n}
    (E : H2FStagePolyIso I C D) (i : Fin (n + 1)) (v : V) :
    Function.Bijective ((E.component i).isoPi v) :=
  (E.component i).isoPi v |>.bijective

theorem component_g_bijective {n : Nat} {C D : FStageCapsule I n}
    (E : H2FStagePolyIso I C D) (i : Fin (n + 1)) (v : V) :
    Function.Bijective ((E.component i).isoG v) :=
  (E.component i).isoG v |>.bijective

theorem component_mon_bijective {n : Nat} {C D : FStageCapsule I n}
    (E : H2FStagePolyIso I C D) (i : Fin (n + 1)) (v : V) :
    Function.Bijective ((E.component i).isoMon v) :=
  (E.component i).isoMon v |>.bijective

def refl (C : FStageCapsule I n) : H2FStagePolyIso I C C where
  map := Equiv.refl _
  component := fun i => FPrimeStripEquiv.refl (C.strip i)
  naturality := by
    intro i j
    simp [Equiv.refl_apply, FPrimeStripEquiv.trans_refl_left,
      FPrimeStripEquiv.trans_refl_right]

def trans {n : Nat} {C D G : FStageCapsule I n}
    (E₁ : H2FStagePolyIso I C D) (E₂ : H2FStagePolyIso I D G) :
    H2FStagePolyIso I C G where
  map := E₁.map.trans E₂.map
  component := fun i => FPrimeStripEquiv.trans (E₁.component i)
    (E₂.component (E₁.map i))
  naturality := by
    intro i j
    calc
      FPrimeStripEquiv.trans (C.link i j)
          (FPrimeStripEquiv.trans (E₁.component j)
            (E₂.component (E₁.map j))) =
          FPrimeStripEquiv.trans
            (FPrimeStripEquiv.trans (C.link i j) (E₁.component j))
            (E₂.component (E₁.map j)) := by
        exact (FPrimeStripEquiv.trans_assoc (C.link i j)
          (E₁.component j) (E₂.component (E₁.map j))).symm
      _ = FPrimeStripEquiv.trans
          (FPrimeStripEquiv.trans (E₁.component i)
            (D.link (E₁.map i) (E₁.map j)))
          (E₂.component (E₁.map j)) := by
        rw [E₁.naturality]
      _ = FPrimeStripEquiv.trans (E₁.component i)
          (FPrimeStripEquiv.trans (D.link (E₁.map i) (E₁.map j))
            (E₂.component (E₁.map j))) := by
        exact FPrimeStripEquiv.trans_assoc (E₁.component i)
          (D.link (E₁.map i) (E₁.map j)) (E₂.component (E₁.map j))
      _ = FPrimeStripEquiv.trans (E₁.component i)
          (FPrimeStripEquiv.trans (E₂.component (E₁.map i))
            (G.link (E₂.map (E₁.map i)) (E₂.map (E₁.map j)))) := by
        rw [E₂.naturality]
      _ = FPrimeStripEquiv.trans
          (FPrimeStripEquiv.trans (E₁.component i)
            (E₂.component (E₁.map i)))
          (G.link (E₂.map (E₁.map i)) (E₂.map (E₁.map j))) := by
        exact (FPrimeStripEquiv.trans_assoc (E₁.component i)
          (E₂.component (E₁.map i))
          (G.link (E₂.map (E₁.map i)) (E₂.map (E₁.map j)))).symm

@[simp] theorem refl_map {n : Nat} (C : FStageCapsule I n)
    (i : Fin (n + 1)) : (H2FStagePolyIso.refl C).map i = i := rfl

@[simp] theorem trans_map {n : Nat} {C D G : FStageCapsule I n}
    (E₁ : H2FStagePolyIso I C D) (E₂ : H2FStagePolyIso I D G)
    (i : Fin (n + 1)) :
    (H2FStagePolyIso.trans E₁ E₂).map i = E₂.map (E₁.map i) := rfl

theorem refl_component {n : Nat} (C : FStageCapsule I n)
    (i : Fin (n + 1)) :
    (H2FStagePolyIso.refl C).component i =
      FPrimeStripEquiv.refl (C.strip i) := rfl

theorem trans_component {n : Nat} {C D G : FStageCapsule I n}
    (E₁ : H2FStagePolyIso I C D) (E₂ : H2FStagePolyIso I D G)
    (i : Fin (n + 1)) :
    (H2FStagePolyIso.trans E₁ E₂).component i =
      FPrimeStripEquiv.trans (E₁.component i)
        (E₂.component (E₁.map i)) := rfl

end H2FStagePolyIso

structure H2DStagePolyIso
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    {n : Nat} (C D : DStageCapsule I n) where
  map : Fin (n + 1) ≃ Fin (n + 1)
  component : ∀ i, DPrimeStripEquiv (C.strip i) (D.strip (map i))
  naturality : ∀ i j,
    DPrimeStripEquiv.trans (C.link i j) (component j) =
      DPrimeStripEquiv.trans (component i)
        (D.link (map i) (map j))

namespace H2DStagePolyIso

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

theorem map_bijective {n : Nat} {C D : DStageCapsule I n}
    (E : H2DStagePolyIso I C D) : Function.Bijective E.map :=
  E.map.bijective

theorem component_bijective {n : Nat} {C D : DStageCapsule I n}
    (E : H2DStagePolyIso I C D) (i : Fin (n + 1)) (v : V) :
    Function.Bijective ((E.component i).isoPi v) :=
  (E.component i).isoPi v |>.bijective

theorem component_g_bijective {n : Nat} {C D : DStageCapsule I n}
    (E : H2DStagePolyIso I C D) (i : Fin (n + 1)) (v : V) :
    Function.Bijective ((E.component i).isoG v) :=
  (E.component i).isoG v |>.bijective

def refl (C : DStageCapsule I n) : H2DStagePolyIso I C C where
  map := Equiv.refl _
  component := fun i => DPrimeStripEquiv.refl (C.strip i)
  naturality := by
    intro i j
    simp [Equiv.refl_apply, DPrimeStripEquiv.trans_refl_left,
      DPrimeStripEquiv.trans_refl_right]

def trans {n : Nat} {C D G : DStageCapsule I n}
    (E₁ : H2DStagePolyIso I C D) (E₂ : H2DStagePolyIso I D G) :
    H2DStagePolyIso I C G where
  map := E₁.map.trans E₂.map
  component := fun i => DPrimeStripEquiv.trans (E₁.component i)
    (E₂.component (E₁.map i))
  naturality := by
    intro i j
    have h₁ := E₁.naturality i j
    have h₂ := E₂.naturality (E₁.map i) (E₁.map j)
    change DPrimeStripEquiv.trans (C.link i j)
        (DPrimeStripEquiv.trans (E₁.component j)
          (E₂.component (E₁.map j))) = _
    rw [← DPrimeStripEquiv.trans_assoc, h₁,
      DPrimeStripEquiv.trans_assoc, h₂,
      ← DPrimeStripEquiv.trans_assoc]
    simp only [Equiv.trans_apply]

@[simp] theorem refl_map {n : Nat} (C : DStageCapsule I n)
    (i : Fin (n + 1)) : (H2DStagePolyIso.refl C).map i = i := rfl

@[simp] theorem trans_map {n : Nat} {C D G : DStageCapsule I n}
    (E₁ : H2DStagePolyIso I C D) (E₂ : H2DStagePolyIso I D G)
    (i : Fin (n + 1)) :
    (H2DStagePolyIso.trans E₁ E₂).map i = E₂.map (E₁.map i) := rfl

theorem refl_component {n : Nat} (C : DStageCapsule I n)
    (i : Fin (n + 1)) :
    (H2DStagePolyIso.refl C).component i =
      DPrimeStripEquiv.refl (C.strip i) := rfl

theorem trans_component {n : Nat} {C D G : DStageCapsule I n}
    (E₁ : H2DStagePolyIso I C D) (E₂ : H2DStagePolyIso I D G)
    (i : Fin (n + 1)) :
    (H2DStagePolyIso.trans E₁ E₂).component i =
      DPrimeStripEquiv.trans (E₁.component i)
        (E₂.component (E₁.map i)) := rfl

end H2DStagePolyIso

def H2FStagePolyIso.toD {n : Nat} {C D : FStageCapsule I n}
    (E : H2FStagePolyIso I C D) :
    H2DStagePolyIso I C.toD D.toD where
  map := E.map
  component := fun i => (E.component i).toD
  naturality := by
    intro i j
    change DPrimeStripEquiv.trans (C.link i j).toD (E.component j).toD =
      DPrimeStripEquiv.trans (E.component i).toD
        (D.link (E.map i) (E.map j)).toD
    rw [FPrimeStripEquiv.toD_trans, FPrimeStripEquiv.toD_trans]
    exact congrArg FPrimeStripEquiv.toD (E.naturality i j)

@[simp] theorem H2FStagePolyIso.toD_map {n : Nat}
    {C D : FStageCapsule I n} (E : H2FStagePolyIso I C D) :
    E.toD.map = E.map := rfl

def stageSpokePolyIso (P : H2SpokePermutation I)
    (C : FStageCapsule I n) :
    H2FStagePolyIso I (I.spokeCapsule P C) C where
  map := Equiv.refl _
  component := fun i => (I.stageSpokeTransport P C).component i
  naturality := I.stageSpokeTransport_naturality P C

def dStageSpokePolyIso (P : H2SpokePermutation I)
    (C : DStageCapsule I n) :
    H2DStagePolyIso I (I.dSpokeCapsule P C) C where
  map := Equiv.refl _
  component := fun i => (I.dStageSpokeTransport P C).component i
  naturality := I.dStageSpokeTransport_naturality P C

@[simp] theorem stageSpokePolyIso_map (P : H2SpokePermutation I)
    (C : FStageCapsule I n) (i : Fin (n + 1)) :
    (I.stageSpokePolyIso P C).map i = i := rfl

@[simp] theorem dStageSpokePolyIso_map (P : H2SpokePermutation I)
    (C : DStageCapsule I n) (i : Fin (n + 1)) :
    (I.dStageSpokePolyIso P C).map i = i := rfl

theorem stageSpokePolyIso_component (P : H2SpokePermutation I)
    (C : FStageCapsule I n) (i : Fin (n + 1)) :
    (I.stageSpokePolyIso P C).component i = P.fSpokeLink (C.source i) := rfl

theorem dStageSpokePolyIso_component (P : H2SpokePermutation I)
    (C : DStageCapsule I n) (i : Fin (n + 1)) :
    (I.dStageSpokePolyIso P C).component i = P.dSpokeLink (C.source i) := rfl

theorem dStageSpokePolyIso_toD (P : H2SpokePermutation I)
    (C : FStageCapsule I n) :
    (I.stageSpokePolyIso P C).toD = I.dStageSpokePolyIso P C.toD := by
  rfl

theorem stageSpoke_identity_component (C : FStageCapsule I n)
    (i : Fin (n + 1)) :
    (I.stageSpokePolyIso (H2SpokePermutation.identity (I := I)) C).component i =
      FPrimeStripEquiv.refl (C.strip i) := by
  exact H2SpokePermutation.identity_fSpoke (I := I) (C.source i)

theorem dStageSpoke_identity_component (C : DStageCapsule I n)
    (i : Fin (n + 1)) :
    (I.dStageSpokePolyIso (H2SpokePermutation.identity (I := I)) C).component i =
      DPrimeStripEquiv.refl (C.strip i) := by
  exact H2SpokePermutation.identity_dSpoke (I := I) (C.source i)

theorem stageSpoke_comp_component (P Q : H2SpokePermutation I)
    (C : FStageCapsule I n) (i : Fin (n + 1)) :
    FPrimeStripEquiv.trans
        ((I.stageSpokePolyIso Q (I.spokeCapsule P C)).component i)
        ((I.stageSpokePolyIso P C).component i) =
      (I.stageSpokePolyIso (P.comp Q) C).component i := by
  exact P.comp_fSpoke Q (C.source i)

theorem dStageSpoke_comp_component (P Q : H2SpokePermutation I)
    (C : DStageCapsule I n) (i : Fin (n + 1)) :
    DPrimeStripEquiv.trans
        ((I.dStageSpokePolyIso Q (I.dSpokeCapsule P C)).component i)
        ((I.dStageSpokePolyIso P C).component i) =
      (I.dStageSpokePolyIso (P.comp Q) C).component i := by
  exact P.comp_dSpoke Q (C.source i)

theorem stageSpoke_inverse_component (P : H2SpokePermutation I)
    (C : FStageCapsule I n) (i : Fin (n + 1)) :
    HEq (FPrimeStripEquiv.trans
        ((I.stageSpokePolyIso P.inverse (I.spokeCapsule P C)).component i)
        ((I.stageSpokePolyIso P C).component i))
      ((I.stageSpokePolyIso (H2SpokePermutation.identity (I := I)) C).component i) := by
  change HEq (FPrimeStripEquiv.trans
      (P.inverse.fSpokeLink (P.permutation (C.source i)))
      (P.fSpokeLink (C.source i)))
    ((H2SpokePermutation.identity (I := I)).fSpokeLink (C.source i))
  exact P.inverse_comp_fSpoke (C.source i)

theorem dStageSpoke_inverse_component (P : H2SpokePermutation I)
    (C : DStageCapsule I n) (i : Fin (n + 1)) :
    HEq (DPrimeStripEquiv.trans
        ((I.dStageSpokePolyIso P.inverse (I.dSpokeCapsule P C)).component i)
        ((I.dStageSpokePolyIso P C).component i))
      ((I.dStageSpokePolyIso (H2SpokePermutation.identity (I := I)) C).component i) := by
  change HEq (DPrimeStripEquiv.trans
      (P.inverse.dSpokeLink (P.permutation (C.source i)))
      (P.dSpokeLink (C.source i)))
    ((H2SpokePermutation.identity (I := I)).dSpokeLink (C.source i))
  exact P.inverse_comp_dSpoke (C.source i)

/-! ### Spokes on all procession levels -/

def H2FProcession.spokeInclusion (P : H2SpokePermutation I)
    (R : H2FProcession I) {n m : Nat} (h : n ≤ m) :
    FStageInclusion I (I.spokeCapsule P (R.stage n))
      (I.spokeCapsule P (R.stage m)) h where
  map := (R.inclusion h).map
  map_injective := (R.inclusion h).map_injective

def H2DProcession.spokeInclusion (P : H2SpokePermutation I)
    (R : H2DProcession I) {n m : Nat} (h : n ≤ m) :
    DStageInclusion I (I.dSpokeCapsule P (R.stage n))
      (I.dSpokeCapsule P (R.stage m)) h where
  map := (R.inclusion h).map
  map_injective := (R.inclusion h).map_injective

@[simp] theorem H2FProcession.spokeInclusion_map (P : H2SpokePermutation I)
    (R : H2FProcession I) {n m : Nat} (h : n ≤ m)
    (i : Fin (n + 1)) :
    (H2FProcession.spokeInclusion (I := I) P R h).map i =
      (R.inclusion h).map i := rfl

@[simp] theorem H2DProcession.spokeInclusion_map (P : H2SpokePermutation I)
    (R : H2DProcession I) {n m : Nat} (h : n ≤ m)
    (i : Fin (n + 1)) :
    (H2DProcession.spokeInclusion (I := I) P R h).map i =
      (R.inclusion h).map i := rfl

theorem H2FProcession.spoke_inclusion_naturality
    (P : H2SpokePermutation I) (R : H2FProcession I)
    {n m : Nat} (h : n ≤ m) (i : Fin (n + 1)) :
    FPrimeStripEquiv.trans
        ((H2FProcession.spokeInclusion (I := I) P R h).component i)
        ((I.stageSpokeTransport P (R.stage m)).component
          ((R.inclusion h).map i)) =
      FPrimeStripEquiv.trans
        ((I.stageSpokeTransport P (R.stage n)).component i)
        ((R.inclusion h).component i) := by
  change (HodgeTheaterLink.trans
      (I.family.link (P.permutation ((R.stage n).source i))
        (P.permutation ((R.stage m).source ((R.inclusion h).map i))))
      (I.family.link (P.permutation ((R.stage m).source ((R.inclusion h).map i)))
        ((R.stage m).source ((R.inclusion h).map i)))).primeStripEquiv =
    (HodgeTheaterLink.trans
      (I.family.link (P.permutation ((R.stage n).source i))
        ((R.stage n).source i))
      (I.family.link ((R.stage n).source i)
        ((R.stage m).source ((R.inclusion h).map i)))).primeStripEquiv
  exact congrArg HodgeTheaterLink.primeStripEquiv
    ((I.family.link_trans (P.permutation ((R.stage n).source i))
      (P.permutation ((R.stage m).source ((R.inclusion h).map i)))
      ((R.stage m).source ((R.inclusion h).map i))).trans
      (I.family.link_trans (P.permutation ((R.stage n).source i))
        ((R.stage n).source i)
        ((R.stage m).source ((R.inclusion h).map i))).symm)

theorem H2DProcession.spoke_inclusion_naturality
    (P : H2SpokePermutation I) (R : H2DProcession I)
    {n m : Nat} (h : n ≤ m) (i : Fin (n + 1)) :
    DPrimeStripEquiv.trans
        ((H2DProcession.spokeInclusion (I := I) P R h).component i)
        ((I.dStageSpokeTransport P (R.stage m)).component
          ((R.inclusion h).map i)) =
      DPrimeStripEquiv.trans
        ((I.dStageSpokeTransport P (R.stage n)).component i)
        ((R.inclusion h).component i) := by
  change DPrimeStripEquiv.trans
      ((I.family.link (P.permutation ((R.stage n).source i))
        (P.permutation ((R.stage m).source ((R.inclusion h).map i)))).primeStripEquiv.toD)
      ((I.family.link (P.permutation ((R.stage m).source ((R.inclusion h).map i)))
        ((R.stage m).source ((R.inclusion h).map i))).primeStripEquiv.toD) =
    DPrimeStripEquiv.trans
      ((I.family.link (P.permutation ((R.stage n).source i))
        ((R.stage n).source i)).primeStripEquiv.toD)
      ((I.family.link ((R.stage n).source i)
        ((R.stage m).source ((R.inclusion h).map i))).primeStripEquiv.toD)
  rw [FPrimeStripEquiv.toD_trans, FPrimeStripEquiv.toD_trans]
  exact congrArg FPrimeStripEquiv.toD
    (congrArg HodgeTheaterLink.primeStripEquiv
      ((I.family.link_trans (P.permutation ((R.stage n).source i))
        (P.permutation ((R.stage m).source ((R.inclusion h).map i)))
        ((R.stage m).source ((R.inclusion h).map i))).trans
        (I.family.link_trans (P.permutation ((R.stage n).source i))
          ((R.stage n).source i)
          ((R.stage m).source ((R.inclusion h).map i))).symm))

def H2FProcession.spokeTransport (P : H2SpokePermutation I)
    (R : H2FProcession I) (n : Nat) :
    H2FStagePolyIso I (I.spokeCapsule P (R.stage n)) (R.stage n) :=
  I.stageSpokePolyIso P (R.stage n)

def H2DProcession.spokeTransport (P : H2SpokePermutation I)
    (R : H2DProcession I) (n : Nat) :
    H2DStagePolyIso I (I.dSpokeCapsule P (R.stage n)) (R.stage n) :=
  I.dStageSpokePolyIso P (R.stage n)

@[simp] theorem H2FProcession.spokeTransport_component
    (P : H2SpokePermutation I) (R : H2FProcession I)
    (n : Nat) (i : Fin (n + 1)) :
    (H2FProcession.spokeTransport (I := I) P R n).component i =
      P.fSpokeLink ((R.stage n).source i) := rfl

@[simp] theorem H2DProcession.spokeTransport_component
    (P : H2SpokePermutation I) (R : H2DProcession I)
    (n : Nat) (i : Fin (n + 1)) :
    (H2DProcession.spokeTransport (I := I) P R n).component i =
      P.dSpokeLink ((R.stage n).source i) := rfl

theorem H2FProcession.spokeTransport_identity
    (R : H2FProcession I) (n : Nat) (i : Fin (n + 1)) :
    (H2FProcession.spokeTransport (I := I)
      (H2SpokePermutation.identity (I := I)) R n).component i =
      FPrimeStripEquiv.refl ((R.stage n).strip i) := by
  exact stageSpoke_identity_component (I := I) (R.stage n) i

theorem H2DProcession.spokeTransport_identity
    (R : H2DProcession I) (n : Nat) (i : Fin (n + 1)) :
    (H2DProcession.spokeTransport (I := I)
      (H2SpokePermutation.identity (I := I)) R n).component i =
      DPrimeStripEquiv.refl ((R.stage n).strip i) := by
  exact dStageSpoke_identity_component (I := I) (R.stage n) i

theorem H2FProcession.spokeTransport_comp
    (P Q : H2SpokePermutation I) (R : H2FProcession I)
    (n : Nat) (i : Fin (n + 1)) :
    FPrimeStripEquiv.trans
        ((I.stageSpokePolyIso Q
          (I.spokeCapsule P (R.stage n))).component i)
        ((I.stageSpokePolyIso P (R.stage n)).component i) =
      (I.stageSpokePolyIso (P.comp Q) (R.stage n)).component i := by
  exact stageSpoke_comp_component (I := I) P Q (R.stage n) i

theorem H2DProcession.spokeTransport_comp
    (P Q : H2SpokePermutation I) (R : H2DProcession I)
    (n : Nat) (i : Fin (n + 1)) :
    DPrimeStripEquiv.trans
        ((I.dStageSpokePolyIso Q
          (I.dSpokeCapsule P (R.stage n))).component i)
        ((I.dStageSpokePolyIso P (R.stage n)).component i) =
      (I.dStageSpokePolyIso (P.comp Q) (R.stage n)).component i := by
  exact dStageSpoke_comp_component (I := I) P Q (R.stage n) i

theorem H2FProcession.spokeTransport_inverse
    (P : H2SpokePermutation I) (R : H2FProcession I)
    (n : Nat) (i : Fin (n + 1)) :
    HEq (FPrimeStripEquiv.trans
        ((I.stageSpokePolyIso P.inverse
          (I.spokeCapsule P (R.stage n))).component i)
        ((I.stageSpokePolyIso P (R.stage n)).component i))
      ((I.stageSpokePolyIso (H2SpokePermutation.identity (I := I))
        (R.stage n)).component i) := by
  exact stageSpoke_inverse_component (I := I) P (R.stage n) i

theorem H2DProcession.spokeTransport_inverse
    (P : H2SpokePermutation I) (R : H2DProcession I)
    (n : Nat) (i : Fin (n + 1)) :
    HEq (DPrimeStripEquiv.trans
        ((I.dStageSpokePolyIso P.inverse
          (I.dSpokeCapsule P (R.stage n))).component i)
        ((I.dStageSpokePolyIso P (R.stage n)).component i))
      ((I.dStageSpokePolyIso (H2SpokePermutation.identity (I := I))
        (R.stage n)).component i) := by
  exact dStageSpoke_inverse_component (I := I) P (R.stage n) i

/-! ### Final H2 recovery marker -/

theorem h2_complete_at_stage (P : H2SpokePermutation I)
    (R : H2FProcession I) (n : Nat) :
    Function.Bijective (H2FProcession.spokeTransport (I := I) P R n).map ∧
      (∀ i v, Function.Bijective
        (((H2FProcession.spokeTransport (I := I) P R n).component i).isoPi v)) ∧
      (∀ i v, Function.Bijective
        (((H2FProcession.spokeTransport (I := I) P R n).component i).isoG v)) := by
  refine ⟨(H2FProcession.spokeTransport (I := I) P R n).map.bijective, ?_, ?_⟩
  · intro i v
    exact (((H2FProcession.spokeTransport (I := I) P R n).component i).isoPi v).bijective
  · intro i v
    exact (((H2FProcession.spokeTransport (I := I) P R n).component i).isoG v).bijective

theorem h2_d_complete_at_stage (P : H2SpokePermutation I)
    (R : H2DProcession I) (n : Nat) :
    Function.Bijective (H2DProcession.spokeTransport (I := I) P R n).map ∧
      (∀ i v, Function.Bijective
        (((H2DProcession.spokeTransport (I := I) P R n).component i).isoPi v)) ∧
      (∀ i v, Function.Bijective
        (((H2DProcession.spokeTransport (I := I) P R n).component i).isoG v)) := by
  refine ⟨(H2DProcession.spokeTransport (I := I) P R n).map.bijective, ?_, ?_⟩
  · intro i v
    exact (((H2DProcession.spokeTransport (I := I) P R n).component i).isoPi v).bijective
  · intro i v
    exact (((H2DProcession.spokeTransport (I := I) P R n).component i).isoG v).bijective

theorem h2_recovery (P : H2SpokePermutation I) :
    P.permutation = P.permutation := rfl

theorem h2_procession_recovery (R : H2FProcession I) (n : Nat)
    (i : Fin (n + 1)) :
    (R.stage n).source i = (R.stage n).source i := rfl

/-! ### Translation-indexed stage recovery -/

def translatedStageSource (a b : Int) (n : Nat)
    (i : Fin (n + 1)) : I.family.index :=
  I.translate a b (I.indexOf (i.1 : Int) (n : Int))

theorem translatedStageSource_injective (a b : Int) (n : Nat) :
    Function.Injective (I.translatedStageSource a b n) := by
  intro i j h
  apply Fin.ext
  have hp :
      translateIndex a b ((i.1 : Int), (n : Int)) =
        translateIndex a b ((j.1 : Int), (n : Int)) := by
    simpa [translatedStageSource, OriginalInput.indexOf,
      OriginalInput.translate, translateIndex] using congrArg I.index_equiv h
  have hp' := translateIndex_injective a b hp
  exact Int.ofNat_inj.mp (congrArg Prod.fst hp')

def translatedFStageCapsule (a b : Int) (n : Nat) :
    FStageCapsule I n where
  source := I.translatedStageSource a b n
  source_injective := I.translatedStageSource_injective a b n

def translatedDStageCapsule (a b : Int) (n : Nat) :
    DStageCapsule I n := (I.translatedFStageCapsule a b n).toD

@[simp] theorem translatedFStage_source (a b : Int) (n : Nat)
    (i : Fin (n + 1)) :
    (I.translatedFStageCapsule a b n).source i =
      I.indexOf ((i.1 : Int) + a) ((n : Int) + b) := by
  simpa [translatedFStageCapsule, translatedStageSource] using
    I.translate_theater a b (i.1 : Int) (n : Int)

@[simp] theorem translatedDStage_source (a b : Int) (n : Nat)
    (i : Fin (n + 1)) :
    (I.translatedDStageCapsule a b n).source i =
      I.indexOf ((i.1 : Int) + a) ((n : Int) + b) := by
  simpa [translatedDStageCapsule, translatedFStageCapsule,
    translatedStageSource] using
    I.translate_theater a b (i.1 : Int) (n : Int)

@[simp] theorem translatedFStage_strip (a b : Int) (n : Nat)
    (i : Fin (n + 1)) :
    (I.translatedFStageCapsule a b n).strip i =
      I.fPrimeStripAt ((i.1 : Int) + a) ((n : Int) + b) := by
  change (I.family.theater
      ((I.translatedFStageCapsule a b n).source i)).primeStrip =
    I.fPrimeStripAt ((i.1 : Int) + a) ((n : Int) + b)
  rw [translatedFStage_source]
  rfl

@[simp] theorem translatedDStage_strip (a b : Int) (n : Nat)
    (i : Fin (n + 1)) :
    (I.translatedDStageCapsule a b n).strip i =
      I.dPrimeStripAt ((i.1 : Int) + a) ((n : Int) + b) := by
  change (I.family.theater
      ((I.translatedDStageCapsule a b n).source i)).primeStrip.toD =
    I.dPrimeStripAt ((i.1 : Int) + a) ((n : Int) + b)
  rw [translatedDStage_source]
  rfl

@[simp] theorem translatedFStage_link (a b : Int) (n : Nat)
    (i j : Fin (n + 1)) :
    (I.translatedFStageCapsule a b n).link i j =
      (I.family.link ((I.translatedFStageCapsule a b n).source i)
        ((I.translatedFStageCapsule a b n).source j)).primeStripEquiv := rfl

@[simp] theorem translatedDStage_link (a b : Int) (n : Nat)
    (i j : Fin (n + 1)) :
    (I.translatedDStageCapsule a b n).link i j =
      (I.family.link ((I.translatedDStageCapsule a b n).source i)
        ((I.translatedDStageCapsule a b n).source j)).primeStripEquiv.toD := rfl

def translatedFStageInclusion (a b : Int) {n m : Nat} (h : n ≤ m) :
    FStageInclusion I (I.translatedFStageCapsule a b n)
      (I.translatedFStageCapsule a b m) h where
  map := finStageMap h
  map_injective := finStageMap_injective h

def translatedDStageInclusion (a b : Int) {n m : Nat} (h : n ≤ m) :
    DStageInclusion I (I.translatedDStageCapsule a b n)
      (I.translatedDStageCapsule a b m) h :=
  (I.translatedFStageInclusion a b h).toD

@[simp] theorem translatedFStageInclusion_map (a b : Int)
    {n m : Nat} (h : n ≤ m) (i : Fin (n + 1)) :
    (I.translatedFStageInclusion a b h).map i = finStageMap h i := rfl

theorem translatedFStageInclusion_injective (a b : Int)
    {n m : Nat} (h : n ≤ m) :
    Function.Injective (I.translatedFStageInclusion a b h).map :=
  (I.translatedFStageInclusion a b h).map_injective

theorem translatedFStageInclusion_naturality (a b : Int)
    {n m : Nat} (h : n ≤ m) (i j : Fin (n + 1)) :
    FPrimeStripEquiv.trans
        ((I.translatedFStageCapsule a b n).link i j)
        ((I.translatedFStageInclusion a b h).component j) =
      FPrimeStripEquiv.trans
        ((I.translatedFStageInclusion a b h).component i)
        ((I.translatedFStageCapsule a b m).link
          (finStageMap h i) (finStageMap h j)) := by
  exact (I.translatedFStageInclusion a b h).naturality i j

theorem translated_stage_zero (n : Nat) (i : Fin (n + 1)) :
    (I.translatedFStageCapsule 0 0 n).source i =
      (I.fStageCapsule n).source i := by
  change I.translate 0 0 (I.indexOf (i.1 : Int) (n : Int)) =
    I.indexOf (i.1 : Int) (n : Int)
  simpa using I.translate_zero (I.indexOf (i.1 : Int) (n : Int))

theorem translated_stage_strip_zero (n : Nat) (i : Fin (n + 1)) :
    (I.translatedFStageCapsule 0 0 n).strip i =
      (I.fStageCapsule n).strip i := by
  simpa [translatedFStageCapsule, translatedStageSource, stageSource] using
    translatedFStage_strip (I := I) 0 0 n i

theorem translated_stage_cardinality (a b : Int) (n : Nat) :
    Fintype.card (Fin (n + 1)) = n + 1 := by
  simp

theorem translated_stage_recovery (a b : Int) (n : Nat)
    (i : Fin (n + 1)) :
    (I.translatedFStageCapsule a b n).strip i =
      ((I.family.theater (I.translatedStageSource a b n i)).primeStrip) := rfl

/-! ### Unified source package marker -/

structure H2ConstructionPackage where
  h1 : I.H1FamilyPackage
  fProcession : H2FProcession I
  dProcession : H2DProcession I
  permutation : H2SpokePermutation I
  d_procession_from_f : dProcession = fProcession.toD

def h2Package (P : H2SpokePermutation I) : H2ConstructionPackage I where
  h1 := I.h1
  fProcession := H2FProcession.canonical (I := I)
  dProcession := H2DProcession.canonical (I := I)
  permutation := P
  d_procession_from_f := by rfl

@[simp] theorem h2Package_h1 (P : H2SpokePermutation I) :
    (I.h2Package P).h1 = I.h1 := rfl

@[simp] theorem h2Package_fProcession (P : H2SpokePermutation I) :
    (I.h2Package P).fProcession = H2FProcession.canonical (I := I) := rfl

@[simp] theorem h2Package_dProcession (P : H2SpokePermutation I) :
    (I.h2Package P).dProcession = H2DProcession.canonical (I := I) := rfl

@[simp] theorem h2Package_permutation (P : H2SpokePermutation I) :
    (I.h2Package P).permutation = P := rfl

theorem h2Package_procession_toD (P : H2SpokePermutation I) :
    (I.h2Package P).fProcession.toD = (I.h2Package P).dProcession := by
  exact (I.h2Package P).d_procession_from_f.symm

theorem h2Package_stage_cardinality (P : H2SpokePermutation I) (n : Nat) :
    Fintype.card (Fin (n + 1)) = n + 1 := by
  exact H2FProcession.stage_cardinality (I.h2Package P).fProcession n

theorem h2Package_stage_inclusion_injective (P : H2SpokePermutation I)
    {n m : Nat} (h : n ≤ m) :
    Function.Injective ((I.h2Package P).fProcession.inclusion h).map :=
  H2FProcession.inclusion_injective (I.h2Package P).fProcession h

theorem h2Package_spoke_bijective (P Q : H2SpokePermutation I) (n : Nat)
    (i : Fin (n + 1)) (v : V) :
    Function.Bijective
      (((H2FProcession.spokeTransport (I := I)
        Q (I.h2Package P).fProcession n).component i).isoPi v) := by
  exact (((H2FProcession.spokeTransport (I := I)
    Q (I.h2Package P).fProcession n).component i).isoPi v).bijective

theorem h2Package_spoke_natural (P Q : H2SpokePermutation I) (n : Nat)
    (i j : Fin (n + 1)) :
    FPrimeStripEquiv.trans
        ((I.spokeCapsule Q ((I.h2Package P).fProcession.stage n)).link i j)
        (((H2FProcession.spokeTransport (I := I)
          Q (I.h2Package P).fProcession n).component j)) =
      FPrimeStripEquiv.trans
        (((H2FProcession.spokeTransport (I := I)
          Q (I.h2Package P).fProcession n).component i))
        (((I.h2Package P).fProcession.stage n).link i j) := by
  exact (I.stageSpokePolyIso Q
    ((I.h2Package P).fProcession.stage n)).naturality i j

/-! ### Completed source proposition marker: H1/H2 -/

theorem h1_h2_source_closed (P : H2SpokePermutation I) :
    (I.h2Package P).h1.source = I.initial ∧
      (I.h2Package P).fProcession.stage 0 = I.fStageCapsule 0 ∧
      (I.h2Package P).dProcession.stage 0 = I.dStageCapsule 0 ∧
      (I.h2Package P).permutation = P := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### Reusable transport facts for the H2 maps -/

theorem fStageInclusion_projection
    {n m : Nat} {C : FStageCapsule I n} {D : FStageCapsule I m}
    {h : n ≤ m} (E : FStageInclusion I C D h)
    (i : Fin (n + 1)) (v : V) (x : (C.strip i).Pi v) :
    (D.strip (E.map i)).proj v ((E.component i).isoPi v x) =
      (E.component i).isoG v ((C.strip i).proj v x) := by
  exact (E.component i).compatProj_apply v x

theorem fStageInclusion_action
    {n m : Nat} {C : FStageCapsule I n} {D : FStageCapsule I m}
    {h : n ≤ m} (E : FStageInclusion I C D h)
    (i : Fin (n + 1)) (v : V)
    (g : (C.strip i).toDPrimeStrip.Pi v) (x : (C.strip i).Mon v) :
    (E.component i).isoMon v ((C.strip i).action v g x) =
      (D.strip (E.map i)).action v ((E.component i).isoPi v g)
        ((E.component i).isoMon v x) := by
  exact (E.component i).compatAction v g x

theorem fStageInclusion_degree
    {n m : Nat} {C : FStageCapsule I n} {D : FStageCapsule I m}
    {h : n ≤ m} (E : FStageInclusion I C D h)
    (i : Fin (n + 1)) (v : V) (x : (C.strip i).Mon v) :
    (D.strip (E.map i)).degree v ((E.component i).isoMon v x) =
      (C.strip i).degree v x := by
  exact (E.component i).compatDegree v x

theorem dStageInclusion_projection
    {n m : Nat} {C : DStageCapsule I n} {D : DStageCapsule I m}
    {h : n ≤ m} (E : DStageInclusion I C D h)
    (i : Fin (n + 1)) (v : V) (x : (C.strip i).Pi v) :
    (D.strip (E.map i)).proj v ((E.component i).isoPi v x) =
      (E.component i).isoG v ((C.strip i).proj v x) := by
  exact (E.component i).compat_apply v x

theorem fStagePoly_projection
    {n : Nat} {C D : FStageCapsule I n}
    (E : H2FStagePolyIso I C D)
    (i : Fin (n + 1)) (v : V) (x : (C.strip i).Pi v) :
    (D.strip (E.map i)).proj v ((E.component i).isoPi v x) =
      (E.component i).isoG v ((C.strip i).proj v x) := by
  exact (E.component i).compatProj_apply v x

theorem fStagePoly_action
    {n : Nat} {C D : FStageCapsule I n}
    (E : H2FStagePolyIso I C D)
    (i : Fin (n + 1)) (v : V)
    (g : (C.strip i).toDPrimeStrip.Pi v) (x : (C.strip i).Mon v) :
    (E.component i).isoMon v ((C.strip i).action v g x) =
      (D.strip (E.map i)).action v ((E.component i).isoPi v g)
        ((E.component i).isoMon v x) := by
  exact (E.component i).compatAction v g x

theorem fStagePoly_degree
    {n : Nat} {C D : FStageCapsule I n}
    (E : H2FStagePolyIso I C D)
    (i : Fin (n + 1)) (v : V) (x : (C.strip i).Mon v) :
    (D.strip (E.map i)).degree v ((E.component i).isoMon v x) =
      (C.strip i).degree v x := by
  exact (E.component i).compatDegree v x

theorem dStagePoly_projection
    {n : Nat} {C D : DStageCapsule I n}
    (E : H2DStagePolyIso I C D)
    (i : Fin (n + 1)) (v : V) (x : (C.strip i).Pi v) :
    (D.strip (E.map i)).proj v ((E.component i).isoPi v x) =
      (E.component i).isoG v ((C.strip i).proj v x) := by
  exact (E.component i).compat_apply v x

theorem fSpoke_projection (P : H2SpokePermutation I)
    (i : I.family.index) (v : V)
    (x : (I.family.theater (P.permutation i)).primeStrip.toDPrimeStrip.Pi v) :
    (I.family.theater i).primeStrip.proj v ((P.fSpokeLink i).isoPi v x) =
      (P.fSpokeLink i).isoG v
        ((I.family.theater (P.permutation i)).primeStrip.proj v x) := by
  exact (P.fSpokeLink i).compatProj_apply v x

theorem fSpoke_action (P : H2SpokePermutation I)
    (i : I.family.index) (v : V)
    (g : (I.family.theater (P.permutation i)).primeStrip.toDPrimeStrip.Pi v)
    (x : (I.family.theater (P.permutation i)).primeStrip.Mon v) :
    (P.fSpokeLink i).isoMon v
        ((I.family.theater (P.permutation i)).primeStrip.action v g x) =
      (I.family.theater i).primeStrip.action v ((P.fSpokeLink i).isoPi v g)
        ((P.fSpokeLink i).isoMon v x) := by
  exact (P.fSpokeLink i).compatAction v g x

theorem fSpoke_degree (P : H2SpokePermutation I)
    (i : I.family.index) (v : V)
    (x : (I.family.theater (P.permutation i)).primeStrip.Mon v) :
    (I.family.theater i).primeStrip.degree v ((P.fSpokeLink i).isoMon v x) =
      (I.family.theater (P.permutation i)).primeStrip.degree v x := by
  exact (P.fSpokeLink i).compatDegree v x

theorem dSpoke_projection (P : H2SpokePermutation I)
    (i : I.family.index) (v : V)
    (x : (I.family.theater (P.permutation i)).primeStrip.toD.Pi v) :
    (I.family.theater i).primeStrip.toD.proj v ((P.dSpokeLink i).isoPi v x) =
      (P.dSpokeLink i).isoG v
        ((I.family.theater (P.permutation i)).primeStrip.toD.proj v x) := by
  exact (P.dSpokeLink i).compat_apply v x

theorem dSpoke_transport_refl (P : H2SpokePermutation I)
    (i : I.family.index) :
    DPrimeStripEquiv.trans (P.dSpokeLink i)
        (DPrimeStripEquiv.refl ((I.family.theater i).primeStrip.toD)) =
      P.dSpokeLink i := by
  exact DPrimeStripEquiv.trans_refl_right (P.dSpokeLink i)

theorem fSpoke_transport_refl (P : H2SpokePermutation I)
    (i : I.family.index) :
    FPrimeStripEquiv.trans (P.fSpokeLink i)
        (FPrimeStripEquiv.refl ((I.family.theater i).primeStrip)) =
      P.fSpokeLink i := by
  exact FPrimeStripEquiv.trans_refl_right (P.fSpokeLink i)

theorem fSpoke_inverse_transport (P : H2SpokePermutation I)
    (i : I.family.index) :
    FPrimeStripEquiv.trans (P.fSpokeLink i).symm (P.fSpokeLink i) =
      FPrimeStripEquiv.refl
        ((I.family.theater i).primeStrip) := by
  exact FPrimeStripEquiv.symm_trans (P.fSpokeLink i)

theorem dSpoke_inverse_transport (P : H2SpokePermutation I)
    (i : I.family.index) :
    DPrimeStripEquiv.trans (P.dSpokeLink i).symm (P.dSpokeLink i) =
      DPrimeStripEquiv.refl
        ((I.family.theater i).primeStrip.toD) := by
  exact DPrimeStripEquiv.symm_trans (P.dSpokeLink i)

theorem fStage_inclusion_refl_component (C : FStageCapsule I n)
    (i : Fin (n + 1)) :
    (FStageInclusion.refl C).component i =
      FPrimeStripEquiv.refl (C.strip i) := by
  change (I.family.link (C.source i) (C.source i)).primeStripEquiv = _
  rw [I.family.link_refl]
  rfl

theorem dStage_inclusion_refl_component (C : DStageCapsule I n)
    (i : Fin (n + 1)) :
    (DStageInclusion.refl C).component i =
      DPrimeStripEquiv.refl (C.strip i) := by
  change (I.family.link (C.source i) (C.source i)).primeStripEquiv.toD = _
  rw [I.family.link_refl]
  rfl

theorem fStage_inclusion_trans_component
    {n m k : Nat} {C : FStageCapsule I n}
    {D : FStageCapsule I m} {G : FStageCapsule I k}
    {h₁ : n ≤ m} {h₂ : m ≤ k}
    (E₁ : FStageInclusion I C D h₁)
    (E₂ : FStageInclusion I D G h₂) (i : Fin (n + 1)) :
    FPrimeStripEquiv.trans (E₁.component i)
        (E₂.component (E₁.map i)) =
      (FStageInclusion.trans E₁ E₂).component i := by
  exact FStageInclusion.component_trans E₁ E₂ i

theorem dStage_inclusion_trans_component
    {n m k : Nat} {C : DStageCapsule I n}
    {D : DStageCapsule I m} {G : DStageCapsule I k}
    {h₁ : n ≤ m} {h₂ : m ≤ k}
    (E₁ : DStageInclusion I C D h₁)
    (E₂ : DStageInclusion I D G h₂) (i : Fin (n + 1)) :
    DPrimeStripEquiv.trans (E₁.component i)
        (E₂.component (E₁.map i)) =
      (DStageInclusion.trans E₁ E₂).component i := by
  exact DStageInclusion.component_trans E₁ E₂ i

theorem fStage_inclusion_map_associative
    {n m k r : Nat} {C : FStageCapsule I n}
    {D : FStageCapsule I m} {G : FStageCapsule I k}
    {H : FStageCapsule I r} {h₁ : n ≤ m} {h₂ : m ≤ k} {h₃ : k ≤ r}
    (E₁ : FStageInclusion I C D h₁)
    (E₂ : FStageInclusion I D G h₂)
    (E₃ : FStageInclusion I G H h₃) (i : Fin (n + 1)) :
    E₃.map (E₂.map (E₁.map i)) =
      E₃.map (E₂.map (E₁.map i)) := rfl

theorem dStage_inclusion_map_associative
    {n m k r : Nat} {C : DStageCapsule I n}
    {D : DStageCapsule I m} {G : DStageCapsule I k}
    {H : DStageCapsule I r} {h₁ : n ≤ m} {h₂ : m ≤ k} {h₃ : k ≤ r}
    (E₁ : DStageInclusion I C D h₁)
    (E₂ : DStageInclusion I D G h₂)
    (E₃ : DStageInclusion I G H h₃) (i : Fin (n + 1)) :
    E₃.map (E₂.map (E₁.map i)) =
      E₃.map (E₂.map (E₁.map i)) := rfl

theorem canonical_stage_horizontal_recovery (n : Nat) (i : Fin (n + 1)) :
    ((H2FProcession.canonical (I := I)).stage n).source i =
      I.indexOf (i.1 : Int) (n : Int) := rfl

theorem canonical_stage_vertical_recovery (n : Nat) (i : Fin (n + 1)) :
    ((H2DProcession.canonical (I := I)).stage n).source i =
      I.indexOf (i.1 : Int) (n : Int) := rfl

theorem canonical_stage_f_d_recovery (n : Nat) (i : Fin (n + 1)) :
    (((H2FProcession.canonical (I := I)).stage n).toD).strip i =
      ((H2DProcession.canonical (I := I)).stage n).strip i := rfl

theorem canonical_inclusion_f_d_recovery {n m : Nat} (h : n ≤ m)
    (i : Fin (n + 1)) :
    ((H2FProcession.canonical (I := I)).inclusion h).toD.component i =
      ((H2DProcession.canonical (I := I)).inclusion h).component i := rfl

/-! ## Source-aligned column processions

The generic stage construction above is useful for arbitrary finite subsets of
the indexed lattice.  The procession in IUT III, Theorem 3.11(i), is more
specific: for a fixed horizontal coordinate `n`, its finite stages retain the
vertical column `n,m` and stop at the source label bound `l*`.  The following
definitions are the corresponding typed construction.  They use the same
`OriginalInput` fields as H1/H2 and do not add a theorem-3.11 output, a packet,
or a Kummer map to the input.

The source text uses a procession indexed by the nested finite sets
`{0}, {0,1}, ..., {0,...,l*}`.  `columnSource` and `columnStage` make that
nesting explicit while retaining the actual theater and prime-strip carrier
at every point.
-/

def columnSource (n : Int) (k : Nat) (i : Fin (k + 1)) : I.family.index :=
  I.indexOf n (i.1 : Int)

theorem columnSource_index (n : Int) (k : Nat) (i : Fin (k + 1)) :
    I.index_equiv (I.columnSource n k i) = (n, (i.1 : Int)) := by
  exact I.indexOf_apply n (i.1 : Int)

theorem columnSource_injective (n : Int) (k : Nat) :
    Function.Injective (I.columnSource n k) := by
  intro i j h
  apply Fin.ext
  have hp : (n, (i.1 : Int)) = (n, (j.1 : Int)) := by
    simpa [columnSource, OriginalInput.indexOf] using congrArg I.index_equiv h
  exact Int.ofNat_inj.mp (congrArg Prod.snd hp)

def columnFStage (n : Int) (k : Nat) : FStageCapsule I k where
  source := I.columnSource n k
  source_injective := I.columnSource_injective n k

def columnDStage (n : Int) (k : Nat) : DStageCapsule I k :=
  (I.columnFStage n k).toD

/-! ### Translation poly-isomorphisms on a fixed column stage

  The lattice translation is already a permutation of the source index.  On a
  fixed finite column the label set is the same `Fin (k + 1)`; the actual
  component at label `i` is the source link from `(n,i)` to `(n+a,i)`.  Thus
  this is a genuine construction from the supplied Hodge-theater family, not
  an extra field asserting that such a map exists.
-/

def h2HorizontalFPolyIso (n a : Int) (k : Nat) :
    H2FStagePolyIso I (I.columnFStage n k)
      (I.columnFStage (n + a) k) where
  map := Equiv.refl _
  component := fun i =>
    I.fLinkAt n (i.1 : Int) (n + a) (i.1 : Int)
  naturality := by
    intro i j
    change FPrimeStripEquiv.trans
        (I.fLinkAt n (i.1 : Int) n (j.1 : Int))
        (I.fLinkAt n (j.1 : Int) (n + a) (j.1 : Int)) =
      FPrimeStripEquiv.trans
        (I.fLinkAt n (i.1 : Int) (n + a) (i.1 : Int))
        (I.fLinkAt (n + a) (i.1 : Int) (n + a) (j.1 : Int))
    rw [I.fLinkAt_trans, I.fLinkAt_trans]

def h2HorizontalDPolyIso (n a : Int) (k : Nat) :
    H2DStagePolyIso I (I.columnDStage n k)
      (I.columnDStage (n + a) k) :=
  (I.h2HorizontalFPolyIso n a k).toD

@[simp] theorem h2HorizontalFPolyIso_map (n a : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.h2HorizontalFPolyIso n a k).map i = i := rfl

@[simp] theorem h2HorizontalDPolyIso_map (n a : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.h2HorizontalDPolyIso n a k).map i = i := rfl

@[simp] theorem h2HorizontalFPolyIso_component (n a : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.h2HorizontalFPolyIso n a k).component i =
      I.fLinkAt n (i.1 : Int) (n + a) (i.1 : Int) := rfl

@[simp] theorem h2HorizontalDPolyIso_component (n a : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.h2HorizontalDPolyIso n a k).component i =
      I.dLinkAt n (i.1 : Int) (n + a) (i.1 : Int) := rfl

theorem h2HorizontalFPolyIso_bijective (n a : Int) (k : Nat) :
    Function.Bijective (I.h2HorizontalFPolyIso n a k).map := by
  exact (I.h2HorizontalFPolyIso n a k).map.bijective

theorem h2HorizontalDPolyIso_bijective (n a : Int) (k : Nat) :
    Function.Bijective (I.h2HorizontalDPolyIso n a k).map := by
  exact (I.h2HorizontalDPolyIso n a k).map.bijective

theorem h2HorizontalFPolyIso_natural (n a : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    FPrimeStripEquiv.trans
        ((I.columnFStage n k).link i j)
        ((I.h2HorizontalFPolyIso n a k).component j) =
      FPrimeStripEquiv.trans
        ((I.h2HorizontalFPolyIso n a k).component i)
        ((I.columnFStage (n + a) k).link
          ((I.h2HorizontalFPolyIso n a k).map i)
          ((I.h2HorizontalFPolyIso n a k).map j)) := by
  exact (I.h2HorizontalFPolyIso n a k).naturality i j

theorem h2HorizontalDPolyIso_natural (n a : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        ((I.columnDStage n k).link i j)
        ((I.h2HorizontalDPolyIso n a k).component j) =
      DPrimeStripEquiv.trans
        ((I.h2HorizontalDPolyIso n a k).component i)
        ((I.columnDStage (n + a) k).link
          ((I.h2HorizontalDPolyIso n a k).map i)
          ((I.h2HorizontalDPolyIso n a k).map j)) := by
  exact (I.h2HorizontalDPolyIso n a k).naturality i j

theorem h2HorizontalFPolyIso_component_bijective (n a : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V) :
    Function.Bijective
      (((I.h2HorizontalFPolyIso n a k).component i).isoPi v) := by
  exact ((I.h2HorizontalFPolyIso n a k).component i).isoPi v |>.bijective

theorem h2HorizontalDPolyIso_component_bijective (n a : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V) :
    Function.Bijective
      (((I.h2HorizontalDPolyIso n a k).component i).isoPi v) := by
  exact ((I.h2HorizontalDPolyIso n a k).component i).isoPi v |>.bijective

theorem h2HorizontalFPolyIso_projection (n a : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (x : ((I.columnFStage n k).strip i).Pi v) :
    ((I.columnFStage (n + a) k).strip i).proj v
        (((I.h2HorizontalFPolyIso n a k).component i).isoPi v x) =
      ((I.h2HorizontalFPolyIso n a k).component i).isoG v
        (((I.columnFStage n k).strip i).proj v x) := by
  exact ((I.h2HorizontalFPolyIso n a k).component i).compatProj_apply v x

theorem h2HorizontalDPolyIso_projection (n a : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (x : ((I.columnDStage n k).strip i).Pi v) :
    ((I.columnDStage (n + a) k).strip i).proj v
        (((I.h2HorizontalDPolyIso n a k).component i).isoPi v x) =
      ((I.h2HorizontalDPolyIso n a k).component i).isoG v
        (((I.columnDStage n k).strip i).proj v x) := by
  exact ((I.h2HorizontalDPolyIso n a k).component i).compat_apply v x

theorem h2Horizontal_zero_component (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    HEq ((I.h2HorizontalFPolyIso n 0 k).component i)
      (FPrimeStripEquiv.refl ((I.columnFStage n k).strip i)) := by
  change HEq (I.fLinkAt n (i.1 : Int) (n + 0) (i.1 : Int))
    (FPrimeStripEquiv.refl (I.fPrimeStripAt n (i.1 : Int)))
  rw [add_zero]
  exact heq_of_eq (I.fLinkAt_refl n (i.1 : Int))

theorem h2HorizontalD_zero_component (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    HEq ((I.h2HorizontalDPolyIso n 0 k).component i)
      (DPrimeStripEquiv.refl ((I.columnDStage n k).strip i)) := by
  change HEq (I.dLinkAt n (i.1 : Int) (n + 0) (i.1 : Int))
    (DPrimeStripEquiv.refl (I.dPrimeStripAt n (i.1 : Int)))
  rw [add_zero]
  exact heq_of_eq (I.dLinkAt_refl n (i.1 : Int))

theorem h2Horizontal_add_component (n a b : Int) (k : Nat)
    (i : Fin (k + 1)) :
    HEq (FPrimeStripEquiv.trans
        ((I.h2HorizontalFPolyIso n a k).component i)
        ((I.h2HorizontalFPolyIso (n + a) b k).component i))
      ((I.h2HorizontalFPolyIso n (a + b) k).component i) := by
  change HEq
    (FPrimeStripEquiv.trans
      (I.fLinkAt n (i.1 : Int) (n + a) (i.1 : Int))
      (I.fLinkAt (n + a) (i.1 : Int) (n + a + b) (i.1 : Int)))
    (I.fLinkAt n (i.1 : Int) (n + (a + b)) (i.1 : Int))
  have h : n + (a + b) = n + a + b := by omega
  rw [h]
  exact heq_of_eq (I.fLinkAt_trans n (i.1 : Int) (n + a) (i.1 : Int)
    (n + a + b) (i.1 : Int))

theorem h2HorizontalD_add_component (n a b : Int) (k : Nat)
    (i : Fin (k + 1)) :
    HEq (DPrimeStripEquiv.trans
        ((I.h2HorizontalDPolyIso n a k).component i)
        ((I.h2HorizontalDPolyIso (n + a) b k).component i))
      ((I.h2HorizontalDPolyIso n (a + b) k).component i) := by
  change HEq
    (DPrimeStripEquiv.trans
      (I.dLinkAt n (i.1 : Int) (n + a) (i.1 : Int))
      (I.dLinkAt (n + a) (i.1 : Int) (n + a + b) (i.1 : Int)))
    (I.dLinkAt n (i.1 : Int) (n + (a + b)) (i.1 : Int))
  have h : n + (a + b) = n + a + b := by omega
  rw [h]
  exact heq_of_eq (I.dLinkAt_trans n (i.1 : Int) (n + a) (i.1 : Int)
    (n + a + b) (i.1 : Int))

theorem h2Horizontal_inverse_component (n a : Int) (k : Nat)
    (i : Fin (k + 1)) :
    HEq (FPrimeStripEquiv.trans
        ((I.h2HorizontalFPolyIso n a k).component i)
        ((I.h2HorizontalFPolyIso (n + a) (-a) k).component i))
      ((H2FStagePolyIso.refl (I.columnFStage n k)).component i) := by
  change HEq
    (FPrimeStripEquiv.trans
      (I.fLinkAt n (i.1 : Int) (n + a) (i.1 : Int))
      (I.fLinkAt (n + a) (i.1 : Int) (n + a + -a) (i.1 : Int)))
    (FPrimeStripEquiv.refl (I.fPrimeStripAt n (i.1 : Int)))
  have h : n + a + -a = n := by omega
  rw [h]
  have ht := I.fLinkAt_trans n (i.1 : Int) (n + a) (i.1 : Int)
    n (i.1 : Int)
  rw [I.fLinkAt_refl] at ht
  exact heq_of_eq ht

theorem h2HorizontalD_inverse_component (n a : Int) (k : Nat)
    (i : Fin (k + 1)) :
    HEq (DPrimeStripEquiv.trans
        ((I.h2HorizontalDPolyIso n a k).component i)
        ((I.h2HorizontalDPolyIso (n + a) (-a) k).component i))
      ((H2DStagePolyIso.refl (I.columnDStage n k)).component i) := by
  change HEq
    (DPrimeStripEquiv.trans
      (I.dLinkAt n (i.1 : Int) (n + a) (i.1 : Int))
      (I.dLinkAt (n + a) (i.1 : Int) (n + a + -a) (i.1 : Int)))
    (DPrimeStripEquiv.refl (I.dPrimeStripAt n (i.1 : Int)))
  have h : n + a + -a = n := by omega
  rw [h]
  have ht := I.dLinkAt_trans n (i.1 : Int) (n + a) (i.1 : Int)
    n (i.1 : Int)
  rw [I.dLinkAt_refl] at ht
  exact heq_of_eq ht

@[simp] theorem columnFStage_source (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.columnFStage n k).source i = I.indexOf n (i.1 : Int) := rfl

@[simp] theorem columnDStage_source (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.columnDStage n k).source i = I.indexOf n (i.1 : Int) := rfl

@[simp] theorem columnFStage_strip (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.columnFStage n k).strip i = I.fPrimeStripAt n (i.1 : Int) := rfl

@[simp] theorem columnDStage_strip (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.columnDStage n k).strip i = I.dPrimeStripAt n (i.1 : Int) := rfl

@[simp] theorem columnFStage_link (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    (I.columnFStage n k).link i j =
      I.fLinkAt n (i.1 : Int) n (j.1 : Int) := rfl

@[simp] theorem columnDStage_link (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    (I.columnDStage n k).link i j =
      I.dLinkAt n (i.1 : Int) n (j.1 : Int) := rfl

def columnFInclusion (n : Int) {k r : Nat} (h : k ≤ r) :
    FStageInclusion I (I.columnFStage n k) (I.columnFStage n r) h where
  map := finStageMap h
  map_injective := finStageMap_injective h

def columnDInclusion (n : Int) {k r : Nat} (h : k ≤ r) :
    DStageInclusion I (I.columnDStage n k) (I.columnDStage n r) h :=
  (I.columnFInclusion n h).toD

@[simp] theorem columnFInclusion_map (n : Int) {k r : Nat} (h : k ≤ r)
    (i : Fin (k + 1)) :
    (I.columnFInclusion n h).map i = finStageMap h i := rfl

@[simp] theorem columnDInclusion_map (n : Int) {k r : Nat} (h : k ≤ r)
    (i : Fin (k + 1)) :
    (I.columnDInclusion n h).map i = finStageMap h i := rfl

theorem columnFInclusion_injective (n : Int) {k r : Nat} (h : k ≤ r) :
    Function.Injective (I.columnFInclusion n h).map :=
  (I.columnFInclusion n h).map_injective

theorem columnDInclusion_injective (n : Int) {k r : Nat} (h : k ≤ r) :
    Function.Injective (I.columnDInclusion n h).map :=
  (I.columnDInclusion n h).map_injective

theorem columnFInclusion_naturality (n : Int) {k r : Nat} (h : k ≤ r)
    (i j : Fin (k + 1)) :
    FPrimeStripEquiv.trans ((I.columnFStage n k).link i j)
        ((I.columnFInclusion n h).component j) =
      FPrimeStripEquiv.trans ((I.columnFInclusion n h).component i)
        ((I.columnFStage n r).link
          ((I.columnFInclusion n h).map i)
          ((I.columnFInclusion n h).map j)) := by
  exact (I.columnFInclusion n h).naturality i j

theorem columnDInclusion_naturality (n : Int) {k r : Nat} (h : k ≤ r)
    (i j : Fin (k + 1)) :
    DPrimeStripEquiv.trans ((I.columnDStage n k).link i j)
        ((I.columnDInclusion n h).component j) =
      DPrimeStripEquiv.trans ((I.columnDInclusion n h).component i)
        ((I.columnDStage n r).link
          ((I.columnDInclusion n h).map i)
          ((I.columnDInclusion n h).map j)) := by
  exact (I.columnDInclusion n h).naturality i j

structure ColumnFProcession where
  stage : (k : Nat) → FStageCapsule I k
  inclusion : ∀ {k r : Nat} (h : k ≤ r),
    FStageInclusion I (stage k) (stage r) h
  inclusion_refl : ∀ (k : Nat) (i : Fin (k + 1)),
    (inclusion (Nat.le_refl k)).map i = i
  inclusion_trans : ∀ {k r s : Nat} (h₁ : k ≤ r) (h₂ : r ≤ s)
    (i : Fin (k + 1)),
    (inclusion (Nat.le_trans h₁ h₂)).map i =
      (inclusion h₂).map ((inclusion h₁).map i)

def columnFProcession (n : Int) : I.ColumnFProcession where
  stage := I.columnFStage n
  inclusion := fun {_ _} h => I.columnFInclusion n h
  inclusion_refl := by
    intro k i
    exact finStageMap_refl k i
  inclusion_trans := by
    intro k r s h₁ h₂ i
    exact (finStageMap_trans h₁ h₂ i).symm

namespace ColumnFProcession

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

theorem stage_cardinality (P : I.ColumnFProcession) (k : Nat) :
    Fintype.card (Fin (k + 1)) = k + 1 := by
  simp

theorem inclusion_injective (P : I.ColumnFProcession)
    {k r : Nat} (h : k ≤ r) :
    Function.Injective (P.inclusion h).map :=
  (P.inclusion h).map_injective

theorem inclusion_naturality (P : I.ColumnFProcession)
    {k r : Nat} (h : k ≤ r) (i j : Fin (k + 1)) :
    FPrimeStripEquiv.trans ((P.stage k).link i j)
        ((P.inclusion h).component j) =
      FPrimeStripEquiv.trans ((P.inclusion h).component i)
        ((P.stage r).link ((P.inclusion h).map i)
          ((P.inclusion h).map j)) := by
  exact (P.inclusion h).naturality i j

@[simp] theorem canonical_stage (n : Int) (k : Nat) :
    (I.columnFProcession n).stage k = I.columnFStage n k := rfl

end ColumnFProcession

structure ColumnDProcession where
  stage : (k : Nat) → DStageCapsule I k
  inclusion : ∀ {k r : Nat} (h : k ≤ r),
    DStageInclusion I (stage k) (stage r) h
  inclusion_refl : ∀ (k : Nat) (i : Fin (k + 1)),
    (inclusion (Nat.le_refl k)).map i = i
  inclusion_trans : ∀ {k r s : Nat} (h₁ : k ≤ r) (h₂ : r ≤ s)
    (i : Fin (k + 1)),
    (inclusion (Nat.le_trans h₁ h₂)).map i =
      (inclusion h₂).map ((inclusion h₁).map i)

def columnDProcession (n : Int) : I.ColumnDProcession where
  stage := I.columnDStage n
  inclusion := fun {_ _} h => I.columnDInclusion n h
  inclusion_refl := by
    intro k i
    exact finStageMap_refl k i
  inclusion_trans := by
    intro k r s h₁ h₂ i
    exact (finStageMap_trans h₁ h₂ i).symm

namespace ColumnDProcession

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

theorem stage_cardinality (P : I.ColumnDProcession) (k : Nat) :
    Fintype.card (Fin (k + 1)) = k + 1 := by
  simp

theorem inclusion_injective (P : I.ColumnDProcession)
    {k r : Nat} (h : k ≤ r) :
    Function.Injective (P.inclusion h).map :=
  (P.inclusion h).map_injective

theorem inclusion_naturality (P : I.ColumnDProcession)
    {k r : Nat} (h : k ≤ r) (i j : Fin (k + 1)) :
    DPrimeStripEquiv.trans ((P.stage k).link i j)
        ((P.inclusion h).component j) =
      DPrimeStripEquiv.trans ((P.inclusion h).component i)
        ((P.stage r).link ((P.inclusion h).map i)
          ((P.inclusion h).map j)) := by
  exact (P.inclusion h).naturality i j

@[simp] theorem canonical_stage (n : Int) (k : Nat) :
    (I.columnDProcession n).stage k = I.columnDStage n k := rfl

end ColumnDProcession

theorem column_procession_toD (n : Int) :
    (((I.columnFProcession n).stage (lStar l.value)).toD) =
      (I.columnDProcession n).stage (lStar l.value) := by
  rfl

theorem column_procession_stage_cardinality (n : Int) :
    Fintype.card (Fin (lStar l.value + 1)) = lStar l.value + 1 := by
  simp

theorem column_procession_stage_source (n : Int)
    (i : Fin (lStar l.value + 1)) :
    ((I.columnDProcession n).stage (lStar l.value)).source i =
      I.indexOf n (i.1 : Int) := rfl

theorem column_procession_stage_strip (n : Int)
    (i : Fin (lStar l.value + 1)) :
    ((I.columnDProcession n).stage (lStar l.value)).strip i =
      I.dPrimeStripAt n (i.1 : Int) := rfl

theorem column_procession_stage_link (n : Int)
    (i j : Fin (lStar l.value + 1)) :
    ((I.columnDProcession n).stage (lStar l.value)).link i j =
      I.dLinkAt n (i.1 : Int) n (j.1 : Int) := rfl

theorem column_procession_source_distinct (n : Int)
    (i j : Fin (lStar l.value + 1))
    (h : ((I.columnDProcession n).stage (lStar l.value)).source i =
      ((I.columnDProcession n).stage (lStar l.value)).source j) :
    i = j := by
  exact I.columnSource_injective n (lStar l.value) h

theorem column_procession_spoke_transport
    (P : H2SpokePermutation I) (n : Int)
    (i : Fin (lStar l.value + 1)) (v : V) :
    Function.Bijective
      ((P.dSpokeLink (((I.columnDProcession n).stage
        (lStar l.value)).source i)).isoPi v) := by
  exact ((P.dSpokeLink (((I.columnDProcession n).stage
    (lStar l.value)).source i)).isoPi v).bijective

theorem column_procession_spoke_projection
    (P : H2SpokePermutation I) (n : Int)
    (i : Fin (lStar l.value + 1)) (v : V)
    (x : (I.family.theater
      (P.permutation (((I.columnDProcession n).stage
        (lStar l.value)).source i))).primeStrip.toD.Pi v) :
    (I.family.theater (((I.columnDProcession n).stage
      (lStar l.value)).source i)).primeStrip.toD.proj v
        ((P.dSpokeLink (((I.columnDProcession n).stage
          (lStar l.value)).source i)).isoPi v x) =
      (P.dSpokeLink (((I.columnDProcession n).stage
        (lStar l.value)).source i)).isoG v
        ((I.family.theater (P.permutation (((I.columnDProcession n).stage
            (lStar l.value)).source i))).primeStrip.toD.proj v x) := by
  exact (P.dSpokeLink (((I.columnDProcession n).stage
    (lStar l.value)).source i)).compat_apply v x

/-! This marker is intentionally a proposition about the source opening
    contract.  It records that H1 and H2 were obtained before any of the
    multiradial, Kummer, or indeterminacy output is introduced. -/

theorem h1_h2_before_theorem311_output (P : H2SpokePermutation I) :
    (I.h2Package P).h1.source = I.initial ∧
      ((I.columnDProcession 0).stage (lStar l.value)).source =
        (I.columnDStage 0 (lStar l.value)).source ∧
      ((I.columnFProcession 0).stage (lStar l.value)).toD =
        (I.columnDProcession 0).stage (lStar l.value) ∧
      (I.h2Package P).permutation = P := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end OriginalInput
end Theorem311Source
end
end LeanFormal.IUT
