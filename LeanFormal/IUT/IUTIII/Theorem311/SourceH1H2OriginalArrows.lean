import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # Source arrows for H1 and H2

  This file is the source-facing wiring layer for the H1/H2 portion of
  IUT III, Theorem 3.11.  Its input is the complete `OriginalInput`: initial
  Theta-data and a distinct, indexed family of Hodge theaters with their
  source links.  Every carrier and arrow below is either a projection of that
  input or a theorem already proved in `SourceH1H2Construction`.

  In particular, this file does not turn an arithmetic-only record into a
  Hodge theater, a vertical-coricit D-theater, a Kummer correspondence, or a
  Frobenioid.  The missing vertical realization is represented by the final
  `DThetaRealizationGate`; no inhabitant is silently manufactured for it.

  The source text uses a procession of finite columns and arbitrary etale
  picture permutations.  The finite carriers are therefore `Fin (k + 1)`,
  while every prime-strip component keeps its dependent source and target.
  This distinction is important: component equalities are stated only at the
  exact dependent type, or as `HEq` when two definitionally equal carriers are
  displayed through different projections.
-/

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

open OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## H1: prime-strip projection and link arrows -/

structure H1PrimeDProjection where
  fStrip : I.family.index -> FPrimeStrip.{umon, uv, upi} V
  dStrip : I.family.index -> DPrimeStrip.{upi, uv} V
  fStrip_source : forall i, fStrip i = (I.family.theater i).primeStrip
  dStrip_source : forall i, dStrip i = (I.family.theater i).primeStrip.toD
  dStrip_toD : forall i, dStrip i = (fStrip i).toD

def h1PrimeDProjection : I.H1PrimeDProjection where
  fStrip := fun i => (I.family.theater i).primeStrip
  dStrip := fun i => (I.family.theater i).primeStrip.toD
  fStrip_source := by intro i; rfl
  dStrip_source := by intro i; rfl
  dStrip_toD := by intro i; rfl

@[simp] theorem h1_fStrip_at (i : I.family.index) :
    (I.h1PrimeDProjection).fStrip i = (I.family.theater i).primeStrip := rfl

@[simp] theorem h1_dStrip_at (i : I.family.index) :
    (I.h1PrimeDProjection).dStrip i =
      (I.family.theater i).primeStrip.toD := rfl

theorem h1_projection_source (i : I.family.index) :
    (I.h1PrimeDProjection).fStrip i = (I.family.theater i).primeStrip :=
  (I.h1PrimeDProjection).fStrip_source i

theorem h1_projection_d_source (i : I.family.index) :
    (I.h1PrimeDProjection).dStrip i =
      (I.family.theater i).primeStrip.toD :=
  (I.h1PrimeDProjection).dStrip_source i

theorem h1_projection_toD (i : I.family.index) :
    (I.h1PrimeDProjection).dStrip i =
      ((I.h1PrimeDProjection).fStrip i).toD :=
  (I.h1PrimeDProjection).dStrip_toD i

theorem h1_family_injective : Function.Injective I.family.theater :=
  I.family.distinct

theorem h1_theater_components_eq {i j : I.family.index}
    (ha : (I.family.theater i).arithmetic =
      (I.family.theater j).arithmetic)
    (hs : (I.family.theater i).primeStrip =
      (I.family.theater j).primeStrip)
    (hp : (I.family.theater i).thetaPacket =
      (I.family.theater j).thetaPacket) :
    I.family.theater i = I.family.theater j := by
  cases hi : I.family.theater i with
  | mk ai si pi =>
    cases hj : I.family.theater j with
    | mk aj sj pj =>
      have ha' : ai = aj := by simpa [hi, hj] using ha
      have hs' : si = sj := by simpa [hi, hj] using hs
      have hp' : pi = pj := by simpa [hi, hj] using hp
      exact (HodgeTheater.mk.injEq ai si pi aj sj pj).mpr ⟨ha', hs', hp'⟩

theorem h1_arithmetic_alignment (i : I.family.index) :
    (I.family.theater i).arithmetic = I.initial.arithmetic :=
  I.arithmetic_alignment i

theorem h1_arithmetic_alignment_symm (i : I.family.index) :
    I.initial.arithmetic = (I.family.theater i).arithmetic :=
  (I.h1_arithmetic_alignment i).symm

theorem h1_projection_f_to_d_heq (i : I.family.index) :
    HEq ((I.h1PrimeDProjection.fStrip i).toD)
      (I.h1PrimeDProjection.dStrip i) :=
  heq_of_eq (I.h1_projection_toD i).symm

structure H1LinkArrow (i j : I.family.index) where
  fLink : FPrimeStripEquiv
    ((I.h1PrimeDProjection).fStrip i)
    ((I.h1PrimeDProjection).fStrip j)
  dLink : DPrimeStripEquiv
    ((I.h1PrimeDProjection).dStrip i)
    ((I.h1PrimeDProjection).dStrip j)
  fLink_source : fLink = (I.family.link i j).primeStripEquiv
  dLink_source : dLink = (I.family.link i j).primeStripEquiv.toD

def h1LinkArrow (i j : I.family.index) : I.H1LinkArrow i j where
  fLink := (I.family.link i j).primeStripEquiv
  dLink := (I.family.link i j).primeStripEquiv.toD
  fLink_source := rfl
  dLink_source := rfl

@[simp] theorem h1_link_f_source (i j : I.family.index) :
    (I.h1LinkArrow i j).fLink = (I.family.link i j).primeStripEquiv := rfl

@[simp] theorem h1_link_d_source (i j : I.family.index) :
    (I.h1LinkArrow i j).dLink =
      (I.family.link i j).primeStripEquiv.toD := rfl

theorem h1_link_f_projection (i j : I.family.index) (v : V)
    (x : ((I.h1PrimeDProjection.fStrip i).toD).Pi v) :
    (I.h1PrimeDProjection.fStrip j).proj v
        ((I.h1LinkArrow i j).fLink.isoPi v x) =
      (I.h1LinkArrow i j).fLink.isoG v
        ((I.h1PrimeDProjection.fStrip i).proj v x) := by
  exact (I.h1LinkArrow i j).fLink.compatProj_apply v x

theorem h1_link_f_action (i j : I.family.index) (v : V)
    (g : ((I.h1PrimeDProjection.fStrip i).toD).Pi v)
    (x : (I.h1PrimeDProjection.fStrip i).Mon v) :
    (I.h1LinkArrow i j).fLink.isoMon v
        ((I.h1PrimeDProjection.fStrip i).action v g x) =
      (I.h1PrimeDProjection.fStrip j).action v
        ((I.h1LinkArrow i j).fLink.isoPi v g)
        ((I.h1LinkArrow i j).fLink.isoMon v x) := by
  exact (I.h1LinkArrow i j).fLink.compatAction v g x

theorem h1_link_f_degree (i j : I.family.index) (v : V)
    (x : (I.h1PrimeDProjection.fStrip i).Mon v) :
    (I.h1PrimeDProjection.fStrip j).degree v
        ((I.h1LinkArrow i j).fLink.isoMon v x) =
      (I.h1PrimeDProjection.fStrip i).degree v x := by
  exact (I.h1LinkArrow i j).fLink.compatDegree v x

theorem h1_link_d_projection (i j : I.family.index) (v : V)
    (x : (I.h1PrimeDProjection.dStrip i).Pi v) :
    (I.h1PrimeDProjection.dStrip j).proj v
        ((I.h1LinkArrow i j).dLink.isoPi v x) =
      (I.h1LinkArrow i j).dLink.isoG v
        ((I.h1PrimeDProjection.dStrip i).proj v x) := by
  exact (I.h1LinkArrow i j).dLink.compat_apply v x

theorem h1_link_f_refl (i : I.family.index) :
    (I.h1LinkArrow i i).fLink =
      FPrimeStripEquiv.refl (I.h1PrimeDProjection.fStrip i) := by
  change (I.family.link i i).primeStripEquiv = _
  rw [I.family.link_refl]
  rfl

theorem h1_link_d_refl (i : I.family.index) :
    (I.h1LinkArrow i i).dLink =
      DPrimeStripEquiv.refl (I.h1PrimeDProjection.dStrip i) := by
  change (I.family.link i i).primeStripEquiv.toD = _
  rw [I.family.link_refl]
  rfl

theorem h1_link_f_symm (i j : I.family.index) :
    FPrimeStripEquiv.symm (I.h1LinkArrow i j).fLink =
      (I.h1LinkArrow j i).fLink := by
  change FPrimeStripEquiv.symm ((I.family.link i j).primeStripEquiv) = _
  change (HodgeTheaterLink.symm (I.family.link i j)).primeStripEquiv = _
  rw [I.family.link_symm]
  rfl

theorem h1_link_d_symm (i j : I.family.index) :
    DPrimeStripEquiv.symm (I.h1LinkArrow i j).dLink =
      (I.h1LinkArrow j i).dLink := by
  change DPrimeStripEquiv.symm ((I.family.link i j).primeStripEquiv.toD) = _
  rw [FPrimeStripEquiv.toD_symm]
  exact congrArg FPrimeStripEquiv.toD
    (congrArg HodgeTheaterLink.primeStripEquiv
      (I.family.link_symm i j))

theorem h1_link_f_trans (i j k : I.family.index) :
    FPrimeStripEquiv.trans (I.h1LinkArrow i j).fLink
        (I.h1LinkArrow j k).fLink =
      (I.h1LinkArrow i k).fLink := by
  change (HodgeTheaterLink.trans (I.family.link i j)
      (I.family.link j k)).primeStripEquiv = _
  rw [I.family.link_trans]
  rfl

theorem h1_link_d_trans (i j k : I.family.index) :
    DPrimeStripEquiv.trans (I.h1LinkArrow i j).dLink
        (I.h1LinkArrow j k).dLink =
      (I.h1LinkArrow i k).dLink := by
  change DPrimeStripEquiv.trans
      ((I.family.link i j).primeStripEquiv.toD)
      ((I.family.link j k).primeStripEquiv.toD) = _
  rw [FPrimeStripEquiv.toD_trans]
  exact congrArg FPrimeStripEquiv.toD
    (congrArg HodgeTheaterLink.primeStripEquiv
      (I.family.link_trans i j k))

theorem h1_link_f_inverse (i j : I.family.index) :
    FPrimeStripEquiv.trans (I.h1LinkArrow i j).fLink
        (I.h1LinkArrow j i).fLink =
      FPrimeStripEquiv.refl (I.h1PrimeDProjection.fStrip i) := by
  calc
    FPrimeStripEquiv.trans (I.h1LinkArrow i j).fLink
        (I.h1LinkArrow j i).fLink = (I.h1LinkArrow i i).fLink :=
      I.h1_link_f_trans i j i
    _ = FPrimeStripEquiv.refl (I.h1PrimeDProjection.fStrip i) :=
      I.h1_link_f_refl i

theorem h1_link_d_inverse (i j : I.family.index) :
    DPrimeStripEquiv.trans (I.h1LinkArrow i j).dLink
        (I.h1LinkArrow j i).dLink =
      DPrimeStripEquiv.refl (I.h1PrimeDProjection.dStrip i) := by
  calc
    DPrimeStripEquiv.trans (I.h1LinkArrow i j).dLink
        (I.h1LinkArrow j i).dLink = (I.h1LinkArrow i i).dLink :=
      I.h1_link_d_trans i j i
    _ = DPrimeStripEquiv.refl (I.h1PrimeDProjection.dStrip i) :=
      I.h1_link_d_refl i

/-! ## H1 coordinate wiring -/

structure H1CoordinateWiring where
  index : SourceTheorem311Index -> I.family.index
  index_recovery : forall p, I.index_equiv (index p) = p
  theater : SourceTheorem311Index -> HodgeTheater l V
  theater_recovery : forall p,
    theater p = I.family.theater (index p)
  theater_injective : Function.Injective theater
  q_transport : forall p q,
    (theater p).thetaPacket.q = (theater q).thetaPacket.q
  scale_transport : forall p q (j : SignedLabel l.value),
    (theater p).thetaPacket.scale j = (theater q).thetaPacket.scale j

def h1CoordinateWiring : I.H1CoordinateWiring where
  index := fun p => I.indexOf p.1 p.2
  index_recovery := by intro p; exact I.indexOf_apply p.1 p.2
  theater := fun p => I.theaterAt p.1 p.2
  theater_recovery := by intro p; rfl
  theater_injective := I.theaterAt_injective
  q_transport := by intro p q; exact I.linkAt_q p.1 p.2 q.1 q.2
  scale_transport := by
    intro p q j
    exact I.linkAt_scale p.1 p.2 q.1 q.2 j

@[simp] theorem h1CoordinateWiring_index (p : SourceTheorem311Index) :
    (I.h1CoordinateWiring).index p = I.indexOf p.1 p.2 := rfl

@[simp] theorem h1CoordinateWiring_theater (p : SourceTheorem311Index) :
    (I.h1CoordinateWiring).theater p = I.theaterAt p.1 p.2 := rfl

theorem h1CoordinateWiring_index_injective :
    Function.Injective (I.h1CoordinateWiring).index := by
  intro p q h
  apply Prod.ext
  · exact congrArg Prod.fst (by
      simpa [h1CoordinateWiring, OriginalInput.indexOf] using
        congrArg I.index_equiv h)
  · exact congrArg Prod.snd (by
      simpa [h1CoordinateWiring, OriginalInput.indexOf] using
        congrArg I.index_equiv h)

theorem h1CoordinateWiring_theater_eq_iff {p q : SourceTheorem311Index} :
    (I.h1CoordinateWiring).theater p =
      (I.h1CoordinateWiring).theater q <-> p = q := by
  constructor
  · intro h
    exact (I.h1CoordinateWiring).theater_injective h
  · intro h
    cases h
    rfl

/-! ## H2: finite column ledger -/

structure H2ColumnSourceLedger (n : Int) where
  fProcession : I.ColumnFProcession
  dProcession : I.ColumnDProcession
  fd_stage : forall k, (fProcession.stage k).toD = dProcession.stage k
  source_f : forall k (i : Fin (k + 1)),
    (fProcession.stage k).source i = I.indexOf n (i.1 : Int)
  source_d : forall k (i : Fin (k + 1)),
    (dProcession.stage k).source i = I.indexOf n (i.1 : Int)
  source_injective_f : forall k, Function.Injective (fProcession.stage k).source
  source_injective_d : forall k, Function.Injective (dProcession.stage k).source
  inclusion_injective_f : forall {k r} (h : k <= r),
    Function.Injective (fProcession.inclusion h).map
  inclusion_injective_d : forall {k r} (h : k <= r),
    Function.Injective (dProcession.inclusion h).map
  inclusion_natural_f : forall {k r} (h : k <= r) (i j : Fin (k + 1)),
    FPrimeStripEquiv.trans ((fProcession.stage k).link i j)
      ((fProcession.inclusion h).component j) =
    FPrimeStripEquiv.trans ((fProcession.inclusion h).component i)
      ((fProcession.stage r).link
        ((fProcession.inclusion h).map i)
        ((fProcession.inclusion h).map j))
  inclusion_natural_d : forall {k r} (h : k <= r) (i j : Fin (k + 1)),
    DPrimeStripEquiv.trans ((dProcession.stage k).link i j)
      ((dProcession.inclusion h).component j) =
    DPrimeStripEquiv.trans ((dProcession.inclusion h).component i)
      ((dProcession.stage r).link
        ((dProcession.inclusion h).map i)
        ((dProcession.inclusion h).map j))

def h2ColumnSourceLedger (n : Int) : I.H2ColumnSourceLedger n where
  fProcession := I.columnFProcession n
  dProcession := I.columnDProcession n
  fd_stage := by intro k; rfl
  source_f := by intro k i; rfl
  source_d := by intro k i; rfl
  source_injective_f := by intro k; exact ((I.columnFProcession n).stage k).source_injective
  source_injective_d := by intro k; exact ((I.columnDProcession n).stage k).source_injective
  inclusion_injective_f := by intro k r h; exact ((I.columnFProcession n).inclusion h).map_injective
  inclusion_injective_d := by intro k r h; exact ((I.columnDProcession n).inclusion h).map_injective
  inclusion_natural_f := by
    intro k r h i j
    exact ((I.columnFProcession n).inclusion h).naturality i j
  inclusion_natural_d := by
    intro k r h i j
    exact ((I.columnDProcession n).inclusion h).naturality i j

@[simp] theorem h2ColumnSourceLedger_fProcession (n : Int) :
    (I.h2ColumnSourceLedger n).fProcession = I.columnFProcession n := rfl

@[simp] theorem h2ColumnSourceLedger_dProcession (n : Int) :
    (I.h2ColumnSourceLedger n).dProcession = I.columnDProcession n := rfl

theorem h2ColumnSourceLedger_fd_stage (n : Int) (k : Nat) :
    ((I.h2ColumnSourceLedger n).fProcession.stage k).toD =
      (I.h2ColumnSourceLedger n).dProcession.stage k :=
  (I.h2ColumnSourceLedger n).fd_stage k

theorem h2ColumnSourceLedger_source_injective (n : Int) (k : Nat) :
    Function.Injective ((I.h2ColumnSourceLedger n).dProcession.stage k).source :=
  (I.h2ColumnSourceLedger n).source_injective_d k

theorem h2ColumnSourceLedger_inclusion_natural (n : Int)
    {k r : Nat} (h : k <= r) (i j : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        (((I.h2ColumnSourceLedger n).dProcession.stage k).link i j)
        (((I.h2ColumnSourceLedger n).dProcession.inclusion h).component j) =
      DPrimeStripEquiv.trans
        (((I.h2ColumnSourceLedger n).dProcession.inclusion h).component i)
        (((I.h2ColumnSourceLedger n).dProcession.stage r).link
          (((I.h2ColumnSourceLedger n).dProcession.inclusion h).map i)
          (((I.h2ColumnSourceLedger n).dProcession.inclusion h).map j)) :=
  (I.h2ColumnSourceLedger n).inclusion_natural_d h i j

/-! ## H2 horizontal translation -/

structure H2HorizontalSourceLedger (n a : Int) (k : Nat) where
  fPoly : H2FStagePolyIso I (I.columnFStage n k)
    (I.columnFStage (n + a) k)
  dPoly : H2DStagePolyIso I (I.columnDStage n k)
    (I.columnDStage (n + a) k)
  d_from_f : dPoly = fPoly.toD
  map_identity : forall i, fPoly.map i = i
  f_natural : forall i j, FPrimeStripEquiv.trans
    ((I.columnFStage n k).link i j) (fPoly.component j) =
      FPrimeStripEquiv.trans (fPoly.component i)
        ((I.columnFStage (n + a) k).link (fPoly.map i) (fPoly.map j))
  d_natural : forall i j, DPrimeStripEquiv.trans
    ((I.columnDStage n k).link i j) (dPoly.component j) =
      DPrimeStripEquiv.trans (dPoly.component i)
        ((I.columnDStage (n + a) k).link (dPoly.map i) (dPoly.map j))

def h2HorizontalSourceLedger (n a : Int) (k : Nat) :
    I.H2HorizontalSourceLedger n a k where
  fPoly := I.h2HorizontalFPolyIso n a k
  dPoly := I.h2HorizontalDPolyIso n a k
  d_from_f := rfl
  map_identity := by intro i; rfl
  f_natural := by intro i j; exact (I.h2HorizontalFPolyIso n a k).naturality i j
  d_natural := by intro i j; exact (I.h2HorizontalDPolyIso n a k).naturality i j

@[simp] theorem h2HorizontalSourceLedger_fPoly (n a : Int) (k : Nat) :
    (I.h2HorizontalSourceLedger n a k).fPoly = I.h2HorizontalFPolyIso n a k := rfl

@[simp] theorem h2HorizontalSourceLedger_dPoly (n a : Int) (k : Nat) :
    (I.h2HorizontalSourceLedger n a k).dPoly = I.h2HorizontalDPolyIso n a k := rfl

theorem h2HorizontalSourceLedger_component (n a : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.h2HorizontalSourceLedger n a k).fPoly.component i =
      I.fLinkAt n (i.1 : Int) (n + a) (i.1 : Int) := rfl

theorem h2HorizontalSourceLedger_d_component (n a : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.h2HorizontalSourceLedger n a k).dPoly.component i =
      I.dLinkAt n (i.1 : Int) (n + a) (i.1 : Int) := rfl

theorem h2HorizontalSourceLedger_zero (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    HEq ((I.h2HorizontalSourceLedger n 0 k).fPoly.component i)
      (FPrimeStripEquiv.refl ((I.columnFStage n k).strip i)) := by
  simpa only [h2HorizontalSourceLedger_fPoly] using
    (LeanFormal.IUT.Theorem311Source.OriginalInput.h2Horizontal_zero_component
      I n k i)

theorem h2HorizontalSourceLedger_add (n a b : Int) (k : Nat)
    (i : Fin (k + 1)) :
    HEq (FPrimeStripEquiv.trans
        ((I.h2HorizontalSourceLedger n a k).fPoly.component i)
        ((I.h2HorizontalSourceLedger (n + a) b k).fPoly.component i))
      ((I.h2HorizontalSourceLedger n (a + b) k).fPoly.component i) := by
  simpa only [h2HorizontalSourceLedger_fPoly] using
    (LeanFormal.IUT.Theorem311Source.OriginalInput.h2Horizontal_add_component
      I n a b k i)

theorem h2HorizontalSourceLedger_inverse (n a : Int) (k : Nat)
    (i : Fin (k + 1)) :
    HEq (FPrimeStripEquiv.trans
        ((I.h2HorizontalSourceLedger n a k).fPoly.component i)
        ((I.h2HorizontalSourceLedger (n + a) (-a) k).fPoly.component i))
      ((H2FStagePolyIso.refl (I.columnFStage n k)).component i) := by
  simpa only [h2HorizontalSourceLedger_fPoly] using
    (LeanFormal.IUT.Theorem311Source.OriginalInput.h2Horizontal_inverse_component
      I n a k i)

/-! ## H2 spoke permutation -/

structure H2SpokeSourceLedger (P : H2SpokePermutation I) (n : Int) (k : Nat) where
  fPoly : H2FStagePolyIso I (I.spokeCapsule P (I.columnFStage n k))
    (I.columnFStage n k)
  dPoly : H2DStagePolyIso I (I.dSpokeCapsule P (I.columnDStage n k))
    (I.columnDStage n k)
  d_from_f : dPoly = fPoly.toD
  f_natural : forall i j, FPrimeStripEquiv.trans
    ((I.spokeCapsule P (I.columnFStage n k)).link i j)
      (fPoly.component j) =
    FPrimeStripEquiv.trans (fPoly.component i)
      ((I.columnFStage n k).link (fPoly.map i) (fPoly.map j))
  d_natural : forall i j, DPrimeStripEquiv.trans
    ((I.dSpokeCapsule P (I.columnDStage n k)).link i j)
      (dPoly.component j) =
    DPrimeStripEquiv.trans (dPoly.component i)
      ((I.columnDStage n k).link (dPoly.map i) (dPoly.map j))

def h2SpokeSourceLedger (P : H2SpokePermutation I) (n : Int) (k : Nat) :
    I.H2SpokeSourceLedger P n k where
  fPoly := I.stageSpokePolyIso P (I.columnFStage n k)
  dPoly := I.dStageSpokePolyIso P (I.columnDStage n k)
  d_from_f := by rfl
  f_natural := by intro i j; exact I.stageSpokeTransport_naturality P (I.columnFStage n k) i j
  d_natural := by intro i j; exact I.dStageSpokeTransport_naturality P (I.columnDStage n k) i j

@[simp] theorem h2SpokeSourceLedger_fPoly (P : H2SpokePermutation I) (n : Int) (k : Nat) :
    (I.h2SpokeSourceLedger P n k).fPoly = I.stageSpokePolyIso P (I.columnFStage n k) := rfl

@[simp] theorem h2SpokeSourceLedger_dPoly (P : H2SpokePermutation I) (n : Int) (k : Nat) :
    (I.h2SpokeSourceLedger P n k).dPoly = I.dStageSpokePolyIso P (I.columnDStage n k) := rfl

theorem h2SpokeSourceLedger_component (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.h2SpokeSourceLedger P n k).fPoly.component i =
      P.fSpokeLink (I.indexOf n (i.1 : Int)) := rfl

theorem h2SpokeSourceLedger_d_component (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.h2SpokeSourceLedger P n k).dPoly.component i =
      P.dSpokeLink (I.indexOf n (i.1 : Int)) := rfl

theorem h2SpokeSourceLedger_natural (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i j : Fin (k + 1)) :
    FPrimeStripEquiv.trans
        ((I.spokeCapsule P (I.columnFStage n k)).link i j)
        ((I.h2SpokeSourceLedger P n k).fPoly.component j) =
      FPrimeStripEquiv.trans
        ((I.h2SpokeSourceLedger P n k).fPoly.component i)
        ((I.columnFStage n k).link i j) := by
  exact I.stageSpokeTransport_naturality P (I.columnFStage n k) i j

theorem h2SpokeSourceLedger_d_natural (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i j : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        ((I.dSpokeCapsule P (I.columnDStage n k)).link i j)
        ((I.h2SpokeSourceLedger P n k).dPoly.component j) =
      DPrimeStripEquiv.trans
        ((I.h2SpokeSourceLedger P n k).dPoly.component i)
        ((I.columnDStage n k).link i j) := by
  exact I.dStageSpokeTransport_naturality P (I.columnDStage n k) i j

theorem h2SpokeSourceLedger_comp (P Q : H2SpokePermutation I)
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    FPrimeStripEquiv.trans
        ((I.stageSpokePolyIso Q
          (I.spokeCapsule P (I.columnFStage n k))).component i)
        ((I.stageSpokePolyIso P (I.columnFStage n k)).component i) =
      (I.stageSpokePolyIso (P.comp Q) (I.columnFStage n k)).component i := by
  exact I.stageSpoke_comp_component P Q (I.columnFStage n k) i

theorem h2SpokeSourceLedger_d_comp (P Q : H2SpokePermutation I)
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        ((I.dStageSpokePolyIso Q
          (I.dSpokeCapsule P (I.columnDStage n k))).component i)
        ((I.dStageSpokePolyIso P (I.columnDStage n k)).component i) =
      (I.dStageSpokePolyIso (P.comp Q) (I.columnDStage n k)).component i := by
  exact I.dStageSpoke_comp_component P Q (I.columnDStage n k) i

/-! ## Contract and explicit source boundary -/

structure H1H2SourceContract where
  h1 : I.H1FamilyPackage
  columnsF : Int -> I.ColumnFProcession
  columnsD : Int -> I.ColumnDProcession
  columns_toD : forall (n : Int) (k : Nat),
    ((columnsF n).stage k).toD = (columnsD n).stage k
  top_cardinality : forall (n : Int), Fintype.card (Fin (lStar l.value + 1)) =
    lStar l.value + 1
  top_source_injective : forall (n : Int),
    Function.Injective ((columnsD n).stage (lStar l.value)).source
  horizontal_poly : forall n a k,
    H2FStagePolyIso I ((columnsF n).stage k)
      ((columnsF (n + a)).stage k)
  spoke_poly : forall (P : H2SpokePermutation I) (n : Int) (k : Nat),
    H2FStagePolyIso I (I.spokeCapsule P ((columnsF n).stage k))
      ((columnsF n).stage k)

def h1H2SourceContract : H1H2SourceContract (I := I) where
  h1 := I.h1
  columnsF := I.columnFProcession
  columnsD := I.columnDProcession
  columns_toD := by intro n k; rfl
  top_cardinality := by intro n; simp
  top_source_injective := by
    intro n
    exact ((I.columnDProcession n).stage (lStar l.value)).source_injective
  horizontal_poly := fun n a k => I.h2HorizontalFPolyIso n a k
  spoke_poly := fun P n k => I.stageSpokePolyIso P (I.columnFStage n k)

@[simp] theorem h1H2_contract_h1 :
    (h1H2SourceContract I).h1 = I.h1 := rfl

theorem h1H2_contract_column_toD (n : Int) (k : Nat) :
    (((h1H2SourceContract I).columnsF n).stage k).toD =
      ((h1H2SourceContract I).columnsD n).stage k :=
  (h1H2SourceContract I).columns_toD n k

theorem h1H2_contract_cardinality (n : Int) :
    Fintype.card (Fin (lStar l.value + 1)) = lStar l.value + 1 :=
  by simp

theorem h1H2_contract_source_injective (n : Int) :
    Function.Injective
      (((h1H2SourceContract I).columnsD n).stage (lStar l.value)).source :=
  by
    exact (h1H2SourceContract (I := I)).top_source_injective n

theorem h1H2_contract_horizontal (n a : Int) (k : Nat) :
    (h1H2SourceContract I).horizontal_poly n a k =
      I.h2HorizontalFPolyIso n a k := rfl

theorem h1H2_contract_spoke (P : H2SpokePermutation I) (n : Int) (k : Nat) :
    (h1H2SourceContract I).spoke_poly P n k =
      I.stageSpokePolyIso P (I.columnFStage n k) := rfl

/-
  The theorem's D-Theta-Hodge-theater is obtained by vertical coricity and is
  not a field of `OriginalInput`.  This gate names precisely the missing
  source construction.  It is intentionally not inhabited by the identity
  projection above: the latter is only the underlying D-prime-strip image.
-/

structure DThetaRealizationGate where
  dTheater : I.family.index -> DPrimeStrip.{upi, uv} V
  bridge : forall i,
    DPrimeStripEquiv (dTheater i)
      ((I.h1PrimeDProjection).dStrip i)

theorem dTheta_gate_bijective (G : I.DThetaRealizationGate)
    (i : I.family.index) (v : V) :
    Function.Bijective ((G.bridge i).isoPi v) := by
  exact ((G.bridge i).isoPi v).bijective

theorem dTheta_gate_projection (G : I.DThetaRealizationGate)
    (i : I.family.index) (v : V) (x : (G.dTheater i).Pi v) :
    (I.h1PrimeDProjection.dStrip i).proj v ((G.bridge i).isoPi v x) =
      (G.bridge i).isoG v ((G.dTheater i).proj v x) := by
  exact (G.bridge i).compat_apply v x

end OriginalInput
end Theorem311Source
end
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def theorem311H1H2OriginalArrows : Obligation :=
  { id := "IUT-III.theorem-3.11-H1-H2-original-input-arrows"
    source := "IUT III, Theorem 3.11 opening paragraph and part (i)"
    status := VerificationStatus.interface
    note :=
      "The module packages source projections, fixed-column processions, " ++
        "stage inclusions, horizontal translation, and spoke naturality. " ++
        "It does not construct the vertical-coricit D-Theta-Hodge-theater " ++
        "or any LGP/Kummer/Frobenioid object; DThetaRealizationGate records " ++
        "that remaining source gate."
    dependsOn := ["IUT-III.source-h1-h2-construction",
      "IUT-I-II.prime-strip-core"] }

end LeanFormal.IUT.Audit
