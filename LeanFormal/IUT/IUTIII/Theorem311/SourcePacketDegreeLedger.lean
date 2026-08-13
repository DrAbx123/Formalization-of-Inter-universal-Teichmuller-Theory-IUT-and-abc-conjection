/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2OriginalArrows
import LeanFormal.IUT.IUTI.HodgeTheater.LinkVolumeTransport
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # Packets, degrees, and finite-stage ledgers from the original input

  The opening input of IUT III Theorem 3.11 already contains an actual
  Hodge-theater family.  Consequently the finite theta packet at every
  lattice point and the F/D prime-strip data at that point are constructible
  by projection.  This module makes those projections explicit and records
  the transport equations needed by the later H1/H2 and P1/P2 layers.

  No arithmetic-only input is enlarged here.  In particular, this module does
  not construct a vertical-coricit D-theater, a log-Kummer shell, an LGP
  monoid, or a Frobenioid.  Those objects remain separate gates because they
  are not fields of `OriginalInput` and cannot be recovered from a finite
  projection.  Every result below is instead a theorem about data which the
  paper's opening paragraph has already supplied.

  Source references: IUT III Theorem 3.11, Props. 3.2, 3.4, 3.5, 3.7,
  3.9, 3.10; IUT I Definition 5.2 and Prop. 6.9; IUT II theta packets and
  prime-strip degree transport.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. A source packet at one lattice coordinate -/

structure ThetaPacketLedger (n m : Int) where
  theater : HodgeTheater.{ua, uv, upi, umon} l V
  packet : FiniteThetaPacket l
  theater_source : theater = I.theaterAt n m
  packet_source : packet = theater.thetaPacket
  q_source : packet.q = (I.theaterAt n m).thetaPacket.q
  q_positive : 0 < packet.q
  scale_source : ∀ j, packet.scale j =
    (I.theaterAt n m).thetaPacket.scale j
  scale_positive : ∀ j, 0 < packet.scale j
  scale_nonzero : ∀ j, packet.scale j ≠ 0
  scale_neg : ∀ j, packet.scale (SignedLabel.neg j) = packet.scale j
  log_scale : ∀ j,
    Real.log (packet.scale j) =
      (gaussExponent j.1).toNat * Real.log packet.q
  log_volume : packet.logVolume =
    ∑ j : SignedLabel l.value, Real.log (packet.scale j)
  log_volume_neg :
    (∑ j : SignedLabel l.value,
      Real.log (packet.scale (SignedLabel.neg j))) = packet.logVolume

def thetaPacketLedgerAt (n m : Int) : I.ThetaPacketLedger n m where
  theater := I.theaterAt n m
  packet := (I.theaterAt n m).thetaPacket
  theater_source := rfl
  packet_source := rfl
  q_source := rfl
  q_positive := (I.theaterAt n m).thetaPacket.q_pos
  scale_source := by intro j; rfl
  scale_positive := by
    intro j
    exact (I.theaterAt n m).thetaPacket.scale_pos j
  scale_nonzero := by
    intro j
    exact (I.theaterAt n m).thetaPacket.scale_ne_zero j
  scale_neg := by
    intro j
    exact (I.theaterAt n m).thetaPacket.scale_neg j
  log_scale := by
    intro j
    exact (I.theaterAt n m).thetaPacket.log_scale j
  log_volume := by
    exact (I.theaterAt n m).thetaPacket.logVolume_eq_sum
  log_volume_neg := by
    exact (I.theaterAt n m).thetaPacket.logVolume_neg_invariant

@[simp] theorem thetaPacketLedgerAt_theater (n m : Int) :
    (I.thetaPacketLedgerAt n m).theater = I.theaterAt n m := rfl

@[simp] theorem thetaPacketLedgerAt_packet (n m : Int) :
    (I.thetaPacketLedgerAt n m).packet =
      (I.theaterAt n m).thetaPacket := rfl

@[simp] theorem thetaPacketLedgerAt_q (n m : Int) :
    (I.thetaPacketLedgerAt n m).packet.q =
      (I.theaterAt n m).thetaPacket.q := rfl

theorem thetaPacketLedgerAt_source (n m : Int) :
    (I.thetaPacketLedgerAt n m).packet =
      (I.thetaPacketLedgerAt n m).theater.thetaPacket :=
  (I.thetaPacketLedgerAt n m).packet_source

theorem thetaPacketLedgerAt_q_positive (n m : Int) :
    0 < (I.thetaPacketLedgerAt n m).packet.q :=
  (I.thetaPacketLedgerAt n m).q_positive

theorem thetaPacketLedgerAt_scale_source (n m : Int)
    (j : SignedLabel l.value) :
    (I.thetaPacketLedgerAt n m).packet.scale j =
      (I.theaterAt n m).thetaPacket.scale j :=
  (I.thetaPacketLedgerAt n m).scale_source j

theorem thetaPacketLedgerAt_scale_positive (n m : Int)
    (j : SignedLabel l.value) :
    0 < (I.thetaPacketLedgerAt n m).packet.scale j :=
  (I.thetaPacketLedgerAt n m).scale_positive j

theorem thetaPacketLedgerAt_scale_nonzero (n m : Int)
    (j : SignedLabel l.value) :
    (I.thetaPacketLedgerAt n m).packet.scale j ≠ 0 :=
  (I.thetaPacketLedgerAt n m).scale_nonzero j

theorem thetaPacketLedgerAt_scale_neg (n m : Int)
    (j : SignedLabel l.value) :
    (I.thetaPacketLedgerAt n m).packet.scale (SignedLabel.neg j) =
      (I.thetaPacketLedgerAt n m).packet.scale j :=
  (I.thetaPacketLedgerAt n m).scale_neg j

theorem thetaPacketLedgerAt_log_scale (n m : Int)
    (j : SignedLabel l.value) :
    Real.log ((I.thetaPacketLedgerAt n m).packet.scale j) =
      (gaussExponent j.1).toNat *
        Real.log (I.thetaPacketLedgerAt n m).packet.q :=
  (I.thetaPacketLedgerAt n m).log_scale j

theorem thetaPacketLedgerAt_log_volume (n m : Int) :
    (I.thetaPacketLedgerAt n m).packet.logVolume =
      ∑ j : SignedLabel l.value,
        Real.log ((I.thetaPacketLedgerAt n m).packet.scale j) :=
  (I.thetaPacketLedgerAt n m).log_volume

theorem thetaPacketLedgerAt_log_volume_neg (n m : Int) :
    (∑ j : SignedLabel l.value,
      Real.log ((I.thetaPacketLedgerAt n m).packet.scale
        (SignedLabel.neg j))) =
      (I.thetaPacketLedgerAt n m).packet.logVolume :=
  (I.thetaPacketLedgerAt n m).log_volume_neg

theorem thetaPacketLedgerAt_q_eq_initial (n m : Int) :
    (I.thetaPacketLedgerAt n m).packet.q =
      (I.thetaPacketLedgerAt 0 0).packet.q := by
  exact I.linkAt_q n m 0 0

theorem thetaPacketLedgerAt_scale_eq_initial (n m : Int)
    (j : SignedLabel l.value) :
    (I.thetaPacketLedgerAt n m).packet.scale j =
      (I.thetaPacketLedgerAt 0 0).packet.scale j := by
  exact I.linkAt_scale n m 0 0 j

theorem thetaPacketLedgerAt_log_volume_eq_initial (n m : Int) :
    (I.thetaPacketLedgerAt n m).packet.logVolume =
      (I.thetaPacketLedgerAt 0 0).packet.logVolume := by
  rw [I.thetaPacketLedgerAt_log_volume,
    I.thetaPacketLedgerAt_log_volume]
  apply Finset.sum_congr rfl
  intro j hj
  rw [I.thetaPacketLedgerAt_scale_eq_initial]

theorem thetaPacketLedgerAt_scale_product_eq_initial (n m : Int) :
    (∏ j : SignedLabel l.value,
      (I.thetaPacketLedgerAt n m).packet.scale j) =
      ∏ j : SignedLabel l.value,
        (I.thetaPacketLedgerAt 0 0).packet.scale j := by
  apply Finset.prod_congr rfl
  intro j hj
  exact I.thetaPacketLedgerAt_scale_eq_initial n m j

/-! ## 2. Packet transport along arbitrary source links -/

structure ThetaPacketLinkLedger (n m n' m' : Int) where
  source : I.ThetaPacketLedger n m
  target : I.ThetaPacketLedger n' m'
  q_transport : source.packet.q = target.packet.q
  scale_transport : ∀ j,
    source.packet.scale j = target.packet.scale j
  log_scale_transport : ∀ j,
    Real.log (source.packet.scale j) =
      Real.log (target.packet.scale j)
  log_volume_transport : source.packet.logVolume = target.packet.logVolume
  scale_product_transport :
    (∏ j : SignedLabel l.value, source.packet.scale j) =
      ∏ j : SignedLabel l.value, target.packet.scale j

def thetaPacketLinkLedgerAt (n m n' m' : Int) :
    I.ThetaPacketLinkLedger n m n' m' where
  source := I.thetaPacketLedgerAt n m
  target := I.thetaPacketLedgerAt n' m'
  q_transport := by
    exact I.linkAt_q n m n' m'
  scale_transport := by
    intro j
    exact I.linkAt_scale n m n' m' j
  log_scale_transport := by
    intro j
    exact (I.linkAt n m n' m').log_scale_eq j
  log_volume_transport := by
    exact (I.linkAt n m n' m').log_volume_eq
  scale_product_transport := by
    exact (I.linkAt n m n' m').scale_product_eq

@[simp] theorem thetaPacketLinkLedgerAt_source (n m n' m' : Int) :
    (I.thetaPacketLinkLedgerAt n m n' m').source =
      I.thetaPacketLedgerAt n m := rfl

@[simp] theorem thetaPacketLinkLedgerAt_target (n m n' m' : Int) :
    (I.thetaPacketLinkLedgerAt n m n' m').target =
      I.thetaPacketLedgerAt n' m' := rfl

theorem thetaPacketLinkLedgerAt_q (n m n' m' : Int) :
    (I.thetaPacketLinkLedgerAt n m n' m').source.packet.q =
      (I.thetaPacketLinkLedgerAt n m n' m').target.packet.q :=
  (I.thetaPacketLinkLedgerAt n m n' m').q_transport

theorem thetaPacketLinkLedgerAt_scale (n m n' m' : Int)
    (j : SignedLabel l.value) :
    (I.thetaPacketLinkLedgerAt n m n' m').source.packet.scale j =
      (I.thetaPacketLinkLedgerAt n m n' m').target.packet.scale j :=
  (I.thetaPacketLinkLedgerAt n m n' m').scale_transport j

theorem thetaPacketLinkLedgerAt_log_scale (n m n' m' : Int)
    (j : SignedLabel l.value) :
    Real.log ((I.thetaPacketLinkLedgerAt n m n' m').source.packet.scale j) =
      Real.log ((I.thetaPacketLinkLedgerAt n m n' m').target.packet.scale j) :=
  (I.thetaPacketLinkLedgerAt n m n' m').log_scale_transport j

theorem thetaPacketLinkLedgerAt_log_volume (n m n' m' : Int) :
    (I.thetaPacketLinkLedgerAt n m n' m').source.packet.logVolume =
      (I.thetaPacketLinkLedgerAt n m n' m').target.packet.logVolume :=
  (I.thetaPacketLinkLedgerAt n m n' m').log_volume_transport

theorem thetaPacketLinkLedgerAt_scale_product (n m n' m' : Int) :
    (∏ j : SignedLabel l.value,
      (I.thetaPacketLinkLedgerAt n m n' m').source.packet.scale j) =
      ∏ j : SignedLabel l.value,
        (I.thetaPacketLinkLedgerAt n m n' m').target.packet.scale j :=
  (I.thetaPacketLinkLedgerAt n m n' m').scale_product_transport

theorem thetaPacketLinkLedgerAt_refl (n m : Int) :
    (I.thetaPacketLinkLedgerAt n m n m).q_transport = rfl := by
  rfl

theorem thetaPacketLinkLedgerAt_symm (n m n' m' : Int) :
    (I.thetaPacketLinkLedgerAt n' m' n m).q_transport =
      (I.thetaPacketLinkLedgerAt n m n' m').q_transport.symm := by
  exact Subsingleton.elim _ _

theorem thetaPacketLinkLedgerAt_trans (n m n' m' n'' m'' : Int) :
    (I.thetaPacketLinkLedgerAt n m n' m').q_transport.trans
      (I.thetaPacketLinkLedgerAt n' m' n'' m'').q_transport =
      (I.thetaPacketLinkLedgerAt n m n'' m'').q_transport := by
  exact Subsingleton.elim _ _

theorem thetaPacketLinkLedgerAt_horizontal (n m : Int) :
    (I.thetaPacketLinkLedgerAt n m (n + 1) m).q_transport =
      I.horizontal_q n m := by
  exact Subsingleton.elim _ _

theorem thetaPacketLinkLedgerAt_vertical (n m : Int) :
    (I.thetaPacketLinkLedgerAt n m n (m + 1)).q_transport =
      I.vertical_q n m := by
  exact Subsingleton.elim _ _

theorem thetaPacketLinkLedgerAt_translation (a b n m : Int) :
    (I.thetaPacketLinkLedgerAt n m (n + a) (m + b)).q_transport =
      I.translate_q a b n m := by
  exact Subsingleton.elim _ _

/-! ## 3. Family-level packet ledger -/

structure ThetaPacketFamilyLedger where
  packet : I.family.index -> FiniteThetaPacket l
  packet_source : ∀ i, packet i = (I.family.theater i).thetaPacket
  q_transport : ∀ i j, (packet i).q = (packet j).q
  scale_transport : ∀ i j x, (packet i).scale x = (packet j).scale x
  log_volume_transport : ∀ i j,
    (packet i).logVolume = (packet j).logVolume
  permutation_q : ∀ i, (packet (I.family.permutation i)).q = (packet i).q
  permutation_scale : ∀ i x,
    (packet (I.family.permutation i)).scale x = (packet i).scale x
  permutation_log_volume : ∀ i,
    (packet (I.family.permutation i)).logVolume = (packet i).logVolume

def thetaPacketFamilyLedger : I.ThetaPacketFamilyLedger where
  packet := fun i => (I.family.theater i).thetaPacket
  packet_source := by intro i; rfl
  q_transport := by
    intro i j
    exact I.family_link_q i j
  scale_transport := by
    intro i j x
    exact I.family_link_scale i j x
  log_volume_transport := by
    intro i j
    exact (I.family.link i j).log_volume_eq
  permutation_q := by
    intro i
    exact I.family_permutation_q i
  permutation_scale := by
    intro i x
    exact I.family_permutation_scale i x
  permutation_log_volume := by
    intro i
    exact (I.family.permutationLink i).log_volume_eq

@[simp] theorem thetaPacketFamilyLedger_packet (i : I.family.index) :
    (I.thetaPacketFamilyLedger).packet i =
      (I.family.theater i).thetaPacket := rfl

theorem thetaPacketFamilyLedger_q (i j : I.family.index) :
    ((I.thetaPacketFamilyLedger).packet i).q =
      ((I.thetaPacketFamilyLedger).packet j).q :=
  (I.thetaPacketFamilyLedger).q_transport i j

theorem thetaPacketFamilyLedger_scale (i j : I.family.index)
    (x : SignedLabel l.value) :
    ((I.thetaPacketFamilyLedger).packet i).scale x =
      ((I.thetaPacketFamilyLedger).packet j).scale x :=
  (I.thetaPacketFamilyLedger).scale_transport i j x

theorem thetaPacketFamilyLedger_log_volume (i j : I.family.index) :
    ((I.thetaPacketFamilyLedger).packet i).logVolume =
      ((I.thetaPacketFamilyLedger).packet j).logVolume :=
  (I.thetaPacketFamilyLedger).log_volume_transport i j

theorem thetaPacketFamilyLedger_permutation_q (i : I.family.index) :
    ((I.thetaPacketFamilyLedger).packet (I.family.permutation i)).q =
      ((I.thetaPacketFamilyLedger).packet i).q :=
  (I.thetaPacketFamilyLedger).permutation_q i

theorem thetaPacketFamilyLedger_permutation_scale (i : I.family.index)
    (x : SignedLabel l.value) :
    ((I.thetaPacketFamilyLedger).packet (I.family.permutation i)).scale x =
      ((I.thetaPacketFamilyLedger).packet i).scale x :=
  (I.thetaPacketFamilyLedger).permutation_scale i x

theorem thetaPacketFamilyLedger_permutation_log_volume (i : I.family.index) :
    ((I.thetaPacketFamilyLedger).packet (I.family.permutation i)).logVolume =
      ((I.thetaPacketFamilyLedger).packet i).logVolume :=
  (I.thetaPacketFamilyLedger).permutation_log_volume i

/-! ## 4. A local F/D prime-strip degree ledger -/

structure PrimeStripDegreeLedger (n m : Int) where
  fStrip : FPrimeStrip.{umon, uv, upi} V
  dStrip : DPrimeStrip.{upi, uv} V
  f_source : fStrip = I.primeStripAt n m
  d_source : dStrip = I.dPrimeStripAt n m
  fd_projection : dStrip = fStrip.toD
  action_mul : ∀ v (g h : fStrip.toD.Pi v) (x : fStrip.Mon v),
    fStrip.action v (g * h) x = fStrip.action v g (fStrip.action v h x)
  action_one : ∀ v (x : fStrip.Mon v), fStrip.action v 1 x = x
  degree_one : ∀ v, fStrip.degree v 1 = 1
  degree_mul : ∀ v (x y : fStrip.Mon v),
    fStrip.degree v (x * y) = fStrip.degree v x * fStrip.degree v y
  total_degree_mul : ∀ (s : Finset V) (x y : ∀ v, fStrip.Mon v),
    fStrip.totalDegree s (fun v => x v * y v) =
      fStrip.totalDegree s x + fStrip.totalDegree s y
  total_degree_one : ∀ (s : Finset V),
    fStrip.totalDegree s (fun _ => 1) = 0

def primeStripDegreeLedgerAt (n m : Int) : I.PrimeStripDegreeLedger n m where
  fStrip := I.primeStripAt n m
  dStrip := I.dPrimeStripAt n m
  f_source := rfl
  d_source := rfl
  fd_projection := rfl
  action_mul := by
    intro v g h x
    exact (I.primeStripAt n m).action_mul v g h x
  action_one := by
    intro v x
    exact (I.primeStripAt n m).action_one v x
  degree_one := by
    intro v
    exact (I.primeStripAt n m).degree v |>.map_one
  degree_mul := by
    intro v x y
    exact (I.primeStripAt n m).degree v |>.map_mul x y
  total_degree_mul := by
    intro s x y
    exact (I.primeStripAt n m).totalDegree_mul s x y
  total_degree_one := by
    intro s
    exact (I.primeStripAt n m).totalDegree_one s

@[simp] theorem primeStripDegreeLedgerAt_fStrip (n m : Int) :
    (I.primeStripDegreeLedgerAt n m).fStrip = I.primeStripAt n m := rfl

@[simp] theorem primeStripDegreeLedgerAt_dStrip (n m : Int) :
    (I.primeStripDegreeLedgerAt n m).dStrip = I.dPrimeStripAt n m := rfl

theorem primeStripDegreeLedgerAt_toD (n m : Int) :
    (I.primeStripDegreeLedgerAt n m).dStrip =
      (I.primeStripDegreeLedgerAt n m).fStrip.toD :=
  (I.primeStripDegreeLedgerAt n m).fd_projection

theorem primeStripDegreeLedgerAt_action_mul (n m : Int)
    (v : V) (g h : (I.primeStripDegreeLedgerAt n m).fStrip.toD.Pi v)
    (x : (I.primeStripDegreeLedgerAt n m).fStrip.Mon v) :
    (I.primeStripDegreeLedgerAt n m).fStrip.action v (g * h) x =
      (I.primeStripDegreeLedgerAt n m).fStrip.action v g
        ((I.primeStripDegreeLedgerAt n m).fStrip.action v h x) :=
  (I.primeStripDegreeLedgerAt n m).action_mul v g h x

theorem primeStripDegreeLedgerAt_action_one (n m : Int)
    (v : V) (x : (I.primeStripDegreeLedgerAt n m).fStrip.Mon v) :
    (I.primeStripDegreeLedgerAt n m).fStrip.action v 1 x = x :=
  (I.primeStripDegreeLedgerAt n m).action_one v x

theorem primeStripDegreeLedgerAt_degree_one (n m : Int) (v : V) :
    (I.primeStripDegreeLedgerAt n m).fStrip.degree v 1 = 1 :=
  (I.primeStripDegreeLedgerAt n m).degree_one v

theorem primeStripDegreeLedgerAt_degree_mul (n m : Int) (v : V)
    (x y : (I.primeStripDegreeLedgerAt n m).fStrip.Mon v) :
    (I.primeStripDegreeLedgerAt n m).fStrip.degree v (x * y) =
      (I.primeStripDegreeLedgerAt n m).fStrip.degree v x *
        (I.primeStripDegreeLedgerAt n m).fStrip.degree v y :=
  (I.primeStripDegreeLedgerAt n m).degree_mul v x y

theorem primeStripDegreeLedgerAt_total_degree_mul (n m : Int)
    (s : Finset V)
    (x y : ∀ v, (I.primeStripDegreeLedgerAt n m).fStrip.Mon v) :
    (I.primeStripDegreeLedgerAt n m).fStrip.totalDegree s
        (fun v => x v * y v) =
      (I.primeStripDegreeLedgerAt n m).fStrip.totalDegree s x +
        (I.primeStripDegreeLedgerAt n m).fStrip.totalDegree s y :=
  (I.primeStripDegreeLedgerAt n m).total_degree_mul s x y

theorem primeStripDegreeLedgerAt_total_degree_one (n m : Int)
    (s : Finset V) :
    (I.primeStripDegreeLedgerAt n m).fStrip.totalDegree s
        (fun _ => 1) = 0 :=
  (I.primeStripDegreeLedgerAt n m).total_degree_one s

theorem primeStripDegreeLedgerAt_degree_transport (n m n' m' : Int)
    (v : V) (x : (I.primeStripDegreeLedgerAt n m).fStrip.Mon v) :
    (I.primeStripDegreeLedgerAt n' m').fStrip.degree v
        ((I.primeStripLinkAt n m n' m').isoMon v x) =
      (I.primeStripDegreeLedgerAt n m).fStrip.degree v x := by
  exact I.primeStripLinkAt_compatDegree n m n' m' v x

theorem primeStripDegreeLedgerAt_action_transport (n m n' m' : Int)
    (v : V) (g : (I.primeStripDegreeLedgerAt n m).fStrip.toD.Pi v)
    (x : (I.primeStripDegreeLedgerAt n m).fStrip.Mon v) :
    (I.primeStripLinkAt n m n' m').isoMon v
        ((I.primeStripDegreeLedgerAt n m).fStrip.action v g x) =
      (I.primeStripDegreeLedgerAt n' m').fStrip.action v
        ((I.primeStripLinkAt n m n' m').isoPi v g)
        ((I.primeStripLinkAt n m n' m').isoMon v x) := by
  exact I.primeStripLinkAt_compatAction n m n' m' v g x

theorem primeStripDegreeLedgerAt_total_degree_transport
    (n m n' m' : Int) (s : Finset V)
    (x : ∀ v, (I.primeStripDegreeLedgerAt n m).fStrip.Mon v) :
    (I.primeStripDegreeLedgerAt n' m').fStrip.totalDegree s
        (fun v => (I.primeStripLinkAt n m n' m').isoMon v (x v)) =
      (I.primeStripDegreeLedgerAt n m).fStrip.totalDegree s x := by
  apply Finset.sum_congr rfl
  intro v hv
  exact I.primeStripDegreeLedgerAt_degree_transport n m n' m' v (x v)

/-! ## 5. Link-level degree/action ledger -/

structure PrimeStripLinkDegreeLedger (n m n' m' : Int) where
  source : I.PrimeStripDegreeLedger n m
  target : I.PrimeStripDegreeLedger n' m'
  link : FPrimeStripEquiv source.fStrip target.fStrip
  dLink : DPrimeStripEquiv source.dStrip target.dStrip
  link_source : HEq link (I.primeStripLinkAt n m n' m')
  dLink_source : HEq dLink (I.dPrimeStripLinkAt n m n' m')
  projection : ∀ v (x : source.fStrip.toD.Pi v),
    target.fStrip.proj v (link.isoPi v x) =
      link.isoG v (source.fStrip.proj v x)
  action : ∀ v (g : source.fStrip.toD.Pi v) (x : source.fStrip.Mon v),
    link.isoMon v (source.fStrip.action v g x) =
      target.fStrip.action v (link.isoPi v g) (link.isoMon v x)
  degree : ∀ v (x : source.fStrip.Mon v),
    target.fStrip.degree v (link.isoMon v x) = source.fStrip.degree v x
  total_degree : ∀ (s : Finset V)
      (x : ∀ v, source.fStrip.Mon v),
    target.fStrip.totalDegree s (fun v => link.isoMon v (x v)) =
      source.fStrip.totalDegree s x

def primeStripLinkDegreeLedgerAt (n m n' m' : Int) :
    PrimeStripLinkDegreeLedger (I := I) n m n' m' where
  source := I.primeStripDegreeLedgerAt n m
  target := I.primeStripDegreeLedgerAt n' m'
  link := I.primeStripLinkAt n m n' m'
  dLink := I.dPrimeStripLinkAt n m n' m'
  link_source := by rfl
  dLink_source := by rfl
  projection := by
    intro v x
    exact I.primeStripLinkAt_compatProj n m n' m' v x
  action := by
    intro v g x
    exact (I.primeStripLinkAt_compatAction n m n' m' v g x)
  degree := by
    intro v x
    exact I.primeStripLinkAt_compatDegree n m n' m' v x
  total_degree := by
    intro s x
    exact I.primeStripDegreeLedgerAt_total_degree_transport n m n' m' s x

@[simp] theorem primeStripLinkDegreeLedgerAt_source (n m n' m' : Int) :
    (I.primeStripLinkDegreeLedgerAt n m n' m').source =
      I.primeStripDegreeLedgerAt n m := rfl

@[simp] theorem primeStripLinkDegreeLedgerAt_target (n m n' m' : Int) :
    (I.primeStripLinkDegreeLedgerAt n m n' m').target =
      I.primeStripDegreeLedgerAt n' m' := rfl

@[simp] theorem primeStripLinkDegreeLedgerAt_link (n m n' m' : Int) :
    (I.primeStripLinkDegreeLedgerAt n m n' m').link =
      I.primeStripLinkAt n m n' m' := rfl

@[simp] theorem primeStripLinkDegreeLedgerAt_dLink (n m n' m' : Int) :
    (I.primeStripLinkDegreeLedgerAt n m n' m').dLink =
      I.dPrimeStripLinkAt n m n' m' := rfl

theorem primeStripLinkDegreeLedgerAt_projection (n m n' m' : Int)
    (v : V) (x : (I.primeStripDegreeLedgerAt n m).fStrip.toD.Pi v) :
    (I.primeStripDegreeLedgerAt n' m').fStrip.proj v
        ((I.primeStripLinkAt n m n' m').isoPi v x) =
      (I.primeStripLinkAt n m n' m').isoG v
        ((I.primeStripDegreeLedgerAt n m).fStrip.proj v x) :=
  (I.primeStripLinkDegreeLedgerAt n m n' m').projection v x

theorem primeStripLinkDegreeLedgerAt_action (n m n' m' : Int)
    (v : V) (g : (I.primeStripDegreeLedgerAt n m).fStrip.toD.Pi v)
    (x : (I.primeStripDegreeLedgerAt n m).fStrip.Mon v) :
    (I.primeStripLinkAt n m n' m').isoMon v
        ((I.primeStripDegreeLedgerAt n m).fStrip.action v g x) =
      (I.primeStripDegreeLedgerAt n' m').fStrip.action v
        ((I.primeStripLinkAt n m n' m').isoPi v g)
        ((I.primeStripLinkAt n m n' m').isoMon v x) :=
  (I.primeStripLinkDegreeLedgerAt n m n' m').action v g x

theorem primeStripLinkDegreeLedgerAt_degree (n m n' m' : Int)
    (v : V) (x : (I.primeStripDegreeLedgerAt n m).fStrip.Mon v) :
    (I.primeStripDegreeLedgerAt n' m').fStrip.degree v
        ((I.primeStripLinkAt n m n' m').isoMon v x) =
      (I.primeStripDegreeLedgerAt n m).fStrip.degree v x :=
  (I.primeStripLinkDegreeLedgerAt n m n' m').degree v x

theorem primeStripLinkDegreeLedgerAt_total_degree
    (n m n' m' : Int) (s : Finset V)
    (x : ∀ v, (I.primeStripDegreeLedgerAt n m).fStrip.Mon v) :
    (I.primeStripDegreeLedgerAt n' m').fStrip.totalDegree s
        (fun v => (I.primeStripLinkAt n m n' m').isoMon v (x v)) =
      (I.primeStripDegreeLedgerAt n m).fStrip.totalDegree s x :=
  (I.primeStripLinkDegreeLedgerAt n m n' m').total_degree s x

theorem primeStripLinkDegreeLedgerAt_refl (n m : Int) :
    (I.primeStripLinkDegreeLedgerAt n m n m).link =
      FPrimeStripEquiv.refl
        (I.primeStripDegreeLedgerAt n m).fStrip := by
  exact I.primeStripLinkAt_refl n m

theorem primeStripLinkDegreeLedgerAt_symm (n m n' m' : Int) :
    FPrimeStripEquiv.symm
        (I.primeStripLinkDegreeLedgerAt n m n' m').link =
      (I.primeStripLinkDegreeLedgerAt n' m' n m).link := by
  exact I.primeStripLinkAt_symm n m n' m'

theorem primeStripLinkDegreeLedgerAt_trans
    (n m n' m' n'' m'' : Int) :
    FPrimeStripEquiv.trans
        (I.primeStripLinkDegreeLedgerAt n m n' m').link
        (I.primeStripLinkDegreeLedgerAt n' m' n'' m'').link =
      (I.primeStripLinkDegreeLedgerAt n m n'' m'').link := by
  exact I.primeStripLinkAt_trans n m n' m' n'' m''

/-! ## 6. F/D finite-stage packet ledger -/

structure ColumnPacketDegreeLedger (n : Int) (k : Nat) where
  fd_stage : ((I.columnFProcession n).stage k).toD =
    (I.columnDProcession n).stage k
  packet : Fin (k + 1) → FiniteThetaPacket l
  packet_source : ∀ i,
    packet i = (I.theaterAt n (i.1 : Int)).thetaPacket
  q_positive : ∀ i, 0 < (packet i).q
  scale_positive : ∀ i j, 0 < (packet i).scale j
  scale_nonzero : ∀ i j, (packet i).scale j ≠ 0
  log_volume : ∀ i,
    (packet i).logVolume =
      ∑ j : SignedLabel l.value, Real.log ((packet i).scale j)
  source_injective : Function.Injective
    ((I.columnFProcession n).stage k).source
  inclusion_map_injective : ∀ {r : Nat} (h : k ≤ r),
    Function.Injective ((I.columnFProcession n).inclusion h).map
  inclusion_packet : ∀ {r : Nat} (h : k ≤ r) (i : Fin (k + 1)),
    packet i = (I.theaterAt n (((I.columnFProcession n).inclusion h).map i).1).thetaPacket

def columnPacketDegreeLedger (n : Int) (k : Nat) :
    ColumnPacketDegreeLedger (I := I) n k where
  fd_stage := by rfl
  packet := fun i => (I.theaterAt n (i.1 : Int)).thetaPacket
  packet_source := by intro i; rfl
  q_positive := by
    intro i
    exact (I.theaterAt n (i.1 : Int)).thetaPacket.q_pos
  scale_positive := by
    intro i j
    exact (I.theaterAt n (i.1 : Int)).thetaPacket.scale_pos j
  scale_nonzero := by
    intro i j
    exact (I.theaterAt n (i.1 : Int)).thetaPacket.scale_ne_zero j
  log_volume := by
    intro i
    exact (I.theaterAt n (i.1 : Int)).thetaPacket.logVolume_eq_sum
  source_injective := by
    exact (I.columnFProcession n).stage k |>.source_injective
  inclusion_map_injective := by
    intro r h
    exact (I.columnFProcession n).inclusion h |>.map_injective
  inclusion_packet := by
    intro r h i
    rfl

@[simp] theorem columnPacketDegreeLedger_packet (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.columnPacketDegreeLedger n k).packet i =
      (I.theaterAt n (i.1 : Int)).thetaPacket := rfl

theorem columnPacketDegreeLedger_fd_stage (n : Int) (k : Nat) :
    ((I.columnFProcession n).stage k).toD =
      (I.columnDProcession n).stage k :=
  (I.columnPacketDegreeLedger n k).fd_stage

theorem columnPacketDegreeLedger_q_positive (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    0 < ((I.columnPacketDegreeLedger n k).packet i).q :=
  (I.columnPacketDegreeLedger n k).q_positive i

theorem columnPacketDegreeLedger_scale_positive (n : Int) (k : Nat)
    (i : Fin (k + 1)) (j : SignedLabel l.value) :
    0 < ((I.columnPacketDegreeLedger n k).packet i).scale j :=
  (I.columnPacketDegreeLedger n k).scale_positive i j

theorem columnPacketDegreeLedger_log_volume (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    ((I.columnPacketDegreeLedger n k).packet i).logVolume =
      ∑ j : SignedLabel l.value,
        Real.log (((I.columnPacketDegreeLedger n k).packet i).scale j) :=
  (I.columnPacketDegreeLedger n k).log_volume i

/-! ## 7. Complete F/D column-stage ledger -/

structure ColumnStageSourceLedger (n : Int) (k : Nat) where
  fStage : FStageCapsule I k
  dStage : DStageCapsule I k
  fd_stage : fStage.toD = dStage
  source : Fin (k + 1) → I.family.index
  source_f : ∀ i, source i = I.indexOf n (i.1 : Int)
  source_d : ∀ i, source i = I.indexOf n (i.1 : Int)
  source_injective : Function.Injective source
  packet : Fin (k + 1) → FiniteThetaPacket l
  packet_source : ∀ i,
    packet i = (I.family.theater (source i)).thetaPacket
  q_transport : ∀ i j, (packet i).q = (packet j).q
  scale_transport : ∀ i j x,
    (packet i).scale x = (packet j).scale x
  log_volume_transport : ∀ i j,
    (packet i).logVolume = (packet j).logVolume
  fLink : ∀ i j, FPrimeStripEquiv (fStage.strip i) (fStage.strip j)
  dLink : ∀ i j, DPrimeStripEquiv (dStage.strip i) (dStage.strip j)
  fLink_source : ∀ i j,
    HEq (fLink i j) ((I.family.link (source i) (source j)).primeStripEquiv)
  dLink_source : ∀ i j,
    HEq (dLink i j) ((I.family.link (source i) (source j)).primeStripEquiv.toD)
  fLink_action : ∀ i j v g x,
    (fLink i j).isoMon v ((fStage.strip i).action v g x) =
      (fStage.strip j).action v ((fLink i j).isoPi v g)
        ((fLink i j).isoMon v x)
  fLink_degree : ∀ i j v x,
    (fStage.strip j).degree v ((fLink i j).isoMon v x) =
      (fStage.strip i).degree v x
  fLink_total_degree : ∀ i j s x,
    (fStage.strip j).totalDegree s
        (fun v => (fLink i j).isoMon v (x v)) =
      (fStage.strip i).totalDegree s x
  dLink_projection : ∀ i j v x,
    (dStage.strip j).proj v ((dLink i j).isoPi v x) =
      (dLink i j).isoG v ((dStage.strip i).proj v x)

def columnStageSourceLedger (n : Int) (k : Nat) :
    I.ColumnStageSourceLedger n k where
  fStage := I.columnFStage n k
  dStage := I.columnDStage n k
  fd_stage := by rfl
  source := I.columnSource n k
  source_f := by intro i; rfl
  source_d := by intro i; rfl
  source_injective := I.columnSource_injective n k
  packet := fun i => (I.family.theater (I.columnSource n k i)).thetaPacket
  packet_source := by intro i; rfl
  q_transport := by
    intro i j
    exact I.family_link_q (I.columnSource n k i) (I.columnSource n k j)
  scale_transport := by
    intro i j x
    exact I.family_link_scale (I.columnSource n k i) (I.columnSource n k j) x
  log_volume_transport := by
    intro i j
    exact (I.family.link (I.columnSource n k i)
      (I.columnSource n k j)).log_volume_eq
  fLink := fun i j => (I.columnFStage n k).link i j
  dLink := fun i j => (I.columnDStage n k).link i j
  fLink_source := by intro i j; exact heq_of_eq rfl
  dLink_source := by intro i j; exact heq_of_eq rfl
  fLink_action := by
    intro i j v g x
    exact ((I.columnFStage n k).link i j).compatAction v g x
  fLink_degree := by
    intro i j v x
    exact ((I.columnFStage n k).link i j).compatDegree v x
  fLink_total_degree := by
    intro i j s x
    apply Finset.sum_congr rfl
    intro v hv
    exact ((I.columnFStage n k).link i j).compatDegree v (x v)
  dLink_projection := by
    intro i j v x
    exact ((I.columnDStage n k).link i j).compat_apply v x

@[simp] theorem columnStageSourceLedger_fStage (n : Int) (k : Nat) :
    (I.columnStageSourceLedger n k).fStage = I.columnFStage n k := rfl

@[simp] theorem columnStageSourceLedger_dStage (n : Int) (k : Nat) :
    (I.columnStageSourceLedger n k).dStage = I.columnDStage n k := rfl

@[simp] theorem columnStageSourceLedger_source (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.columnStageSourceLedger n k).source i = I.indexOf n (i.1 : Int) := rfl

@[simp] theorem columnStageSourceLedger_packet (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.columnStageSourceLedger n k).packet i =
      (I.theaterAt n (i.1 : Int)).thetaPacket := rfl

theorem columnStageSourceLedger_fd_stage (n : Int) (k : Nat) :
    (I.columnStageSourceLedger n k).fStage.toD =
      (I.columnStageSourceLedger n k).dStage :=
  (I.columnStageSourceLedger n k).fd_stage

theorem columnStageSourceLedger_source_injective (n : Int) (k : Nat) :
    Function.Injective (I.columnStageSourceLedger n k).source :=
  (I.columnStageSourceLedger n k).source_injective

theorem columnStageSourceLedger_q_transport (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    ((I.columnStageSourceLedger n k).packet i).q =
      ((I.columnStageSourceLedger n k).packet j).q :=
  (I.columnStageSourceLedger n k).q_transport i j

theorem columnStageSourceLedger_scale_transport (n : Int) (k : Nat)
    (i j : Fin (k + 1)) (x : SignedLabel l.value) :
    ((I.columnStageSourceLedger n k).packet i).scale x =
      ((I.columnStageSourceLedger n k).packet j).scale x :=
  (I.columnStageSourceLedger n k).scale_transport i j x

theorem columnStageSourceLedger_log_volume_transport (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    ((I.columnStageSourceLedger n k).packet i).logVolume =
      ((I.columnStageSourceLedger n k).packet j).logVolume :=
  (I.columnStageSourceLedger n k).log_volume_transport i j

theorem columnStageSourceLedger_fLink_action (n : Int) (k : Nat)
    (i j : Fin (k + 1)) (v : V)
    (g : ((I.columnStageSourceLedger n k).fStage.strip i).toD.Pi v)
    (x : ((I.columnStageSourceLedger n k).fStage.strip i).Mon v) :
    ((I.columnStageSourceLedger n k).fLink i j).isoMon v
        (((I.columnStageSourceLedger n k).fStage.strip i).action v g x) =
      ((I.columnStageSourceLedger n k).fStage.strip j).action v
        (((I.columnStageSourceLedger n k).fLink i j).isoPi v g)
        (((I.columnStageSourceLedger n k).fLink i j).isoMon v x) :=
  (I.columnStageSourceLedger n k).fLink_action i j v g x

theorem columnStageSourceLedger_fLink_degree (n : Int) (k : Nat)
    (i j : Fin (k + 1)) (v : V)
    (x : ((I.columnStageSourceLedger n k).fStage.strip i).Mon v) :
    ((I.columnStageSourceLedger n k).fStage.strip j).degree v
        (((I.columnStageSourceLedger n k).fLink i j).isoMon v x) =
      ((I.columnStageSourceLedger n k).fStage.strip i).degree v x :=
  (I.columnStageSourceLedger n k).fLink_degree i j v x

theorem columnStageSourceLedger_fLink_total_degree (n : Int) (k : Nat)
    (i j : Fin (k + 1)) (s : Finset V)
    (x : ∀ v, ((I.columnStageSourceLedger n k).fStage.strip i).Mon v) :
    ((I.columnStageSourceLedger n k).fStage.strip j).totalDegree s
        (fun v => ((I.columnStageSourceLedger n k).fLink i j).isoMon v (x v)) =
      ((I.columnStageSourceLedger n k).fStage.strip i).totalDegree s x :=
  (I.columnStageSourceLedger n k).fLink_total_degree i j s x

theorem columnStageSourceLedger_dLink_projection (n : Int) (k : Nat)
    (i j : Fin (k + 1)) (v : V)
    (x : ((I.columnStageSourceLedger n k).dStage.strip i).Pi v) :
    ((I.columnStageSourceLedger n k).dStage.strip j).proj v
        (((I.columnStageSourceLedger n k).dLink i j).isoPi v x) =
      ((I.columnStageSourceLedger n k).dLink i j).isoG v
        (((I.columnStageSourceLedger n k).dStage.strip i).proj v x) :=
  (I.columnStageSourceLedger n k).dLink_projection i j v x

theorem columnStageSourceLedger_fLink_refl (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.columnStageSourceLedger n k).fLink i i =
      FPrimeStripEquiv.refl
        ((I.columnStageSourceLedger n k).fStage.strip i) := by
  exact FStageCapsule.link_refl _ i

theorem columnStageSourceLedger_fLink_symm (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    FPrimeStripEquiv.symm
        ((I.columnStageSourceLedger n k).fLink i j) =
      (I.columnStageSourceLedger n k).fLink j i := by
  exact FStageCapsule.link_symm _ i j

theorem columnStageSourceLedger_fLink_trans (n : Int) (k : Nat)
    (i j h : Fin (k + 1)) :
    FPrimeStripEquiv.trans
        ((I.columnStageSourceLedger n k).fLink i j)
        ((I.columnStageSourceLedger n k).fLink j h) =
      (I.columnStageSourceLedger n k).fLink i h := by
  exact FStageCapsule.link_trans _ i j h

theorem columnStageSourceLedger_dLink_refl (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.columnStageSourceLedger n k).dLink i i =
      DPrimeStripEquiv.refl
        ((I.columnStageSourceLedger n k).dStage.strip i) := by
  exact DStageCapsule.link_refl _ i

theorem columnStageSourceLedger_dLink_symm (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    DPrimeStripEquiv.symm
        ((I.columnStageSourceLedger n k).dLink i j) =
      (I.columnStageSourceLedger n k).dLink j i := by
  exact DStageCapsule.link_symm _ i j

theorem columnStageSourceLedger_dLink_trans (n : Int) (k : Nat)
    (i j h : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        ((I.columnStageSourceLedger n k).dLink i j)
        ((I.columnStageSourceLedger n k).dLink j h) =
      (I.columnStageSourceLedger n k).dLink i h := by
  exact DStageCapsule.link_trans _ i j h

structure ColumnProcessionSourceLedger (n : Int) where
  stage : ∀ k, I.ColumnStageSourceLedger n k
  inclusion_map : ∀ {k r : Nat} (h : k ≤ r), Fin (k + 1) → Fin (r + 1)
  inclusion_injective : ∀ {k r : Nat} (h : k ≤ r),
    Function.Injective (inclusion_map h)
  inclusion_source : ∀ {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)),
    (stage k).source i = (stage r).source (inclusion_map h i)
  inclusion_component : ∀ {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)),
    FPrimeStripEquiv ((stage k).fStage.strip i)
      ((stage r).fStage.strip (inclusion_map h i))
  inclusion_component_source : ∀ {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)),
    HEq (inclusion_component h i)
      ((I.family.link ((stage k).source i)
        ((stage r).source (inclusion_map h i))).primeStripEquiv)
  inclusion_natural : ∀ {k r : Nat} (h : k ≤ r) (i j : Fin (k + 1)),
    FPrimeStripEquiv.trans ((stage k).fLink i j)
        (inclusion_component h j) =
      FPrimeStripEquiv.trans (inclusion_component h i)
        ((stage r).fLink (inclusion_map h i) (inclusion_map h j))
  inclusion_refl : ∀ (k : Nat) (i : Fin (k + 1)),
    inclusion_map (Nat.le_refl k) i = i
  inclusion_trans : ∀ {k r s : Nat} (h₁ : k ≤ r) (h₂ : r ≤ s)
      (i : Fin (k + 1)),
    inclusion_map (Nat.le_trans h₁ h₂) i =
      inclusion_map h₂ (inclusion_map h₁ i)
  inclusion_d_component : ∀ {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)),
    DPrimeStripEquiv ((stage k).dStage.strip i)
      ((stage r).dStage.strip (inclusion_map h i))
  inclusion_d_component_source : ∀ {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)),
    HEq (inclusion_d_component h i)
      ((I.family.link ((stage k).source i)
        ((stage r).source (inclusion_map h i))).primeStripEquiv.toD)
  inclusion_d_natural : ∀ {k r : Nat} (h : k ≤ r) (i j : Fin (k + 1)),
    DPrimeStripEquiv.trans ((stage k).dLink i j)
        (inclusion_d_component h j) =
      DPrimeStripEquiv.trans (inclusion_d_component h i)
        ((stage r).dLink (inclusion_map h i) (inclusion_map h j))

def columnProcessionSourceLedger (n : Int) : I.ColumnProcessionSourceLedger n where
  stage := I.columnStageSourceLedger n
  inclusion_map := fun {_ _} h => finStageMap h
  inclusion_injective := by
    intro k r h
    exact finStageMap_injective h
  inclusion_source := by
    intro k r h i
    rfl
  inclusion_component := by
    intro k r h i
    exact (I.columnFProcession n).inclusion h |>.component i
  inclusion_component_source := by
    intro k r h i
    exact heq_of_eq rfl
  inclusion_natural := by
    intro k r h i j
    exact (I.columnFProcession n).inclusion h |>.naturality i j
  inclusion_refl := by
    intro k i
    exact finStageMap_refl k i
  inclusion_trans := by
    intro k r s h₁ h₂ i
    exact (finStageMap_trans h₁ h₂ i).symm
  inclusion_d_component := by
    intro k r h i
    exact (I.columnDProcession n).inclusion h |>.component i
  inclusion_d_component_source := by
    intro k r h i
    exact heq_of_eq rfl
  inclusion_d_natural := by
    intro k r h i j
    exact (I.columnDProcession n).inclusion h |>.naturality i j

@[simp] theorem columnProcessionSourceLedger_stage (n : Int) (k : Nat) :
    (I.columnProcessionSourceLedger n).stage k =
      I.columnStageSourceLedger n k := rfl

theorem columnProcessionSourceLedger_inclusion_injective (n : Int)
    {k r : Nat} (h : k ≤ r) :
    Function.Injective ((I.columnProcessionSourceLedger n).inclusion_map h) :=
  (I.columnProcessionSourceLedger n).inclusion_injective h

theorem columnProcessionSourceLedger_inclusion_source (n : Int)
    {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)) :
    ((I.columnProcessionSourceLedger n).stage k).source i =
      ((I.columnProcessionSourceLedger n).stage r).source
        ((I.columnProcessionSourceLedger n).inclusion_map h i) :=
  (I.columnProcessionSourceLedger n).inclusion_source h i

theorem columnProcessionSourceLedger_inclusion_natural (n : Int)
    {k r : Nat} (h : k ≤ r) (i j : Fin (k + 1)) :
    FPrimeStripEquiv.trans
        (((I.columnProcessionSourceLedger n).stage k).fLink i j)
        ((I.columnProcessionSourceLedger n).inclusion_component h j) =
      FPrimeStripEquiv.trans
        ((I.columnProcessionSourceLedger n).inclusion_component h i)
        (((I.columnProcessionSourceLedger n).stage r).fLink
          ((I.columnProcessionSourceLedger n).inclusion_map h i)
          ((I.columnProcessionSourceLedger n).inclusion_map h j)) :=
  (I.columnProcessionSourceLedger n).inclusion_natural h i j

theorem columnProcessionSourceLedger_inclusion_action (n : Int)
    {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)) (v : V)
    (g : (((I.columnProcessionSourceLedger n).stage k).fStage.strip i).toD.Pi v)
    (x : (((I.columnProcessionSourceLedger n).stage k).fStage.strip i).Mon v) :
    ((I.columnProcessionSourceLedger n).inclusion_component h i).isoMon v
        ((((I.columnProcessionSourceLedger n).stage k).fStage.strip i).action v g x) =
      (((I.columnProcessionSourceLedger n).stage r).fStage.strip
        ((I.columnProcessionSourceLedger n).inclusion_map h i)).action v
        ((I.columnProcessionSourceLedger n).inclusion_component h i).isoPi v g
        ((I.columnProcessionSourceLedger n).inclusion_component h i).isoMon v x :=
  ((I.columnProcessionSourceLedger n).stage k).fLink_action i
    ((I.columnProcessionSourceLedger n).inclusion_map h i) v g x

theorem columnProcessionSourceLedger_inclusion_degree (n : Int)
    {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)) (v : V)
    (x : (((I.columnProcessionSourceLedger n).stage k).fStage.strip i).Mon v) :
    (((I.columnProcessionSourceLedger n).stage r).fStage.strip
      ((I.columnProcessionSourceLedger n).inclusion_map h i)).degree v
        (((I.columnProcessionSourceLedger n).inclusion_component h i).isoMon v x) =
      (((I.columnProcessionSourceLedger n).stage k).fStage.strip i).degree v x :=
  ((I.columnProcessionSourceLedger n).stage k).fLink_degree i
    ((I.columnProcessionSourceLedger n).inclusion_map h i) v x

theorem columnProcessionSourceLedger_inclusion_d_natural (n : Int)
    {k r : Nat} (h : k ≤ r) (i j : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        (((I.columnProcessionSourceLedger n).stage k).dLink i j)
        ((I.columnProcessionSourceLedger n).inclusion_d_component h j) =
      DPrimeStripEquiv.trans
        ((I.columnProcessionSourceLedger n).inclusion_d_component h i)
        (((I.columnProcessionSourceLedger n).stage r).dLink
          ((I.columnProcessionSourceLedger n).inclusion_map h i)
          ((I.columnProcessionSourceLedger n).inclusion_map h j)) :=
  (I.columnProcessionSourceLedger n).inclusion_d_natural h i j

theorem columnProcessionSourceLedger_inclusion_total_degree (n : Int)
    {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)) (s : Finset V)
    (x : ∀ v, (((I.columnProcessionSourceLedger n).stage k).fStage.strip i).Mon v) :
    (((I.columnProcessionSourceLedger n).stage r).fStage.strip
      ((I.columnProcessionSourceLedger n).inclusion_map h i)).totalDegree s
        (fun v => ((I.columnProcessionSourceLedger n).inclusion_component h i).isoMon v
          (x v)) =
      (((I.columnProcessionSourceLedger n).stage k).fStage.strip i).totalDegree s x := by
  apply Finset.sum_congr rfl
  intro v hv
  exact ((I.columnProcessionSourceLedger n).inclusion_component h i).compatDegree v (x v)

/-! ## 9.2 Translation groupoid laws -/

theorem translatedColumnSourceLedger_zero (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.translatedColumnSourceLedger 0 n k).component i =
      FPrimeStripEquiv.refl
        ((I.translatedColumnSourceLedger 0 n k).base.fStage.strip i) := by
  change I.fLinkAt n (i.1 : Int) (n + 0) (i.1 : Int) = _
  simpa using I.fLinkAt_refl n (i.1 : Int)

theorem translatedColumnSourceLedger_add (a c n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    FPrimeStripEquiv.trans
        ((I.translatedColumnSourceLedger a n k).component i)
        ((I.translatedColumnSourceLedger c (n + a) k).component i) =
      (I.translatedColumnSourceLedger (a + c) n k).component i := by
  change FPrimeStripEquiv.trans
      (I.fLinkAt n (i.1 : Int) (n + a) (i.1 : Int))
      (I.fLinkAt (n + a) (i.1 : Int) (n + a + c) (i.1 : Int)) =
    I.fLinkAt n (i.1 : Int) (n + (a + c)) (i.1 : Int)
  rw [I.fLinkAt_trans]
  congr 2 <;> omega

theorem translatedColumnSourceLedger_inverse (a n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    FPrimeStripEquiv.trans
        ((I.translatedColumnSourceLedger a n k).component i)
        ((I.translatedColumnSourceLedger (-a) (n + a) k).component i) =
      (I.translatedColumnSourceLedger 0 n k).component i := by
  rw [I.translatedColumnSourceLedger_add]
  have ha : a + (-a) = (0 : Int) := by omega
  rw [ha]
  rfl

theorem translatedColumnSourceLedger_projection (a n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (x : ((I.translatedColumnSourceLedger a n k).base.fStage.strip i).toD.Pi v) :
    ((I.translatedColumnSourceLedger a n k).target.fStage.strip i).proj v
        (((I.translatedColumnSourceLedger a n k).component i).isoPi v x) =
      ((I.translatedColumnSourceLedger a n k).component i).isoG v
        (((I.translatedColumnSourceLedger a n k).base.fStage.strip i).proj v x) :=
  ((I.translatedColumnSourceLedger a n k).component i).compatProj_apply v x

theorem translatedColumnSourceLedger_component_bijective
    (a n : Int) (k : Nat) (i : Fin (k + 1)) (v : V) :
    Function.Bijective
      (((I.translatedColumnSourceLedger a n k).component i).isoMon v) := by
  exact ((I.translatedColumnSourceLedger a n k).component i).isoMon v |>.bijective

theorem translatedColumnSourceLedger_total_degree_transport
    (a n : Int) (k : Nat) (i : Fin (k + 1)) (s : Finset V)
    (x : ∀ v, ((I.translatedColumnSourceLedger a n k).base.fStage.strip i).Mon v) :
    ((I.translatedColumnSourceLedger a n k).target.fStage.strip i).totalDegree s
        (fun v => ((I.translatedColumnSourceLedger a n k).component i).isoMon v (x v)) =
      ((I.translatedColumnSourceLedger a n k).base.fStage.strip i).totalDegree s x :=
  (I.translatedColumnSourceLedger a n k).component_total_degree i s x

/-! ## 8. Translation and spoke transport of packet/degree ledgers -/

structure TranslatedColumnSourceLedger (a n : Int) (k : Nat) where
  base : I.ColumnStageSourceLedger n k
  target : I.ColumnStageSourceLedger (n + a) k
  map : Fin (k + 1) ≃ Fin (k + 1)
  map_identity : ∀ i, map i = i
  packet_q : ∀ i, (base.packet i).q = (target.packet (map i)).q
  packet_scale : ∀ i j,
    (base.packet i).scale j = (target.packet (map i)).scale j
  packet_log_volume : ∀ i,
    (base.packet i).logVolume = (target.packet (map i)).logVolume
  component : ∀ i,
    FPrimeStripEquiv (base.fStage.strip i) (target.fStage.strip (map i))
  component_source : ∀ i,
    component i = I.fLinkAt n (i.1 : Int) (n + a) (i.1 : Int)
  component_action : ∀ i v g x,
    (component i).isoMon v (base.fStage.strip i).action v g x =
      (target.fStage.strip (map i)).action v ((component i).isoPi v g)
        ((component i).isoMon v x)
  component_degree : ∀ i v x,
    (target.fStage.strip (map i)).degree v ((component i).isoMon v x) =
      (base.fStage.strip i).degree v x
  component_total_degree : ∀ i s x,
    (target.fStage.strip (map i)).totalDegree s
        (fun v => (component i).isoMon v (x v)) =
      (base.fStage.strip i).totalDegree s x
  naturality : ∀ i j,
    FPrimeStripEquiv.trans (base.fStage.link i j) (component j) =
      FPrimeStripEquiv.trans (component i)
        (target.fStage.link (map i) (map j))

def translatedColumnSourceLedger (a n : Int) (k : Nat) :
    I.TranslatedColumnSourceLedger a n k where
  base := I.columnStageSourceLedger n k
  target := I.columnStageSourceLedger (n + a) k
  map := Equiv.refl _
  map_identity := by intro i; rfl
  packet_q := by
    intro i
    exact I.linkAt_q n (i.1 : Int) (n + a) (i.1 : Int)
  packet_scale := by
    intro i j
    exact I.linkAt_scale n (i.1 : Int) (n + a) (i.1 : Int) j
  packet_log_volume := by
    intro i
    exact (I.linkAt n (i.1 : Int) (n + a) (i.1 : Int)).log_volume_eq
  component := fun i => I.fLinkAt n (i.1 : Int) (n + a) (i.1 : Int)
  component_source := by intro i; rfl
  component_action := by
    intro i v g x
    exact I.fLinkAt_action n (i.1 : Int) (n + a) (i.1 : Int) v g x
  component_degree := by
    intro i v x
    exact I.fLinkAt_degree n (i.1 : Int) (n + a) (i.1 : Int) v x
  component_total_degree := by
    intro i s x
    apply Finset.sum_congr rfl
    intro v hv
    exact I.fLinkAt_degree n (i.1 : Int) (n + a) (i.1 : Int) v (x v)
  naturality := by
    intro i j
    exact I.h2HorizontalFPolyIso n a k |>.naturality i j

@[simp] theorem translatedColumnSourceLedger_map (a n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.translatedColumnSourceLedger a n k).map i = i := rfl

@[simp] theorem translatedColumnSourceLedger_component (a n : Int)
    (k : Nat) (i : Fin (k + 1)) :
    (I.translatedColumnSourceLedger a n k).component i =
      I.fLinkAt n (i.1 : Int) (n + a) (i.1 : Int) := rfl

theorem translatedColumnSourceLedger_q (a n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    ((I.translatedColumnSourceLedger a n k).base.packet i).q =
      ((I.translatedColumnSourceLedger a n k).target.packet i).q := by
  simpa using (I.translatedColumnSourceLedger a n k).packet_q i

theorem translatedColumnSourceLedger_scale (a n : Int) (k : Nat)
    (i : Fin (k + 1)) (j : SignedLabel l.value) :
    ((I.translatedColumnSourceLedger a n k).base.packet i).scale j =
      ((I.translatedColumnSourceLedger a n k).target.packet i).scale j := by
  simpa using (I.translatedColumnSourceLedger a n k).packet_scale i j

theorem translatedColumnSourceLedger_log_volume (a n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    ((I.translatedColumnSourceLedger a n k).base.packet i).logVolume =
      ((I.translatedColumnSourceLedger a n k).target.packet i).logVolume := by
  simpa using (I.translatedColumnSourceLedger a n k).packet_log_volume i

theorem translatedColumnSourceLedger_action (a n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (g : ((I.translatedColumnSourceLedger a n k).base.fStage.strip i).toD.Pi v)
    (x : ((I.translatedColumnSourceLedger a n k).base.fStage.strip i).Mon v) :
    ((I.translatedColumnSourceLedger a n k).component i).isoMon v
        (((I.translatedColumnSourceLedger a n k).base.fStage.strip i).action v g x) =
      ((I.translatedColumnSourceLedger a n k).target.fStage.strip i).action v
        ((I.translatedColumnSourceLedger a n k).component i).isoPi v g
        ((I.translatedColumnSourceLedger a n k).component i).isoMon v x :=
  (I.translatedColumnSourceLedger a n k).component_action i v g x

theorem translatedColumnSourceLedger_degree (a n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (x : ((I.translatedColumnSourceLedger a n k).base.fStage.strip i).Mon v) :
    ((I.translatedColumnSourceLedger a n k).target.fStage.strip i).degree v
        (((I.translatedColumnSourceLedger a n k).component i).isoMon v x) =
      ((I.translatedColumnSourceLedger a n k).base.fStage.strip i).degree v x :=
  (I.translatedColumnSourceLedger a n k).component_degree i v x

theorem translatedColumnSourceLedger_total_degree (a n : Int) (k : Nat)
    (i : Fin (k + 1)) (s : Finset V)
    (x : ∀ v, ((I.translatedColumnSourceLedger a n k).base.fStage.strip i).Mon v) :
    ((I.translatedColumnSourceLedger a n k).target.fStage.strip i).totalDegree s
        (fun v => ((I.translatedColumnSourceLedger a n k).component i).isoMon v (x v)) =
      ((I.translatedColumnSourceLedger a n k).base.fStage.strip i).totalDegree s x :=
  (I.translatedColumnSourceLedger a n k).component_total_degree i s x

theorem translatedColumnSourceLedger_natural (a n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    FPrimeStripEquiv.trans
        ((I.translatedColumnSourceLedger a n k).base.fStage.link i j)
        ((I.translatedColumnSourceLedger a n k).component j) =
      FPrimeStripEquiv.trans
        ((I.translatedColumnSourceLedger a n k).component i)
        ((I.translatedColumnSourceLedger a n k).target.fStage.link i j) :=
  (I.translatedColumnSourceLedger a n k).naturality i j

structure SpokeColumnSourceLedger (P : H2SpokePermutation I)
    (n : Int) (k : Nat) where
  source : I.ColumnStageSourceLedger n k
  target : I.ColumnStageSourceLedger n k
  permutation : Equiv.Perm I.family.index
  map : Fin (k + 1) ≃ Fin (k + 1)
  map_identity : ∀ i, map i = i
  packet_q : ∀ i,
    (I.family.theater (P.permutation (source.source i))).thetaPacket.q =
      (target.packet (map i)).q
  packet_scale : ∀ i j,
    (I.family.theater (P.permutation (source.source i))).thetaPacket.scale j =
      (target.packet (map i)).scale j
  packet_log_volume : ∀ i,
    (I.family.theater (P.permutation (source.source i))).thetaPacket.logVolume =
      (target.packet (map i)).logVolume
  component : ∀ i,
    FPrimeStripEquiv
      ((I.spokeCapsule P source.fStage).strip i)
      (target.fStage.strip (map i))
  component_source : ∀ i,
    component i = P.fSpokeLink (source.source i)
  component_action : ∀ i v g x,
    (component i).isoMon v
        ((I.spokeCapsule P source.fStage).strip i).action v g x =
      (target.fStage.strip (map i)).action v
        ((component i).isoPi v g) ((component i).isoMon v x)
  component_degree : ∀ i v x,
    (target.fStage.strip (map i)).degree v ((component i).isoMon v x) =
      ((I.spokeCapsule P source.fStage).strip i).degree v x
  naturality : ∀ i j,
    FPrimeStripEquiv.trans
        (I.spokeCapsule P source.fStage |>.link i j) (component j) =
      FPrimeStripEquiv.trans (component i)
        (target.fStage.link (map i) (map j))

def spokeColumnSourceLedger (P : H2SpokePermutation I)
    (n : Int) (k : Nat) : I.SpokeColumnSourceLedger P n k where
  source := I.columnStageSourceLedger n k
  target := I.columnStageSourceLedger n k
  permutation := P.permutation
  map := Equiv.refl _
  map_identity := by intro i; rfl
  packet_q := by
    intro i
    exact P.spoke_q (I.columnSource n k i)
  packet_scale := by
    intro i j
    exact P.spoke_scale (I.columnSource n k i) j
  packet_log_volume := by
    intro i
    exact (P.spokeLink (I.columnSource n k i)).log_volume_eq
  component := fun i => P.fSpokeLink (I.columnSource n k i)
  component_source := by intro i; rfl
  component_action := by
    intro i v g x
    exact P.fSpokeLink (I.columnSource n k i) |>.compatAction v g x
  component_degree := by
    intro i v x
    exact P.fSpokeLink (I.columnSource n k i) |>.compatDegree v x
  naturality := by
    intro i j
    exact I.stageSpokePolyIso P (I.columnFStage n k) |>.naturality i j

@[simp] theorem spokeColumnSourceLedger_map (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.spokeColumnSourceLedger P n k).map i = i := rfl

@[simp] theorem spokeColumnSourceLedger_component (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.spokeColumnSourceLedger P n k).component i =
      P.fSpokeLink (I.indexOf n (i.1 : Int)) := rfl

theorem spokeColumnSourceLedger_q (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.family.theater
      (P.permutation ((I.spokeColumnSourceLedger P n k).source.source i))).thetaPacket.q =
      ((I.spokeColumnSourceLedger P n k).target.packet i).q :=
  (I.spokeColumnSourceLedger P n k).packet_q i

theorem spokeColumnSourceLedger_scale (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i : Fin (k + 1)) (j : SignedLabel l.value) :
    (I.family.theater
      (P.permutation ((I.spokeColumnSourceLedger P n k).source.source i))).thetaPacket.scale j =
      ((I.spokeColumnSourceLedger P n k).target.packet i).scale j :=
  (I.spokeColumnSourceLedger P n k).packet_scale i j

theorem spokeColumnSourceLedger_log_volume (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.family.theater
      (P.permutation ((I.spokeColumnSourceLedger P n k).source.source i))).thetaPacket.logVolume =
      ((I.spokeColumnSourceLedger P n k).target.packet i).logVolume :=
  (I.spokeColumnSourceLedger P n k).packet_log_volume i

theorem spokeColumnSourceLedger_action (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i : Fin (k + 1)) (v : V)
    (g : (I.spokeCapsule P
      (I.spokeColumnSourceLedger P n k).source.fStage |>.strip i).toD.Pi v)
    (x : (I.spokeCapsule P
      (I.spokeColumnSourceLedger P n k).source.fStage |>.strip i).Mon v) :
    ((I.spokeColumnSourceLedger P n k).component i).isoMon v
        ((I.spokeCapsule P
          (I.spokeColumnSourceLedger P n k).source.fStage |>.strip i).action v g x) =
      ((I.spokeColumnSourceLedger P n k).target.fStage.strip
        ((I.spokeColumnSourceLedger P n k).map i)).action v
        ((I.spokeColumnSourceLedger P n k).component i).isoPi v g
        ((I.spokeColumnSourceLedger P n k).component i).isoMon v x :=
  (I.spokeColumnSourceLedger P n k).component_action i v g x

theorem spokeColumnSourceLedger_degree (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i : Fin (k + 1)) (v : V)
    (x : (I.spokeCapsule P
      (I.spokeColumnSourceLedger P n k).source.fStage |>.strip i).Mon v) :
    ((I.spokeColumnSourceLedger P n k).target.fStage.strip
      ((I.spokeColumnSourceLedger P n k).map i)).degree v
        (((I.spokeColumnSourceLedger P n k).component i).isoMon v x) =
      (I.spokeCapsule P
        (I.spokeColumnSourceLedger P n k).source.fStage |>.strip i).degree v x :=
  (I.spokeColumnSourceLedger P n k).component_degree i v x

theorem spokeColumnSourceLedger_natural (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i j : Fin (k + 1)) :
    FPrimeStripEquiv.trans
        (I.spokeCapsule P (I.columnFStage n k) |>.link i j)
        ((I.spokeColumnSourceLedger P n k).component j) =
      FPrimeStripEquiv.trans
        ((I.spokeColumnSourceLedger P n k).component i)
        ((I.columnFStage n k).link i j) :=
  (I.spokeColumnSourceLedger P n k).naturality i j

theorem spokeColumnSourceLedger_projection (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i : Fin (k + 1)) (v : V)
    (x : (I.spokeCapsule P (I.columnFStage n k) |>.strip i).toD.Pi v) :
    ((I.columnFStage n k).strip i).proj v
        (((I.spokeColumnSourceLedger P n k).component i).isoPi v x) =
      ((I.spokeColumnSourceLedger P n k).component i).isoG v
        ((I.spokeCapsule P (I.columnFStage n k) |>.strip i).proj v x) :=
  ((I.spokeColumnSourceLedger P n k).component i).compatProj_apply v x

theorem spokeColumnSourceLedger_total_degree_transport
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) (s : Finset V)
    (x : ∀ v, (I.spokeCapsule P (I.columnFStage n k) |>.strip i).Mon v) :
    ((I.columnFStage n k).strip i).totalDegree s
        (fun v => ((I.spokeColumnSourceLedger P n k).component i).isoMon v (x v)) =
      (I.spokeCapsule P (I.columnFStage n k) |>.strip i).totalDegree s x := by
  apply Finset.sum_congr rfl
  intro v hv
  exact (I.spokeColumnSourceLedger P n k).component_degree i v (x v)

theorem spokeColumnSourceLedger_identity (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.spokeColumnSourceLedger (H2SpokePermutation.identity (I := I)) n k).component i =
      FPrimeStripEquiv.refl ((I.columnFStage n k).strip i) := by
  exact I.stageSpoke_identity_component (I.columnFStage n k) i

theorem spokeColumnSourceLedger_comp
    (P Q : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    FPrimeStripEquiv.trans
        ((I.spokeColumnSourceLedger Q n k).component i)
        ((I.spokeColumnSourceLedger P n k).component i) =
      (I.spokeColumnSourceLedger (P.comp Q) n k).component i := by
  exact I.stageSpoke_comp_component Q P (I.columnFStage n k) i

theorem spokeColumnSourceLedger_component_bijective
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V) :
    Function.Bijective
      ((I.spokeColumnSourceLedger P n k).component i |>.isoMon v) := by
  exact ((I.spokeColumnSourceLedger P n k).component i).isoMon v |>.bijective

/-! ## 9. Combined H1/H2 source ledger -/

structure H1H2PacketDegreeLedger (P : H2SpokePermutation I) where
  h1 : I.ThetaPacketFamilyLedger
  h2_column : ∀ n k, I.ColumnStageSourceLedger n k
  h2_procession : ∀ n, I.ColumnProcessionSourceLedger n
  translation : ∀ a n k, I.TranslatedColumnSourceLedger a n k
  spoke : ∀ n k, I.SpokeColumnSourceLedger P n k
  top_cardinality : ∀ n,
    Fintype.card (Fin (lStar l.value + 1)) = lStar l.value + 1
  f_d_stage : ∀ n k,
    ((h2_column n k).fStage).toD = (h2_column n k).dStage
  horizontal_natural : ∀ a n k i j,
    FPrimeStripEquiv.trans
        ((translation a n k).base.fStage.link i j)
        ((translation a n k).component j) =
      FPrimeStripEquiv.trans
        ((translation a n k).component i)
        ((translation a n k).target.fStage.link i j)
  spoke_natural : ∀ n k i j,
    FPrimeStripEquiv.trans
        (I.spokeCapsule P (h2_column n k).fStage |>.link i j)
        ((spoke n k).component j) =
      FPrimeStripEquiv.trans ((spoke n k).component i)
        ((h2_column n k).fStage.link i j)

def h1H2PacketDegreeLedger (P : H2SpokePermutation I) :
    I.H1H2PacketDegreeLedger P where
  h1 := I.thetaPacketFamilyLedger
  h2_column := fun n k => I.columnStageSourceLedger n k
  h2_procession := fun n => I.columnProcessionSourceLedger n
  translation := I.translatedColumnSourceLedger
  spoke := fun n k => I.spokeColumnSourceLedger P n k
  top_cardinality := by intro n; simp
  f_d_stage := by intro n k; rfl
  horizontal_natural := by
    intro a n k i j
    exact I.translatedColumnSourceLedger_natural a n k i j
  spoke_natural := by
    intro n k i j
    exact I.spokeColumnSourceLedger_natural P n k i j

@[simp] theorem h1H2PacketDegreeLedger_h1 (P : H2SpokePermutation I) :
    (I.h1H2PacketDegreeLedger P).h1 = I.thetaPacketFamilyLedger := rfl

theorem h1H2PacketDegreeLedger_top_cardinality (P : H2SpokePermutation I)
    (n : Int) :
    Fintype.card (Fin (lStar l.value + 1)) = lStar l.value + 1 :=
  (I.h1H2PacketDegreeLedger P).top_cardinality n

theorem h1H2PacketDegreeLedger_f_d_stage (P : H2SpokePermutation I)
    (n : Int) (k : Nat) :
    ((I.h1H2PacketDegreeLedger P).h2_column n k).fStage.toD =
      ((I.h1H2PacketDegreeLedger P).h2_column n k).dStage :=
  (I.h1H2PacketDegreeLedger P).f_d_stage n k

theorem h1H2PacketDegreeLedger_horizontal_natural
    (P : H2SpokePermutation I) (a n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    FPrimeStripEquiv.trans
        ((I.h1H2PacketDegreeLedger P).translation a n k).base.fStage.link i j
        ((I.h1H2PacketDegreeLedger P).translation a n k).component j =
      FPrimeStripEquiv.trans
        ((I.h1H2PacketDegreeLedger P).translation a n k).component i
        ((I.h1H2PacketDegreeLedger P).translation a n k).target.fStage.link i j :=
  (I.h1H2PacketDegreeLedger P).horizontal_natural a n k i j

theorem h1H2PacketDegreeLedger_spoke_natural
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    FPrimeStripEquiv.trans
        (I.spokeCapsule P ((I.h1H2PacketDegreeLedger P).h2_column n k).fStage
          |>.link i j)
        ((I.h1H2PacketDegreeLedger P).spoke n k).component j =
      FPrimeStripEquiv.trans
        ((I.h1H2PacketDegreeLedger P).spoke n k).component i
        (((I.h1H2PacketDegreeLedger P).h2_column n k).fStage.link i j) :=
  (I.h1H2PacketDegreeLedger P).spoke_natural n k i j

end OriginalInput
end Theorem311Source
end
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def theorem311SourcePacketDegreeLedger : Obligation :=
  { id := "IUT-III.theorem-3.11-source-packet-degree-ledger"
    source :=
      "IUT III Theorem 3.11, Props. 3.2, 3.4, 3.5, 3.7, 3.9, 3.10; " ++
        "IUT I Definition 5.2 and Prop. 6.9; IUT II prime-strip degree"
    status := VerificationStatus.interface
    note :=
      "From OriginalInput, every lattice theater supplies a concrete finite " ++
      "theta packet, positive scales, q/log-volume formulas, F/D prime-strip " ++
        "actions and degrees, and total-degree transport. The source-facing " ++
        "ledger is still under dependent-type repair and has no successful " ++
        "current-HEAD compilation evidence; it must not be treated as a closed " ++
        "Proposition 3.2/3.4 proof. The vertical-coricit D-theater, log-Kummer " ++
        "shell, LGP monoid, and Frobenioid remain separate gates."
    dependsOn := ["IUT-III.theorem-3.11-H1-H2-original-input-arrows",
      "IUT-I-II.prime-strip-degree-kernel",
      "IUT-I.hodge-theater-link-log-volume-transport"] }

end LeanFormal.IUT.Audit
