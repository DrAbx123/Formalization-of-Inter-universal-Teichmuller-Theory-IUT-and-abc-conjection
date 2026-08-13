import LeanFormal.IUT.IUTIII.Theorem311.SourcePacketDegreeLedger
import LeanFormal.IUT.IUTIII.Theorem311.SourceVerticalDThetaProjection
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # Source geometric-kernel ledger

  This module records the geometric kernel which is already visible in the
  supplied D-prime-strip projection.  The kernel is the actual kernel of the
  source projection at each place.  Consequently every membership statement
  below has a source carrier and a source projection in its type.

  The ledger is deliberately narrower than Theorem 1.5(i).  It does not add a
  holomorphic log-shell, a vertical coricity certificate, a Frobenioid, or a
  Kummer realization.  It packages only the source facts which follow from
  `OriginalInput`: subgroup closure, source-link transport, degree transport,
  finite-column inclusions, lattice translations, and spoke permutations.

  Source references: IUT I, Definition 5.2; IUT I, Proposition 6.9(ii);
  IUT III, Theorem 1.5(i), Proposition 3.4(ii), Proposition 3.5(ii)(c), and
  Theorem 3.11(i)--(iii).
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. One source geometric kernel -/

structure GeometricKernelLedger (n m : Int) where
  dStrip : DPrimeStrip.{upi, uv} V
  kernel : ∀ v : V, Subgroup (dStrip.Pi v)
  source_strip : dStrip = I.dPrimeStripAt n m
  source_kernel : ∀ v, kernel v = I.geometricAt n m v
  projection_surjective : ∀ v, Function.Surjective (dStrip.proj v)
  kernel_iff : ∀ v (x : dStrip.Pi v), x ∈ kernel v ↔ dStrip.proj v x = 1

def geometricKernelLedgerAt (n m : Int) : I.GeometricKernelLedger n m where
  dStrip := I.dPrimeStripAt n m
  kernel := fun v => I.geometricAt n m v
  source_strip := rfl
  source_kernel := by
    intro v
    rfl
  projection_surjective := by
    intro v
    exact (I.dPrimeStripAt n m).proj_surjective v
  kernel_iff := by
    intro v x
    rfl

@[simp] theorem geometricKernelLedgerAt_dStrip (n m : Int) :
    (I.geometricKernelLedgerAt n m).dStrip = I.dPrimeStripAt n m := rfl

@[simp] theorem geometricKernelLedgerAt_kernel (n m : Int) (v : V) :
    (I.geometricKernelLedgerAt n m).kernel v = I.geometricAt n m v := rfl

theorem geometricKernelLedgerAt_source_strip (n m : Int) :
    (I.geometricKernelLedgerAt n m).dStrip = I.dPrimeStripAt n m :=
  (I.geometricKernelLedgerAt n m).source_strip

theorem geometricKernelLedgerAt_source_kernel (n m : Int) (v : V) :
    (I.geometricKernelLedgerAt n m).kernel v = I.geometricAt n m v :=
  (I.geometricKernelLedgerAt n m).source_kernel v

theorem geometricKernelLedgerAt_proj_surjective (n m : Int) (v : V) :
    Function.Surjective
      ((I.geometricKernelLedgerAt n m).dStrip.proj v) :=
  (I.geometricKernelLedgerAt n m).projection_surjective v

theorem geometricKernelLedgerAt_mem_iff (n m : Int) (v : V)
    (x : (I.geometricKernelLedgerAt n m).dStrip.Pi v) :
    x ∈ (I.geometricKernelLedgerAt n m).kernel v ↔
      (I.geometricKernelLedgerAt n m).dStrip.proj v x = 1 :=
  (I.geometricKernelLedgerAt n m).kernel_iff v x

theorem geometricKernelLedgerAt_mem_source_iff (n m : Int) (v : V)
    (x : I.dPrimeStripAt n m |>.Pi v) :
    x ∈ I.geometricAt n m v ↔
      I.dPrimeStripAt n m |>.proj v x = 1 := by
  exact I.geometricAt_mem_iff n m v x

theorem geometricKernelLedgerAt_one_mem (n m : Int) (v : V) :
    (1 : (I.geometricKernelLedgerAt n m).dStrip.Pi v) ∈
      (I.geometricKernelLedgerAt n m).kernel v := by
  rw [(I.geometricKernelLedgerAt n m).source_kernel]
  exact (I.geometricAt n m v).one_mem

theorem geometricKernelLedgerAt_mul_mem (n m : Int) (v : V)
    {x y : (I.geometricKernelLedgerAt n m).dStrip.Pi v}
    (hx : x ∈ (I.geometricKernelLedgerAt n m).kernel v)
    (hy : y ∈ (I.geometricKernelLedgerAt n m).kernel v) :
    x * y ∈ (I.geometricKernelLedgerAt n m).kernel v := by
  rw [(I.geometricKernelLedgerAt n m).source_kernel] at hx hy ⊢
  exact (I.geometricAt n m v).mul_mem hx hy

theorem geometricKernelLedgerAt_inv_mem (n m : Int) (v : V)
    {x : (I.geometricKernelLedgerAt n m).dStrip.Pi v}
    (hx : x ∈ (I.geometricKernelLedgerAt n m).kernel v) :
    x⁻¹ ∈ (I.geometricKernelLedgerAt n m).kernel v := by
  rw [(I.geometricKernelLedgerAt n m).source_kernel] at hx ⊢
  exact (I.geometricAt n m v).inv_mem hx

theorem geometricKernelLedgerAt_proj_one (n m : Int) (v : V) :
    (I.geometricKernelLedgerAt n m).dStrip.proj v 1 = 1 := by
  exact (I.geometricKernelLedgerAt n m).dStrip.proj v |>.map_one

theorem geometricKernelLedgerAt_kernel_eq_ker (n m : Int) (v : V) :
    (I.geometricKernelLedgerAt n m).kernel v =
      (I.geometricKernelLedgerAt n m).dStrip.geometric v := by
  rw [(I.geometricKernelLedgerAt n m).source_kernel]
  rfl

theorem geometricKernelLedgerAt_kernel_subgroup (n m : Int) (v : V) :
    Subgroup (I.dPrimeStripAt n m |>.Pi v) :=
  I.geometricAt n m v

/-! ## 2. Source link transport of geometric kernels -/

structure GeometricKernelLinkLedger (n m n' m' : Int) where
  source : I.GeometricKernelLedger n m
  target : I.GeometricKernelLedger n' m'
  link : DPrimeStripEquiv source.dStrip target.dStrip
  source_link : link = I.dPrimeStripLinkAt n m n' m'
  projection : ∀ v (x : source.dStrip.Pi v),
    target.dStrip.proj v (link.isoPi v x) =
      link.isoG v (source.dStrip.proj v x)
  kernel_transport : ∀ v (x : source.dStrip.Pi v),
    x ∈ source.kernel v ↔ link.isoPi v x ∈ target.kernel v

def geometricKernelLinkLedgerAt (n m n' m' : Int) :
    I.GeometricKernelLinkLedger n m n' m' where
  source := I.geometricKernelLedgerAt n m
  target := I.geometricKernelLedgerAt n' m'
  link := I.dPrimeStripLinkAt n m n' m'
  source_link := rfl
  projection := by
    intro v x
    exact I.dPrimeStripLinkAt_compatProj n m n' m' v x
  kernel_transport := by
    intro v x
    exact I.link_geometric_commutes n m n' m' v x

@[simp] theorem geometricKernelLinkLedgerAt_source (n m n' m' : Int) :
    (I.geometricKernelLinkLedgerAt n m n' m').source =
      I.geometricKernelLedgerAt n m := rfl

@[simp] theorem geometricKernelLinkLedgerAt_target (n m n' m' : Int) :
    (I.geometricKernelLinkLedgerAt n m n' m').target =
      I.geometricKernelLedgerAt n' m' := rfl

@[simp] theorem geometricKernelLinkLedgerAt_link (n m n' m' : Int) :
    (I.geometricKernelLinkLedgerAt n m n' m').link =
      I.dPrimeStripLinkAt n m n' m' := rfl

theorem geometricKernelLinkLedgerAt_source_link (n m n' m' : Int) :
    (I.geometricKernelLinkLedgerAt n m n' m').link =
      I.dPrimeStripLinkAt n m n' m' :=
  (I.geometricKernelLinkLedgerAt n m n' m').source_link

theorem geometricKernelLinkLedgerAt_projection (n m n' m' : Int)
    (v : V) (x : (I.geometricKernelLinkLedgerAt n m n' m').source.dStrip.Pi v) :
    (I.geometricKernelLinkLedgerAt n m n' m').target.dStrip.proj v
        ((I.geometricKernelLinkLedgerAt n m n' m').link.isoPi v x) =
      (I.geometricKernelLinkLedgerAt n m n' m').link.isoG v
        ((I.geometricKernelLinkLedgerAt n m n' m').source.dStrip.proj v x) :=
  (I.geometricKernelLinkLedgerAt n m n' m').projection v x

theorem geometricKernelLinkLedgerAt_kernel_transport
    (n m n' m' : Int) (v : V)
    (x : (I.geometricKernelLinkLedgerAt n m n' m').source.dStrip.Pi v) :
    x ∈ (I.geometricKernelLinkLedgerAt n m n' m').source.kernel v ↔
      (I.geometricKernelLinkLedgerAt n m n' m').link.isoPi v x ∈
        (I.geometricKernelLinkLedgerAt n m n' m').target.kernel v :=
  (I.geometricKernelLinkLedgerAt n m n' m').kernel_transport v x

theorem geometricKernelLinkLedgerAt_kernel_source_iff
    (n m n' m' : Int) (v : V)
    (x : I.dPrimeStripAt n m |>.Pi v) :
    x ∈ I.geometricAt n m v ↔
      (I.dPrimeStripLinkAt n m n' m').isoPi v x ∈ I.geometricAt n' m' v := by
  exact I.link_geometric_commutes n m n' m' v x

theorem geometricKernelLinkLedgerAt_isoPi_bijective
    (n m n' m' : Int) (v : V) :
    Function.Bijective
      ((I.geometricKernelLinkLedgerAt n m n' m').link.isoPi v) := by
  exact ((I.geometricKernelLinkLedgerAt n m n' m').link.isoPi v).bijective

theorem geometricKernelLinkLedgerAt_isoG_bijective
    (n m n' m' : Int) (v : V) :
    Function.Bijective
      ((I.geometricKernelLinkLedgerAt n m n' m').link.isoG v) := by
  exact ((I.geometricKernelLinkLedgerAt n m n' m').link.isoG v).bijective

theorem geometricKernelLinkLedgerAt_source_surjective
    (n m n' m' : Int) (v : V) :
    Function.Surjective
      ((I.geometricKernelLinkLedgerAt n m n' m').source.dStrip.proj v) :=
  (I.geometricKernelLinkLedgerAt n m n' m').source.projection_surjective v

theorem geometricKernelLinkLedgerAt_target_surjective
    (n m n' m' : Int) (v : V) :
    Function.Surjective
      ((I.geometricKernelLinkLedgerAt n m n' m').target.dStrip.proj v) :=
  (I.geometricKernelLinkLedgerAt n m n' m').target.projection_surjective v

theorem geometricKernelLinkLedgerAt_kernel_one (n m n' m' : Int) (v : V) :
    (1 : (I.geometricKernelLinkLedgerAt n m n' m').source.dStrip.Pi v) ∈
      (I.geometricKernelLinkLedgerAt n m n' m').source.kernel v := by
  exact geometricKernelLedgerAt_one_mem I n m v

theorem geometricKernelLinkLedgerAt_kernel_mul (n m n' m' : Int) (v : V)
    {x y : (I.geometricKernelLinkLedgerAt n m n' m').source.dStrip.Pi v}
    (hx : x ∈ (I.geometricKernelLinkLedgerAt n m n' m').source.kernel v)
    (hy : y ∈ (I.geometricKernelLinkLedgerAt n m n' m').source.kernel v) :
    x * y ∈ (I.geometricKernelLinkLedgerAt n m n' m').source.kernel v := by
  exact geometricKernelLedgerAt_mul_mem I n m v hx hy

theorem geometricKernelLinkLedgerAt_kernel_inv (n m n' m' : Int) (v : V)
    {x : (I.geometricKernelLinkLedgerAt n m n' m').source.dStrip.Pi v}
    (hx : x ∈ (I.geometricKernelLinkLedgerAt n m n' m').source.kernel v) :
    x⁻¹ ∈ (I.geometricKernelLinkLedgerAt n m n' m').source.kernel v := by
  exact geometricKernelLedgerAt_inv_mem I n m v hx

/-! ## 3. Link groupoid laws with kernel transport -/

theorem geometricKernelLinkLedgerAt_refl (n m : Int) :
    (I.geometricKernelLinkLedgerAt n m n m).link =
      DPrimeStripEquiv.refl
        (I.geometricKernelLinkLedgerAt n m n m).source.dStrip := by
  exact I.dPrimeStripLinkAt_refl n m

theorem geometricKernelLinkLedgerAt_symm (n m n' m' : Int) :
    DPrimeStripEquiv.symm
        (I.geometricKernelLinkLedgerAt n m n' m').link =
      (I.geometricKernelLinkLedgerAt n' m' n m).link := by
  exact I.dPrimeStripLinkAt_symm n m n' m'

theorem geometricKernelLinkLedgerAt_trans
    (n m n' m' n'' m'' : Int) :
    DPrimeStripEquiv.trans
        (I.geometricKernelLinkLedgerAt n m n' m').link
        (I.geometricKernelLinkLedgerAt n' m' n'' m'').link =
      (I.geometricKernelLinkLedgerAt n m n'' m'').link := by
  exact I.dPrimeStripLinkAt_trans n m n' m' n'' m''

theorem geometricKernelLinkLedgerAt_trans_isoPi
    (n m n' m' n'' m'' : Int) (v : V)
    (x : I.dPrimeStripAt n m |>.Pi v) :
    (I.geometricKernelLinkLedgerAt n m n'' m'').link.isoPi v x =
      (I.geometricKernelLinkLedgerAt n' m' n'' m'').link.isoPi v
        ((I.geometricKernelLinkLedgerAt n m n' m').link.isoPi v x) := by
  exact I.dPrimeStripLinkAt_trans_isoPi n m n' m' n'' m'' v x

theorem geometricKernelLinkLedgerAt_trans_isoG
    (n m n' m' n'' m'' : Int) (v : V)
    (x : I.dPrimeStripAt n m |>.G v) :
    (I.geometricKernelLinkLedgerAt n m n'' m'').link.isoG v x =
      (I.geometricKernelLinkLedgerAt n' m' n'' m'').link.isoG v
        ((I.geometricKernelLinkLedgerAt n m n' m').link.isoG v x) := by
  exact I.dPrimeStripLinkAt_trans_isoG n m n' m' n'' m'' v x

theorem geometricKernelLinkLedgerAt_inverse_pi
    (n m n' m' : Int) (v : V)
    (x : I.dPrimeStripAt n m |>.Pi v) :
    (I.geometricKernelLinkLedgerAt n' m' n m).link.isoPi v
        ((I.geometricKernelLinkLedgerAt n m n' m').link.isoPi v x) = x := by
  exact I.dPrimeStripLinkAt_symm_isoPi_apply n m n' m' v x

theorem geometricKernelLinkLedgerAt_inverse_g
    (n m n' m' : Int) (v : V)
    (x : I.dPrimeStripAt n m |>.G v) :
    (I.geometricKernelLinkLedgerAt n' m' n m).link.isoG v
        ((I.geometricKernelLinkLedgerAt n m n' m').link.isoG v x) = x := by
  exact I.dPrimeStripLinkAt_symm_isoG_apply n m n' m' v x

theorem geometricKernelLinkLedgerAt_transport_chain
    (n m n' m' n'' m'' : Int) (v : V)
    (x : I.dPrimeStripAt n m |>.Pi v) :
    x ∈ I.geometricAt n m v ↔
      (I.geometricKernelLinkLedgerAt n' m' n'' m'').link.isoPi v
        ((I.geometricKernelLinkLedgerAt n m n' m').link.isoPi v x) ∈
        I.geometricAt n'' m'' v := by
  rw [← I.dPrimeStripLinkAt_trans_isoPi n m n' m' n'' m'' v x]
  exact I.link_geometric_commutes n m n'' m'' v x

/-! ## 4. Source arithmetic and theta packet attached to the kernel -/

structure GeometricKernelPacketLedger (n m : Int) where
  geometric : I.GeometricKernelLedger n m
  arithmetic : InitialThetaArithmeticData.{ua} l
  packet : FiniteThetaPacket l
  arithmetic_source : arithmetic = I.initial.arithmetic
  packet_source : packet = (I.theaterAt n m).thetaPacket
  q_positive : 0 < packet.q
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

def geometricKernelPacketLedgerAt (n m : Int) :
    I.GeometricKernelPacketLedger n m where
  geometric := I.geometricKernelLedgerAt n m
  arithmetic := I.initial.arithmetic
  packet := (I.theaterAt n m).thetaPacket
  arithmetic_source := rfl
  packet_source := rfl
  q_positive := (I.theaterAt n m).thetaPacket.q_pos
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
  log_volume := (I.theaterAt n m).thetaPacket.logVolume_eq_sum
  log_volume_neg := (I.theaterAt n m).thetaPacket.logVolume_neg_invariant

@[simp] theorem geometricKernelPacketLedgerAt_geometric (n m : Int) :
    (I.geometricKernelPacketLedgerAt n m).geometric =
      I.geometricKernelLedgerAt n m := rfl

@[simp] theorem geometricKernelPacketLedgerAt_packet (n m : Int) :
    (I.geometricKernelPacketLedgerAt n m).packet =
      (I.theaterAt n m).thetaPacket := rfl

@[simp] theorem geometricKernelPacketLedgerAt_arithmetic (n m : Int) :
    (I.geometricKernelPacketLedgerAt n m).arithmetic =
      I.initial.arithmetic := rfl

theorem geometricKernelPacketLedgerAt_q_positive (n m : Int) :
    0 < (I.geometricKernelPacketLedgerAt n m).packet.q :=
  (I.geometricKernelPacketLedgerAt n m).q_positive

theorem geometricKernelPacketLedgerAt_scale_positive (n m : Int)
    (j : SignedLabel l.value) :
    0 < (I.geometricKernelPacketLedgerAt n m).packet.scale j :=
  (I.geometricKernelPacketLedgerAt n m).scale_positive j

theorem geometricKernelPacketLedgerAt_scale_nonzero (n m : Int)
    (j : SignedLabel l.value) :
    (I.geometricKernelPacketLedgerAt n m).packet.scale j ≠ 0 :=
  (I.geometricKernelPacketLedgerAt n m).scale_nonzero j

theorem geometricKernelPacketLedgerAt_scale_neg (n m : Int)
    (j : SignedLabel l.value) :
    (I.geometricKernelPacketLedgerAt n m).packet.scale (SignedLabel.neg j) =
      (I.geometricKernelPacketLedgerAt n m).packet.scale j :=
  (I.geometricKernelPacketLedgerAt n m).scale_neg j

theorem geometricKernelPacketLedgerAt_log_scale (n m : Int)
    (j : SignedLabel l.value) :
    Real.log ((I.geometricKernelPacketLedgerAt n m).packet.scale j) =
      (gaussExponent j.1).toNat *
        Real.log (I.geometricKernelPacketLedgerAt n m).packet.q :=
  (I.geometricKernelPacketLedgerAt n m).log_scale j

theorem geometricKernelPacketLedgerAt_log_volume (n m : Int) :
    (I.geometricKernelPacketLedgerAt n m).packet.logVolume =
      ∑ j : SignedLabel l.value,
        Real.log ((I.geometricKernelPacketLedgerAt n m).packet.scale j) :=
  (I.geometricKernelPacketLedgerAt n m).log_volume

theorem geometricKernelPacketLedgerAt_log_volume_neg (n m : Int) :
    (∑ j : SignedLabel l.value,
      Real.log ((I.geometricKernelPacketLedgerAt n m).packet.scale
        (SignedLabel.neg j))) =
      (I.geometricKernelPacketLedgerAt n m).packet.logVolume :=
  (I.geometricKernelPacketLedgerAt n m).log_volume_neg

theorem geometricKernelPacketLedgerAt_q_transport
    (n m n' m' : Int) :
    (I.geometricKernelPacketLedgerAt n m).packet.q =
      (I.geometricKernelPacketLedgerAt n' m').packet.q :=
  I.linkAt_q n m n' m'

theorem geometricKernelPacketLedgerAt_scale_transport
    (n m n' m' : Int) (j : SignedLabel l.value) :
    (I.geometricKernelPacketLedgerAt n m).packet.scale j =
      (I.geometricKernelPacketLedgerAt n' m').packet.scale j :=
  I.linkAt_scale n m n' m' j

theorem geometricKernelPacketLedgerAt_log_volume_transport
    (n m n' m' : Int) :
    (I.geometricKernelPacketLedgerAt n m).packet.logVolume =
      (I.geometricKernelPacketLedgerAt n' m').packet.logVolume := by
  rw [I.geometricKernelPacketLedgerAt_log_volume,
    I.geometricKernelPacketLedgerAt_log_volume]
  apply Finset.sum_congr rfl
  intro j hj
  rw [I.geometricKernelPacketLedgerAt_scale_transport n m n' m' j]

theorem geometricKernelPacketLedgerAt_kernel_packet_bundle (n m : Int) :
    (I.geometricKernelPacketLedgerAt n m).geometric.dStrip =
        I.dPrimeStripAt n m ∧
      (I.geometricKernelPacketLedgerAt n m).packet.q > 0 ∧
      (I.geometricKernelPacketLedgerAt n m).packet.logVolume =
        ∑ j : SignedLabel l.value,
          Real.log ((I.geometricKernelPacketLedgerAt n m).packet.scale j) := by
  exact ⟨(I.geometricKernelPacketLedgerAt n m).geometric.source_strip,
    (I.geometricKernelPacketLedgerAt n m).q_positive,
    (I.geometricKernelPacketLedgerAt n m).log_volume⟩

/-! ## 5. Value action and degree retained beside the kernel -/

structure GeometricKernelValueLedger (n m : Int) where
  geometric : I.GeometricKernelLedger n m
  fStrip : FPrimeStrip.{umon, uv, upi} V
  f_source : fStrip = I.primeStripAt n m
  d_projection : fStrip.toD = geometric.dStrip
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

def geometricKernelValueLedgerAt (n m : Int) :
    I.GeometricKernelValueLedger n m where
  geometric := I.geometricKernelLedgerAt n m
  fStrip := I.primeStripAt n m
  f_source := rfl
  d_projection := by rfl
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

@[simp] theorem geometricKernelValueLedgerAt_geometric (n m : Int) :
    (I.geometricKernelValueLedgerAt n m).geometric =
      I.geometricKernelLedgerAt n m := rfl

@[simp] theorem geometricKernelValueLedgerAt_fStrip (n m : Int) :
    (I.geometricKernelValueLedgerAt n m).fStrip =
      I.primeStripAt n m := rfl

theorem geometricKernelValueLedgerAt_source (n m : Int) :
    (I.geometricKernelValueLedgerAt n m).fStrip =
      I.primeStripAt n m :=
  (I.geometricKernelValueLedgerAt n m).f_source

theorem geometricKernelValueLedgerAt_projection (n m : Int) :
    (I.geometricKernelValueLedgerAt n m).fStrip.toD =
      (I.geometricKernelValueLedgerAt n m).geometric.dStrip :=
  (I.geometricKernelValueLedgerAt n m).d_projection

theorem geometricKernelValueLedgerAt_action_mul (n m : Int)
    (v : V) (g h : (I.geometricKernelValueLedgerAt n m).fStrip.toD.Pi v)
    (x : (I.geometricKernelValueLedgerAt n m).fStrip.Mon v) :
    (I.geometricKernelValueLedgerAt n m).fStrip.action v (g * h) x =
      (I.geometricKernelValueLedgerAt n m).fStrip.action v g
        ((I.geometricKernelValueLedgerAt n m).fStrip.action v h x) :=
  (I.geometricKernelValueLedgerAt n m).action_mul v g h x

theorem geometricKernelValueLedgerAt_action_one (n m : Int)
    (v : V) (x : (I.geometricKernelValueLedgerAt n m).fStrip.Mon v) :
    (I.geometricKernelValueLedgerAt n m).fStrip.action v 1 x = x :=
  (I.geometricKernelValueLedgerAt n m).action_one v x

theorem geometricKernelValueLedgerAt_degree_one (n m : Int) (v : V) :
    (I.geometricKernelValueLedgerAt n m).fStrip.degree v 1 = 1 :=
  (I.geometricKernelValueLedgerAt n m).degree_one v

theorem geometricKernelValueLedgerAt_degree_mul (n m : Int) (v : V)
    (x y : (I.geometricKernelValueLedgerAt n m).fStrip.Mon v) :
    (I.geometricKernelValueLedgerAt n m).fStrip.degree v (x * y) =
      (I.geometricKernelValueLedgerAt n m).fStrip.degree v x *
        (I.geometricKernelValueLedgerAt n m).fStrip.degree v y :=
  (I.geometricKernelValueLedgerAt n m).degree_mul v x y

theorem geometricKernelValueLedgerAt_total_degree_mul (n m : Int)
    (s : Finset V)
    (x y : ∀ v, (I.geometricKernelValueLedgerAt n m).fStrip.Mon v) :
    (I.geometricKernelValueLedgerAt n m).fStrip.totalDegree s
        (fun v => x v * y v) =
      (I.geometricKernelValueLedgerAt n m).fStrip.totalDegree s x +
        (I.geometricKernelValueLedgerAt n m).fStrip.totalDegree s y :=
  (I.geometricKernelValueLedgerAt n m).total_degree_mul s x y

theorem geometricKernelValueLedgerAt_total_degree_one (n m : Int)
    (s : Finset V) :
    (I.geometricKernelValueLedgerAt n m).fStrip.totalDegree s
        (fun _ => 1) = 0 :=
  (I.geometricKernelValueLedgerAt n m).total_degree_one s

theorem geometricKernelValueLedgerAt_degree_transport
    (n m n' m' : Int) (v : V)
    (x : (I.geometricKernelValueLedgerAt n m).fStrip.Mon v) :
    (I.geometricKernelValueLedgerAt n' m').fStrip.degree v
        ((I.primeStripLinkAt n m n' m').isoMon v x) =
      (I.geometricKernelValueLedgerAt n m).fStrip.degree v x :=
  I.primeStripLinkAt_compatDegree n m n' m' v x

theorem geometricKernelValueLedgerAt_action_transport
    (n m n' m' : Int) (v : V)
    (g : (I.geometricKernelValueLedgerAt n m).fStrip.toD.Pi v)
    (x : (I.geometricKernelValueLedgerAt n m).fStrip.Mon v) :
    (I.primeStripLinkAt n m n' m').isoMon v
        ((I.geometricKernelValueLedgerAt n m).fStrip.action v g x) =
      (I.geometricKernelValueLedgerAt n' m').fStrip.action v
        ((I.primeStripLinkAt n m n' m').isoPi v g)
        ((I.primeStripLinkAt n m n' m').isoMon v x) :=
  I.primeStripLinkAt_compatAction n m n' m' v g x

theorem geometricKernelValueLedgerAt_total_degree_transport
    (n m n' m' : Int) (s : Finset V)
    (x : ∀ v, (I.geometricKernelValueLedgerAt n m).fStrip.Mon v) :
    (I.geometricKernelValueLedgerAt n' m').fStrip.totalDegree s
        (fun v => (I.primeStripLinkAt n m n' m').isoMon v (x v)) =
      (I.geometricKernelValueLedgerAt n m).fStrip.totalDegree s x := by
  apply Finset.sum_congr rfl
  intro v hv
  exact I.geometricKernelValueLedgerAt_degree_transport n m n' m' v (x v)

theorem geometricKernelValueLedgerAt_kernel_transport
    (n m n' m' : Int) (v : V)
    (x : (I.geometricKernelValueLedgerAt n m).geometric.dStrip.Pi v) :
    x ∈ (I.geometricKernelValueLedgerAt n m).geometric.kernel v ↔
      (I.dPrimeStripLinkAt n m n' m').isoPi v x ∈
        (I.geometricKernelValueLedgerAt n' m').geometric.kernel v :=
  I.geometricKernelLinkLedgerAt_kernel_transport n m n' m' v x

/-! ## 6. Explicit source point bundle -/

structure SourcePointBundle (n m : Int) where
  kernel : I.GeometricKernelLedger n m
  value : I.GeometricKernelValueLedger n m
  packet : I.GeometricKernelPacketLedger n m
  value_kernel : value.geometric = kernel
  packet_kernel : packet.geometric = kernel
  arithmetic_eq : packet.arithmetic = I.initial.arithmetic
  q_positive : 0 < packet.packet.q
  kernel_projection_surjective : ∀ v,
    Function.Surjective (kernel.dStrip.proj v)

def sourcePointBundle (n m : Int) : I.SourcePointBundle n m where
  kernel := I.geometricKernelLedgerAt n m
  value := I.geometricKernelValueLedgerAt n m
  packet := I.geometricKernelPacketLedgerAt n m
  value_kernel := rfl
  packet_kernel := rfl
  arithmetic_eq := rfl
  q_positive := (I.geometricKernelPacketLedgerAt n m).q_positive
  kernel_projection_surjective :=
    (I.geometricKernelLedgerAt n m).projection_surjective

@[simp] theorem sourcePointBundle_kernel (n m : Int) :
    (I.sourcePointBundle n m).kernel = I.geometricKernelLedgerAt n m := rfl

@[simp] theorem sourcePointBundle_value (n m : Int) :
    (I.sourcePointBundle n m).value = I.geometricKernelValueLedgerAt n m := rfl

@[simp] theorem sourcePointBundle_packet (n m : Int) :
    (I.sourcePointBundle n m).packet = I.geometricKernelPacketLedgerAt n m := rfl

theorem sourcePointBundle_value_kernel (n m : Int) :
    (I.sourcePointBundle n m).value.geometric =
      (I.sourcePointBundle n m).kernel :=
  (I.sourcePointBundle n m).value_kernel

theorem sourcePointBundle_packet_kernel (n m : Int) :
    (I.sourcePointBundle n m).packet.geometric =
      (I.sourcePointBundle n m).kernel :=
  (I.sourcePointBundle n m).packet_kernel

theorem sourcePointBundle_q_positive (n m : Int) :
    0 < (I.sourcePointBundle n m).packet.packet.q :=
  (I.sourcePointBundle n m).q_positive

theorem sourcePointBundle_projection_surjective (n m : Int) (v : V) :
    Function.Surjective ((I.sourcePointBundle n m).kernel.dStrip.proj v) :=
  (I.sourcePointBundle n m).kernel_projection_surjective v

theorem sourcePointBundle_kernel_mem_iff (n m : Int) (v : V)
    (x : (I.sourcePointBundle n m).kernel.dStrip.Pi v) :
    x ∈ (I.sourcePointBundle n m).kernel.kernel v ↔
      (I.sourcePointBundle n m).kernel.dStrip.proj v x = 1 :=
  (I.sourcePointBundle n m).kernel.kernel_iff v x

theorem sourcePointBundle_packet_q_transport (n m n' m' : Int) :
    (I.sourcePointBundle n m).packet.packet.q =
      (I.sourcePointBundle n' m').packet.packet.q :=
  I.geometricKernelPacketLedgerAt_q_transport n m n' m'

theorem sourcePointBundle_packet_scale_transport (n m n' m' : Int)
    (j : SignedLabel l.value) :
    (I.sourcePointBundle n m).packet.packet.scale j =
      (I.sourcePointBundle n' m').packet.packet.scale j :=
  I.geometricKernelPacketLedgerAt_scale_transport n m n' m' j

theorem sourcePointBundle_kernel_transport (n m n' m' : Int) (v : V)
    (x : (I.sourcePointBundle n m).kernel.dStrip.Pi v) :
    x ∈ (I.sourcePointBundle n m).kernel.kernel v ↔
      (I.dPrimeStripLinkAt n m n' m').isoPi v x ∈
        (I.sourcePointBundle n' m').kernel.kernel v :=
  I.geometricKernelLinkLedgerAt_kernel_transport n m n' m' v x

/-! ## 7. Finite column kernels -/

structure GeometricColumnKernelLedger (n : Int) (k : Nat) where
  column : I.ColumnStageSourceLedger n k
  kernel : ∀ i : Fin (k + 1), ∀ v : V,
    Subgroup ((column.dStage.strip i).Pi v)
  kernel_source : ∀ i v,
    kernel i v = I.geometricAt n (i.1 : Int) v
  source_injective : Function.Injective column.source
  cardinality : Fintype.card (Fin (k + 1)) = k + 1
  link_kernel_transport : ∀ (i j : Fin (k + 1)) (v : V)
      (x : (column.dStage.strip i).Pi v),
    x ∈ kernel i v ↔
      (column.dLink i j).isoPi v x ∈ kernel j v
  inclusion_kernel_transport : ∀ {r : Nat} (h : k ≤ r)
      (i : Fin (k + 1)) (v : V)
      (x : (column.dStage.strip i).Pi v),
    x ∈ kernel i v ↔
      ((I.columnProcessionSourceLedger n).inclusion_d_component h i).isoPi v x ∈
        (I.columnStageSourceLedger n r).dStage.strip
          ((I.columnProcessionSourceLedger n).inclusion_map h i) |>.geometric v

def geometricColumnKernelLedger (n : Int) (k : Nat) :
    I.GeometricColumnKernelLedger n k where
  column := I.columnStageSourceLedger n k
  kernel := fun i v => I.geometricAt n (i.1 : Int) v
  kernel_source := by
    intro i v
    rfl
  source_injective := I.columnStageSourceLedger_source_injective n k
  cardinality := by
    simp
  link_kernel_transport := by
    intro i j v x
    exact I.link_geometric_commutes n (i.1 : Int) n (j.1 : Int) v x
  inclusion_kernel_transport := by
    intro r h i v x
    exact I.link_geometric_commutes n (i.1 : Int) n
      ((I.columnProcessionSourceLedger n).inclusion_map h i).1 v x

@[simp] theorem geometricColumnKernelLedger_column (n : Int) (k : Nat) :
    (I.geometricColumnKernelLedger n k).column =
      I.columnStageSourceLedger n k := rfl

@[simp] theorem geometricColumnKernelLedger_kernel (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V) :
    (I.geometricColumnKernelLedger n k).kernel i v =
      I.geometricAt n (i.1 : Int) v := rfl

theorem geometricColumnKernelLedger_source_injective (n : Int) (k : Nat) :
    Function.Injective (I.geometricColumnKernelLedger n k).column.source :=
  (I.geometricColumnKernelLedger n k).source_injective

theorem geometricColumnKernelLedger_cardinality (n : Int) (k : Nat) :
    Fintype.card (Fin (k + 1)) = k + 1 :=
  (I.geometricColumnKernelLedger n k).cardinality

theorem geometricColumnKernelLedger_kernel_source (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V) :
    (I.geometricColumnKernelLedger n k).kernel i v =
      I.geometricAt n (i.1 : Int) v :=
  (I.geometricColumnKernelLedger n k).kernel_source i v

theorem geometricColumnKernelLedger_link_kernel_transport
    (n : Int) (k : Nat) (i j : Fin (k + 1)) (v : V)
    (x : ((I.geometricColumnKernelLedger n k).column.dStage.strip i).Pi v) :
    x ∈ (I.geometricColumnKernelLedger n k).kernel i v ↔
      (((I.geometricColumnKernelLedger n k).column.dLink i j).isoPi v x) ∈
        (I.geometricColumnKernelLedger n k).kernel j v :=
  (I.geometricColumnKernelLedger n k).link_kernel_transport i j v x

theorem geometricColumnKernelLedger_link_kernel_source_iff
    (n : Int) (k : Nat) (i j : Fin (k + 1)) (v : V)
    (x : (I.dPrimeStripAt n (i.1 : Int)).Pi v) :
    x ∈ I.geometricAt n (i.1 : Int) v ↔
      (I.dLinkAt n (i.1 : Int) n (j.1 : Int)).isoPi v x ∈
        I.geometricAt n (j.1 : Int) v := by
  exact I.link_geometric_commutes n (i.1 : Int) n (j.1 : Int) v x

theorem geometricColumnKernelLedger_link_isoPi_bijective
    (n : Int) (k : Nat) (i j : Fin (k + 1)) (v : V) :
    Function.Bijective
      (((I.geometricColumnKernelLedger n k).column.dLink i j).isoPi v) :=
  (((I.geometricColumnKernelLedger n k).column.dLink i j).isoPi v).bijective

theorem geometricColumnKernelLedger_link_isoG_bijective
    (n : Int) (k : Nat) (i j : Fin (k + 1)) (v : V) :
    Function.Bijective
      (((I.geometricColumnKernelLedger n k).column.dLink i j).isoG v) :=
  (((I.geometricColumnKernelLedger n k).column.dLink i j).isoG v).bijective

theorem geometricColumnKernelLedger_link_refl
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.geometricColumnKernelLedger n k).column.dLink i i =
      DPrimeStripEquiv.refl
        ((I.geometricColumnKernelLedger n k).column.dStage.strip i) := by
  exact I.columnStageSourceLedger_dLink_refl n k i

theorem geometricColumnKernelLedger_link_symm
    (n : Int) (k : Nat) (i j : Fin (k + 1)) :
    DPrimeStripEquiv.symm
        ((I.geometricColumnKernelLedger n k).column.dLink i j) =
      (I.geometricColumnKernelLedger n k).column.dLink j i := by
  exact I.columnStageSourceLedger_dLink_symm n k i j

theorem geometricColumnKernelLedger_link_trans
    (n : Int) (k : Nat) (i j h : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        ((I.geometricColumnKernelLedger n k).column.dLink i j)
        ((I.geometricColumnKernelLedger n k).column.dLink j h) =
      (I.geometricColumnKernelLedger n k).column.dLink i h := by
  exact I.columnStageSourceLedger_dLink_trans n k i j h

theorem geometricColumnKernelLedger_one_mem
    (n : Int) (k : Nat) (i : Fin (k + 1)) (v : V) :
    (1 : ((I.geometricColumnKernelLedger n k).column.dStage.strip i).Pi v) ∈
      (I.geometricColumnKernelLedger n k).kernel i v := by
  rw [geometricColumnKernelLedger_kernel]
  exact (I.geometricAt n (i.1 : Int) v).one_mem

theorem geometricColumnKernelLedger_mul_mem
    (n : Int) (k : Nat) (i : Fin (k + 1)) (v : V)
    {x y : ((I.geometricColumnKernelLedger n k).column.dStage.strip i).Pi v}
    (hx : x ∈ (I.geometricColumnKernelLedger n k).kernel i v)
    (hy : y ∈ (I.geometricColumnKernelLedger n k).kernel i v) :
    x * y ∈ (I.geometricColumnKernelLedger n k).kernel i v := by
  rw [geometricColumnKernelLedger_kernel] at hx hy ⊢
  exact (I.geometricAt n (i.1 : Int) v).mul_mem hx hy

theorem geometricColumnKernelLedger_inv_mem
    (n : Int) (k : Nat) (i : Fin (k + 1)) (v : V)
    {x : ((I.geometricColumnKernelLedger n k).column.dStage.strip i).Pi v}
    (hx : x ∈ (I.geometricColumnKernelLedger n k).kernel i v) :
    x⁻¹ ∈ (I.geometricColumnKernelLedger n k).kernel i v := by
  rw [geometricColumnKernelLedger_kernel] at hx ⊢
  exact (I.geometricAt n (i.1 : Int) v).inv_mem hx

/-! ## 8. Procession-level kernel transport -/

structure GeometricColumnProcessionLedger (n : Int) where
  stage : ∀ k, I.GeometricColumnKernelLedger n k
  inclusion_map : ∀ {k r : Nat} (h : k ≤ r), Fin (k + 1) → Fin (r + 1)
  inclusion_injective : ∀ {k r : Nat} (h : k ≤ r),
    Function.Injective (inclusion_map h)
  inclusion_refl : ∀ (k : Nat) (i : Fin (k + 1)),
    inclusion_map (Nat.le_refl k) i = i
  inclusion_trans : ∀ {k r s : Nat} (h₁ : k ≤ r) (h₂ : r ≤ s)
      (i : Fin (k + 1)),
    inclusion_map (Nat.le_trans h₁ h₂) i =
      inclusion_map h₂ (inclusion_map h₁ i)
  inclusion_kernel_transport : ∀ {k r : Nat} (h : k ≤ r)
      (i : Fin (k + 1)) (v : V)
      (x : ((stage k).column.dStage.strip i).Pi v),
    x ∈ (stage k).kernel i v ↔
      (((I.columnProcessionSourceLedger n).inclusion_d_component h i).isoPi v x) ∈
        (stage r).kernel (inclusion_map h i) v
  inclusion_natural : ∀ {k r : Nat} (h : k ≤ r)
      (i j : Fin (k + 1)),
    DPrimeStripEquiv.trans ((stage k).column.dLink i j)
        ((I.columnProcessionSourceLedger n).inclusion_d_component h j) =
      DPrimeStripEquiv.trans
        ((I.columnProcessionSourceLedger n).inclusion_d_component h i)
        ((stage r).column.dLink (inclusion_map h i) (inclusion_map h j))

def geometricColumnProcessionLedger (n : Int) :
    I.GeometricColumnProcessionLedger n where
  stage := I.geometricColumnKernelLedger n
  inclusion_map := fun {_ _} h =>
    (I.columnProcessionSourceLedger n).inclusion_map h
  inclusion_injective := by
    intro k r h
    exact (I.columnProcessionSourceLedger n).inclusion_injective h
  inclusion_refl := by
    intro k i
    exact (I.columnProcessionSourceLedger n).inclusion_refl k i
  inclusion_trans := by
    intro k r s h₁ h₂ i
    exact (I.columnProcessionSourceLedger n).inclusion_trans h₁ h₂ i
  inclusion_kernel_transport := by
    intro k r h i v x
    exact (I.geometricColumnKernelLedger n k).inclusion_kernel_transport h i v x
  inclusion_natural := by
    intro k r h i j
    exact I.columnProcessionSourceLedger_inclusion_d_natural n h i j

@[simp] theorem geometricColumnProcessionLedger_stage
    (n : Int) (k : Nat) :
    (I.geometricColumnProcessionLedger n).stage k =
      I.geometricColumnKernelLedger n k := rfl

theorem geometricColumnProcessionLedger_inclusion_injective (n : Int)
    {k r : Nat} (h : k ≤ r) :
    Function.Injective
      (I.geometricColumnProcessionLedger n).inclusion_map h :=
  (I.geometricColumnProcessionLedger n).inclusion_injective h

theorem geometricColumnProcessionLedger_inclusion_refl (n : Int)
    (k : Nat) (i : Fin (k + 1)) :
    (I.geometricColumnProcessionLedger n).inclusion_map
      (Nat.le_refl k) i = i :=
  (I.geometricColumnProcessionLedger n).inclusion_refl k i

theorem geometricColumnProcessionLedger_inclusion_trans (n : Int)
    {k r s : Nat} (h₁ : k ≤ r) (h₂ : r ≤ s) (i : Fin (k + 1)) :
    (I.geometricColumnProcessionLedger n).inclusion_map
      (Nat.le_trans h₁ h₂) i =
      (I.geometricColumnProcessionLedger n).inclusion_map h₂
        ((I.geometricColumnProcessionLedger n).inclusion_map h₁ i) :=
  (I.geometricColumnProcessionLedger n).inclusion_trans h₁ h₂ i

theorem geometricColumnProcessionLedger_kernel_transport (n : Int)
    {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)) (v : V)
    (x : ((I.geometricColumnProcessionLedger n).stage k).column.dStage.strip i.Pi v) :
    x ∈ ((I.geometricColumnProcessionLedger n).stage k).kernel i v ↔
      (((I.columnProcessionSourceLedger n).inclusion_d_component h i).isoPi v x) ∈
        ((I.geometricColumnProcessionLedger n).stage r).kernel
          ((I.geometricColumnProcessionLedger n).inclusion_map h i) v :=
  (I.geometricColumnProcessionLedger n).inclusion_kernel_transport h i v x

theorem geometricColumnProcessionLedger_natural (n : Int)
    {k r : Nat} (h : k ≤ r) (i j : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        (((I.geometricColumnProcessionLedger n).stage k).column.dLink i j)
        ((I.columnProcessionSourceLedger n).inclusion_d_component h j) =
      DPrimeStripEquiv.trans
        ((I.columnProcessionSourceLedger n).inclusion_d_component h i)
        (((I.geometricColumnProcessionLedger n).stage r).column.dLink
          ((I.geometricColumnProcessionLedger n).inclusion_map h i)
          ((I.geometricColumnProcessionLedger n).inclusion_map h j)) :=
  (I.geometricColumnProcessionLedger n).inclusion_natural h i j

theorem geometricColumnProcessionLedger_top_cardinality (n : Int) :
    Fintype.card (Fin (lStar l.value + 1)) = lStar l.value + 1 := by
  exact (I.geometricColumnProcessionLedger n).stage lStar |>.cardinality

theorem geometricColumnProcessionLedger_top_source_injective (n : Int) :
    Function.Injective
      ((I.geometricColumnProcessionLedger n).stage (lStar l.value)).column.source :=
  (I.geometricColumnProcessionLedger n).stage lStar |>.source_injective

/-! ## 9. Horizontal translation of column kernels -/

structure GeometricTranslationKernelLedger (a n : Int) (k : Nat) where
  base : I.GeometricColumnKernelLedger n k
  target : I.GeometricColumnKernelLedger (n + a) k
  map : Fin (k + 1) ≃ Fin (k + 1)
  map_identity : ∀ i, map i = i
  component : ∀ i,
    DPrimeStripEquiv (base.column.dStage.strip i)
      (target.column.dStage.strip (map i))
  component_source : ∀ i,
    component i = (I.h2HorizontalDPolyIso n a k).component i
  packet_q : ∀ i,
    (I.theaterAt n (i.1 : Int)).thetaPacket.q =
      (I.theaterAt (n + a) (map i).1).thetaPacket.q
  packet_scale : ∀ i j,
    (I.theaterAt n (i.1 : Int)).thetaPacket.scale j =
      (I.theaterAt (n + a) (map i).1).thetaPacket.scale j
  kernel_transport : ∀ i v (x : (base.column.dStage.strip i).Pi v),
    x ∈ base.kernel i v ↔
      (component i).isoPi v x ∈ target.kernel (map i) v
  naturality : ∀ i j,
    DPrimeStripEquiv.trans (base.column.dLink i j) (component j) =
      DPrimeStripEquiv.trans (component i)
        (target.column.dLink (map i) (map j))

def geometricTranslationKernelLedger (a n : Int) (k : Nat) :
    I.GeometricTranslationKernelLedger a n k where
  base := I.geometricColumnKernelLedger n k
  target := I.geometricColumnKernelLedger (n + a) k
  map := Equiv.refl _
  map_identity := by intro i; rfl
  component := fun i => (I.h2HorizontalDPolyIso n a k).component i
  component_source := by intro i; rfl
  packet_q := by
    intro i
    exact I.linkAt_q n (i.1 : Int) (n + a) (i.1 : Int)
  packet_scale := by
    intro i j
    exact I.linkAt_scale n (i.1 : Int) (n + a) (i.1 : Int) j
  kernel_transport := by
    intro i v x
    exact I.link_geometric_commutes n (i.1 : Int) (n + a) (i.1 : Int) v x
  naturality := by
    intro i j
    exact I.h2HorizontalDPolyIso_natural n a k i j

@[simp] theorem geometricTranslationKernelLedger_base (a n : Int) (k : Nat) :
    (I.geometricTranslationKernelLedger a n k).base =
      I.geometricColumnKernelLedger n k := rfl

@[simp] theorem geometricTranslationKernelLedger_target (a n : Int) (k : Nat) :
    (I.geometricTranslationKernelLedger a n k).target =
      I.geometricColumnKernelLedger (n + a) k := rfl

@[simp] theorem geometricTranslationKernelLedger_map (a n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.geometricTranslationKernelLedger a n k).map i = i := rfl

@[simp] theorem geometricTranslationKernelLedger_component (a n : Int)
    (k : Nat) (i : Fin (k + 1)) :
    (I.geometricTranslationKernelLedger a n k).component i =
      (I.h2HorizontalDPolyIso n a k).component i := rfl

theorem geometricTranslationKernelLedger_q (a n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.geometricTranslationKernelLedger a n k).base.column.packet i |>.q =
      (I.geometricTranslationKernelLedger a n k).target.column.packet i |>.q := by
  exact I.linkAt_q n (i.1 : Int) (n + a) (i.1 : Int)

theorem geometricTranslationKernelLedger_scale (a n : Int) (k : Nat)
    (i : Fin (k + 1)) (j : SignedLabel l.value) :
    (I.geometricTranslationKernelLedger a n k).base.column.packet i |>.scale j =
      (I.geometricTranslationKernelLedger a n k).target.column.packet i |>.scale j := by
  exact I.linkAt_scale n (i.1 : Int) (n + a) (i.1 : Int) j

theorem geometricTranslationKernelLedger_kernel_transport (a n : Int)
    (k : Nat) (i : Fin (k + 1)) (v : V)
    (x : ((I.geometricTranslationKernelLedger a n k).base.column.dStage.strip i).Pi v) :
    x ∈ (I.geometricTranslationKernelLedger a n k).base.kernel i v ↔
      ((I.geometricTranslationKernelLedger a n k).component i).isoPi v x ∈
        (I.geometricTranslationKernelLedger a n k).target.kernel i v :=
  (I.geometricTranslationKernelLedger a n k).kernel_transport i v x

theorem geometricTranslationKernelLedger_natural (a n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        ((I.geometricTranslationKernelLedger a n k).base.column.dLink i j)
        ((I.geometricTranslationKernelLedger a n k).component j) =
      DPrimeStripEquiv.trans
        ((I.geometricTranslationKernelLedger a n k).component i)
        ((I.geometricTranslationKernelLedger a n k).target.column.dLink i j) :=
  (I.geometricTranslationKernelLedger a n k).naturality i j

theorem geometricTranslationKernelLedger_zero_component (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.geometricTranslationKernelLedger 0 n k).component i =
      DPrimeStripEquiv.refl
        ((I.geometricTranslationKernelLedger 0 n k).base.column.dStage.strip i) := by
  exact I.h2HorizontalD_zero_component n k i

theorem geometricTranslationKernelLedger_add_component (a b n : Int)
    (k : Nat) (i : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        ((I.geometricTranslationKernelLedger a n k).component i)
        ((I.geometricTranslationKernelLedger b (n + a) k).component i) =
      (I.geometricTranslationKernelLedger (a + b) n k).component i := by
  exact I.h2HorizontalD_add_component n a b k i

theorem geometricTranslationKernelLedger_inverse_component (a n : Int)
    (k : Nat) (i : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        ((I.geometricTranslationKernelLedger a n k).component i)
        ((I.geometricTranslationKernelLedger (-a) (n + a) k).component i) =
      DPrimeStripEquiv.refl
        ((I.geometricTranslationKernelLedger 0 n k).base.column.dStage.strip i) := by
  rw [geometricTranslationKernelLedger_add_component]
  have h : a + (-a) = (0 : Int) := by omega
  rw [h, geometricTranslationKernelLedger_zero_component]

/-! ## 10. Spoke permutations of column kernels -/

structure GeometricSpokeKernelLedger (P : H2SpokePermutation I)
    (n : Int) (k : Nat) where
  base : I.GeometricColumnKernelLedger n k
  spoke : I.SpokeColumnSourceLedger P n k
  component : ∀ i,
    DPrimeStripEquiv
      ((I.spokeCapsule P base.column.fStage).strip i)
      (base.column.dStage.strip i)
  component_source : ∀ i,
    component i = (I.dStageSpokePolyIso P (I.columnDStage n k)).component i
  packet_q : ∀ i,
    (I.family.theater (P.permutation (base.column.source i))).thetaPacket.q =
      base.column.packet i |>.q
  packet_scale : ∀ i j,
    (I.family.theater (P.permutation (base.column.source i))).thetaPacket.scale j =
      base.column.packet i |>.scale j
  kernel_transport : ∀ i v
      (x : ((I.spokeCapsule P base.column.fStage).strip i).toD.Pi v),
    x ∈ (I.spokeCapsule P base.column.fStage |>.strip i).toD.geometric v ↔
      (component i).isoPi v x ∈ base.kernel i v
  naturality : ∀ i j,
    DPrimeStripEquiv.trans
        ((I.dSpokeCapsule P base.column.dStage).link i j)
        (component j) =
      DPrimeStripEquiv.trans (component i) (base.column.dLink i j)

def geometricSpokeKernelLedger (P : H2SpokePermutation I)
    (n : Int) (k : Nat) : I.GeometricSpokeKernelLedger P n k where
  base := I.geometricColumnKernelLedger n k
  spoke := I.spokeColumnSourceLedger P n k
  component := fun i => (I.dStageSpokePolyIso P (I.columnDStage n k)).component i
  component_source := by intro i; rfl
  packet_q := by
    intro i
    exact P.spoke_q (I.columnSource n k i)
  packet_scale := by
    intro i j
    exact P.spoke_scale (I.columnSource n k i) j
  kernel_transport := by
    intro i v x
    exact I.link_geometric_commutes
      (P.permutation (I.columnSource n k i)) 0
      n (i.1 : Int) v x
  naturality := by
    intro i j
    exact I.dStageSpokeTransport_naturality P (I.columnDStage n k) i j

@[simp] theorem geometricSpokeKernelLedger_base (P : H2SpokePermutation I)
    (n : Int) (k : Nat) :
    (I.geometricSpokeKernelLedger P n k).base =
      I.geometricColumnKernelLedger n k := rfl

@[simp] theorem geometricSpokeKernelLedger_component
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.geometricSpokeKernelLedger P n k).component i =
      (I.dStageSpokePolyIso P (I.columnDStage n k)).component i := rfl

theorem geometricSpokeKernelLedger_packet_q (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.family.theater
      (P.permutation ((I.geometricSpokeKernelLedger P n k).base.column.source i))).thetaPacket.q =
      (I.geometricSpokeKernelLedger P n k).base.column.packet i |>.q :=
  (I.geometricSpokeKernelLedger P n k).packet_q i

theorem geometricSpokeKernelLedger_packet_scale (P : H2SpokePermutation I)
    (n : Int) (k : Nat) (i : Fin (k + 1)) (j : SignedLabel l.value) :
    (I.family.theater
      (P.permutation ((I.geometricSpokeKernelLedger P n k).base.column.source i))).thetaPacket.scale j =
      (I.geometricSpokeKernelLedger P n k).base.column.packet i |>.scale j :=
  (I.geometricSpokeKernelLedger P n k).packet_scale i j

theorem geometricSpokeKernelLedger_kernel_transport
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (x : ((I.spokeCapsule P (I.columnFStage n k)).strip i).toD.Pi v) :
    x ∈ (I.spokeCapsule P (I.columnFStage n k) |>.strip i).toD.geometric v ↔
      ((I.geometricSpokeKernelLedger P n k).component i).isoPi v x ∈
        (I.geometricSpokeKernelLedger P n k).base.kernel i v :=
  (I.geometricSpokeKernelLedger P n k).kernel_transport i v x

theorem geometricSpokeKernelLedger_natural
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        ((I.dSpokeCapsule P (I.columnDStage n k)).link i j)
        ((I.geometricSpokeKernelLedger P n k).component j) =
      DPrimeStripEquiv.trans
        ((I.geometricSpokeKernelLedger P n k).component i)
        ((I.geometricSpokeKernelLedger P n k).base.column.dLink i j) :=
  (I.geometricSpokeKernelLedger P n k).naturality i j

theorem geometricSpokeKernelLedger_component_bijective
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V) :
    Function.Bijective
      ((I.geometricSpokeKernelLedger P n k).component i |>.isoPi v) := by
  exact ((I.geometricSpokeKernelLedger P n k).component i).isoPi v |>.bijective

theorem geometricSpokeKernelLedger_identity
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.geometricSpokeKernelLedger (H2SpokePermutation.identity (I := I)) n k).component i =
      DPrimeStripEquiv.refl
        ((I.geometricSpokeKernelLedger (H2SpokePermutation.identity (I := I)) n k).base.column.dStage.strip i) := by
  exact I.stageSpoke_identity_component (I.columnDStage n k) i

/-! ## 11. Combined geometric-kernel source ledger -/

structure CombinedGeometricKernelLedger (P : H2SpokePermutation I) where
  point : ∀ n m, I.SourcePointBundle n m
  column : ∀ n k, I.GeometricColumnKernelLedger n k
  procession : ∀ n, I.GeometricColumnProcessionLedger n
  translation : ∀ a n k, I.GeometricTranslationKernelLedger a n k
  spoke : ∀ n k, I.GeometricSpokeKernelLedger P n k
  point_kernel_transport : ∀ n m n' m' v x,
    x ∈ (point n m).kernel.kernel v ↔
      (I.dPrimeStripLinkAt n m n' m').isoPi v x ∈
        (point n' m').kernel.kernel v
  column_point_source : ∀ n k i,
    (column n k).kernel i =
      (point n (i.1 : Int)).kernel.kernel

def combinedGeometricKernelLedger (P : H2SpokePermutation I) :
    I.CombinedGeometricKernelLedger P where
  point := I.sourcePointBundle
  column := I.geometricColumnKernelLedger
  procession := I.geometricColumnProcessionLedger
  translation := I.geometricTranslationKernelLedger
  spoke := I.geometricSpokeKernelLedger P
  point_kernel_transport := by
    intro n m n' m' v x
    exact I.sourcePointBundle_kernel_transport n m n' m' v x
  column_point_source := by
    intro n k i
    rfl

@[simp] theorem combinedGeometricKernelLedger_point
    (P : H2SpokePermutation I) (n m : Int) :
    (I.combinedGeometricKernelLedger P).point n m =
      I.sourcePointBundle n m := rfl

@[simp] theorem combinedGeometricKernelLedger_column
    (P : H2SpokePermutation I) (n : Int) (k : Nat) :
    (I.combinedGeometricKernelLedger P).column n k =
      I.geometricColumnKernelLedger n k := rfl

theorem combinedGeometricKernelLedger_point_transport
    (P : H2SpokePermutation I) (n m n' m' : Int) (v : V)
    (x : (I.combinedGeometricKernelLedger P).point n m |>.kernel.dStrip.Pi v) :
    x ∈ (I.combinedGeometricKernelLedger P).point n m |>.kernel.kernel v ↔
      (I.dPrimeStripLinkAt n m n' m').isoPi v x ∈
        (I.combinedGeometricKernelLedger P).point n' m' |>.kernel.kernel v :=
  (I.combinedGeometricKernelLedger P).point_kernel_transport n m n' m' v x

theorem combinedGeometricKernelLedger_column_source
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.combinedGeometricKernelLedger P).column n k |>.kernel i =
      (I.combinedGeometricKernelLedger P).point n (i.1 : Int) |>.kernel.kernel :=
  (I.combinedGeometricKernelLedger P).column_point_source n k i

/-! ## 12. Point-link packet and kernel ledger -/

structure GeometricKernelPointLinkLedger (n m n' m' : Int) where
  source : I.SourcePointBundle n m
  target : I.SourcePointBundle n' m'
  link : DPrimeStripEquiv source.kernel.dStrip target.kernel.dStrip
  link_source : link = I.dPrimeStripLinkAt n m n' m'
  projection : ∀ v (x : source.kernel.dStrip.Pi v),
    target.kernel.dStrip.proj v (link.isoPi v x) =
      link.isoG v (source.kernel.dStrip.proj v x)
  kernel_transport : ∀ v (x : source.kernel.dStrip.Pi v),
    x ∈ source.kernel.kernel v ↔ link.isoPi v x ∈ target.kernel.kernel v
  q_transport : source.packet.packet.q = target.packet.packet.q
  scale_transport : ∀ j,
    source.packet.packet.scale j = target.packet.packet.scale j
  log_volume_transport : source.packet.packet.logVolume =
    target.packet.packet.logVolume
  arithmetic_transport : source.packet.arithmetic = target.packet.arithmetic

def geometricKernelPointLinkLedgerAt (n m n' m' : Int) :
    I.GeometricKernelPointLinkLedger n m n' m' where
  source := I.sourcePointBundle n m
  target := I.sourcePointBundle n' m'
  link := I.dPrimeStripLinkAt n m n' m'
  link_source := rfl
  projection := by
    intro v x
    exact I.dPrimeStripLinkAt_compatProj n m n' m' v x
  kernel_transport := by
    intro v x
    exact I.sourcePointBundle_kernel_transport n m n' m' v x
  q_transport := I.sourcePointBundle_packet_q_transport n m n' m'
  scale_transport := by
    intro j
    exact I.sourcePointBundle_packet_scale_transport n m n' m' j
  log_volume_transport := by
    exact I.geometricKernelPacketLedgerAt_log_volume_transport n m n' m'
  arithmetic_transport := by
    rfl

@[simp] theorem geometricKernelPointLinkLedgerAt_source
    (n m n' m' : Int) :
    (I.geometricKernelPointLinkLedgerAt n m n' m').source =
      I.sourcePointBundle n m := rfl

@[simp] theorem geometricKernelPointLinkLedgerAt_target
    (n m n' m' : Int) :
    (I.geometricKernelPointLinkLedgerAt n m n' m').target =
      I.sourcePointBundle n' m' := rfl

@[simp] theorem geometricKernelPointLinkLedgerAt_link
    (n m n' m' : Int) :
    (I.geometricKernelPointLinkLedgerAt n m n' m').link =
      I.dPrimeStripLinkAt n m n' m' := rfl

theorem geometricKernelPointLinkLedgerAt_projection
    (n m n' m' : Int) (v : V)
    (x : (I.geometricKernelPointLinkLedgerAt n m n' m').source.kernel.dStrip.Pi v) :
    (I.geometricKernelPointLinkLedgerAt n m n' m').target.kernel.dStrip.proj v
        ((I.geometricKernelPointLinkLedgerAt n m n' m').link.isoPi v x) =
      (I.geometricKernelPointLinkLedgerAt n m n' m').link.isoG v
        ((I.geometricKernelPointLinkLedgerAt n m n' m').source.kernel.dStrip.proj v x) :=
  (I.geometricKernelPointLinkLedgerAt n m n' m').projection v x

theorem geometricKernelPointLinkLedgerAt_kernel_transport
    (n m n' m' : Int) (v : V)
    (x : (I.geometricKernelPointLinkLedgerAt n m n' m').source.kernel.dStrip.Pi v) :
    x ∈ (I.geometricKernelPointLinkLedgerAt n m n' m').source.kernel.kernel v ↔
      (I.geometricKernelPointLinkLedgerAt n m n' m').link.isoPi v x ∈
        (I.geometricKernelPointLinkLedgerAt n m n' m').target.kernel.kernel v :=
  (I.geometricKernelPointLinkLedgerAt n m n' m').kernel_transport v x

theorem geometricKernelPointLinkLedgerAt_q_transport
    (n m n' m' : Int) :
    (I.geometricKernelPointLinkLedgerAt n m n' m').source.packet.packet.q =
      (I.geometricKernelPointLinkLedgerAt n m n' m').target.packet.packet.q :=
  (I.geometricKernelPointLinkLedgerAt n m n' m').q_transport

theorem geometricKernelPointLinkLedgerAt_scale_transport
    (n m n' m' : Int) (j : SignedLabel l.value) :
    (I.geometricKernelPointLinkLedgerAt n m n' m').source.packet.packet.scale j =
      (I.geometricKernelPointLinkLedgerAt n m n' m').target.packet.packet.scale j :=
  (I.geometricKernelPointLinkLedgerAt n m n' m').scale_transport j

theorem geometricKernelPointLinkLedgerAt_log_volume_transport
    (n m n' m' : Int) :
    (I.geometricKernelPointLinkLedgerAt n m n' m').source.packet.packet.logVolume =
      (I.geometricKernelPointLinkLedgerAt n m n' m').target.packet.packet.logVolume :=
  (I.geometricKernelPointLinkLedgerAt n m n' m').log_volume_transport

theorem geometricKernelPointLinkLedgerAt_arithmetic_transport
    (n m n' m' : Int) :
    (I.geometricKernelPointLinkLedgerAt n m n' m').source.packet.arithmetic =
      (I.geometricKernelPointLinkLedgerAt n m n' m').target.packet.arithmetic :=
  (I.geometricKernelPointLinkLedgerAt n m n' m').arithmetic_transport

theorem geometricKernelPointLinkLedgerAt_isoPi_bijective
    (n m n' m' : Int) (v : V) :
    Function.Bijective
      ((I.geometricKernelPointLinkLedgerAt n m n' m').link.isoPi v) := by
  exact ((I.geometricKernelPointLinkLedgerAt n m n' m').link.isoPi v).bijective

theorem geometricKernelPointLinkLedgerAt_refl (n m : Int) :
    (I.geometricKernelPointLinkLedgerAt n m n m).link =
      DPrimeStripEquiv.refl
        (I.geometricKernelPointLinkLedgerAt n m n m).source.kernel.dStrip := by
  exact I.dPrimeStripLinkAt_refl n m

theorem geometricKernelPointLinkLedgerAt_symm (n m n' m' : Int) :
    DPrimeStripEquiv.symm
        (I.geometricKernelPointLinkLedgerAt n m n' m').link =
      (I.geometricKernelPointLinkLedgerAt n' m' n m).link := by
  exact I.dPrimeStripLinkAt_symm n m n' m'

theorem geometricKernelPointLinkLedgerAt_trans
    (n m n' m' n'' m'' : Int) :
    DPrimeStripEquiv.trans
        (I.geometricKernelPointLinkLedgerAt n m n' m').link
        (I.geometricKernelPointLinkLedgerAt n' m' n'' m'').link =
      (I.geometricKernelPointLinkLedgerAt n m n'' m'').link := by
  exact I.dPrimeStripLinkAt_trans n m n' m' n'' m''

/-! ## 13. Finite column packet-kernel ledger -/

structure GeometricColumnPacketKernelLedger (n : Int) (k : Nat) where
  geometric : I.GeometricColumnKernelLedger n k
  packet : Fin (k + 1) → FiniteThetaPacket l
  packet_source : ∀ i,
    packet i = (I.theaterAt n (i.1 : Int)).thetaPacket
  packet_kernel : ∀ i v,
    geometric.kernel i v = I.geometricAt n (i.1 : Int) v
  q_positive : ∀ i, 0 < (packet i).q
  scale_positive : ∀ i j, 0 < (packet i).scale j
  log_volume : ∀ i,
    (packet i).logVolume =
      ∑ j : SignedLabel l.value, Real.log ((packet i).scale j)
  q_transport : ∀ i j, (packet i).q = (packet j).q
  scale_transport : ∀ i j x, (packet i).scale x = (packet j).scale x
  log_volume_transport : ∀ i j, (packet i).logVolume = (packet j).logVolume
  source_injective : Function.Injective geometric.column.source
  cardinality : Fintype.card (Fin (k + 1)) = k + 1

def geometricColumnPacketKernelLedger (n : Int) (k : Nat) :
    I.GeometricColumnPacketKernelLedger n k where
  geometric := I.geometricColumnKernelLedger n k
  packet := fun i => (I.theaterAt n (i.1 : Int)).thetaPacket
  packet_source := by intro i; rfl
  packet_kernel := by intro i v; rfl
  q_positive := by
    intro i
    exact (I.theaterAt n (i.1 : Int)).thetaPacket.q_pos
  scale_positive := by
    intro i j
    exact (I.theaterAt n (i.1 : Int)).thetaPacket.scale_pos j
  log_volume := by
    intro i
    exact (I.theaterAt n (i.1 : Int)).thetaPacket.logVolume_eq_sum
  q_transport := by
    intro i j
    exact I.linkAt_q n (i.1 : Int) n (j.1 : Int)
  scale_transport := by
    intro i j x
    exact I.linkAt_scale n (i.1 : Int) n (j.1 : Int) x
  log_volume_transport := by
    intro i j
    exact (I.linkAt n (i.1 : Int) n (j.1 : Int)).log_volume_eq
  source_injective :=
    (I.geometricColumnKernelLedger n k).source_injective
  cardinality := (I.geometricColumnKernelLedger n k).cardinality

@[simp] theorem geometricColumnPacketKernelLedger_geometric
    (n : Int) (k : Nat) :
    (I.geometricColumnPacketKernelLedger n k).geometric =
      I.geometricColumnKernelLedger n k := rfl

@[simp] theorem geometricColumnPacketKernelLedger_packet
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.geometricColumnPacketKernelLedger n k).packet i =
      (I.theaterAt n (i.1 : Int)).thetaPacket := rfl

theorem geometricColumnPacketKernelLedger_packet_source
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.geometricColumnPacketKernelLedger n k).packet i =
      (I.theaterAt n (i.1 : Int)).thetaPacket :=
  (I.geometricColumnPacketKernelLedger n k).packet_source i

theorem geometricColumnPacketKernelLedger_packet_kernel
    (n : Int) (k : Nat) (i : Fin (k + 1)) (v : V) :
    (I.geometricColumnPacketKernelLedger n k).geometric.kernel i v =
      I.geometricAt n (i.1 : Int) v :=
  (I.geometricColumnPacketKernelLedger n k).packet_kernel i v

theorem geometricColumnPacketKernelLedger_q_positive
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    0 < (I.geometricColumnPacketKernelLedger n k).packet i |>.q :=
  (I.geometricColumnPacketKernelLedger n k).q_positive i

theorem geometricColumnPacketKernelLedger_scale_positive
    (n : Int) (k : Nat) (i : Fin (k + 1)) (j : SignedLabel l.value) :
    0 < (I.geometricColumnPacketKernelLedger n k).packet i |>.scale j :=
  (I.geometricColumnPacketKernelLedger n k).scale_positive i j

theorem geometricColumnPacketKernelLedger_log_volume
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.geometricColumnPacketKernelLedger n k).packet i |>.logVolume =
      ∑ j : SignedLabel l.value,
        Real.log ((I.geometricColumnPacketKernelLedger n k).packet i |>.scale j) :=
  (I.geometricColumnPacketKernelLedger n k).log_volume i

theorem geometricColumnPacketKernelLedger_q_transport
    (n : Int) (k : Nat) (i j : Fin (k + 1)) :
    (I.geometricColumnPacketKernelLedger n k).packet i |>.q =
      (I.geometricColumnPacketKernelLedger n k).packet j |>.q :=
  (I.geometricColumnPacketKernelLedger n k).q_transport i j

theorem geometricColumnPacketKernelLedger_scale_transport
    (n : Int) (k : Nat) (i j : Fin (k + 1)) (x : SignedLabel l.value) :
    (I.geometricColumnPacketKernelLedger n k).packet i |>.scale x =
      (I.geometricColumnPacketKernelLedger n k).packet j |>.scale x :=
  (I.geometricColumnPacketKernelLedger n k).scale_transport i j x

theorem geometricColumnPacketKernelLedger_log_volume_transport
    (n : Int) (k : Nat) (i j : Fin (k + 1)) :
    (I.geometricColumnPacketKernelLedger n k).packet i |>.logVolume =
      (I.geometricColumnPacketKernelLedger n k).packet j |>.logVolume :=
  (I.geometricColumnPacketKernelLedger n k).log_volume_transport i j

theorem geometricColumnPacketKernelLedger_source_injective
    (n : Int) (k : Nat) :
    Function.Injective
      (I.geometricColumnPacketKernelLedger n k).geometric.column.source :=
  (I.geometricColumnPacketKernelLedger n k).source_injective

theorem geometricColumnPacketKernelLedger_cardinality
    (n : Int) (k : Nat) :
    Fintype.card (Fin (k + 1)) = k + 1 :=
  (I.geometricColumnPacketKernelLedger n k).cardinality

theorem geometricColumnPacketKernelLedger_kernel_link
    (n : Int) (k : Nat) (i j : Fin (k + 1)) (v : V)
    (x : (I.geometricColumnPacketKernelLedger n k).geometric.column.dStage.strip i.Pi v) :
    x ∈ (I.geometricColumnPacketKernelLedger n k).geometric.kernel i v ↔
      ((I.geometricColumnPacketKernelLedger n k).geometric.column.dLink i j).isoPi v x ∈
        (I.geometricColumnPacketKernelLedger n k).geometric.kernel j v := by
  exact I.geometricColumnKernelLedger_link_kernel_transport n k i j v x

/-! ## 14. Translation groupoid wrappers -/

theorem geometricTranslationKernelLedger_map_bijective
    (a n : Int) (k : Nat) :
    Function.Bijective (I.geometricTranslationKernelLedger a n k).map := by
  exact (I.geometricTranslationKernelLedger a n k).map.bijective

theorem geometricTranslationKernelLedger_component_bijective
    (a n : Int) (k : Nat) (i : Fin (k + 1)) (v : V) :
    Function.Bijective
      ((I.geometricTranslationKernelLedger a n k).component i |>.isoPi v) := by
  exact ((I.geometricTranslationKernelLedger a n k).component i).isoPi v |>.bijective

theorem geometricTranslationKernelLedger_component_projection
    (a n : Int) (k : Nat) (i : Fin (k + 1)) (v : V)
    (x : (I.geometricTranslationKernelLedger a n k).base.column.dStage.strip i.Pi v) :
    (I.geometricTranslationKernelLedger a n k).target.column.dStage.strip i.proj v
        ((I.geometricTranslationKernelLedger a n k).component i |>.isoPi v x) =
      (I.geometricTranslationKernelLedger a n k).component i |>.isoG v
        ((I.geometricTranslationKernelLedger a n k).base.column.dStage.strip i.proj v x) := by
  exact (I.geometricTranslationKernelLedger a n k).component i |>.compat_apply v x

theorem geometricTranslationKernelLedger_kernel_source_iff
    (a n : Int) (k : Nat) (i : Fin (k + 1)) (v : V)
    (x : (I.geometricTranslationKernelLedger a n k).base.column.dStage.strip i.Pi v) :
    x ∈ (I.geometricTranslationKernelLedger a n k).base.kernel i v ↔
      (I.geometricTranslationKernelLedger a n k).component i |>.isoPi v x ∈
        (I.geometricTranslationKernelLedger a n k).target.kernel i v :=
  (I.geometricTranslationKernelLedger a n k).kernel_transport i v x

theorem geometricTranslationKernelLedger_zero_kernel
    (n : Int) (k : Nat) (i : Fin (k + 1)) (v : V)
    (x : (I.geometricTranslationKernelLedger 0 n k).base.column.dStage.strip i.Pi v) :
    x ∈ (I.geometricTranslationKernelLedger 0 n k).base.kernel i v ↔
      (I.geometricTranslationKernelLedger 0 n k).component i |>.isoPi v x ∈
        (I.geometricTranslationKernelLedger 0 n k).target.kernel i v :=
  (I.geometricTranslationKernelLedger 0 n k).kernel_transport i v x

theorem geometricTranslationKernelLedger_add_kernel
    (a b n : Int) (k : Nat) (i : Fin (k + 1)) (v : V)
    (x : (I.geometricTranslationKernelLedger a n k).base.column.dStage.strip i.Pi v) :
    x ∈ (I.geometricTranslationKernelLedger a n k).base.kernel i v ↔
      ((I.geometricTranslationKernelLedger b (n + a) k).component i |>.isoPi v
        ((I.geometricTranslationKernelLedger a n k).component i |>.isoPi v x)) ∈
        (I.geometricTranslationKernelLedger (a + b) n k).target.kernel i v := by
  rw [← geometricTranslationKernelLedger_add_component]
  exact (I.geometricTranslationKernelLedger (a + b) n k).kernel_transport i v x

theorem geometricTranslationKernelLedger_inverse_kernel
    (a n : Int) (k : Nat) (i : Fin (k + 1)) (v : V)
    (x : (I.geometricTranslationKernelLedger a n k).base.column.dStage.strip i.Pi v) :
    x ∈ (I.geometricTranslationKernelLedger a n k).base.kernel i v ↔
      ((I.geometricTranslationKernelLedger (-a) (n + a) k).component i |>.isoPi v
        ((I.geometricTranslationKernelLedger a n k).component i |>.isoPi v x)) ∈
        (I.geometricTranslationKernelLedger 0 n k).target.kernel i v := by
  rw [← geometricTranslationKernelLedger_inverse_component]
  exact (I.geometricTranslationKernelLedger 0 n k).kernel_transport i v x

/-! ## 15. Spoke packet and degree wrappers -/

theorem geometricSpokeKernelLedger_component_projection
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (x : (I.geometricSpokeKernelLedger P n k).spoke.source.fStage.strip i.Pi v) :
    (I.geometricSpokeKernelLedger P n k).base.column.dStage.strip i.proj v
        ((I.geometricSpokeKernelLedger P n k).component i |>.isoPi v x) =
      (I.geometricSpokeKernelLedger P n k).component i |>.isoG v
        ((I.geometricSpokeKernelLedger P n k).spoke.source.fStage.strip i.toD.proj v x) := by
  exact (I.geometricSpokeKernelLedger P n k).component i |>.compat_apply v x

theorem geometricSpokeKernelLedger_component_degree
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (x : (I.geometricSpokeKernelLedger P n k).spoke.source.fStage.strip i.Mon v) :
    (I.geometricSpokeKernelLedger P n k).base.column.dStage.strip i.toD.degree v
        ((I.geometricSpokeKernelLedger P n k).component i |>.isoMon v x) =
      (I.geometricSpokeKernelLedger P n k).spoke.source.fStage.strip i.degree v x := by
  exact (I.geometricSpokeKernelLedger P n k).spoke.source.fStage.strip i |>.link_degree_commutes
    _ _ _ _ _

theorem geometricSpokeKernelLedger_kernel_source_iff
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (x : ((I.spokeCapsule P (I.columnFStage n k)).strip i).toD.Pi v) :
    x ∈ (I.spokeCapsule P (I.columnFStage n k) |>.strip i).toD.geometric v ↔
      (I.geometricSpokeKernelLedger P n k).component i |>.isoPi v x ∈
        (I.geometricSpokeKernelLedger P n k).base.kernel i v :=
  (I.geometricSpokeKernelLedger P n k).kernel_transport i v x

theorem geometricSpokeKernelLedger_packet_q_transport
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.family.theater
      (P.permutation ((I.geometricSpokeKernelLedger P n k).base.column.source i))).thetaPacket.q =
      (I.geometricSpokeKernelLedger P n k).base.column.packet i |>.q :=
  (I.geometricSpokeKernelLedger P n k).packet_q i

theorem geometricSpokeKernelLedger_packet_scale_transport
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) (j : SignedLabel l.value) :
    (I.family.theater
      (P.permutation ((I.geometricSpokeKernelLedger P n k).base.column.source i))).thetaPacket.scale j =
      (I.geometricSpokeKernelLedger P n k).base.column.packet i |>.scale j :=
  (I.geometricSpokeKernelLedger P n k).packet_scale i j

/-! ## 16. Final reusable source bundle -/

structure GeometricKernelSourceBundle (P : H2SpokePermutation I) where
  combined : I.CombinedGeometricKernelLedger P
  point_link : ∀ n m n' m', I.GeometricKernelPointLinkLedger n m n' m'
  column_packet : ∀ n k, I.GeometricColumnPacketKernelLedger n k
  combined_source : combined = I.combinedGeometricKernelLedger P

def geometricKernelSourceBundle (P : H2SpokePermutation I) :
    I.GeometricKernelSourceBundle P where
  combined := I.combinedGeometricKernelLedger P
  point_link := I.geometricKernelPointLinkLedgerAt
  column_packet := I.geometricColumnPacketKernelLedger
  combined_source := rfl

@[simp] theorem geometricKernelSourceBundle_combined
    (P : H2SpokePermutation I) :
    (I.geometricKernelSourceBundle P).combined =
      I.combinedGeometricKernelLedger P := rfl

theorem geometricKernelSourceBundle_point_link
    (P : H2SpokePermutation I) (n m n' m' : Int) :
    (I.geometricKernelSourceBundle P).point_link n m n' m' =
      I.geometricKernelPointLinkLedgerAt n m n' m' := rfl

theorem geometricKernelSourceBundle_column_packet
    (P : H2SpokePermutation I) (n : Int) (k : Nat) :
    (I.geometricKernelSourceBundle P).column_packet n k =
      I.geometricColumnPacketKernelLedger n k := rfl

theorem geometricKernelSourceBundle_point_transport
    (P : H2SpokePermutation I) (n m n' m' : Int) (v : V)
    (x : ((I.geometricKernelSourceBundle P).combined.point n m).kernel.dStrip.Pi v) :
    x ∈ ((I.geometricKernelSourceBundle P).combined.point n m).kernel.kernel v ↔
      (I.dPrimeStripLinkAt n m n' m').isoPi v x ∈
        ((I.geometricKernelSourceBundle P).combined.point n' m').kernel.kernel v :=
  (I.geometricKernelSourceBundle P).combined.point_kernel_transport n m n' m' v x

theorem geometricKernelSourceBundle_column_kernel
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V) :
    ((I.geometricKernelSourceBundle P).column_packet n k).geometric.kernel i v =
      I.geometricAt n (i.1 : Int) v := by
  exact I.geometricColumnPacketKernelLedger_packet_kernel n k i v

theorem geometricKernelSourceBundle_column_q
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    ((I.geometricKernelSourceBundle P).column_packet n k).packet i |>.q =
      ((I.geometricKernelSourceBundle P).column_packet n k).packet j |>.q :=
  I.geometricColumnPacketKernelLedger_q_transport n k i j

theorem geometricKernelSourceBundle_column_scale
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i j : Fin (k + 1)) (x : SignedLabel l.value) :
    ((I.geometricKernelSourceBundle P).column_packet n k).packet i |>.scale x =
      ((I.geometricKernelSourceBundle P).column_packet n k).packet j |>.scale x :=
  I.geometricColumnPacketKernelLedger_scale_transport n k i j x

theorem geometricKernelSourceBundle_translation_kernel
    (P : H2SpokePermutation I) (a n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (x : (I.geometricTranslationKernelLedger a n k).base.column.dStage.strip i.Pi v) :
    x ∈ (I.geometricTranslationKernelLedger a n k).base.kernel i v ↔
      (I.geometricTranslationKernelLedger a n k).component i |>.isoPi v x ∈
        (I.geometricTranslationKernelLedger a n k).target.kernel i v :=
  I.geometricTranslationKernelLedger_kernel_source_iff a n k i v x

theorem geometricKernelSourceBundle_spoke_kernel
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (x : ((I.spokeCapsule P (I.columnFStage n k)).strip i).toD.Pi v) :
    x ∈ (I.spokeCapsule P (I.columnFStage n k) |>.strip i).toD.geometric v ↔
      (I.geometricSpokeKernelLedger P n k).component i |>.isoPi v x ∈
        (I.geometricSpokeKernelLedger P n k).base.kernel i v :=
  I.geometricSpokeKernelLedger_kernel_source_iff P n k i v x

/-! ## 17. Kernel, action, and degree at a linked point -/

structure GeometricKernelDegreeLinkLedger (n m n' m' : Int) where
  source : I.GeometricKernelValueLedger n m
  target : I.GeometricKernelValueLedger n' m'
  link : FPrimeStripEquiv source.fStrip target.fStrip
  dLink : DPrimeStripEquiv source.geometric.dStrip target.geometric.dStrip
  link_source : link = I.primeStripLinkAt n m n' m'
  dLink_source : dLink = I.dPrimeStripLinkAt n m n' m'
  action_transport : ∀ v (g : source.fStrip.toD.Pi v)
      (x : source.fStrip.Mon v),
    link.isoMon v (source.fStrip.action v g x) =
      target.fStrip.action v (link.isoPi v g) (link.isoMon v x)
  degree_transport : ∀ v (x : source.fStrip.Mon v),
    target.fStrip.degree v (link.isoMon v x) = source.fStrip.degree v x
  total_degree_transport : ∀ (s : Finset V)
      (x : ∀ v, source.fStrip.Mon v),
    target.fStrip.totalDegree s
        (fun v => link.isoMon v (x v)) = source.fStrip.totalDegree s x
  kernel_transport : ∀ v (x : source.geometric.dStrip.Pi v),
    x ∈ source.geometric.kernel v ↔
      dLink.isoPi v x ∈ target.geometric.kernel v
  source_projection : ∀ v (x : source.geometric.dStrip.Pi v),
    target.geometric.dStrip.proj v (dLink.isoPi v x) =
      dLink.isoG v (source.geometric.dStrip.proj v x)

def geometricKernelDegreeLinkLedgerAt (n m n' m' : Int) :
    I.GeometricKernelDegreeLinkLedger n m n' m' where
  source := I.geometricKernelValueLedgerAt n m
  target := I.geometricKernelValueLedgerAt n' m'
  link := I.primeStripLinkAt n m n' m'
  dLink := I.dPrimeStripLinkAt n m n' m'
  link_source := rfl
  dLink_source := rfl
  action_transport := by
    intro v g x
    exact I.primeStripLinkAt_compatAction n m n' m' v g x
  degree_transport := by
    intro v x
    exact I.primeStripLinkAt_compatDegree n m n' m' v x
  total_degree_transport := by
    intro s x
    exact I.geometricKernelValueLedgerAt_total_degree_transport n m n' m' s x
  kernel_transport := by
    intro v x
    exact I.geometricKernelValueLedgerAt_kernel_transport n m n' m' v x
  source_projection := by
    intro v x
    exact I.dPrimeStripLinkAt_compatProj n m n' m' v x

@[simp] theorem geometricKernelDegreeLinkLedgerAt_source
    (n m n' m' : Int) :
    (I.geometricKernelDegreeLinkLedgerAt n m n' m').source =
      I.geometricKernelValueLedgerAt n m := rfl

@[simp] theorem geometricKernelDegreeLinkLedgerAt_target
    (n m n' m' : Int) :
    (I.geometricKernelDegreeLinkLedgerAt n m n' m').target =
      I.geometricKernelValueLedgerAt n' m' := rfl

@[simp] theorem geometricKernelDegreeLinkLedgerAt_link
    (n m n' m' : Int) :
    (I.geometricKernelDegreeLinkLedgerAt n m n' m').link =
      I.primeStripLinkAt n m n' m' := rfl

@[simp] theorem geometricKernelDegreeLinkLedgerAt_dLink
    (n m n' m' : Int) :
    (I.geometricKernelDegreeLinkLedgerAt n m n' m').dLink =
      I.dPrimeStripLinkAt n m n' m' := rfl

theorem geometricKernelDegreeLinkLedgerAt_action
    (n m n' m' : Int) (v : V)
    (g : (I.geometricKernelDegreeLinkLedgerAt n m n' m').source.fStrip.toD.Pi v)
    (x : (I.geometricKernelDegreeLinkLedgerAt n m n' m').source.fStrip.Mon v) :
    (I.geometricKernelDegreeLinkLedgerAt n m n' m').link.isoMon v
        ((I.geometricKernelDegreeLinkLedgerAt n m n' m').source.fStrip.action v g x) =
      (I.geometricKernelDegreeLinkLedgerAt n m n' m').target.fStrip.action v
        ((I.geometricKernelDegreeLinkLedgerAt n m n' m').link.isoPi v g)
        ((I.geometricKernelDegreeLinkLedgerAt n m n' m').link.isoMon v x) :=
  (I.geometricKernelDegreeLinkLedgerAt n m n' m').action_transport v g x

theorem geometricKernelDegreeLinkLedgerAt_degree
    (n m n' m' : Int) (v : V)
    (x : (I.geometricKernelDegreeLinkLedgerAt n m n' m').source.fStrip.Mon v) :
    (I.geometricKernelDegreeLinkLedgerAt n m n' m').target.fStrip.degree v
        ((I.geometricKernelDegreeLinkLedgerAt n m n' m').link.isoMon v x) =
      (I.geometricKernelDegreeLinkLedgerAt n m n' m').source.fStrip.degree v x :=
  (I.geometricKernelDegreeLinkLedgerAt n m n' m').degree_transport v x

theorem geometricKernelDegreeLinkLedgerAt_total_degree
    (n m n' m' : Int) (s : Finset V)
    (x : ∀ v, (I.geometricKernelDegreeLinkLedgerAt n m n' m').source.fStrip.Mon v) :
    (I.geometricKernelDegreeLinkLedgerAt n m n' m').target.fStrip.totalDegree s
        (fun v => (I.geometricKernelDegreeLinkLedgerAt n m n' m').link.isoMon v
          (x v)) =
      (I.geometricKernelDegreeLinkLedgerAt n m n' m').source.fStrip.totalDegree s x :=
  (I.geometricKernelDegreeLinkLedgerAt n m n' m').total_degree_transport s x

theorem geometricKernelDegreeLinkLedgerAt_kernel
    (n m n' m' : Int) (v : V)
    (x : (I.geometricKernelDegreeLinkLedgerAt n m n' m').source.geometric.dStrip.Pi v) :
    x ∈ (I.geometricKernelDegreeLinkLedgerAt n m n' m').source.geometric.kernel v ↔
      (I.geometricKernelDegreeLinkLedgerAt n m n' m').dLink.isoPi v x ∈
        (I.geometricKernelDegreeLinkLedgerAt n m n' m').target.geometric.kernel v :=
  (I.geometricKernelDegreeLinkLedgerAt n m n' m').kernel_transport v x

theorem geometricKernelDegreeLinkLedgerAt_projection
    (n m n' m' : Int) (v : V)
    (x : (I.geometricKernelDegreeLinkLedgerAt n m n' m').source.geometric.dStrip.Pi v) :
    (I.geometricKernelDegreeLinkLedgerAt n m n' m').target.geometric.dStrip.proj v
        ((I.geometricKernelDegreeLinkLedgerAt n m n' m').dLink.isoPi v x) =
      (I.geometricKernelDegreeLinkLedgerAt n m n' m').dLink.isoG v
        ((I.geometricKernelDegreeLinkLedgerAt n m n' m').source.geometric.dStrip.proj v x) :=
  (I.geometricKernelDegreeLinkLedgerAt n m n' m').source_projection v x

theorem geometricKernelDegreeLinkLedgerAt_link_pi_bijective
    (n m n' m' : Int) (v : V) :
    Function.Bijective
      ((I.geometricKernelDegreeLinkLedgerAt n m n' m').link.isoPi v) := by
  exact ((I.geometricKernelDegreeLinkLedgerAt n m n' m').link.isoPi v).bijective

theorem geometricKernelDegreeLinkLedgerAt_link_mon_bijective
    (n m n' m' : Int) (v : V) :
    Function.Bijective
      ((I.geometricKernelDegreeLinkLedgerAt n m n' m').link.isoMon v) := by
  exact ((I.geometricKernelDegreeLinkLedgerAt n m n' m').link.isoMon v).bijective

theorem geometricKernelDegreeLinkLedgerAt_dlink_pi_bijective
    (n m n' m' : Int) (v : V) :
    Function.Bijective
      ((I.geometricKernelDegreeLinkLedgerAt n m n' m').dLink.isoPi v) := by
  exact ((I.geometricKernelDegreeLinkLedgerAt n m n' m').dLink.isoPi v).bijective

theorem geometricKernelDegreeLinkLedgerAt_dlink_g_bijective
    (n m n' m' : Int) (v : V) :
    Function.Bijective
      ((I.geometricKernelDegreeLinkLedgerAt n m n' m').dLink.isoG v) := by
  exact ((I.geometricKernelDegreeLinkLedgerAt n m n' m').dLink.isoG v).bijective

theorem geometricKernelDegreeLinkLedgerAt_refl (n m : Int) :
    (I.geometricKernelDegreeLinkLedgerAt n m n m).link =
      FPrimeStripEquiv.refl
        (I.geometricKernelDegreeLinkLedgerAt n m n m).source.fStrip := by
  exact I.primeStripLinkAt_refl n m

theorem geometricKernelDegreeLinkLedgerAt_symm (n m n' m' : Int) :
    FPrimeStripEquiv.symm
        (I.geometricKernelDegreeLinkLedgerAt n m n' m').link =
      (I.geometricKernelDegreeLinkLedgerAt n' m' n m).link := by
  exact I.primeStripLinkAt_symm n m n' m'

theorem geometricKernelDegreeLinkLedgerAt_trans
    (n m n' m' n'' m'' : Int) :
    FPrimeStripEquiv.trans
        (I.geometricKernelDegreeLinkLedgerAt n m n' m').link
        (I.geometricKernelDegreeLinkLedgerAt n' m' n'' m'').link =
      (I.geometricKernelDegreeLinkLedgerAt n m n'' m'').link := by
  exact I.primeStripLinkAt_trans n m n' m' n'' m''

/-! ## 18. Column action/degree/kernel ledger -/

structure GeometricColumnActionLedger (n : Int) (k : Nat) where
  column : I.GeometricColumnPacketKernelLedger n k
  action : ∀ (i : Fin (k + 1)) (v : V)
      (g : (column.geometric.column.fStage.strip i).toD.Pi v)
      (x : (column.geometric.column.fStage.strip i).Mon v),
    (column.geometric.column.fStage.strip i).action v (g) x =
      (column.geometric.column.fStage.strip i).action v g x
  degree : ∀ (i : Fin (k + 1)) (v : V)
      (x : (column.geometric.column.fStage.strip i).Mon v),
    (column.geometric.column.fStage.strip i).degree v x =
      (column.geometric.column.fStage.strip i).degree v x
  total_degree : ∀ (i : Fin (k + 1)) (s : Finset V)
      (x : ∀ v, (column.geometric.column.fStage.strip i).Mon v),
    (column.geometric.column.fStage.strip i).totalDegree s x =
      (column.geometric.column.fStage.strip i).totalDegree s x
  source_injective : Function.Injective column.geometric.column.source
  cardinality : Fintype.card (Fin (k + 1)) = k + 1

def geometricColumnActionLedger (n : Int) (k : Nat) :
    I.GeometricColumnActionLedger n k where
  column := I.geometricColumnPacketKernelLedger n k
  action := by intro i v g x; rfl
  degree := by intro i v x; rfl
  total_degree := by intro i s x; rfl
  source_injective :=
    (I.geometricColumnPacketKernelLedger n k).source_injective
  cardinality := (I.geometricColumnPacketKernelLedger n k).cardinality

@[simp] theorem geometricColumnActionLedger_column (n : Int) (k : Nat) :
    (I.geometricColumnActionLedger n k).column =
      I.geometricColumnPacketKernelLedger n k := rfl

theorem geometricColumnActionLedger_action (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (g : ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).toD.Pi v)
    (x : ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).Mon v) :
    ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).action v g x =
      ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).action v g x :=
  (I.geometricColumnActionLedger n k).action i v g x

theorem geometricColumnActionLedger_degree (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (x : ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).Mon v) :
    ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).degree v x =
      ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).degree v x :=
  (I.geometricColumnActionLedger n k).degree i v x

theorem geometricColumnActionLedger_total_degree (n : Int) (k : Nat)
    (i : Fin (k + 1)) (s : Finset V)
    (x : ∀ v, ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).Mon v) :
    ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).totalDegree s x =
      ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).totalDegree s x :=
  (I.geometricColumnActionLedger n k).total_degree i s x

theorem geometricColumnActionLedger_kernel (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V)
    (x : ((I.geometricColumnActionLedger n k).column.geometric.column.dStage.strip i).Pi v) :
    x ∈ (I.geometricColumnActionLedger n k).column.geometric.kernel i v ↔
      ((I.geometricColumnActionLedger n k).column.geometric.column.dStage.strip i).proj v x = 1 := by
  rw [geometricColumnActionLedger_column,
    geometricColumnPacketKernelLedger_geometric,
    geometricColumnKernelLedger_kernel]
  rfl

theorem geometricColumnActionLedger_packet_q (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.geometricColumnActionLedger n k).column.packet i |>.q > 0 :=
  (I.geometricColumnActionLedger n k).column.q_positive i

theorem geometricColumnActionLedger_packet_log_volume (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.geometricColumnActionLedger n k).column.packet i |>.logVolume =
      ∑ j : SignedLabel l.value,
        Real.log ((I.geometricColumnActionLedger n k).column.packet i |>.scale j) :=
  (I.geometricColumnActionLedger n k).column.log_volume i

theorem geometricColumnActionLedger_link_degree (n : Int) (k : Nat)
    (i j : Fin (k + 1)) (v : V)
    (x : ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).Mon v) :
    ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip j).degree v
        (((I.geometricColumnActionLedger n k).column.geometric.column.fLink i j).isoMon v x) =
      ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).degree v x := by
  exact ((I.geometricColumnActionLedger n k).column.geometric.column.fLink i j).compatDegree v x

theorem geometricColumnActionLedger_link_action (n : Int) (k : Nat)
    (i j : Fin (k + 1)) (v : V)
    (g : ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).toD.Pi v)
    (x : ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).Mon v) :
    ((I.geometricColumnActionLedger n k).column.geometric.column.fLink i j).isoMon v
        (((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i).action v g x) =
      ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip j).action v
        (((I.geometricColumnActionLedger n k).column.geometric.column.fLink i j).isoPi v g)
        (((I.geometricColumnActionLedger n k).column.geometric.column.fLink i j).isoMon v x) := by
  exact ((I.geometricColumnActionLedger n k).column.geometric.column.fLink i j).compatAction v g x

theorem geometricColumnActionLedger_link_kernel (n : Int) (k : Nat)
    (i j : Fin (k + 1)) (v : V)
    (x : ((I.geometricColumnActionLedger n k).column.geometric.column.dStage.strip i).Pi v) :
    x ∈ (I.geometricColumnActionLedger n k).column.geometric.kernel i v ↔
      ((I.geometricColumnActionLedger n k).column.geometric.column.dLink i j).isoPi v x ∈
        (I.geometricColumnActionLedger n k).column.geometric.kernel j v := by
  exact I.geometricColumnKernelLedger_link_kernel_transport n k i j v x

theorem geometricColumnActionLedger_link_projection (n : Int) (k : Nat)
    (i j : Fin (k + 1)) (v : V)
    (x : ((I.geometricColumnActionLedger n k).column.geometric.column.dStage.strip i).Pi v) :
    ((I.geometricColumnActionLedger n k).column.geometric.column.dStage.strip j).proj v
        (((I.geometricColumnActionLedger n k).column.geometric.column.dLink i j).isoPi v x) =
      ((I.geometricColumnActionLedger n k).column.geometric.column.dLink i j).isoG v
        (((I.geometricColumnActionLedger n k).column.geometric.column.dStage.strip i).proj v x) := by
  exact ((I.geometricColumnActionLedger n k).column.geometric.column.dLink i j).compat_apply v x

theorem geometricColumnActionLedger_link_refl (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.geometricColumnActionLedger n k).column.geometric.column.fLink i i =
      FPrimeStripEquiv.refl
        ((I.geometricColumnActionLedger n k).column.geometric.column.fStage.strip i) := by
  exact I.columnStageSourceLedger_fLink_refl n k i

theorem geometricColumnActionLedger_link_trans (n : Int) (k : Nat)
    (i j h : Fin (k + 1)) :
    FPrimeStripEquiv.trans
        ((I.geometricColumnActionLedger n k).column.geometric.column.fLink i j)
        ((I.geometricColumnActionLedger n k).column.geometric.column.fLink j h) =
      (I.geometricColumnActionLedger n k).column.geometric.column.fLink i h := by
  exact I.columnStageSourceLedger_fLink_trans n k i j h

theorem geometricColumnActionLedger_link_symm (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    FPrimeStripEquiv.symm
        ((I.geometricColumnActionLedger n k).column.geometric.column.fLink i j) =
      (I.geometricColumnActionLedger n k).column.geometric.column.fLink j i := by
  exact I.columnStageSourceLedger_fLink_symm n k i j

/-! ## 19. Fixed-column procession wrappers -/

theorem geometricColumnProcessionLedger_stage_kernel (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V) :
    ((I.geometricColumnProcessionLedger n).stage k).kernel i v =
      I.geometricAt n (i.1 : Int) v := by
  rfl

theorem geometricColumnProcessionLedger_stage_packet (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    ((I.geometricColumnProcessionLedger n).stage k).column.packet i =
      (I.theaterAt n (i.1 : Int)).thetaPacket := by
  rfl

theorem geometricColumnProcessionLedger_stage_q (n : Int) (k : Nat)
    (i j : Fin (k + 1)) :
    ((I.geometricColumnProcessionLedger n).stage k).column.packet i |>.q =
      ((I.geometricColumnProcessionLedger n).stage k).column.packet j |>.q := by
  exact I.geometricColumnPacketKernelLedger_q_transport n k i j

theorem geometricColumnProcessionLedger_stage_scale (n : Int) (k : Nat)
    (i j : Fin (k + 1)) (x : SignedLabel l.value) :
    ((I.geometricColumnProcessionLedger n).stage k).column.packet i |>.scale x =
      ((I.geometricColumnProcessionLedger n).stage k).column.packet j |>.scale x := by
  exact I.geometricColumnPacketKernelLedger_scale_transport n k i j x

theorem geometricColumnProcessionLedger_stage_log_volume (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    ((I.geometricColumnProcessionLedger n).stage k).column.packet i |>.logVolume =
      ∑ j : SignedLabel l.value,
        Real.log (((I.geometricColumnProcessionLedger n).stage k).column.packet i |>.scale j) := by
  exact I.geometricColumnPacketKernelLedger_log_volume n k i

theorem geometricColumnProcessionLedger_inclusion_source (n : Int)
    {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)) :
    ((I.geometricColumnProcessionLedger n).stage k).column.source i =
      ((I.geometricColumnProcessionLedger n).stage r).column.source
        ((I.geometricColumnProcessionLedger n).inclusion_map h i) := by
  exact I.columnProcessionSourceLedger_inclusion_source n h i

theorem geometricColumnProcessionLedger_inclusion_kernel (n : Int)
    {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)) (v : V)
    (x : ((I.geometricColumnProcessionLedger n).stage k).column.dStage.strip i.Pi v) :
    x ∈ ((I.geometricColumnProcessionLedger n).stage k).kernel i v ↔
      (((I.columnProcessionSourceLedger n).inclusion_d_component h i).isoPi v x) ∈
        ((I.geometricColumnProcessionLedger n).stage r).kernel
          ((I.geometricColumnProcessionLedger n).inclusion_map h i) v :=
  (I.geometricColumnProcessionLedger n).inclusion_kernel_transport h i v x

theorem geometricColumnProcessionLedger_inclusion_projection (n : Int)
    {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)) (v : V)
    (x : ((I.geometricColumnProcessionLedger n).stage k).column.dStage.strip i.Pi v) :
    ((I.geometricColumnProcessionLedger n).stage r).column.dStage.strip
        ((I.geometricColumnProcessionLedger n).inclusion_map h i).proj v
        (((I.columnProcessionSourceLedger n).inclusion_d_component h i).isoPi v x) =
      ((I.columnProcessionSourceLedger n).inclusion_d_component h i).isoG v
        (((I.geometricColumnProcessionLedger n).stage k).column.dStage.strip i.proj v x) := by
  exact ((I.columnProcessionSourceLedger n).inclusion_d_component h i).compat_apply v x

theorem geometricColumnProcessionLedger_inclusion_natural (n : Int)
    {k r : Nat} (h : k ≤ r) (i j : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        (((I.geometricColumnProcessionLedger n).stage k).column.dLink i j)
        ((I.columnProcessionSourceLedger n).inclusion_d_component h j) =
      DPrimeStripEquiv.trans
        ((I.columnProcessionSourceLedger n).inclusion_d_component h i)
        (((I.geometricColumnProcessionLedger n).stage r).column.dLink
          ((I.geometricColumnProcessionLedger n).inclusion_map h i)
          ((I.geometricColumnProcessionLedger n).inclusion_map h j)) :=
  I.geometricColumnProcessionLedger_natural n h i j

theorem geometricColumnProcessionLedger_inclusion_degree (n : Int)
    {k r : Nat} (h : k ≤ r) (i : Fin (k + 1)) (v : V)
    (x : ∀ v, ((I.geometricColumnProcessionLedger n).stage k).column.fStage.strip i.Mon v) :
    ((I.geometricColumnProcessionLedger n).stage r).column.fStage.strip
        ((I.geometricColumnProcessionLedger n).inclusion_map h i).totalDegree Finset.univ
        (fun v => ((I.columnProcessionSourceLedger n).inclusion_component h i).isoMon v (x v)) =
      ((I.geometricColumnProcessionLedger n).stage k).column.fStage.strip i.totalDegree Finset.univ x := by
  apply Finset.sum_congr rfl
  intro w hw
  exact ((I.columnProcessionSourceLedger n).inclusion_component h i).compatDegree w (x w)

/-! ## 20. Source boundary summary for the geometric kernel -/

structure GeometricKernelBoundarySummary (P : H2SpokePermutation I) where
  point : ∀ n m, I.GeometricKernelPointLinkLedger n m n m
  column : ∀ n k, I.GeometricColumnActionLedger n k
  procession : ∀ n, I.GeometricColumnProcessionLedger n
  translation : ∀ a n k, I.GeometricTranslationKernelLedger a n k
  spoke : ∀ n k, I.GeometricSpokeKernelLedger P n k
  point_refl : ∀ n m, (point n m).link =
    DPrimeStripEquiv.refl (point n m).source.kernel.dStrip
  column_cardinality : ∀ n k, Fintype.card (Fin (k + 1)) = k + 1
  top_cardinality : ∀ n, Fintype.card (Fin (lStar l.value + 1)) = lStar l.value + 1

def geometricKernelBoundarySummary (P : H2SpokePermutation I) :
    I.GeometricKernelBoundarySummary P where
  point := fun n m => I.geometricKernelPointLinkLedgerAt n m n m
  column := I.geometricColumnActionLedger
  procession := I.geometricColumnProcessionLedger
  translation := I.geometricTranslationKernelLedger
  spoke := I.geometricSpokeKernelLedger P
  point_refl := by
    intro n m
    exact I.geometricKernelPointLinkLedgerAt_refl n m
  column_cardinality := by
    intro n k
    exact I.geometricColumnActionLedger n k |>.cardinality
  top_cardinality := by
    intro n
    exact I.geometricColumnProcessionLedger_top_cardinality n

@[simp] theorem geometricKernelBoundarySummary_point
    (P : H2SpokePermutation I) (n m : Int) :
    (I.geometricKernelBoundarySummary P).point n m =
      I.geometricKernelPointLinkLedgerAt n m n m := rfl

@[simp] theorem geometricKernelBoundarySummary_column
    (P : H2SpokePermutation I) (n : Int) (k : Nat) :
    (I.geometricKernelBoundarySummary P).column n k =
      I.geometricColumnActionLedger n k := rfl

theorem geometricKernelBoundarySummary_point_refl
    (P : H2SpokePermutation I) (n m : Int) :
    (I.geometricKernelBoundarySummary P).point n m |>.link =
      DPrimeStripEquiv.refl
        ((I.geometricKernelBoundarySummary P).point n m).source.kernel.dStrip :=
  (I.geometricKernelBoundarySummary P).point_refl n m

theorem geometricKernelBoundarySummary_column_cardinality
    (P : H2SpokePermutation I) (n : Int) (k : Nat) :
    Fintype.card (Fin (k + 1)) = k + 1 :=
  (I.geometricKernelBoundarySummary P).column_cardinality n k

theorem geometricKernelBoundarySummary_top_cardinality
    (P : H2SpokePermutation I) (n : Int) :
    Fintype.card (Fin (lStar l.value + 1)) = lStar l.value + 1 :=
  (I.geometricKernelBoundarySummary P).top_cardinality n

theorem geometricKernelBoundarySummary_point_packet_q
    (P : H2SpokePermutation I) (n m : Int) :
    (I.sourcePointBundle n m).packet.packet.q > 0 :=
  I.sourcePointBundle_q_positive n m

theorem geometricKernelBoundarySummary_point_projection_surjective
    (P : H2SpokePermutation I) (n m : Int) (v : V) :
    Function.Surjective ((I.sourcePointBundle n m).kernel.dStrip.proj v) :=
  I.sourcePointBundle_projection_surjective n m v

theorem geometricKernelBoundarySummary_translation_component_bijective
    (P : H2SpokePermutation I) (a n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V) :
    Function.Bijective
      ((I.geometricTranslationKernelLedger a n k).component i |>.isoPi v) :=
  I.geometricTranslationKernelLedger_component_bijective a n k i v

theorem geometricKernelBoundarySummary_spoke_component_bijective
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) (v : V) :
    Function.Bijective
      ((I.geometricSpokeKernelLedger P n k).component i |>.isoPi v) :=
  I.geometricSpokeKernelLedger_component_bijective P n k i v

theorem geometricKernelBoundarySummary_translation_packet
    (P : H2SpokePermutation I) (a n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.geometricTranslationKernelLedger a n k).base.column.packet i |>.q =
      (I.geometricTranslationKernelLedger a n k).target.column.packet i |>.q :=
  I.geometricTranslationKernelLedger_q a n k i

theorem geometricKernelBoundarySummary_spoke_packet
    (P : H2SpokePermutation I) (n : Int) (k : Nat)
    (i : Fin (k + 1)) :
    (I.family.theater
      (P.permutation ((I.geometricSpokeKernelLedger P n k).base.column.source i))).thetaPacket.q =
      (I.geometricSpokeKernelLedger P n k).base.column.packet i |>.q :=
  I.geometricSpokeKernelLedger_packet_q_transport P n k i

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def theorem311SourceGeometricKernelLedger : Obligation :=
  { id := "IUT-III.theorem-3.11-source-geometric-kernel-ledger"
    source :=
      "IUT I, Definition 5.2 and Proposition 6.9(ii); IUT III, " ++
        "Theorem 1.5(i), Propositions 3.4 and 3.5, Theorem 3.11"
    status := VerificationStatus.sourceProjection
    note :=
      "From every OriginalInput point, constructs the actual kernel of the " ++
        "D-prime-strip projection, proves subgroup closure and projection " ++
        "surjectivity, and transports kernels through source links. It also " ++
        "packages the source theta packet, value action, degree, finite-stage " ++
        "and source point bundle. This is a source projection only: no " ++
        "vertical-coricit holomorphic log-shell, Kummer, splitting monoid, or " ++
        "Frobenioid is inferred from the kernel."
    dependsOn :=
      [ "IUT-III.theorem-3.11-original-input-boundary",
        "IUT-I-II.prime-strip-core",
        "IUT-I-II.prime-strip-degree-kernel",
        "IUT-II.finite-theta-packet" ] }

end LeanFormal.IUT.Audit
