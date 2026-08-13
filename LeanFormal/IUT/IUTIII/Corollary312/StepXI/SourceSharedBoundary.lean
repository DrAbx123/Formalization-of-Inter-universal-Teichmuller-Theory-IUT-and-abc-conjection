import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
import LeanFormal.IUT.Foundations.Arithmetic.FiniteLabels
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

/-!
  # Shared source boundary for Theorem 3.11 and Corollary 3.12

  Theorem 3.11 and Corollary 3.12 use the same source-facing lattice data,
  but they do not have the same conclusion.  This file exposes only the
  fixed one-column projections of the already supplied H1/H2 input.  In
  particular, it does not construct a Theorem-3.11 output, IPL, SHE, APT, a
  holomorphic hull, or the Corollary-3.12 inequality.

  The useful common facts are:

  * the finite procession at column `1` and its `l*` stage;
  * the actual source theaters and D-prime-strips at that stage;
  * the D-spoke transport and its projection compatibility; and
  * q- and label-scale transport along the one-column links.

  These are projections and consequences of `OriginalInput`; no additional
  arithmetic or geometric hypothesis is introduced here.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

local instance primeFactForSourceShared (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) := l.factPrime

/-! ## Fixed one-column projections -/

abbrev OneColumnIndex (l : PrimeGeFive) := Fin (lStar l.value + 1)

def oneColumnFProcession : I.ColumnFProcession :=
  I.columnFProcession 1

def oneColumnDProcession : I.ColumnDProcession :=
  I.columnDProcession 1

@[simp] theorem oneColumnFProcession_stage (k : Nat) :
    (I.oneColumnFProcession).stage k = I.columnFStage 1 k :=
  rfl

@[simp] theorem oneColumnDProcession_stage (k : Nat) :
    (I.oneColumnDProcession).stage k = I.columnDStage 1 k :=
  rfl

@[simp] theorem oneColumnFProcession_inclusion {k r : Nat} (h : k ≤ r) :
    (I.oneColumnFProcession).inclusion h = I.columnFInclusion 1 h :=
  rfl

@[simp] theorem oneColumnDProcession_inclusion {k r : Nat} (h : k ≤ r) :
    (I.oneColumnDProcession).inclusion h = I.columnDInclusion 1 h :=
  rfl

def oneColumnStage : (k : Nat) → I.DStageCapsule k :=
  fun k => (I.oneColumnDProcession).stage k

def oneColumnTopStage : I.DStageCapsule (lStar l.value) :=
  I.oneColumnStage (lStar l.value)

@[simp] theorem oneColumnTopStage_source (i : OneColumnIndex l) :
    (I.oneColumnTopStage).source i = I.indexOf 1 (i.1 : Int) :=
  rfl

@[simp] theorem oneColumnTopStage_strip (i : OneColumnIndex l) :
    (I.oneColumnTopStage).strip i = I.dPrimeStripAt 1 (i.1 : Int) :=
  rfl

@[simp] theorem oneColumnTopStage_link
    (i j : OneColumnIndex l) :
    (I.oneColumnTopStage).link i j =
      I.dLinkAt 1 (i.1 : Int) 1 (j.1 : Int) :=
  rfl

theorem oneColumnTopStage_source_injective :
    Function.Injective (oneColumnTopStage I).source := by
  exact I.columnSource_injective 1 (lStar l.value)

theorem oneColumnTopStage_cardinality :
    Fintype.card (OneColumnIndex l) = lStar l.value + 1 := by
  simp [OneColumnIndex]

theorem oneColumnTopStage_source_distinct
    (i j : OneColumnIndex l)
    (h : (oneColumnTopStage I).source i = (oneColumnTopStage I).source j) :
    i = j :=
  oneColumnTopStage_source_injective (I := I) h

theorem oneColumnProcession_toD (k : Nat) :
    (I.oneColumnFProcession.stage k).toD =
      (I.oneColumnDProcession.stage k) := by
  rfl

theorem oneColumnInclusion_injective {k r : Nat} (h : k ≤ r) :
    Function.Injective ((I.oneColumnDProcession).inclusion h).map :=
  ((I.oneColumnDProcession).inclusion h).map_injective

theorem oneColumnInclusion_naturality {k r : Nat} (h : k ≤ r)
    (i j : Fin (k + 1)) :
    DPrimeStripEquiv.trans
        (DStageCapsule.link ((I.oneColumnDProcession).stage k) i j)
        (((I.oneColumnDProcession).inclusion h).component j) =
      DPrimeStripEquiv.trans
        (((I.oneColumnDProcession).inclusion h).component i)
        (DStageCapsule.link ((I.oneColumnDProcession).stage r)
          (((I.oneColumnDProcession).inclusion h).map i)
          (((I.oneColumnDProcession).inclusion h).map j)) := by
  exact DStageInclusion.naturality
    ((I.oneColumnDProcession).inclusion h) i j

/-! ## Source links and spoke transport used by Step (xi) -/

def oneColumnLink (m m' : Int) :
    DPrimeStripEquiv (I.dPrimeStripAt 1 m) (I.dPrimeStripAt 1 m') :=
  I.dLinkAt 1 m 1 m'

theorem oneColumnLink_refl (m : Int) :
    I.oneColumnLink m m = DPrimeStripEquiv.refl (I.dPrimeStripAt 1 m) := by
  exact I.dLinkAt_refl 1 m

theorem oneColumnLink_symm (m m' : Int) :
    DPrimeStripEquiv.symm (I.oneColumnLink m m') = I.oneColumnLink m' m := by
  exact I.dLinkAt_symm 1 m 1 m'

theorem oneColumnLink_trans (m m' m'' : Int) :
    DPrimeStripEquiv.trans (I.oneColumnLink m m')
        (I.oneColumnLink m' m'') = I.oneColumnLink m m'' := by
  exact I.dLinkAt_trans 1 m 1 m' 1 m''

def oneColumnSpoke (P : H2SpokePermutation I)
    (i : OneColumnIndex l) : DPrimeStripEquiv
      ((I.family.theater (P.permutation ((oneColumnTopStage I).source i))).primeStrip.toD)
      ((I.family.theater ((oneColumnTopStage I).source i)).primeStrip.toD) :=
  P.dSpokeLink ((oneColumnTopStage I).source i)

theorem oneColumnSpoke_bijective (P : H2SpokePermutation I)
    (i : OneColumnIndex l) (v : V) :
    Function.Bijective ((I.oneColumnSpoke P i).isoPi v) := by
  exact (I.oneColumnSpoke P i).isoPi v |>.bijective

theorem oneColumnSpoke_projection (P : H2SpokePermutation I)
    (i : OneColumnIndex l) (v : V)
    (x : ((I.family.theater
      (P.permutation ((oneColumnTopStage I).source i))).primeStrip.toD).Pi v) :
      ((I.family.theater ((oneColumnTopStage I).source i)).primeStrip.toD).proj v
        ((I.oneColumnSpoke P i).isoPi v x) =
      (I.oneColumnSpoke P i).isoG v
        (((I.family.theater
          (P.permutation ((oneColumnTopStage I).source i))).primeStrip.toD).proj v x) := by
  exact (I.oneColumnSpoke P i).compat_apply v x

theorem oneColumnSpoke_naturality (P : H2SpokePermutation I)
    (i j : OneColumnIndex l) :
    DPrimeStripEquiv.trans
        ((I.family.link
          (P.permutation ((oneColumnTopStage I).source i))
          (P.permutation ((oneColumnTopStage I).source j))).primeStripEquiv.toD)
        (I.oneColumnSpoke P j) =
      DPrimeStripEquiv.trans (I.oneColumnSpoke P i)
        ((I.family.link
          ((oneColumnTopStage I).source i)
          ((oneColumnTopStage I).source j)).primeStripEquiv.toD) := by
  exact P.dSpoke_naturality _ _

/-! ## q and label-scale transport on the fixed column -/

def oneColumnTheater (m : Int) : HodgeTheater l V :=
  I.theaterAt 1 m

def oneColumnPacket (m : Int) : FiniteThetaPacket l :=
  (I.oneColumnTheater m).thetaPacket

def oneColumnQ (m : Int) : Real :=
  (I.oneColumnPacket m).q

def oneColumnScale (m : Int) (j : SignedLabel l.value) : Real :=
  (I.oneColumnPacket m).scale j

theorem oneColumnQ_transport (m m' : Int) :
    I.oneColumnQ m = I.oneColumnQ m' := by
  exact I.linkAt_q 1 m 1 m'

theorem oneColumnScale_transport (m m' : Int)
    (j : SignedLabel l.value) :
    I.oneColumnScale m j = I.oneColumnScale m' j := by
  exact I.linkAt_scale 1 m 1 m' j

theorem oneColumnQ_vertical (m : Int) :
    I.oneColumnQ m = I.oneColumnQ (m + 1) := by
  exact I.oneColumnQ_transport m (m + 1)

theorem oneColumnScale_neg_invariant (m : Int)
    (j : SignedLabel l.value) :
    I.oneColumnScale m (SignedLabel.neg j) = I.oneColumnScale m j := by
  exact (I.oneColumnPacket m).scale_neg j

theorem oneColumnQ_spoke (P : H2SpokePermutation I)
    (i : OneColumnIndex l) :
    (I.family.theater
      (P.permutation ((oneColumnTopStage I).source i))).thetaPacket.q =
      (I.family.theater ((oneColumnTopStage I).source i)).thetaPacket.q :=
  P.spoke_q _

theorem oneColumnScale_spoke (P : H2SpokePermutation I)
    (i : OneColumnIndex l) (j : SignedLabel l.value) :
    (I.family.theater
      (P.permutation ((oneColumnTopStage I).source i))).thetaPacket.scale j =
      (I.family.theater ((oneColumnTopStage I).source i)).thetaPacket.scale j := by
  letI : Fact (Nat.Prime l.value) := l.factPrime
  exact P.spoke_scale _ j

/-! ## Finite label cardinalities for later normalization -/

abbrev NonzeroFiniteLabel (l : PrimeGeFive) :=
  {x : Fl l.value // x ≠ 0}

abbrev CuspLabel (l : PrimeGeFive) := LabCusp l.value

theorem signedLabel_cardinality (l : PrimeGeFive) :
    Fintype.card (SignedLabel l.value) = l.value := by
  exact SignedLabel.card_signedLabel l

theorem nonzeroFiniteLabel_cardinality (l : PrimeGeFive) :
    Fintype.card (NonzeroFiniteLabel l) = 2 * lStar l.value := by
  letI : Fact (Nat.Prime l.value) := l.factPrime
  exact card_compl_zero l.value l.odd

theorem cuspLabel_cardinality (l : PrimeGeFive) :
    Nat.card (CuspLabel l) = lStar l.value := by
  letI : Fact (Nat.Prime l.value) := l.factPrime
  simpa [CuspLabel] using card_LabCusp l.value l.ge_five

/-! This proposition is intentionally only a shared-input marker. -/

theorem oneColumn_shared_boundary (P : H2SpokePermutation I) :
    (∀ k, (I.oneColumnFProcession.stage k).toD =
      (I.oneColumnDProcession.stage k)) ∧
      Function.Injective (oneColumnTopStage I).source ∧
      Fintype.card (OneColumnIndex l) = lStar l.value + 1 ∧
      (∀ v, Function.Bijective ((I.oneColumnSpoke P (⟨0, by
        omega⟩ : OneColumnIndex l)).isoPi v)) := by
  refine ⟨?_, oneColumnTopStage_source_injective (I := I), ?_, ?_⟩
  · intro k
    exact oneColumnProcession_toD (I := I) k
  · simp [OneColumnIndex]
  · intro v
    exact oneColumnSpoke_bijective (I := I) P _ v

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT
