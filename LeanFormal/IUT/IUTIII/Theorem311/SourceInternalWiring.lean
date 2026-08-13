import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2Construction
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # Internal source wiring for Theorem 3.11

  The preceding files deliberately keep the opening source input, the H1/H2
  projections, and the theorem-facing realization in separate contracts.  A
  mere import list does not connect those contracts.  This file supplies the
  missing typed wiring layer.

  `SourceH1H2Alignment` records the carrier, index, q, scale, and permutation
  maps which identify the two presentations.  The record is an
  explicit source-facing premise: it does not manufacture a Hodge theater or
  a procession from arithmetic data.  Once it is supplied, the theorems below
  consume the canonical H1/H2 projections and the supplied realization in a
  common chain.

  The P1/P2 constructors are similarly split.  Packet, vertical, and
  tensor-power data that can be constructed from the realization are built
  here.  The genuinely source-specific local LGP, Kummer evaluation, spoke,
  and lattice-bound data remain explicit boundary records.  This preserves
  the quantifiers and the direction of every upper-semi assertion.

  Source references: IUT III Theorem 1.5, Proposition 2.1, Corollary 2.3,
  Propositions 3.2, 3.4, 3.5, 3.7, 3.9, 3.10, and Theorem 3.11.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe ua uv upi umon ui u v w ux uy

namespace Theorem311Source

open SourceHodgeTheaterBridge
open SourceDependencyChain
open OriginalInput

variable {l : PrimeGeFive}
variable {V : Type uv}
variable {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## 1. The H1/H2 to realization alignment boundary -/

/-
The abstract hodge system inside a realization has an independent index and
carrier.  The original input has the actual Hodge-theater family.  The
following record is the exact data needed to compare them.  In particular,
the decoding equivalence is not replaced by an equality of unrelated types.
-/
structure SourceH1H2Alignment
    (I : OriginalInput.{u, uv, upi, umon, ui} l V)
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice) where
  hodgeIndex : R.procession.hodge.index ≃ I.family.index
  hodgeDecode :
    R.procession.hodge.theaterCarrier ≃
      HodgeTheater.{u, uv, upi, umon} l V
  source_heq : HEq R.procession.hodge.source I.initial
  theater_decode : ∀ i,
    hodgeDecode (R.procession.hodge.theater i) =
      I.family.theater (hodgeIndex i)
  q_decode : ∀ i,
    R.procession.hodge.qParameter i =
      (I.family.theater (hodgeIndex i)).thetaPacket.q
  scale_decode : ∀ i x,
    R.procession.hodge.scale i x =
      (I.family.theater (hodgeIndex i)).thetaPacket.scale x
  choiceHodgeIndex : Choice ≃ R.procession.hodge.index
  choiceFamilyIndex : Choice ≃ I.family.index
  choice_index_square : ∀ c,
    hodgeIndex (choiceHodgeIndex c) = choiceFamilyIndex c
  source_index_decode : ∀ c,
    R.procession.source_index c = choiceHodgeIndex c
  genericDecode : Choice ≃ HodgeTheater.{u, uv, upi, umon} l V
  generic_theater_decode : ∀ c,
    genericDecode (R.genericFamily.theater c) =
      I.family.theater (choiceFamilyIndex c)
  generic_permutation_conjugate : ∀ c,
    choiceFamilyIndex (R.genericFamily.permutation c) =
      I.family.permutation (choiceFamilyIndex c)
  hodge_permutation_conjugate : ∀ c,
    choiceHodgeIndex (R.genericFamily.permutation c) =
      R.procession.hodge.permutation (choiceHodgeIndex c)

namespace SourceH1H2Alignment

variable {I : OriginalInput.{u, uv, upi, umon, ui} l V}
variable {R : SourceTheorem311Realization.{u, v, w} l Label Choice}
variable (A : SourceH1H2Alignment I R)
include A

theorem source_at : HEq R.procession.hodge.source I.initial :=
  A.source_heq

theorem source_at_symm : HEq I.initial R.procession.hodge.source :=
  A.source_heq.symm

theorem hodge_index_bijective :
    Function.Bijective A.hodgeIndex :=
  A.hodgeIndex.bijective

theorem hodge_decode_bijective :
    Function.Bijective A.hodgeDecode :=
  A.hodgeDecode.bijective

theorem choice_hodge_index_bijective :
    Function.Bijective A.choiceHodgeIndex :=
  A.choiceHodgeIndex.bijective

theorem choice_family_index_bijective :
    Function.Bijective A.choiceFamilyIndex :=
  A.choiceFamilyIndex.bijective

theorem theater_at (i : R.procession.hodge.index) :
    A.hodgeDecode (R.procession.hodge.theater i) =
      I.family.theater (A.hodgeIndex i) :=
  A.theater_decode i

theorem theater_at_converse (i : R.procession.hodge.index) :
    I.family.theater (A.hodgeIndex i) =
      A.hodgeDecode (R.procession.hodge.theater i) :=
  (A.theater_at i).symm

theorem q_at (i : R.procession.hodge.index) :
    R.procession.hodge.qParameter i =
      (I.family.theater (A.hodgeIndex i)).thetaPacket.q :=
  A.q_decode i

theorem q_at_converse (i : R.procession.hodge.index) :
    (I.family.theater (A.hodgeIndex i)).thetaPacket.q =
      R.procession.hodge.qParameter i :=
  (A.q_at i).symm

theorem scale_at (i : R.procession.hodge.index)
    (x : SignedLabel l.value) :
    R.procession.hodge.scale i x =
      (I.family.theater (A.hodgeIndex i)).thetaPacket.scale x :=
  A.scale_decode i x

theorem scale_at_converse (i : R.procession.hodge.index)
    (x : SignedLabel l.value) :
    (I.family.theater (A.hodgeIndex i)).thetaPacket.scale x =
      R.procession.hodge.scale i x :=
  (A.scale_at i x).symm

theorem choice_index_at (c : Choice) :
    A.hodgeIndex (A.choiceHodgeIndex c) = A.choiceFamilyIndex c :=
  A.choice_index_square c

theorem choice_index_at_symm (c : Choice) :
    A.choiceFamilyIndex c = A.hodgeIndex (A.choiceHodgeIndex c) :=
  (A.choice_index_at c).symm

theorem source_index_at (c : Choice) :
    R.procession.source_index c = A.choiceHodgeIndex c :=
  A.source_index_decode c

theorem source_index_at_converse (c : Choice) :
    A.choiceHodgeIndex c = R.procession.source_index c :=
  (A.source_index_at c).symm

theorem generic_theater_at (c : Choice) :
    A.genericDecode (R.genericFamily.theater c) =
      I.family.theater (A.choiceFamilyIndex c) :=
  A.generic_theater_decode c

theorem generic_theater_at_converse (c : Choice) :
    I.family.theater (A.choiceFamilyIndex c) =
      A.genericDecode (R.genericFamily.theater c) :=
  (A.generic_theater_at c).symm

theorem generic_permutation_at (c : Choice) :
    A.choiceFamilyIndex (R.genericFamily.permutation c) =
      I.family.permutation (A.choiceFamilyIndex c) :=
  A.generic_permutation_conjugate c

theorem generic_permutation_at_symm (c : Choice) :
    I.family.permutation (A.choiceFamilyIndex c) =
      A.choiceFamilyIndex (R.genericFamily.permutation c) :=
  (A.generic_permutation_at c).symm

theorem hodge_permutation_at (c : Choice) :
    A.choiceHodgeIndex (R.genericFamily.permutation c) =
      R.procession.hodge.permutation (A.choiceHodgeIndex c) :=
  A.hodge_permutation_conjugate c

theorem hodge_permutation_at_symm (c : Choice) :
    R.procession.hodge.permutation (A.choiceHodgeIndex c) =
      A.choiceHodgeIndex (R.genericFamily.permutation c) :=
  (A.hodge_permutation_at c).symm

theorem generic_family_distinct :
    Function.Injective R.genericFamily.theater :=
  R.genericFamily.distinct

theorem generic_family_link_refl (c : Choice) (t : Choice) :
    R.genericFamily.link c c t = t :=
  R.genericFamily.link_refl c t

theorem generic_family_link_trans (c d e : Choice) (t : Choice) :
    R.genericFamily.link d e (R.genericFamily.link c d t) =
      R.genericFamily.link c e t :=
  R.genericFamily.link_trans c d e t

theorem generic_family_permutation_natural (c : Choice) (t : Choice) :
    R.genericFamily.link (R.genericFamily.permutation c)
        (R.genericFamily.permutation c) t =
      R.genericFamily.link c c t :=
  R.genericFamily.permutation_naturality c t

theorem procession_base_source_index :
    R.procession.source_index R.procession.base =
      A.choiceHodgeIndex R.procession.base :=
  A.source_index_at R.procession.base

theorem procession_base_family_index :
    A.hodgeIndex (R.procession.source_index R.procession.base) =
      A.choiceFamilyIndex R.procession.base := by
  rw [A.source_index_at]
  exact A.choice_index_at R.procession.base

theorem procession_ind1_source_index (g : Label) (c : Choice) :
    R.procession.source_index (R.procession.ind1 g c) =
      R.procession.source_index c :=
  R.procession.ind1_index g c

theorem procession_ind2_source_index (g : Label) (c : Choice) :
    R.procession.source_index (R.procession.ind2 g c) =
      R.procession.source_index c :=
  R.procession.ind2_index g c

theorem procession_ind3_source_index (n : Nat) (c : Choice) :
    R.procession.source_index (R.procession.ind3 n c) =
      R.procession.source_index c :=
  R.procession.ind3_index n c

theorem procession_ind1_family_index (g : Label) (c : Choice) :
    A.hodgeIndex (A.choiceHodgeIndex (R.procession.ind1 g c)) =
      A.choiceFamilyIndex c := by
  calc
    A.hodgeIndex (A.choiceHodgeIndex (R.procession.ind1 g c)) =
        A.hodgeIndex (R.procession.source_index (R.procession.ind1 g c)) := by
      rw [A.source_index_at]
    _ = A.hodgeIndex (R.procession.source_index c) :=
      congrArg A.hodgeIndex (R.procession.ind1_index g c)
    _ = A.hodgeIndex (A.choiceHodgeIndex c) := by
      rw [A.source_index_at]
    _ = A.choiceFamilyIndex c := A.choice_index_at c

theorem procession_ind2_family_index (g : Label) (c : Choice) :
    A.hodgeIndex (A.choiceHodgeIndex (R.procession.ind2 g c)) =
      A.choiceFamilyIndex c := by
  calc
    A.hodgeIndex (A.choiceHodgeIndex (R.procession.ind2 g c)) =
        A.hodgeIndex (R.procession.source_index (R.procession.ind2 g c)) := by
      rw [A.source_index_at]
    _ = A.hodgeIndex (R.procession.source_index c) :=
      congrArg A.hodgeIndex (R.procession.ind2_index g c)
    _ = A.hodgeIndex (A.choiceHodgeIndex c) := by
      rw [A.source_index_at]
    _ = A.choiceFamilyIndex c := A.choice_index_at c

theorem procession_ind3_family_index (n : Nat) (c : Choice) :
    A.hodgeIndex (A.choiceHodgeIndex (R.procession.ind3 n c)) =
      A.choiceFamilyIndex c := by
  calc
    A.hodgeIndex (A.choiceHodgeIndex (R.procession.ind3 n c)) =
        A.hodgeIndex (R.procession.source_index (R.procession.ind3 n c)) := by
      rw [A.source_index_at]
    _ = A.hodgeIndex (R.procession.source_index c) :=
      congrArg A.hodgeIndex (R.procession.ind3_index n c)
    _ = A.hodgeIndex (A.choiceHodgeIndex c) := by
      rw [A.source_index_at]
    _ = A.choiceFamilyIndex c := A.choice_index_at c

theorem h1_source_recovered :
    I.h1.source = I.initial :=
  rfl

theorem h1_family_recovered :
    I.h1.family = I.family :=
  rfl

theorem h1_index_recovered :
    I.h1.index_equiv = I.index_equiv :=
  rfl

theorem h1_bridge_recovered :
    I.h1.bridge = I.bridge :=
  rfl

theorem h2_source_recovered (P : H2SpokePermutation I) :
    (I.h2Package P).h1.source = I.initial :=
  rfl

theorem h2_f_procession_recovered (P : H2SpokePermutation I) :
    (I.h2Package P).fProcession = H2FProcession.canonical (I := I) :=
  rfl

theorem h2_d_procession_recovered (P : H2SpokePermutation I) :
    (I.h2Package P).dProcession = H2DProcession.canonical (I := I) :=
  rfl

theorem h2_procession_toD_recovered (P : H2SpokePermutation I) :
    (I.h2Package P).fProcession.toD = (I.h2Package P).dProcession := by
  exact (I.h2Package_procession_toD P)

theorem h2_permutation_recovered (P : H2SpokePermutation I) :
    (I.h2Package P).permutation = P :=
  rfl

theorem h2_stage_source_recovered (P : H2SpokePermutation I)
    (n : Nat) (i : Fin (n + 1)) :
    ((I.h2Package P).dProcession.stage n).source i =
      I.indexOf (i.1 : Int) (n : Int) := by
  change (I.dStageCapsule n).source i = _
  rfl

theorem h2_stage_strip_recovered (P : H2SpokePermutation I)
    (n : Nat) (i : Fin (n + 1)) :
    ((I.h2Package P).dProcession.stage n).strip i =
      I.dPrimeStripAt (i.1 : Int) (n : Int) := by
  change (I.dStageCapsule n).strip i = _
  rfl

theorem h2_stage_link_recovered (P : H2SpokePermutation I)
    (n : Nat) (i j : Fin (n + 1)) :
    ((I.h2Package P).dProcession.stage n).link i j =
      I.dLinkAt (i.1 : Int) (n : Int) (j.1 : Int) (n : Int) := by
  change (I.dStageCapsule n).link i j = _
  rfl

theorem h2_stage_cardinality (P : H2SpokePermutation I) (n : Nat) :
    Fintype.card (Fin (n + 1)) = n + 1 :=
  I.h2Package_stage_cardinality P n

theorem h2_stage_inclusion_injective (P : H2SpokePermutation I)
    {n m : Nat} (h : n ≤ m) :
    Function.Injective ((I.h2Package P).fProcession.inclusion h).map :=
  I.h2Package_stage_inclusion_injective P h

theorem h2_spoke_f_natural (P Q : H2SpokePermutation I) (n : Nat)
    (i j : Fin (n + 1)) :
    FPrimeStripEquiv.trans
        ((I.spokeCapsule Q ((I.h2Package P).fProcession.stage n)).link i j)
        (((H2FProcession.spokeTransport (I := I) Q
          (I.h2Package P).fProcession n).component j)) =
      FPrimeStripEquiv.trans
        (((H2FProcession.spokeTransport (I := I) Q
          (I.h2Package P).fProcession n).component i))
        (((I.h2Package P).fProcession.stage n).link i j) :=
  I.h2Package_spoke_natural P Q n i j

theorem h2_spoke_d_projection (P : H2SpokePermutation I)
    (n : Nat) (i : Fin (n + 1)) (v : V)
    (x : (I.family.theater
      (P.permutation (((I.h2Package P).dProcession.stage n).source i))).primeStrip.toD.Pi v) :
    (I.family.theater (((I.h2Package P).dProcession.stage n).source i)).primeStrip.toD.proj v
        ((P.dSpokeLink (((I.h2Package P).dProcession.stage n).source i)).isoPi v x) =
      (P.dSpokeLink (((I.h2Package P).dProcession.stage n).source i)).isoG v
        ((I.family.theater (P.permutation
          (((I.h2Package P).dProcession.stage n).source i))).primeStrip.toD.proj v x) := by
  exact (P.dSpokeLink
    (((I.h2Package P).dProcession.stage n).source i)).compat_apply v x

end SourceH1H2Alignment

/-! ## 2. The explicit internal wiring object -/

structure SourceInternalWiring
    (I : OriginalInput.{u, uv, upi, umon, ui} l V)
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice)
    (P : H2SpokePermutation I)
    (X : Type ux) (Y : Type uy)
  [CommMonoid X] [CommMonoid Y] where
  alignment : SourceH1H2Alignment I R
  h2 : I.H2ConstructionPackage
  h2_canonical : h2 = I.h2Package P
  k1 : K1VerticalBoundary R.procession R.packet
  k1_canonical : k1 = k1OfRealization R
  k2 : K2FrobenioidBoundary R k1 X Y

namespace SourceInternalWiring

variable {I : OriginalInput.{u, uv, upi, umon, ui} l V}
variable {R : SourceTheorem311Realization.{u, v, w} l Label Choice}
variable {P : H2SpokePermutation I}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable (W : SourceInternalWiring I R P X Y)
include W

def h1 (W : SourceInternalWiring I R P X Y) : I.H1FamilyPackage := I.h1

def canonical
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (B : K2FrobenioidBoundary R (k1OfRealization R) X Y) :
    SourceInternalWiring I R P X Y where
  alignment := A
  h2 := I.h2Package P
  h2_canonical := rfl
  k1 := k1OfRealization R
  k1_canonical := rfl
  k2 := B

theorem alignment_source :
    HEq R.procession.hodge.source I.initial :=
  W.alignment.source_at

theorem alignment_hodge_index_bijective :
    Function.Bijective W.alignment.hodgeIndex :=
  W.alignment.hodge_index_bijective

theorem alignment_choice_index_bijective :
    Function.Bijective W.alignment.choiceFamilyIndex :=
  W.alignment.choice_family_index_bijective

theorem h1_source : W.h1.source = I.initial := by
  rfl

theorem h1_family : W.h1.family = I.family := by
  rfl

theorem h1_index_equiv : W.h1.index_equiv = I.index_equiv := by
  rfl

theorem h1_bridge : W.h1.bridge = I.bridge := by
  rfl

theorem h2_h1 : W.h2.h1 = W.h1 := by
  rw [W.h2_canonical]
  rfl

theorem h2_source : W.h2.h1.source = I.initial := by
  rw [W.h2_canonical]
  rfl

theorem h2_f_procession :
    W.h2.fProcession = H2FProcession.canonical (I := I) := by
  rw [W.h2_canonical]
  rfl

theorem h2_d_procession :
    W.h2.dProcession = H2DProcession.canonical (I := I) := by
  rw [W.h2_canonical]
  rfl

theorem h2_procession_toD : W.h2.fProcession.toD = W.h2.dProcession := by
  rw [W.h2_canonical]
  exact I.h2Package_procession_toD P

theorem h2_permutation : W.h2.permutation = P := by
  rw [W.h2_canonical]
  rfl

theorem k1_source : W.k1 = k1OfRealization R :=
  W.k1_canonical

theorem k1_vertical : W.k1.vertical = R.vertical.vertical := by
  rw [W.k1_canonical]
  rfl

theorem k1_nonarchimedean_image (m : Nat) (S : Set Real) :
    W.k1.nonarchimedeanImage m S = R.vertical.nonarchimedeanImage m S := by
  rw [W.k1_canonical]
  rfl

theorem k1_archimedean_image (m : Nat) (S : Set Real) :
    W.k1.archimedeanImage m S = R.vertical.archimedeanImage m S := by
  rw [W.k1_canonical]
  rfl

theorem k1_kummer (c : Choice) :
    W.k1.labelledKummer c = R.vertical.kummer c := by
  rw [W.k1_canonical]
  rfl

theorem k2_local :
    W.k2.localFrobenioid = W.k2.localFrobenioid := rfl

theorem k2_global :
    W.k2.globalFrobenioid = W.k2.globalFrobenioid := rfl

theorem k2_comparison :
    W.k2.comparison.localMap = R.evaluation.evaluation.localMap :=
  W.k2.comparison_local

theorem k2_comparison_global :
    W.k2.comparison.globalMap = R.evaluation.evaluation.globalMap :=
  W.k2.comparison_global

theorem k2_comparison_lower :
    W.k2.comparison.lower = R.evaluation.evaluation.localComp :=
  W.k2.comparison_lower

theorem k2_comparison_upper :
    W.k2.comparison.upper = R.evaluation.evaluation.globalComp :=
  W.k2.comparison_upper

theorem k2_upperSemi : W.k2.upperSemi = W.k1.vertical :=
  W.k2.upperSemi_eq_k1

theorem k2_k1_vertical : W.k2.upperSemi = R.vertical.vertical := by
  rw [W.k2.upperSemi_eq_k1, W.k1_canonical]
  rfl

theorem source_to_hodge_index (c : Choice) :
    R.procession.source_index c = W.alignment.choiceHodgeIndex c :=
  W.alignment.source_index_at c

theorem source_to_family_index (c : Choice) :
    W.alignment.hodgeIndex (R.procession.source_index c) =
      W.alignment.choiceFamilyIndex c := by
  rw [W.source_to_hodge_index, W.alignment.choice_index_at]

theorem source_ind1_to_family_index (g : Label) (c : Choice) :
    W.alignment.hodgeIndex (R.procession.source_index
      (R.procession.ind1 g c)) =
      W.alignment.choiceFamilyIndex c := by
  simpa only [W.alignment.source_index_at] using
    W.alignment.procession_ind1_family_index g c

theorem source_ind2_to_family_index (g : Label) (c : Choice) :
    W.alignment.hodgeIndex (R.procession.source_index
      (R.procession.ind2 g c)) =
      W.alignment.choiceFamilyIndex c := by
  simpa only [W.alignment.source_index_at] using
    W.alignment.procession_ind2_family_index g c

theorem source_ind3_to_family_index (n : Nat) (c : Choice) :
    W.alignment.hodgeIndex (R.procession.source_index
      (R.procession.ind3 n c)) =
      W.alignment.choiceFamilyIndex c := by
  simpa only [W.alignment.source_index_at] using
    W.alignment.procession_ind3_family_index n c

theorem generic_permutation_to_source (c : Choice) :
    W.alignment.choiceFamilyIndex (R.genericFamily.permutation c) =
      I.family.permutation (W.alignment.choiceFamilyIndex c) :=
  W.alignment.generic_permutation_at c

theorem h2_permutation_to_generic (c : Choice) :
    I.family.permutation (W.alignment.choiceFamilyIndex c) =
      W.alignment.choiceFamilyIndex (R.genericFamily.permutation c) :=
  (W.generic_permutation_to_source c).symm

theorem h1_h2_closed :
    W.h1.source = I.initial ∧
      W.h2.h1 = W.h1 ∧
      W.h2.fProcession.toD = W.h2.dProcession ∧
      W.h2.permutation = P :=
  ⟨W.h1_source, W.h2_h1, W.h2_procession_toD, W.h2_permutation⟩

theorem internal_chain_closed :
    W.h1.source = I.initial ∧
      W.h2.h1.source = I.initial ∧
      W.k1 = k1OfRealization R ∧
      W.k2.upperSemi = R.vertical.vertical := by
  exact ⟨W.h1_source, W.h2_source, W.k1_source, W.k2_k1_vertical⟩

end SourceInternalWiring

/-! ## 3. Reusable P1 packet constructor -/

namespace SourceP1

variable {R : SourceTheorem311Realization.{u, v, w} l Label Choice}

def proposition32 (R : SourceTheorem311Realization.{u, v, w} l Label Choice) :
    SourceProposition32Packet.{u, v, w, w} R.procession R.packet where
  tensorName := fun _ => PUnit
  tensorNonempty := fun _ => ⟨PUnit.unit⟩
  tensorCarrier := fun c _ => R.packet.distinguished c
  tensorDistinguished := by
    intro c
    rfl
  determinant_scale := fun c r => R.packet.determinant c * r
  scale_positive := by
    intro c r hr
    exact mul_pos (R.packet.determinant_positive c) hr
  scale_log_add := by
    intro c r s hr hs
    have hdet : R.packet.determinant c ≠ 0 :=
      ne_of_gt (R.packet.determinant_positive c)
    have hrs : r * s ≠ 0 := ne_of_gt (mul_pos hr hs)
    have hr0 : r ≠ 0 := ne_of_gt hr
    calc
      Real.log (R.packet.determinant c * (r * s)) =
          Real.log (R.packet.determinant c) + Real.log (r * s) :=
        Real.log_mul hdet hrs
      _ = Real.log (R.packet.determinant c) +
          (Real.log r + Real.log s) := by
        rw [Real.log_mul hr0 (ne_of_gt hs)]
      _ = Real.log (R.packet.determinant c * r) + Real.log s := by
        rw [Real.log_mul hdet hr0]
        ring
  tensor_ind1 := by
    intro g c
    simp [R.packet.ind1_determinant]
  tensor_ind2 := by
    intro g c
    simp [R.packet.ind2_determinant]
  tensor_ind3 := by
    intro n c
    simpa using R.packet.ind3_determinant n c
  profile := R.packet.logVolume
  profile_logVolume := by
    intro c
    rfl
  profile_det_eq := by
    intro c
    exact R.packet.log_determinant c

@[simp] theorem proposition32_profile (c : Choice) :
    (proposition32 R).profile c = R.packet.logVolume c := rfl

@[simp] theorem proposition32_tensor_name (c : Choice) :
    (proposition32 R).tensorName c = PUnit := rfl

theorem proposition32_tensor_carrier (c : Choice)
    (x : (proposition32 R).tensorName c) :
    (proposition32 R).tensorCarrier c x = R.packet.distinguished c := rfl

theorem proposition32_tensor_nonempty (c : Choice) :
    Nonempty ((proposition32 R).tensorName c) :=
  (proposition32 R).tensorNonempty c

theorem proposition32_distinguished (c : Choice) :
    (proposition32 R).tensorCarrier c
        (Classical.choice ((proposition32 R).tensorNonempty c)) =
      R.packet.distinguished c := by
  rfl

theorem proposition32_scale_positive (c : Choice) {r : Real}
    (hr : 0 < r) :
    0 < (proposition32 R).determinant_scale c r :=
  (proposition32 R).scale_positive c r hr

theorem proposition32_scale_nonzero (c : Choice) {r : Real}
    (hr : 0 < r) :
    (proposition32 R).determinant_scale c r ≠ 0 :=
  ne_of_gt (proposition32_scale_positive (R := R) c hr)

theorem proposition32_scale_log_add (c : Choice) {r s : Real}
    (hr : 0 < r) (hs : 0 < s) :
    Real.log ((proposition32 R).determinant_scale c (r * s)) =
      Real.log ((proposition32 R).determinant_scale c r) + Real.log s :=
  (proposition32 R).scale_log_add c r s hr hs

theorem proposition32_ind1 (g : Label) (c : Choice) :
    (proposition32 R).determinant_scale (R.procession.ind1 g c) 1 =
      (proposition32 R).determinant_scale c 1 :=
  (proposition32 R).tensor_ind1 g c

theorem proposition32_ind2 (g : Label) (c : Choice) :
    (proposition32 R).determinant_scale (R.procession.ind2 g c) 1 =
      (proposition32 R).determinant_scale c 1 :=
  (proposition32 R).tensor_ind2 g c

theorem proposition32_ind3 (n : Nat) (c : Choice) :
    (proposition32 R).determinant_scale c 1 ≤
      (proposition32 R).determinant_scale (R.procession.ind3 n c) 1 :=
  (proposition32 R).tensor_ind3 n c

theorem proposition32_profile_det (c : Choice) :
    Real.log (R.packet.determinant c) = R.packet.logVolume c :=
  (proposition32 R).profile_det_eq c

theorem proposition32_packet_ind1 (g : Label) (c : Choice) :
    R.packet.logVolume (R.procession.ind1 g c) = R.packet.logVolume c :=
  R.packet.ind1_volume g c

theorem proposition32_packet_ind2 (g : Label) (c : Choice) :
    R.packet.logVolume (R.procession.ind2 g c) = R.packet.logVolume c :=
  R.packet.ind2_volume g c

theorem proposition32_packet_ind3 (n : Nat) (c : Choice) :
    R.packet.logVolume c ≤ R.packet.logVolume (R.procession.ind3 n c) :=
  R.packet.ind3_volume n c

theorem proposition32_image_ind1 (g : Label) (c : Choice) :
    R.packet.possibleImage (R.procession.ind1 g c) =
      R.packet.possibleImage c :=
  R.packet.image_ind1 g c

theorem proposition32_image_ind2 (g : Label) (c : Choice) :
    R.packet.possibleImage (R.procession.ind2 g c) =
      R.packet.possibleImage c :=
  R.packet.image_ind2 g c

theorem proposition32_image_ind3 (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage c) :
    ∃ y, y ∈ R.packet.possibleImage (R.procession.ind3 n c) ∧ z ≤ y :=
  R.packet.image_ind3 n c z hz

theorem proposition32_determinant_ind1 (g : Label) (c : Choice) :
    R.packet.determinant (R.procession.ind1 g c) = R.packet.determinant c :=
  R.packet.ind1_determinant g c

theorem proposition32_determinant_ind2 (g : Label) (c : Choice) :
    R.packet.determinant (R.procession.ind2 g c) = R.packet.determinant c :=
  R.packet.ind2_determinant g c

theorem proposition32_determinant_ind3 (n : Nat) (c : Choice) :
    R.packet.determinant c ≤
      R.packet.determinant (R.procession.ind3 n c) :=
  R.packet.ind3_determinant n c

end SourceP1

/-! ## 4. P1 vertical, local LGP, and volume constructors -/

namespace SourceP1

variable {R : SourceTheorem311Realization.{u, v, w} l Label Choice}

theorem proposition35
    (R : SourceTheorem311Realization.{u, v, w} l Label Choice) :
    SourceProposition35Vertical R.procession R.packet R.vertical where
  nonarch_inclusion := by
    intro m c z hz
    exact R.vertical.nonarchimedean_inclusion m z _ hz
  arch_surjection := by
    intro m c z hz
    exact R.vertical.archimedean_surjection m z _ hz
  nonarch_target := by
    intro m c
    exact R.vertical.nonarchimedean_profile m c
  arch_target := by
    intro m c
    exact R.vertical.archimedean_profile m c
  vertical_monotone := by
    intro m n h z hz
    exact R.vertical.vertical_monotone m n h z hz
  labelled_bijective := by
    intro c
    exact R.vertical.kummer_bijective c
  labelled_left := by
    intro c a
    exact R.vertical.kummer_left_inverse c a
  labelled_right := by
    intro c b
    exact R.vertical.kummer_right_inverse c b

theorem proposition35_nonarch (R : SourceTheorem311Realization l Label Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage c) :
    z ∈ R.vertical.nonarchimedeanImage m (R.packet.possibleImage c) :=
  (proposition35 R).nonarch_inclusion m c z hz

theorem proposition35_arch (R : SourceTheorem311Realization l Label Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.vertical.archimedeanImage m
      (R.packet.possibleImage c)) :
    ∃ y, y ∈ R.packet.possibleImage c ∧ z ≤ y :=
  (proposition35 R).arch_surjection m c z hz

theorem proposition35_nonarch_target
    (R : SourceTheorem311Realization l Label Choice)
    (m : Nat) (c : Choice) :
    R.vertical.nonarchimedeanImage m (R.packet.possibleImage c) =
      R.packet.possibleImage (R.procession.ind3 m c) :=
  (proposition35 R).nonarch_target m c

theorem proposition35_arch_target
    (R : SourceTheorem311Realization l Label Choice)
    (m : Nat) (c : Choice) :
    R.vertical.archimedeanImage m (R.packet.possibleImage c) =
      R.packet.possibleImage (R.procession.ind3 m c) :=
  (proposition35 R).arch_target m c

theorem proposition35_vertical_monotone
    (R : SourceTheorem311Realization l Label Choice)
    (m n : Nat) (h : m ≤ n) (z : Real)
    (hz : z ∈ R.vertical.vertical.image m) :
    ∃ y, y ∈ R.vertical.vertical.image n ∧ z ≤ y :=
  (proposition35 R).vertical_monotone m n h z hz

theorem proposition35_kummer_bijective
    (R : SourceTheorem311Realization l Label Choice) (c : Choice) :
    Function.Bijective (R.vertical.kummer c).map :=
  (proposition35 R).labelled_bijective c

theorem proposition35_kummer_left
    (R : SourceTheorem311Realization l Label Choice) (c a : Choice) :
    (R.vertical.kummer c).inverse ((R.vertical.kummer c).map a) = a :=
  (proposition35 R).labelled_left c a

theorem proposition35_kummer_right
    (R : SourceTheorem311Realization l Label Choice) (c b : Choice) :
    (R.vertical.kummer c).map ((R.vertical.kummer c).inverse b) = b :=
  (proposition35 R).labelled_right c b

theorem proposition35_nonarch_upper
    (R : SourceTheorem311Realization l Label Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage c) :
    ∃ y, y ∈ R.packet.possibleImage (R.procession.ind3 m c) ∧ z ≤ y := by
  exact SourceProposition35Vertical.nonarch_upper
    (proposition35 R) m c z hz

theorem proposition35_arch_target_lift
    (R : SourceTheorem311Realization l Label Choice)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage (R.procession.ind3 m c)) :
    ∃ y, y ∈ R.packet.possibleImage c ∧ z ≤ y := by
  exact SourceProposition35Vertical.arch_target_lift
    (proposition35 R) m c z hz

/-! A raw place boundary retains the actual place-indexed strip. -/

structure LGPBoundary (R : SourceTheorem311Realization l Label Choice)
    (S : Type uv) where
  strip : FPrimeStrip.{v, uv, u} S
  place : Choice → S
  monElement : ∀ c, strip.Mon (place c)
  profile : Choice → Real
  degree_profile : ∀ c,
    strip.degree (place c) (monElement c) = profile c
  groupElement : ∀ c, strip.toDPrimeStrip.Pi (place c)
  action_profile : ∀ c,
    strip.degree (place c)
      (strip.action (place c) (groupElement c) (monElement c)) = profile c
  action_transport : ∀ c,
    strip.action (place c) (groupElement c) (monElement c) = monElement c
  place_ind1 : ∀ (g : Label) (c : Choice), place c = place c
  place_ind2 : ∀ (g : Label) (c : Choice), place c = place c
  place_ind3 : ∀ (n : Nat) (c : Choice), place c = place c

def proposition34
    (L : LGPBoundary R V) :
    SourceProposition34LGP Label Choice V where
  strip := L.strip
  place := L.place
  monElement := L.monElement
  profile := L.profile
  degree_profile := L.degree_profile
  groupElement := L.groupElement
  action_profile := L.action_profile
  action_transport := L.action_transport
  place_ind1 := L.place_ind1
  place_ind2 := L.place_ind2
  place_ind3 := L.place_ind3

theorem proposition34_strip (L : LGPBoundary R V) :
    (proposition34 L).strip = L.strip := rfl

theorem proposition34_place (L : LGPBoundary R V) (c : Choice) :
    (proposition34 L).place c = L.place c := rfl

theorem proposition34_mon (L : LGPBoundary R V) (c : Choice) :
    (proposition34 L).monElement c = L.monElement c := rfl

theorem proposition34_profile (L : LGPBoundary R V) (c : Choice) :
    (proposition34 L).profile c = L.profile c := rfl

theorem proposition34_degree (L : LGPBoundary R V) (c : Choice) :
    L.strip.degree (L.place c) (L.monElement c) = L.profile c :=
  L.degree_profile c

theorem proposition34_action_degree (L : LGPBoundary R V) (c : Choice) :
    L.strip.degree (L.place c)
        (L.strip.action (L.place c) (L.groupElement c)
          (L.monElement c)) = L.profile c :=
  L.action_profile c

theorem proposition34_action_transport (L : LGPBoundary R V) (c : Choice) :
    L.strip.action (L.place c) (L.groupElement c) (L.monElement c) =
      L.monElement c :=
  L.action_transport c

theorem proposition34_degree_action_eq (L : LGPBoundary R V) (c : Choice) :
    L.strip.degree (L.place c)
        (L.strip.action (L.place c) (L.groupElement c)
          (L.monElement c)) =
      L.strip.degree (L.place c) (L.monElement c) := by
  exact (L.action_profile c).trans (L.degree_profile c).symm

theorem proposition34_place_ind1 (L : LGPBoundary R V)
    (g : Label) (c : Choice) : L.place c = L.place c :=
  L.place_ind1 g c

theorem proposition34_place_ind2 (L : LGPBoundary R V)
    (g : Label) (c : Choice) : L.place c = L.place c :=
  L.place_ind2 g c

theorem proposition34_place_ind3 (L : LGPBoundary R V)
    (n : Nat) (c : Choice) : L.place c = L.place c :=
  L.place_ind3 n c

theorem proposition34_action_mul (L : LGPBoundary R V)
    (s : Finset V) (x y : ∀ p, L.strip.Mon p) :
    L.strip.totalDegree s (fun p => x p * y p) =
      L.strip.totalDegree s x + L.strip.totalDegree s y := by
  exact L.strip.totalDegree_mul s x y

theorem proposition34_action_one (L : LGPBoundary R V)
    (p : V) (x : L.strip.Mon p) :
    L.strip.action p 1 x = x := by
  exact L.strip.action_one p x

theorem proposition34_total_degree_one (L : LGPBoundary R V)
    (s : Finset V) : L.strip.totalDegree s (fun _ => 1) = 0 := by
  exact L.strip.totalDegree_one s

theorem proposition34_profile_round_trip (L : LGPBoundary R V)
    (c : Choice) :
    L.strip.degree (L.place c)
        (L.strip.action (L.place c) (L.groupElement c)
          (L.strip.action (L.place c) 1 (L.monElement c))) = L.profile c := by
  rw [L.strip.action_one, L.action_profile]

theorem proposition34_profile_stable (L : LGPBoundary R V)
    (c : Choice) :
    L.strip.degree (L.place c) (L.monElement c) =
      L.strip.degree (L.place c)
        (L.strip.action (L.place c) (L.groupElement c)
          (L.monElement c)) := by
  rw [L.action_transport]

structure VolumeBoundary (R : SourceTheorem311Realization l Label Choice) where
  latticeIndex : Choice → Nat
  latticeIndex_pos : ∀ c, 0 < latticeIndex c
  lattice_bound : ∀ c,
    R.packet.logVolume c ≤ latticeIndex c

def proposition39
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) : SourceProposition39Volume Choice where
  determinant := R.packet.determinant
  logVolume := R.packet.logVolume
  positive := R.packet.determinant_positive
  log_determinant := R.packet.log_determinant
  tensorPower := fun c n => R.packet.determinant c ^ n
  tensorPower_zero := by
    intro c
    simp
  tensorPower_succ := by
    intro c n
    rw [pow_succ]
  tensorPower_positive := by
    intro c n
    exact pow_pos (R.packet.determinant_positive c) n
  tensorPower_log := by
    intro c n
    rw [Real.log_pow, R.packet.log_determinant]
  latticeIndex := B.latticeIndex
  latticeIndex_pos := B.latticeIndex_pos
  lattice_bound := B.lattice_bound

@[simp] theorem proposition39_determinant
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) (c : Choice) :
    (proposition39 R B).determinant c = R.packet.determinant c := rfl

@[simp] theorem proposition39_log_volume
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) (c : Choice) :
    (proposition39 R B).logVolume c = R.packet.logVolume c := rfl

theorem proposition39_positive
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) (c : Choice) :
    0 < (proposition39 R B).determinant c :=
  (proposition39 R B).positive c

theorem proposition39_nonzero
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) (c : Choice) :
    (proposition39 R B).determinant c ≠ 0 :=
  ne_of_gt (proposition39_positive R B c)

theorem proposition39_tensor_zero
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) (c : Choice) :
    (proposition39 R B).tensorPower c 0 = 1 := by
  exact (proposition39 R B).tensorPower_zero c

theorem proposition39_tensor_succ
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) (c : Choice) (n : Nat) :
    (proposition39 R B).tensorPower c (n + 1) =
      (proposition39 R B).tensorPower c n *
        (proposition39 R B).determinant c := by
  exact (proposition39 R B).tensorPower_succ c n

theorem proposition39_tensor_positive
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) (c : Choice) (n : Nat) :
    0 < (proposition39 R B).tensorPower c n :=
  (proposition39 R B).tensorPower_positive c n

theorem proposition39_tensor_log
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) (c : Choice) (n : Nat) :
    Real.log ((proposition39 R B).tensorPower c n) =
      n * (proposition39 R B).logVolume c :=
  (proposition39 R B).tensorPower_log c n

theorem proposition39_lattice_positive
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) (c : Choice) :
    0 < (proposition39 R B).latticeIndex c :=
  (proposition39 R B).latticeIndex_pos c

theorem proposition39_lattice_bound
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) (c : Choice) :
    (proposition39 R B).logVolume c ≤ (proposition39 R B).latticeIndex c :=
  (proposition39 R B).lattice_bound c

theorem proposition39_log_determinant_volume
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) (c : Choice) :
    Real.log ((proposition39 R B).determinant c) =
      (proposition39 R B).logVolume c :=
  (proposition39 R B).log_determinant c

theorem proposition39_tensor_one
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) (c : Choice) :
    (proposition39 R B).tensorPower c 1 =
      (proposition39 R B).determinant c := by
  simpa using SourceProposition39Volume.tensor_power_one
    (proposition39 R B) c

theorem proposition39_tensor_two
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) (c : Choice) :
    (proposition39 R B).tensorPower c 2 =
      (proposition39 R B).determinant c *
        (proposition39 R B).determinant c := by
  simpa using SourceProposition39Volume.tensor_power_two
    (proposition39 R B) c

theorem proposition39_tensor_three
    (R : SourceTheorem311Realization l Label Choice)
    (B : VolumeBoundary R) (c : Choice) :
    (proposition39 R B).tensorPower c 3 =
      (proposition39 R B).determinant c *
        (proposition39 R B).determinant c *
        (proposition39 R B).determinant c := by
  simpa using SourceProposition39Volume.tensor_power_three
    (proposition39 R B) c

end SourceP1

/-! ## 5. P2 constructors: Theorem 1.5, Proposition 2.1, Corollary 2.3 -/

namespace SourceP2

variable {R : SourceTheorem311Realization.{u, v, w} l Label Choice}

def theorem15
    (R : SourceTheorem311Realization l Label Choice) :
    SourceTheorem15Coricity R.procession where
  vertical := R.procession.ind3
  horizontal := R.procession.ind1
  vertical_eq_ind3 := by intro n c; rfl
  horizontal_eq_ind1 := by intro g c; rfl
  vertical_level := R.procession.ind3_level
  horizontal_level := R.procession.ind1_level
  vertical_source := R.procession.ind3_index
  horizontal_source := R.procession.ind1_index
  vertical_add := R.procession.ind3_add
  horizontal_add := R.procession.ind1_add
  horizontal_vertical_commute := R.procession.ind1_ind3_commute
  vertical_horizontal_commute := by
    intro g n c
    exact (R.procession.ind1_ind3_commute g n c).symm
  vertical_zero := R.procession.ind3_zero
  horizontal_zero := R.procession.ind1_zero

theorem theorem15_vertical_at
    (R : SourceTheorem311Realization l Label Choice)
    (n : Nat) (c : Choice) :
    (theorem15 R).vertical n c = R.procession.ind3 n c := rfl

theorem theorem15_horizontal_at
    (R : SourceTheorem311Realization l Label Choice)
    (g : Label) (c : Choice) :
    (theorem15 R).horizontal g c = R.procession.ind1 g c := rfl

theorem theorem15_vertical_zero
    (R : SourceTheorem311Realization l Label Choice) (c : Choice) :
    (theorem15 R).vertical 0 c = c :=
  (theorem15 R).vertical_zero c

theorem theorem15_horizontal_zero
    (R : SourceTheorem311Realization l Label Choice) (c : Choice) :
    (theorem15 R).horizontal 0 c = c :=
  (theorem15 R).horizontal_zero c

theorem theorem15_vertical_level
    (R : SourceTheorem311Realization l Label Choice)
    (n : Nat) (c : Choice) :
    R.procession.level c ≤ R.procession.level ((theorem15 R).vertical n c) :=
  (theorem15 R).vertical_level n c

theorem theorem15_horizontal_level
    (R : SourceTheorem311Realization l Label Choice)
    (g : Label) (c : Choice) :
    R.procession.level ((theorem15 R).horizontal g c) =
      R.procession.level c :=
  (theorem15 R).horizontal_level g c

theorem theorem15_vertical_source
    (R : SourceTheorem311Realization l Label Choice)
    (n : Nat) (c : Choice) :
    R.procession.source_index ((theorem15 R).vertical n c) =
      R.procession.source_index c :=
  (theorem15 R).vertical_source n c

theorem theorem15_horizontal_source
    (R : SourceTheorem311Realization l Label Choice)
    (g : Label) (c : Choice) :
    R.procession.source_index ((theorem15 R).horizontal g c) =
      R.procession.source_index c :=
  (theorem15 R).horizontal_source g c

theorem theorem15_vertical_add
    (R : SourceTheorem311Realization l Label Choice)
    (m n : Nat) (c : Choice) :
    (theorem15 R).vertical (m + n) c =
      (theorem15 R).vertical n ((theorem15 R).vertical m c) :=
  (theorem15 R).vertical_add m n c

theorem theorem15_horizontal_add
    (R : SourceTheorem311Realization l Label Choice)
    (g h : Label) (c : Choice) :
    (theorem15 R).horizontal (g + h) c =
      (theorem15 R).horizontal h ((theorem15 R).horizontal g c) :=
  (theorem15 R).horizontal_add g h c

theorem theorem15_horizontal_vertical
    (R : SourceTheorem311Realization l Label Choice)
    (g : Label) (n : Nat) (c : Choice) :
    (theorem15 R).horizontal g ((theorem15 R).vertical n c) =
      (theorem15 R).vertical n ((theorem15 R).horizontal g c) :=
  (theorem15 R).horizontal_vertical_commute g n c

theorem theorem15_vertical_horizontal
    (R : SourceTheorem311Realization l Label Choice)
    (g : Label) (n : Nat) (c : Choice) :
    (theorem15 R).vertical n ((theorem15 R).horizontal g c) =
      (theorem15 R).horizontal g ((theorem15 R).vertical n c) :=
  (theorem15 R).vertical_horizontal_commute g n c

/-! Proposition 2.1 needs its labelled map together with degree and
evaluation transport.  The fields below are deliberately source-facing. -/

structure KummerBoundary
    (R : SourceTheorem311Realization l Label Choice) where
  correspondence : LabelledKummerIso Choice Choice
  degree : Choice → Nat
  degree_inverse : Choice → Nat
  degree_map : ∀ a,
    degree_inverse (correspondence.map a) = degree a
  degree_inverse_map : ∀ b,
    degree (correspondence.inverse b) = degree_inverse b
  evaluation : Choice → Real
  evaluation_target : Choice → Real
  evaluation_map : ∀ a,
    evaluation_target (correspondence.map a) = evaluation a
  evaluation_inverse : ∀ b,
    evaluation (correspondence.inverse b) = evaluation_target b
  q_parameter : Real
  q_positive : 0 < q_parameter
  q_log : Choice → Real
  q_log_map : ∀ a,
    q_log (correspondence.inverse (correspondence.map a)) = q_log a

def proposition21
    (K : KummerBoundary R) :
    SourceProposition21Kummer Choice Choice where
  correspondence := K.correspondence
  degree := K.degree
  degree_inverse := K.degree_inverse
  degree_map := K.degree_map
  degree_inverse_map := K.degree_inverse_map
  evaluation := K.evaluation
  evaluation_target := K.evaluation_target
  evaluation_map := K.evaluation_map
  evaluation_inverse := K.evaluation_inverse
  q_parameter := K.q_parameter
  q_positive := K.q_positive
  q_log := K.q_log
  q_log_map := K.q_log_map

theorem proposition21_correspondence
    (K : KummerBoundary R) :
    (proposition21 K).correspondence = K.correspondence := rfl

theorem proposition21_map_left
    (K : KummerBoundary R) (a : Choice) :
    K.correspondence.inverse (K.correspondence.map a) = a :=
  K.correspondence.left_inverse a

theorem proposition21_map_right
    (K : KummerBoundary R) (b : Choice) :
    K.correspondence.map (K.correspondence.inverse b) = b :=
  K.correspondence.right_inverse b

theorem proposition21_map_injective
    (K : KummerBoundary R) :
    Function.Injective K.correspondence.map :=
  K.correspondence.map_injective

theorem proposition21_map_surjective
    (K : KummerBoundary R) :
    Function.Surjective K.correspondence.map :=
  K.correspondence.map_surjective

theorem proposition21_map_bijective
    (K : KummerBoundary R) :
    Function.Bijective K.correspondence.map :=
  ⟨K.correspondence.map_injective, K.correspondence.map_surjective⟩

theorem proposition21_degree_map
    (K : KummerBoundary R) (a : Choice) :
    K.degree_inverse (K.correspondence.map a) = K.degree a :=
  K.degree_map a

theorem proposition21_degree_inverse
    (K : KummerBoundary R) (b : Choice) :
    K.degree (K.correspondence.inverse b) = K.degree_inverse b :=
  K.degree_inverse_map b

theorem proposition21_evaluation_map
    (K : KummerBoundary R) (a : Choice) :
    K.evaluation_target (K.correspondence.map a) = K.evaluation a :=
  K.evaluation_map a

theorem proposition21_evaluation_inverse
    (K : KummerBoundary R) (b : Choice) :
    K.evaluation (K.correspondence.inverse b) =
      K.evaluation_target b :=
  K.evaluation_inverse b

theorem proposition21_q_positive
    (K : KummerBoundary R) : 0 < K.q_parameter :=
  K.q_positive

theorem proposition21_q_nonzero
    (K : KummerBoundary R) : K.q_parameter ≠ 0 :=
  ne_of_gt K.q_positive

theorem proposition21_q_log_transport
    (K : KummerBoundary R) (a : Choice) :
    K.q_log (K.correspondence.inverse (K.correspondence.map a)) =
      K.q_log a :=
  K.q_log_map a

theorem proposition21_degree_round_trip
    (K : KummerBoundary R) (a : Choice) :
    K.degree (K.correspondence.inverse (K.correspondence.map a)) =
      K.degree a := by
  rw [proposition21_map_left K a]

theorem proposition21_evaluation_round_trip
    (K : KummerBoundary R) (a : Choice) :
    K.evaluation (K.correspondence.inverse (K.correspondence.map a)) =
      K.evaluation a := by
  rw [proposition21_map_left K a]

theorem proposition21_target_round_trip
    (K : KummerBoundary R) (b : Choice) :
    K.evaluation_target (K.correspondence.map
      (K.correspondence.inverse b)) = K.evaluation_target b := by
  rw [proposition21_map_right K b]

theorem proposition21_degree_map_cancel
    (K : KummerBoundary R) (a : Choice) :
    K.degree_inverse (K.correspondence.map a) =
      K.degree (K.correspondence.inverse (K.correspondence.map a)) := by
  rw [proposition21_map_left K a]
  exact K.degree_map a

theorem proposition21_evaluation_map_cancel
    (K : KummerBoundary R) (a : Choice) :
    K.evaluation_target (K.correspondence.map a) =
      K.evaluation (K.correspondence.inverse (K.correspondence.map a)) := by
  rw [proposition21_map_left K a]
  exact K.evaluation_map a

theorem proposition21_degree_inverse_cancel
    (K : KummerBoundary R) (b : Choice) :
    K.degree (K.correspondence.inverse b) =
      K.degree_inverse (K.correspondence.map
        (K.correspondence.inverse b)) := by
  rw [proposition21_map_right K b]
  exact K.degree_inverse_map b

theorem proposition21_evaluation_inverse_cancel
    (K : KummerBoundary R) (b : Choice) :
    K.evaluation (K.correspondence.inverse b) =
      K.evaluation_target (K.correspondence.map
        (K.correspondence.inverse b)) := by
  rw [proposition21_map_right K b]
  exact K.evaluation_inverse b

structure PermutationBoundary
    (R : SourceTheorem311Realization l Label Choice) where
  spoke : Choice → Choice
  spoke_permutation : ∀ c,
    spoke (R.genericFamily.permutation c) = spoke c

def corollary23
    (K : PermutationBoundary R) :
    SourceCorollary23Permutation Choice Choice where
  theater := R.genericFamily.theater
  permutation := R.genericFamily.permutation
  theater_injective := R.genericFamily.distinct
  link := R.genericFamily.link
  link_refl := R.genericFamily.link_refl
  link_trans := R.genericFamily.link_trans
  permutation_link := R.genericFamily.permutation_naturality
  spoke := K.spoke
  spoke_permutation := K.spoke_permutation

theorem corollary23_theater
    (K : PermutationBoundary R) (c : Choice) :
    (corollary23 K).theater c = R.genericFamily.theater c := rfl

theorem corollary23_permutation
    (K : PermutationBoundary R) :
    (corollary23 K).permutation = R.genericFamily.permutation := rfl

theorem corollary23_link
    (K : PermutationBoundary R) (c d : Choice) (t : Choice) :
    (corollary23 K).link c d t = R.genericFamily.link c d t := rfl

theorem corollary23_spoke
    (K : PermutationBoundary R) (c : Choice) :
    (corollary23 K).spoke c = K.spoke c := rfl

theorem corollary23_theater_injective
    (K : PermutationBoundary R) :
    Function.Injective (corollary23 K).theater :=
  (corollary23 K).theater_injective

theorem corollary23_permutation_bijective
    (K : PermutationBoundary R) :
    Function.Bijective (corollary23 K).permutation :=
  (corollary23 K).permutation.bijective

theorem corollary23_link_refl
    (K : PermutationBoundary R) (c : Choice) (t : Choice) :
    (corollary23 K).link c c t = t :=
  (corollary23 K).link_refl c t

theorem corollary23_link_trans
    (K : PermutationBoundary R) (c d e : Choice) (t : Choice) :
    (corollary23 K).link d e ((corollary23 K).link c d t) =
      (corollary23 K).link c e t :=
  (corollary23 K).link_trans c d e t

theorem corollary23_permutation_link
    (K : PermutationBoundary R) (c : Choice) (t : Choice) :
    (corollary23 K).link ((corollary23 K).permutation c)
        ((corollary23 K).permutation c) t =
      (corollary23 K).link c c t :=
  (corollary23 K).permutation_link c t

theorem corollary23_spoke_permutation
    (K : PermutationBoundary R) (c : Choice) :
    (corollary23 K).spoke ((corollary23 K).permutation c) =
      (corollary23 K).spoke c :=
  (corollary23 K).spoke_permutation c

theorem corollary23_permutation_inverse_spoke
    (K : PermutationBoundary R) (c : Choice) :
    (corollary23 K).spoke ((corollary23 K).permutation.symm c) =
      (corollary23 K).spoke c := by
  exact SourceCorollary23Permutation.permutation_inverse_spoke
    (corollary23 K) c

end SourceP2

/-! ## 6. P1/P2 assembly and the closed dependency arrow -/

structure SourceP1P2Input
    {l : PrimeGeFive} {V : Type uv}
    {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    {I : OriginalInput.{u, uv, upi, umon, ui} l V}
    {R : SourceTheorem311Realization.{u, v, w} l Label Choice}
    {P : H2SpokePermutation I}
    {X : Type ux} {Y : Type uy}
    [CommMonoid X] [CommMonoid Y]
    (W : SourceInternalWiring I R P X Y)
    where
  lgp : SourceP1.LGPBoundary R V
  volume : SourceP1.VolumeBoundary R
  kummer : SourceP2.KummerBoundary R
  permutation : SourceP2.PermutationBoundary R

namespace SourceP1P2Input

variable {I : OriginalInput.{u, uv, upi, umon, ui} l V}
variable {R : SourceTheorem311Realization.{u, v, w} l Label Choice}
variable {P : H2SpokePermutation I}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable {W : SourceInternalWiring I R P X Y}
variable (S : SourceP1P2Input (I := I) (R := R) (P := P) (X := X) (Y := Y)
  W)
include S

theorem lgp_strip : S.lgp.strip = S.lgp.strip := rfl

theorem lgp_place (c : Choice) : S.lgp.place c = S.lgp.place c := rfl

theorem lgp_profile (c : Choice) : S.lgp.profile c = S.lgp.profile c := rfl

theorem volume_index (c : Choice) :
    S.volume.latticeIndex c = S.volume.latticeIndex c := rfl

theorem volume_index_positive (c : Choice) :
    0 < S.volume.latticeIndex c := S.volume.latticeIndex_pos c

theorem kummer_map (c : Choice) :
    S.kummer.correspondence.map c = S.kummer.correspondence.map c := rfl

theorem permutation_spoke (c : Choice) :
    S.permutation.spoke c = S.permutation.spoke c := rfl

end SourceP1P2Input

structure SourceP1P2Bundle
    {l : PrimeGeFive} {V : Type uv}
    {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    {I : OriginalInput.{u, uv, upi, umon, ui} l V}
    {R : SourceTheorem311Realization.{u, v, w} l Label Choice}
    {P : H2SpokePermutation I}
    {X : Type ux} {Y : Type uy}
    [CommMonoid X] [CommMonoid Y]
    (W : SourceInternalWiring I R P X Y)
    (S : SourceP1P2Input (I := I) (R := R) (P := P) (X := X) (Y := Y) W) where
  theorem15 : SourceTheorem15Coricity R.procession
  proposition21 : SourceProposition21Kummer Choice Choice
  proposition23 : SourceCorollary23Permutation Choice Choice
  proposition32 : SourceProposition32Packet.{u, v, w, w}
    R.procession R.packet
  proposition34 : SourceProposition34LGP Label Choice V
  proposition35 : SourceProposition35Vertical R.procession R.packet R.vertical
  proposition37Local : SourceProposition37Frobenioid X
  proposition37Global : SourceProposition37Frobenioid Y
  proposition39 : SourceProposition39Volume Choice
  proposition310 : SourceProposition310Comparison Choice Choice
  dependency : SourceTheorem311DependencyPackage R
  theorem15_eq : theorem15 = SourceP2.theorem15 R
  proposition21_eq : proposition21 = SourceP2.proposition21 S.kummer
  proposition23_eq : proposition23 = SourceP2.corollary23 S.permutation
  proposition32_eq : proposition32 = SourceP1.proposition32 R
  proposition34_eq : proposition34 = SourceP1.proposition34 S.lgp
  proposition35_eq : proposition35 = SourceP1.proposition35 R
  proposition37Local_eq : proposition37Local = W.k2.localFrobenioid
  proposition37Global_eq : proposition37Global = W.k2.globalFrobenioid
  proposition39_eq : proposition39 = SourceP1.proposition39 R S.volume
  proposition310_eq : proposition310 = W.k2.comparison
  dependency_theorem15_eq : dependency.theorem15 = SourceP2.theorem15 R
  dependency_proposition21_eq :
    dependency.proposition21 = SourceP2.proposition21 S.kummer
  dependency_proposition23_eq :
    dependency.proposition23 = SourceP2.corollary23 S.permutation
  dependency_proposition32_eq :
    dependency.proposition32 = SourceP1.proposition32 R
  dependency_vertical35_eq :
    dependency.vertical35 = SourceP1.proposition35 R
  dependency_proposition39_eq :
    dependency.proposition39 = SourceP1.proposition39 R S.volume
  dependency_proposition310_eq : dependency.proposition310 = W.k2.comparison

namespace SourceP1P2Bundle

variable {I : OriginalInput.{u, uv, upi, umon, ui} l V}
variable {R : SourceTheorem311Realization.{u, v, w} l Label Choice}
variable {P : H2SpokePermutation I}
variable {X : Type ux} {Y : Type uy}
variable [CommMonoid X] [CommMonoid Y]
variable {W : SourceInternalWiring I R P X Y}
variable {S : SourceP1P2Input (I := I) (R := R) (P := P) (X := X) (Y := Y) W}

def assemble
    (W : SourceInternalWiring I R P X Y)
    (S : SourceP1P2Input (I := I) (R := R) (P := P) (X := X) (Y := Y) W) :
      SourceP1P2Bundle W S where
  theorem15 := SourceP2.theorem15 R
  proposition21 := SourceP2.proposition21 S.kummer
  proposition23 := SourceP2.corollary23 S.permutation
  proposition32 := SourceP1.proposition32 R
  proposition34 := SourceP1.proposition34 S.lgp
  proposition35 := SourceP1.proposition35 R
  proposition37Local := W.k2.localFrobenioid
  proposition37Global := W.k2.globalFrobenioid
  proposition39 := SourceP1.proposition39 R S.volume
  proposition310 := W.k2.comparison
  dependency :=
    { theorem15 := SourceP2.theorem15 R
      proposition21 := SourceP2.proposition21 S.kummer
      proposition23 := SourceP2.corollary23 S.permutation
      proposition32 := SourceP1.proposition32 R
      vertical35 := SourceP1.proposition35 R
      proposition39 := SourceP1.proposition39 R S.volume
      proposition310 := W.k2.comparison
      source_alignment := by
        change R.procession.ind3 0 R.procession.base = R.procession.base
        exact R.procession.ind3_zero R.procession.base
      packet_alignment := by
        rfl
      volume_alignment := by
        rfl
      horizontal_alignment := by
        exact W.k2.comparison.localEqGlobal R.procession.base }
  theorem15_eq := rfl
  proposition21_eq := rfl
  proposition23_eq := rfl
  proposition32_eq := rfl
  proposition34_eq := rfl
  proposition35_eq := rfl
  proposition37Local_eq := rfl
  proposition37Global_eq := rfl
  proposition39_eq := rfl
  proposition310_eq := rfl
  dependency_theorem15_eq := rfl
  dependency_proposition21_eq := rfl
  dependency_proposition23_eq := rfl
  dependency_proposition32_eq := rfl
  dependency_vertical35_eq := rfl
  dependency_proposition39_eq := rfl
  dependency_proposition310_eq := rfl

def canonical
    (A : SourceH1H2Alignment I R)
    (P : H2SpokePermutation I)
    (B : K2FrobenioidBoundary R (k1OfRealization R) X Y)
    (S : SourceP1P2Input (I := I) (R := R) (P := P) (X := X) (Y := Y)
      (SourceInternalWiring.canonical (I := I) (R := R) (X := X) (Y := Y)
        A P B)) :
    SourceP1P2Bundle
      (SourceInternalWiring.canonical (I := I) (R := R) (X := X) (Y := Y)
        A P B) S :=
  assemble _ S

theorem theorem15_recovered (B : SourceP1P2Bundle W S) :
    B.theorem15 = SourceP2.theorem15 R := B.theorem15_eq

theorem proposition21_recovered (B : SourceP1P2Bundle W S) :
    B.proposition21 = SourceP2.proposition21 S.kummer := B.proposition21_eq

theorem proposition23_recovered (B : SourceP1P2Bundle W S) :
    B.proposition23 = SourceP2.corollary23 S.permutation := B.proposition23_eq

theorem proposition32_recovered (B : SourceP1P2Bundle W S) :
    B.proposition32 = SourceP1.proposition32 R := B.proposition32_eq

theorem proposition34_recovered (B : SourceP1P2Bundle W S) :
    B.proposition34 = SourceP1.proposition34 S.lgp := B.proposition34_eq

theorem proposition35_recovered (B : SourceP1P2Bundle W S) :
    B.proposition35 = SourceP1.proposition35 R := B.proposition35_eq

theorem proposition37_local_recovered (B : SourceP1P2Bundle W S) :
    B.proposition37Local = W.k2.localFrobenioid := B.proposition37Local_eq

theorem proposition37_global_recovered (B : SourceP1P2Bundle W S) :
    B.proposition37Global = W.k2.globalFrobenioid := B.proposition37Global_eq

theorem proposition39_recovered (B : SourceP1P2Bundle W S) :
    B.proposition39 = SourceP1.proposition39 R S.volume := B.proposition39_eq

theorem proposition310_recovered (B : SourceP1P2Bundle W S) :
    B.proposition310 = W.k2.comparison := B.proposition310_eq

theorem dependency_recovered (B : SourceP1P2Bundle W S) :
    B.dependency.theorem15 = SourceP2.theorem15 R := B.dependency_theorem15_eq

theorem dependency_proposition21 (B : SourceP1P2Bundle W S) :
    B.dependency.proposition21 = SourceP2.proposition21 S.kummer :=
  B.dependency_proposition21_eq

theorem dependency_proposition23 (B : SourceP1P2Bundle W S) :
    B.dependency.proposition23 = SourceP2.corollary23 S.permutation :=
  B.dependency_proposition23_eq

theorem dependency_proposition32 (B : SourceP1P2Bundle W S) :
    B.dependency.proposition32 = SourceP1.proposition32 R :=
  B.dependency_proposition32_eq

theorem dependency_vertical35 (B : SourceP1P2Bundle W S) :
    B.dependency.vertical35 = SourceP1.proposition35 R :=
  B.dependency_vertical35_eq

theorem dependency_proposition39 (B : SourceP1P2Bundle W S) :
    B.dependency.proposition39 = SourceP1.proposition39 R S.volume :=
  B.dependency_proposition39_eq

theorem dependency_proposition310 (B : SourceP1P2Bundle W S) :
    B.dependency.proposition310 = W.k2.comparison :=
  B.dependency_proposition310_eq

theorem dependency_source_alignment (B : SourceP1P2Bundle W S) :
    B.dependency.theorem15.vertical 0 R.procession.base =
      R.procession.base := by
  exact B.dependency.source_alignment

theorem dependency_packet_alignment (B : SourceP1P2Bundle W S) :
    B.dependency.proposition32.profile R.procession.base =
      R.packet.logVolume R.procession.base := by
  exact B.dependency.packet_alignment

theorem dependency_volume_alignment (B : SourceP1P2Bundle W S) :
    B.dependency.proposition39.logVolume R.procession.base =
      R.packet.logVolume R.procession.base := by
  exact B.dependency.volume_alignment

theorem dependency_horizontal_alignment (B : SourceP1P2Bundle W S) :
    B.dependency.proposition310.localMap R.procession.base =
      B.dependency.proposition310.globalMap R.procession.base := by
  exact B.dependency.horizontal_alignment

theorem dependency_output (B : SourceP1P2Bundle W S) :
    B.dependency.output = R.output := rfl

theorem dependency_output_source (B : SourceP1P2Bundle W S) :
    B.dependency.output.source = R.input.core.base := by
  exact B.dependency.output_source

theorem dependency_output_quotient (B : SourceP1P2Bundle W S) :
    B.dependency.output.quotient =
      quotientMap R.input B.dependency.output.source := by
  exact B.dependency.output_quotient

theorem dependency_output_labelled (B : SourceP1P2Bundle W S) (c : Choice) :
    Function.Bijective (R.input.labelledKummer c).map := by
  exact B.dependency.output_labelled c

theorem dependency_output_ind3 (B : SourceP1P2Bundle W S)
    (n : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.input.profile.possibleImage c) :
    ∃ y, y ∈ R.input.profile.possibleImage (R.input.core.ind3 n c) ∧
      z ≤ y := by
  exact B.dependency.output_ind3 n c z hz

theorem dependency_output_horizontal (B : SourceP1P2Bundle W S)
    (c : Choice) :
    R.input.horizontal.upper (R.input.horizontal.left c) =
      R.input.horizontal.right (R.input.horizontal.lower c) := by
  exact B.dependency.output_horizontal c

theorem dependency_output_evaluation (B : SourceP1P2Bundle W S)
    (c : Choice) :
    R.input.evaluation.localMap (R.input.horizontal.left c) =
      R.input.horizontal.right
        (R.input.evaluation.localMap (R.input.horizontal.lower c)) := by
  exact B.dependency.output_evaluation c

theorem dependency_output_parts (B : SourceP1P2Bundle W S) :
    B.dependency.output.part_i = partI R.input ∧
      B.dependency.output.part_ii = partII R.input ∧
      B.dependency.output.part_iii = partIII R.input := by
  exact B.dependency.output_parts

/-! ## 7. Explicit arrows from H1/H2 through K1/K2 to P1/P2 -/

theorem arrow_h1_to_h2 (B : SourceP1P2Bundle W S) :
    W.h2.h1 = W.h1 := W.h2_h1

theorem arrow_h2_to_realization_source (B : SourceP1P2Bundle W S) :
    HEq R.procession.hodge.source I.initial := W.alignment_source

theorem arrow_h2_to_realization_index (B : SourceP1P2Bundle W S)
    (c : Choice) :
    W.alignment.hodgeIndex (R.procession.source_index c) =
      W.alignment.choiceFamilyIndex c :=
  W.source_to_family_index c

theorem arrow_h2_to_realization_q (B : SourceP1P2Bundle W S)
    (c : Choice) :
    R.procession.hodge.qParameter (R.procession.source_index c) =
      (I.family.theater (W.alignment.choiceFamilyIndex c)).thetaPacket.q := by
  rw [W.source_to_hodge_index]
  simpa [W.alignment.choice_index_at c] using
    W.alignment.q_at (W.alignment.choiceHodgeIndex c)

theorem arrow_h2_to_realization_scale (B : SourceP1P2Bundle W S)
    (c : Choice) (x : SignedLabel l.value) :
    R.procession.hodge.scale (R.procession.source_index c) x =
      (I.family.theater (W.alignment.choiceFamilyIndex c)).thetaPacket.scale x := by
  rw [W.source_to_hodge_index]
  simpa [W.alignment.choice_index_at c] using
    W.alignment.scale_at (W.alignment.choiceHodgeIndex c) x

theorem arrow_h2_to_realization_permutation (B : SourceP1P2Bundle W S)
    (c : Choice) :
    I.family.permutation (W.alignment.choiceFamilyIndex c) =
      W.alignment.choiceFamilyIndex (R.genericFamily.permutation c) :=
  W.h2_permutation_to_generic c

theorem arrow_realization_to_k1 (B : SourceP1P2Bundle W S) :
    W.k1 = k1OfRealization R := W.k1_source

theorem arrow_k1_to_k2 (B : SourceP1P2Bundle W S) :
    W.k2.upperSemi = W.k1.vertical := W.k2.upperSemi_recovered

theorem arrow_k2_to_prop35 (B : SourceP1P2Bundle W S)
    (m : Nat) (c : Choice) (z : Real)
    (hz : z ∈ R.packet.possibleImage c) :
    ∃ y, y ∈ R.packet.possibleImage (R.procession.ind3 m c) ∧ z ≤ y := by
  exact SourceP1.proposition35_nonarch_upper R m c z hz

theorem arrow_k2_to_prop310 (B : SourceP1P2Bundle W S) :
    B.proposition310.localMap = W.k2.comparison.localMap := by
  rw [B.proposition310_eq]

theorem arrow_prop32_to_prop39 (B : SourceP1P2Bundle W S)
    (c : Choice) :
    B.proposition32.profile c =
      B.proposition39.logVolume c := by
  rw [B.proposition32_recovered, B.proposition39_recovered]
  rfl

end SourceP1P2Bundle

/-! Completed source-wiring marker.  This marker is subordinate to the
explicit records above; it is not a theorem about arbitrary arithmetic input. -/

theorem source_internal_wiring_status : True := by
  trivial

end Theorem311Source
end
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def theorem311InternalWiring : Obligation :=
  { id := "IUT-III.theorem-3.11-internal-wiring"
    source :=
      "IUT III Theorem 1.5, Proposition 2.1, Corollary 2.3, " ++
        "Propositions 3.2, 3.4, 3.5, 3.7, 3.9, 3.10"
    status := VerificationStatus.interface
    note :=
      "SourceH1H2Alignment explicitly connects the original Hodge family " ++
        "to the realization index/carrier, links, q/scale data, and " ++
        "permutation. SourceInternalWiring then consumes canonical H1/H2, " ++
        "the realization-projected K1 boundary, and the supplied K2 boundary. " ++
        "P1/P2 constructors build packet, vertical, tensor-power, coricity, " ++
        "Kummer, permutation, and comparison outputs. Arithmetic-geometric " ++
        "existence remains an explicit source boundary."
    dependsOn :=
      [ "IUT-III.source-h1-h2-construction",
        "IUT-III.source-theorem311-realization",
        "IUT-III.K1.vertical-log-kummer-boundary",
        "IUT-III.K2.frobenioid-mod-realification-boundary" ] }

end LeanFormal.IUT.Audit
